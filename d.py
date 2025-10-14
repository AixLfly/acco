#!/usr/bin/env python
# -*- coding: utf-8 -*-

# --- GUI IMPORTS ---
import tkinter as tk
from tkinter import filedialog, scrolledtext, messagebox
import ttkbootstrap as ttk
from ttkbootstrap.constants import *
from ttkbootstrap.scrolled import ScrolledFrame
import queue
import threading
import os
import subprocess
import sys
import hashlib

# --- CORE SCRIPT IMPORTS ---
import asyncio
import logging
import random
import re
from pathlib import Path
from urllib.parse import urlparse
import time

import httpx
import pandas as pd
import pdfplumber
from playwright.async_api import async_playwright, Error as PlaywrightError
from bs4 import BeautifulSoup # <-- 已添加 BeautifulSoup 导入

try:
    import lxml
except ImportError:
    print("警告: HTML解析库 'lxml' 未找到。请运行 'pip install lxml' 进行安装。")

# ================================================================================================
# ==                      CORE SCANNING LOGIC                                                   ==
# ================================================================================================

logger = logging.getLogger(__name__)

# --- MODIFICATION: Default values, can be overridden by settings UI ---
SEARCH_KEYWORDS = ["身份证", "奖学金", "公示", "名单", "学号", "联系方式"]
BLACKLIST = ["课表", "选课", "培养方案", "招聘", "引进", "聘用", "应聘", "面试",
             "采购", "招标", "中标", "预算", "决算", "项目", "会议", "供应商", "教材","统一身份认证平台","智慧校园","登录"]

TITLE_FILTER_KEYWORDS = ["奖学金", "助学金", "名单", "公示", "评审表", "毕业生", "拟录取", "联系", "通讯录"]
SENSITIVE_KEYWORDS = {"学号", "身份证", "手机", "邮箱"}
GENERAL_KEYWORDS = {"名单", "信息", "表", "公示", "通讯录"}
# --- END MODIFICATION ---

CHINESE_NAME_REGEX = re.compile(r'[\u4e00-\u9fa5]{2,4}')
ID_LIKE_NUMBER_REGEX = re.compile(r'(?<!\d)(?!\d{11}(?!\d))\d{8,}(?!\d)')


def check_title_is_relevant(title: str) -> bool:
    return any(keyword in title for keyword in TITLE_FILTER_KEYWORDS)


def check_content_is_relevant(snippet: str) -> bool:
    contains_sensitive = any(kw in snippet for kw in SENSITIVE_KEYWORDS)
    contains_general = any(kw in snippet for kw in GENERAL_KEYWORDS)
    contains_name = CHINESE_NAME_REGEX.search(snippet)
    contains_long_num = ID_LIKE_NUMBER_REGEX.search(snippet)

    if contains_sensitive and (contains_name or contains_long_num):
        return True
    if contains_general:
        return True
    if contains_name and contains_long_num:
        return True
    return False


_ID_CARD_PATTERN = r'[1-9]\d{5}(?:18|19|20)\d{2}(?:0[1-9]|1[0-2])(?:0[1-9]|[12]\d|3[01])\d{3}[0-9Xx]'
PDF_ID_CARD_CONTEXT_REGEX = re.compile(r'(?:居民身份证号|居民身份证|身份证号码|身份证号|身份证)\s*[:：]?\s*(' + _ID_CARD_PATTERN + r')')
ID_CARD_FORMAT_REGEX = re.compile(r'^' + _ID_CARD_PATTERN + r'$')
ID_LAST6_REGEX = re.compile(r'^\d{5}[\dxX]$')
STUDENT_ID_FORMAT_REGEX = re.compile(r'^\d{4,20}$')
PDF_STUDENT_ID_CONTEXT_REGEX = re.compile(r'(?:学号|学生证号)\s*[:：]?\s*(\d{4,20})')
PDF_NAME_STUDENT_ID_REGEX = re.compile(r'([\u4e00-\u9fa5]{2,4})\s+(\d{8,20})')
PHONE_REGEX = re.compile(r'1[3-9]\d{9}')
EMAIL_REGEX = re.compile(r'\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Z|a-z]{2,}\b')
NAME_PHONE_REGEX = re.compile(r'([\u4e00-\u9fa5]{2,4})\s*[:：]?\s*(1[3-9]\d{9})')
NAME_EMAIL_REGEX = re.compile(r'([\u4e00-\u9fa5]{2,4})\s*[:：]?\s*([A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Z|a-z]{2,})')

MIN_FILE_SIZE = 256
MAX_PDF_PAGES = 10
MAX_XLS_SHEETS = 4
HEADER_RANGE = 5
ID_HEADERS = {"身份证", "身份证号", "身份证号码", "居民身份证", "居民身份证号"}
STUDENT_ID_HEADERS = {"学号", "学生证号"}
PHONE_EMAIL_HEADERS = {"手机", "电话", "联系方式", "邮箱", "email", "e-mail"}
NAME_HEADERS = {"姓名", "联系人"}

MAX_CONCURRENT_TASKS = 25
semaphore = asyncio.Semaphore(MAX_CONCURRENT_TASKS)

domain_reports = {}
report_lock = threading.Lock()
ssl_failed_domains = set()


def is_valid_id_full(id_str: str) -> bool:
    if not isinstance(id_str, str) or not ID_CARD_FORMAT_REGEX.fullmatch(id_str):
        return False
    factors = [7, 9, 10, 5, 8, 4, 2, 1, 6, 3, 7, 9, 10, 5, 8, 4, 2]
    checksum_map = {0: '1', 1: '0', 2: 'X', 3: '9', 4: '8', 5: '7', 6: '6', 7: '5', 8: '4', 9: '3', 10: '2'}
    try:
        body = id_str[:-1]
        s = sum(int(a) * b for a, b in zip(body, factors))
        return id_str[-1].upper() == checksum_map[s % 11]
    except (ValueError, KeyError):
        return False


def is_valid_id_last6(id_str: str) -> bool:
    return isinstance(id_str, str) and bool(ID_LAST6_REGEX.fullmatch(id_str))


def is_valid_student_id_format(id_str: str) -> bool:
    return isinstance(id_str, str) and bool(STUDENT_ID_FORMAT_REGEX.fullmatch(id_str)) and '*' not in id_str


def extract_pdf_ids(file_path: Path, collect_contacts: bool) -> tuple[dict, dict, dict, list]:
    full_ids, last6_ids, student_ids = {}, {}, {}
    phone_email_results = []
    try:
        with pdfplumber.open(file_path) as pdf:
            for page_num, page in enumerate(pdf.pages[:MAX_PDF_PAGES], 1):
                # Always extract IDs and Student IDs
                for table in page.extract_tables():
                    if not table or len(table) < 2: continue
                    header = [str(cell).strip() if cell else "" for cell in table[0]]
                    id_cols = [i for i, col in enumerate(header) if any(h in col for h in ID_HEADERS)]
                    student_id_cols = [i for i, col in enumerate(header) if any(h in col for h in STUDENT_ID_HEADERS)]
                    for col_idx in id_cols:
                        for row in table[1:]:
                            if len(row) > col_idx and row[col_idx]:
                                cell = str(row[col_idx]).strip().split('.')[0]
                                if is_valid_id_full(cell): full_ids[f"第{page_num}页-表格"] = full_ids.get(f"第{page_num}页-表格", 0) + 1
                                elif len(cell) >= 6 and is_valid_id_last6(cell[-6:].upper()): last6_ids[f"第{page_num}页-表格"] = last6_ids.get(f"第{page_num}页-表格", 0) + 1
                    for col_idx in student_id_cols:
                        for row in table[1:]:
                            if len(row) > col_idx and row[col_idx]:
                                cell = str(row[col_idx]).strip().split('.')[0]
                                if is_valid_student_id_format(cell):
                                    student_ids[f"第{page_num}页-表格"] = student_ids.get(f"第{page_num}页-表格", 0) + 1
                    # Conditionally extract contact info
                    if collect_contacts:
                        name_cols = [i for i, col in enumerate(header) if any(h in col for h in NAME_HEADERS)]
                        phone_email_cols = [i for i, col in enumerate(header) if any(h in col for h in PHONE_EMAIL_HEADERS)]
                        if name_cols and phone_email_cols:
                            name_col_idx = name_cols[0]
                            for pe_col_idx in phone_email_cols:
                                for row in table[1:]:
                                    if len(row) > name_col_idx and len(row) > pe_col_idx and row[name_col_idx] and row[pe_col_idx]:
                                        name = str(row[name_col_idx]).strip()
                                        contact_info = str(row[pe_col_idx]).strip()
                                        if name and (PHONE_REGEX.search(contact_info) or EMAIL_REGEX.search(contact_info)):
                                            phone_email_results.append(f"{name}: {contact_info}")

                text = page.extract_text() or ""
                for match in PDF_ID_CARD_CONTEXT_REGEX.finditer(text):
                    if is_valid_id_full(match.group(1)): full_ids[f"第{page_num}页-文本"] = full_ids.get(f"第{page_num}页-文本", 0) + 1
                for match in PDF_STUDENT_ID_CONTEXT_REGEX.finditer(text):
                    if is_valid_student_id_format(match.group(1)): student_ids[f"第{page_num}页-文本"] = student_ids.get(f"第{page_num}页-文本", 0) + 1
                for match in PDF_NAME_STUDENT_ID_REGEX.finditer(text):
                    if is_valid_student_id_format(match.group(2)): student_ids[f"第{page_num}页-文本(姓名+学号)"] = student_ids.get(f"第{page_num}页-文本(姓名+学号)", 0) + 1

                if collect_contacts:
                    for match in NAME_PHONE_REGEX.finditer(text): phone_email_results.append(f"{match.group(1)}: {match.group(2)}")
                    for match in NAME_EMAIL_REGEX.finditer(text): phone_email_results.append(f"{match.group(1)}: {match.group(2)}")
                    for phone in PHONE_REGEX.findall(text): phone_email_results.append(f"单独手机号: {phone}")
                    for email in EMAIL_REGEX.findall(text): phone_email_results.append(f"单独邮箱: {email}")
    except Exception as e:
        logger.error(f"PDF解析失败: {file_path.name} - {e}")
    return full_ids, last6_ids, student_ids, phone_email_results


def extract_xlsx_ids(file_path: Path, collect_contacts: bool) -> tuple[dict, dict, dict, bool]:
    full_ids, last6_ids, student_ids = {}, {}, {}
    has_phone_email = False
    try:
        with pd.ExcelFile(file_path) as xls:
            for sheet in xls.sheet_names[:MAX_XLS_SHEETS]:
                df = pd.read_excel(xls, sheet_name=sheet, header=None)
                if df.empty: continue
                id_col, student_id_col, header_row = -1, -1, -1
                temp_student_id_col = -1
                for r in range(min(HEADER_RANGE, len(df))):
                    for c in range(len(df.columns)):
                        cell = str(df.iloc[r, c]).strip()
                        if id_col == -1 and any(h in cell for h in ID_HEADERS): id_col = c
                        if temp_student_id_col == -1 and "学号" in cell: temp_student_id_col = c
                        if collect_contacts and not has_phone_email and (any(h in cell for h in PHONE_EMAIL_HEADERS) or any(h in cell for h in NAME_HEADERS)):
                            has_phone_email = True
                    if temp_student_id_col != -1:
                        student_id_col = temp_student_id_col
                        header_row = r
                        break
                if id_col != -1 and header_row == -1:
                        header_row = 0
                start_row = header_row + 1 if header_row != -1 else 0
                if id_col != -1:
                    for cell in df.iloc[start_row:, id_col].dropna():
                        cell_str = str(cell).strip().split('.')[0]
                        if is_valid_id_full(cell_str): full_ids[sheet] = full_ids.get(sheet, 0) + 1
                        elif len(cell_str) >= 6 and is_valid_id_last6(cell_str[-6:].upper()): last6_ids[sheet] = last6_ids.get(sheet, 0) + 1
                if student_id_col != -1 and not student_ids:
                    for cell in df.iloc[start_row:, student_id_col].dropna():
                        cell_str = str(cell).strip().split('.')[0]
                        if cell_str.isdigit() and len(cell_str) >= 4:
                            student_ids['found'] = True
                            break
    except Exception as e:
        logger.error(f"Excel解析失败: {file_path.name} - {e}")
    return full_ids, last6_ids, student_ids, has_phone_email


def extract_html_ids(file_path: Path, collect_contacts: bool) -> tuple[dict, dict, dict, list]:
    full_ids, last6_ids, student_ids = {}, {}, {}
    phone_email_results = []

    # --- 增强的解析逻辑 ---
    # 优先级1：尝试使用Pandas进行结构化解析
    try:
        # 使用更宽容的html5lib解析器
        dfs = pd.read_html(str(file_path), encoding='utf-8', flavor='html5lib')
        for i, df in enumerate(dfs):
            if df.empty: continue
            sheet_name = f"表格-{i+1}"
            id_col, student_id_col, name_col, pe_col, header_row = -1, -1, -1, -1, -1
            for r in range(min(HEADER_RANGE, len(df))):
                for c_idx in range(len(df.columns)):
                    # --- [代码修复] ---
                    # 先获取原始值，然后进行安全的字符串转换，避免NoneType错误
                    header_val = df.columns[c_idx]
                    content_val = df.iloc[r, c_idx]
                    
                    # 如果值是None，则转换为空字符串；否则，正常转换为字符串。
                    # pd.notna() 可以同时处理 None 和 NaN 的情况，更适合Pandas。
                    cell_header = str(header_val) if header_val is not None else ""
                    cell_content = str(content_val) if pd.notna(content_val) else ""
                    
                    # 使用 f-string 进行拼接，更清晰
                    cell = f"{cell_header} {cell_content}"
                    # --- [修复结束] ---

                    if any(h in cell for h in ID_HEADERS): id_col = c_idx
                    if any(h in cell for h in STUDENT_ID_HEADERS): student_id_col = c_idx
                    if collect_contacts:
                        if any(h in cell for h in NAME_HEADERS): name_col = c_idx
                        if any(h in cell for h in PHONE_EMAIL_HEADERS): pe_col = c_idx
                if any(c != -1 for c in [id_col, student_id_col, name_col, pe_col]):
                    header_row = r; break
            if header_row == -1: continue
            data_df = df.iloc[header_row + 1:]
            if id_col != -1:
                for cell in data_df.iloc[:, id_col].dropna():
                    cell_str = str(cell).strip().split('.')[0]
                    if is_valid_id_full(cell_str): full_ids[sheet_name] = full_ids.get(sheet_name, 0) + 1
                    elif len(cell_str) >= 6 and is_valid_id_last6(cell_str[-6:].upper()): last6_ids[sheet_name] = last6_ids.get(sheet_name, 0) + 1
            if student_id_col != -1:
                for cell in data_df.iloc[:, student_id_col].dropna():
                    cell_str = str(cell).strip().split('.')[0]
                    if is_valid_student_id_format(cell_str): student_ids[sheet_name] = student_ids.get(sheet_name, 0) + 1
            if collect_contacts and name_col != -1 and pe_col != -1:
                for _, row in data_df.iterrows():
                    name = str(row.iloc[name_col]).strip()
                    contact = str(row.iloc[pe_col]).strip()
                    if name and contact and (PHONE_REGEX.search(contact) or EMAIL_REGEX.search(contact)):
                            phone_email_results.append(f"{name}: {contact}")
    except ValueError:
        logger.debug(f"在 {file_path.name} 中未找到HTML表格 (Pandas)，将尝试纯文本正则匹配。")
    except Exception as e:
        logger.error(f"Pandas HTML表格解析失败: {file_path.name} - {e}")

    # 优先级2：如果Pandas未找到学号，则使用BeautifulSoup进行强大的纯文本正则匹配
    if not student_ids:
        try:
            html_content = file_path.read_text(encoding='utf-8', errors='ignore')
            soup = BeautifulSoup(html_content, 'lxml') # 使用lxml解析器

            # 关键步骤：提取所有纯文本，并用空格作为分隔符
            # 这会把 `<td>张三</td><td>123</td>` 转换成 "张三 123"
            text = soup.get_text(separator=' ')

            # 在清理后的干净文本上执行正则匹配
            for match in PDF_ID_CARD_CONTEXT_REGEX.finditer(text):
                if is_valid_id_full(match.group(1)): full_ids["页面文本"] = full_ids.get("页面文本", 0) + 1
            for match in PDF_STUDENT_ID_CONTEXT_REGEX.finditer(text):
                if is_valid_student_id_format(match.group(1)): student_ids["页面文本"] = student_ids.get("页面文本", 0) + 1
            
            # 这个正则表达式现在能成功匹配 "姓名 学号" 的组合了
            name_sid_matches = PDF_NAME_STUDENT_ID_REGEX.findall(text)
            valid_student_ids_from_regex = [sid for name, sid in name_sid_matches if is_valid_student_id_format(sid)]
            if valid_student_ids_from_regex:
                student_ids["页面文本(姓名+学号)"] = student_ids.get("页面文本(姓名+学号)", 0) + len(valid_student_ids_from_regex)

            if collect_contacts:
                for match in NAME_PHONE_REGEX.finditer(text): phone_email_results.append(f"{match.group(1)}: {match.group(2)}")
                for match in NAME_EMAIL_REGEX.finditer(text): phone_email_results.append(f"{match.group(1)}: {match.group(2)}")
                for phone in PHONE_REGEX.findall(text): phone_email_results.append(f"单独手机号: {phone}")
                for email in EMAIL_REGEX.findall(text): phone_email_results.append(f"单独邮箱: {email}")
        except Exception as e:
            logger.error(f"HTML纯文本解析失败 (BeautifulSoup): {file_path.name} - {e}")

    return full_ids, last6_ids, student_ids, phone_email_results


def process_file(file_path: Path, title: str, url: str, domain: str, id_card_dir: Path, student_id_dir: Path, phone_email_dir: Path, processed_phone_email: set, collect_contacts: bool):
    full_ids, last6_ids, student_ids, has_phone_email_flag = {}, {}, {}, False
    phone_email_list = []
    suffix = file_path.suffix.lower()

    if suffix == '.pdf':
        full_ids, last6_ids, student_ids, phone_email_list = extract_pdf_ids(file_path, collect_contacts)
    elif suffix in ['.xlsx', '.xls']:
        full_ids, last6_ids, student_ids, has_phone_email_flag = extract_xlsx_ids(file_path, collect_contacts)
    elif suffix in ['.html', '.htm']:
        full_ids, last6_ids, student_ids, phone_email_list = extract_html_ids(file_path, collect_contacts)

    if phone_email_list:
        with report_lock:
            processed_phone_email.update(phone_email_list)

    details, report_type, target_dir = [], "", None
    is_sensitive = False

    if full_ids or last6_ids:
        report_type, target_dir = "身份证", id_card_dir
        if full_ids: details.append(f"完整身份证号: {'; '.join(f'{k}:{v}' for k, v in full_ids.items())}")
        if last6_ids: details.append(f"身份证后6位: {'; '.join(f'{k}:{v}' for k, v in last6_ids.items())}")
        is_sensitive = True
    elif student_ids:
        report_type, target_dir = "学号", student_id_dir
        details.append(f"检测到学号 (来源: {'; '.join(student_ids.keys())})")
        is_sensitive = True
    elif (has_phone_email_flag or phone_email_list) and collect_contacts:
        report_type, target_dir = "手机号和邮箱", phone_email_dir
        is_sensitive = True

    if is_sensitive and target_dir:
        details_str = '; '.join(details) if details else "检测到手机号/邮箱等联系方式"
        logger.warning(f"🚨 敏感文件({report_type}) [{domain}]: {file_path.name} → {details_str}")
        with report_lock:
            domain_reports[domain].append({"file": file_path.name, "title": title, "url": url, "type": report_type, "details": details_str})
        try:
            dst = target_dir / file_path.name
            if dst.exists():
                dst = target_dir / f"{file_path.stem}_{int(time.time())}{file_path.suffix}"
            file_path.rename(dst)
        except Exception as e:
            logger.error(f"移动敏感文件失败: {e}")
    else:
        logger.info(f"✅ 无敏感信息 [{domain}]: {file_path.name}")
        try:
            if file_path.exists():
                file_path.unlink()
        except Exception as e:
            logger.error(f"删除非敏感文件失败: {e}")


def sanitize_name(name: str) -> str:
    return re.sub(r'[\\/*?:"<>|]', '_', name).strip()[:150]


def check_blacklist(title: str, content: str) -> bool:
    return any(word.lower() in (title + ' ' + content).lower() for word in BLACKLIST)


async def download_and_analyze(url: str, title: str, domain: str, download_dir: Path, id_card_dir: Path, student_id_dir: Path, phone_email_dir: Path, file_counter_state: dict, processed_phone_email: set, processed_content_hashes: set, collect_contacts: bool):
    async with semaphore:
        save_path = None
        
        # --- [代码修改] ---
        # 为解决 403 Forbidden 错误，添加模拟浏览器的 HTTP 头部
        parsed_url = urlparse(url)
        headers = {
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36 Edg/120.0.0.0',
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7',
            'Accept-Language': 'zh-CN,zh;q=0.9,en;q=0.8',
            'Referer': f"{parsed_url.scheme}://{parsed_url.netloc}/"
        }
        # --- [修改结束] ---

        with report_lock:
            verify_param = domain not in ssl_failed_domains
        for attempt in range(2):
            try:
                async with httpx.AsyncClient(verify=verify_param, follow_redirects=True, timeout=30) as client:
                    # --- [代码修改] ---
                    # 在 get 请求中加入 headers
                    resp = await client.get(url, headers=headers)
                    # --- [修改结束] ---
                    resp.raise_for_status()

                content_hash = hashlib.md5(resp.content).hexdigest()
                with report_lock:
                    if content_hash in processed_content_hashes:
                        logger.info(f"🔄️ 文件内容重复 (不同URL), 跳过: {url}")
                        return
                    processed_content_hashes.add(content_hash)

                if len(resp.content) < MIN_FILE_SIZE:
                    logger.debug(f"文件过小，跳过: {url}"); return

                content_type = resp.headers.get('content-type', '').lower()
                url_path = Path(urlparse(str(resp.url)).path)
                ext = url_path.suffix.lower()
                final_ext = ""
                if 'html' in content_type or ext in ['.html', '.htm']: final_ext = '.html'
                elif ext in ['.pdf', '.xlsx', '.xls']: final_ext = ext
                elif 'excel' in content_type or 'spreadsheet' in content_type: final_ext = '.xlsx'
                else: logger.debug(f"非目标文件类型({ext if ext else content_type})，跳过: {url}"); return

                with report_lock:
                    save_name = f"{file_counter_state['count']} - {sanitize_name(title)}{final_ext}"
                    file_counter_state['count'] += 1
                save_path = download_dir / save_name
                save_path.write_bytes(resp.content)
                logger.info(f"HTTP下载成功 [{domain}]: {save_path.name}")
                break
            except httpx.ConnectError as e:
                if "CERTIFICATE_VERIFY_FAILED" in str(e) and verify_param:
                    logger.warning(f"🚨 域名 '{domain}' 首次SSL证书验证失败。该域名后续请求将自动禁用验证。")
                    with report_lock: ssl_failed_domains.add(domain)
                    verify_param = False; continue
                else: logger.error(f"下载时发生网络连接错误 ({attempt+1}/2): {url} - {e}"); break
            # 捕获并记录HTTP状态错误（如403, 404等）
            except httpx.HTTPStatusError as e:
                logger.error(f"下载时发生HTTP错误 ({attempt+1}/2): {url} - {e}")
                break
            except Exception as e: 
                logger.error(f"下载时发生未知错误 ({attempt+1}/2): {url} - {e}"); break

        if save_path and save_path.exists():
            loop = asyncio.get_running_loop()
            await loop.run_in_executor(None, process_file, save_path, title, url, domain, id_card_dir, student_id_dir, phone_email_dir, processed_phone_email, collect_contacts)


async def extract_results_from_page(page, domain: str, download_dir: Path, id_card_dir: Path, student_id_dir: Path, phone_email_dir: Path, file_counter_state: dict, processed_urls: set, processed_phone_email: set, processed_content_hashes: set, collect_contacts: bool):
    tasks, page_had_results = [], False
    try:
        await page.wait_for_selector("//li[@class='b_algo']", timeout=15000)
        page_had_results = True
    except PlaywrightError:
        logger.info("页面上未找到任何结果 (class='b_algo')，可能出现人机验证或无结果。")
        return [], False
    results = await page.locator("//li[@class='b_algo']").all()
    for result in results:
        try:
            title_elem = result.locator("h2 a").first
            href = await title_elem.get_attribute('href', timeout=5000)
            if not href or not urlparse(href).netloc.endswith(domain): continue
            title = await title_elem.inner_text(timeout=5000)
            snippet = await result.inner_text(timeout=5000)
            if check_blacklist(title, snippet): logger.debug(f"跳过黑名单内容: {title[:40]}"); continue
            if not (check_title_is_relevant(title) or check_content_is_relevant(snippet)): logger.debug(f"不满足白名单规则，跳过: {title[:40]}"); continue
            with report_lock:
                if href in processed_urls: continue
                processed_urls.add(href)
            logger.warning(f"🎯 命中 [{domain}]: {title[:60]}")
            tasks.append(asyncio.create_task(
                download_and_analyze(href, title, domain, download_dir, id_card_dir, student_id_dir, phone_email_dir, file_counter_state, processed_phone_email, processed_content_hashes, collect_contacts)
            ))
        except PlaywrightError as e: logger.error(f"处理单个搜索结果时失败: {e.name} - {e.message.splitlines()[0]}")
        except Exception as e: logger.error(f"处理结果时发生未知错误: {e}")
    return tasks, page_had_results


async def search_worker(context, file_type: str, domain: str, pages: int, download_dir: Path, id_card_dir: Path, student_id_dir: Path, phone_email_dir: Path, file_counter_state: dict, processed_urls: set, processed_phone_email: set, processed_content_hashes: set, collect_contacts: bool, search_keywords: list):
    page = await context.new_page()
    await page.route("**/*", lambda route: route.abort() if route.request.resource_type not in ["document", "script", "xhr", "fetch"] else route.continue_())
    tasks = []
    try:
        await page.goto("https://www.bing.com", wait_until="domcontentloaded", timeout=30000)
        search_box = page.locator("//*[@id='sb_form_q']")
        await search_box.wait_for(timeout=10000)
        for keyword in search_keywords:
            # Check for cancellation before starting a new keyword search
            await asyncio.sleep(0) # Yield control to allow cancellation to be processed
            query = f'site:{domain} intext:"{keyword}" filetype:{file_type}'
            logger.info(f"🔍 输入搜索语法: {query}")
            await search_box.click()
            await search_box.fill(query)
            await search_box.press("Enter")
            await asyncio.sleep(random.uniform(3, 5))
            await page.wait_for_load_state("domcontentloaded", timeout=20000)
            for page_num in range(pages):
                # Check for cancellation before processing each page
                await asyncio.sleep(0) # Yield control
                if page_num > 0:
                    current_url = page.url.split('&first=')[0]
                    first_val = 1 + page_num * 10
                    new_url = f"{current_url}&first={first_val}"
                    try:
                        await page.goto(new_url, wait_until="domcontentloaded", timeout=20000)
                        logger.info(f"📄 翻页到第{page_num+1}页 (first={first_val})")
                    except PlaywrightError:
                        logger.warning(f"翻页失败，可能遇到人机验证，终止该关键词扫描。"); break
                current_tasks, page_had_results = await extract_results_from_page(page, domain, download_dir, id_card_dir, student_id_dir, phone_email_dir, file_counter_state, processed_urls, processed_phone_email, processed_content_hashes, collect_contacts)
                if not page_had_results: logger.info(f"❌ 第{page_num+1}页未返回任何搜索结果，终止该关键词扫描"); break
                if not current_tasks and page_had_results: logger.info(f"ℹ️  第{page_num+1}页结果均被过滤，继续翻页...")
                tasks.extend(current_tasks)
            await asyncio.sleep(random.uniform(1.5, 3))
    except Exception as e:
        logger.error(f"搜索任务失败 (类型: {file_type}): {e}")
    finally:
        await page.close()
        if tasks: await asyncio.gather(*tasks)


async def scan_domain(browser, domain: str, pages: int, show_browser: bool, proxy: str, collect_contacts: bool):
    logger.info(f"\n{'='*20} 开始扫描域名: {domain} {'='*20}")
    base_dir = Path.home() / "Desktop" / "sfz_scan"
    download_dir = base_dir / "downloads" / domain
    sensitive_base_dir = base_dir / "sensitive_files" / domain
    id_card_dir = sensitive_base_dir / "身份证"
    student_id_dir = sensitive_base_dir / "学号"
    phone_email_dir = sensitive_base_dir / "手机号和邮箱"
    for dir_path in [download_dir, id_card_dir, student_id_dir, phone_email_dir]:
        dir_path.mkdir(parents=True, exist_ok=True)
    with report_lock:
        domain_reports[domain] = []

    processed_urls_domain = set()
    processed_content_hashes = set()
    file_counter_domain = {'count': 1}
    processed_phone_email = set()

    current_search_keywords = SEARCH_KEYWORDS.copy()
    if not collect_contacts:
        logger.info("ℹ️ 已禁用联系方式收集，将跳过相关关键字搜索和文件内容解析。")
        if "联系方式" in current_search_keywords:
            current_search_keywords.remove("联系方式")

    try:
        context = await browser.new_context(
            user_agent="Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36 Edg/120.0.0.0",
            java_script_enabled=True)
        search_tasks = [
            search_worker(context, "pdf", domain, pages, download_dir, id_card_dir, student_id_dir, phone_email_dir, file_counter_domain, processed_urls_domain, processed_phone_email, processed_content_hashes, collect_contacts, current_search_keywords),
            search_worker(context, "xlsx", domain, pages, download_dir, id_card_dir, student_id_dir, phone_email_dir, file_counter_domain, processed_urls_domain, processed_phone_email, processed_content_hashes, collect_contacts, current_search_keywords),
            search_worker(context, "html", domain, pages, download_dir, id_card_dir, student_id_dir, phone_email_dir, file_counter_domain, processed_urls_domain, processed_phone_email, processed_content_hashes, collect_contacts, current_search_keywords),
        ]
        await asyncio.gather(*search_tasks)
        await context.close()
        if processed_phone_email:
            output_file = phone_email_dir / "手机号和邮箱提取结果.txt"
            sorted_results = sorted(list(processed_phone_email))
            output_file.write_text('\n'.join(sorted_results) + '\n', encoding='utf-8')
            logger.info(f"✅ [{domain}] 手机号/邮箱信息已收集并保存到结果文件夹")
    except PlaywrightError as e:
        logger.critical(f"浏览器操作失败 [{domain}]: {e}")


def print_final_report():
    logger.info(f"\n{'='*25} 扫描完成 - 检测报告 {'='*25}")
    found_any = False
    for domain, report in domain_reports.items():
        if not report:
            logger.info(f"\n✅ 域名: {domain} → 未发现敏感文件！")
        else:
            found_any = True
            logger.warning(f"\n🚨 域名: {domain} → 发现 {len(report)} 个敏感文件/记录:")
            try:
                sorted_report = sorted(report, key=lambda x: int(x['file'].split(' - ')[0]))
            except (ValueError, IndexError):
                sorted_report = report

            phone_email_reported = False
            for i, item in enumerate(sorted_report, 1):
                if item['type'] == '手机号和邮箱' and phone_email_reported:
                    continue

                log_message = f"\n  --- [{i}] 文件名/来源: {item['file']}\n    类型: {item['type']}\n    标题: {item['title']}\n    URL: {item['url']}\n    详情: {item['details']}"
                logger.warning(log_message)

                if item['type'] == '手机号和邮箱':
                    phone_email_reported = True

    if not found_any:
        logger.info("\n🎉 未发现任何敏感文件！")
    else:
        results_path = Path.home() / 'Desktop' / 'sfz_scan' / 'sensitive_files'
        logger.warning(f"\n👉 敏感文件保存路径: {results_path}")


async def async_main_logic(target_domains, pages, show_browser, proxy, collect_contacts):
    async with async_playwright() as p:
        browser_opts = {"headless": not show_browser, "args": ["--no-sandbox", "--disable-gpu"]}
        if proxy:
            browser_opts["proxy"] = {"server": proxy}
        logger.info("正在启动Edge浏览器...")
        try:
            browser = await p.chromium.launch(channel="msedge", **browser_opts)
        except PlaywrightError:
            logger.critical("Edge浏览器启动失败, 可能是首次运行。")
            logger.info("正在尝试自动安装浏览器依赖，请稍候...")
            try:
                class InstallHandler:
                    def __init__(self, app_instance):
                        self.app = app_instance
                    def show_message(self):
                        self.app.show_playwright_install_prompt()
                if 'app_instance' in globals():
                    handler = InstallHandler(globals()['app_instance'])
                    handler.show_message()
                return
            except Exception as install_e:
                logger.critical(f"自动安装失败: {install_e}。请手动执行 'playwright install msedge' 和 'playwright install-deps msedge'")
            return
        logger.info(f"开始扫描（每个关键词最多扫描 {pages} 页）...")
        for domain in target_domains:
            # Check for cancellation before starting a new domain
            await asyncio.sleep(0)
            await scan_domain(browser, domain, pages, show_browser, proxy, collect_contacts)
        await browser.close()
        logger.info("Edge浏览器已关闭")
    print_final_report()

# ================================================================================================
# ==                                      GUI Application                                       ==
# ================================================================================================

class QueueHandler(logging.Handler):
    def __init__(self, log_queue):
        super().__init__()
        self.log_queue = log_queue

    def emit(self, record):
        self.log_queue.put(self.format(record))

class SettingsWindow(tk.Toplevel):
    def __init__(self, parent):
        super().__init__(parent)
        self.title("设置")
        self.transient(parent)
        self.grab_set()

        self.bg_color = parent.style.colors.get('bg')
        self.configure(bg=self.bg_color)
        self.create_widgets()
        self.center_window()

    def center_window(self):
        """Centers the Toplevel window over its parent."""
        self.update_idletasks()
        width = 700
        # <--- MODIFICATION: Increased height to show all settings ---
        height = 600
        parent = self.master
        x = parent.winfo_x() + (parent.winfo_width() // 2) - (width // 2)
        y = parent.winfo_y() + (parent.winfo_height() // 2) - (height // 2)
        self.geometry(f'{width}x{height}+{x}+{y}')

    def create_widgets(self):
        # --- MODIFICATION START: Replaced direct packing with a Notebook (Tabs) ---
        main_container = ttk.Frame(self, padding=10)
        main_container.pack(fill=BOTH, expand=True)

        notebook = ttk.Notebook(main_container)
        notebook.pack(fill=BOTH, expand=True, pady=(0, 10))

        # --- Tab 1: Search Keywords ---
        tab_search = ttk.Frame(notebook, padding=10)
        notebook.add(tab_search, text="搜索关键词")
        ttk.Label(tab_search, text="搜索关键词 (每行一个):", style='White.TLabel').pack(fill=X, pady=(5, 5), anchor='w')
        self.search_keywords_text = scrolledtext.ScrolledText(tab_search, height=15, relief="solid", borderwidth=1, font=("Microsoft YaHei UI", 10), background="#2C3E50", foreground="white", insertbackground="white")
        self.search_keywords_text.pack(fill=BOTH, expand=True)
        self.search_keywords_text.insert(tk.END, "\n".join(SEARCH_KEYWORDS))

        # --- Tab 2: URL Blacklist ---
        tab_blacklist = ttk.Frame(notebook, padding=10)
        notebook.add(tab_blacklist, text="标题黑名单")
        ttk.Label(tab_blacklist, text="URL黑名单关键词 (每行一个):", style='White.TLabel').pack(fill=X, pady=(5, 5), anchor='w')
        self.blacklist_text = scrolledtext.ScrolledText(tab_blacklist, height=15, relief="solid", borderwidth=1, font=("Microsoft YaHei UI", 10), background="#2C3E50", foreground="white", insertbackground="white")
        self.blacklist_text.pack(fill=BOTH, expand=True)
        self.blacklist_text.insert(tk.END, "\n".join(BLACKLIST))

        # --- Tab 3: Title Whitelist ---
        tab_title_whitelist = ttk.Frame(notebook, padding=10)
        notebook.add(tab_title_whitelist, text="标题白名单")
        ttk.Label(tab_title_whitelist, text="标题白名单关键词 (每行一个):", style='White.TLabel').pack(fill=X, pady=(5, 5), anchor='w')
        self.title_filter_text = scrolledtext.ScrolledText(tab_title_whitelist, height=15, relief="solid", borderwidth=1, font=("Microsoft YaHei UI", 10), background="#2C3E50", foreground="white", insertbackground="white")
        self.title_filter_text.pack(fill=BOTH, expand=True)
        self.title_filter_text.insert(tk.END, "\n".join(TITLE_FILTER_KEYWORDS))
        
        # --- Tab 4: Content Detection Keywords ---
        tab_content_keywords = ttk.Frame(notebook, padding=10)
        tab_content_keywords.columnconfigure(0, weight=1)
        tab_content_keywords.rowconfigure(1, weight=1) # Allow text boxes to expand vertically
        tab_content_keywords.rowconfigure(3, weight=1)
        notebook.add(tab_content_keywords, text="内容检测关键字")
        
        ttk.Label(tab_content_keywords, text="内容敏感关键词 (用于判断相关性, 每行一个):", style='White.TLabel').grid(row=0, column=0, sticky='w', pady=(5,5))
        self.sensitive_keywords_text = scrolledtext.ScrolledText(tab_content_keywords, height=6, relief="solid", borderwidth=1, font=("Microsoft YaHei UI", 10), background="#2C3E50", foreground="white", insertbackground="white")
        self.sensitive_keywords_text.grid(row=1, column=0, sticky='nsew')
        self.sensitive_keywords_text.insert(tk.END, "\n".join(SENSITIVE_KEYWORDS))

        ttk.Label(tab_content_keywords, text="内容通用关键词 (用于判断相关性, 每行一个):", style='White.TLabel').grid(row=2, column=0, sticky='w', pady=(15,5))
        self.general_keywords_text = scrolledtext.ScrolledText(tab_content_keywords, height=6, relief="solid", borderwidth=1, font=("Microsoft YaHei UI", 10), background="#2C3E50", foreground="white", insertbackground="white")
        self.general_keywords_text.grid(row=3, column=0, sticky='nsew')
        self.general_keywords_text.insert(tk.END, "\n".join(GENERAL_KEYWORDS))
        
        # --- Buttons remain at the bottom ---
        button_frame = ttk.Frame(main_container)
        button_frame.pack(side=BOTTOM, fill=X, pady=(10, 0))
        button_frame.columnconfigure(0, weight=1)
        ttk.Button(button_frame, text="保存", command=self.save_settings, bootstyle="success").pack(side=RIGHT)
        ttk.Button(button_frame, text="取消", command=self.destroy, bootstyle="secondary-outline").pack(side=RIGHT, padx=5)
        # --- MODIFICATION END ---

    def save_settings(self):
        # <--- MODIFICATION: Added new keywords to save ---
        global SEARCH_KEYWORDS, BLACKLIST, TITLE_FILTER_KEYWORDS, SENSITIVE_KEYWORDS, GENERAL_KEYWORDS
        SEARCH_KEYWORDS = [line.strip() for line in self.search_keywords_text.get("1.0", tk.END).splitlines() if line.strip()]
        BLACKLIST = [line.strip() for line in self.blacklist_text.get("1.0", tk.END).splitlines() if line.strip()]
        TITLE_FILTER_KEYWORDS = [line.strip() for line in self.title_filter_text.get("1.0", tk.END).splitlines() if line.strip()]
        SENSITIVE_KEYWORDS = {line.strip() for line in self.sensitive_keywords_text.get("1.0", tk.END).splitlines() if line.strip()}
        GENERAL_KEYWORDS = {line.strip() for line in self.general_keywords_text.get("1.0", tk.END).splitlines() if line.strip()}
        # --- END MODIFICATION ---
        messagebox.showinfo("成功", "设置已保存。", parent=self)
        self.destroy()

class GradientFrame(tk.Canvas):
    def __init__(self, parent, colors=("gray20", "gray10"), **kwargs):
        tk.Canvas.__init__(self, parent, **kwargs)
        self.colors = colors
        self.bind("<Configure>", self.draw_gradient)

    def draw_gradient(self, event=None):
        self.delete("gradient")
        width = self.winfo_width()
        height = self.winfo_height()
        (r1, g1, b1) = self.winfo_rgb(self.colors[0])
        (r2, g2, b2) = self.winfo_rgb(self.colors[1])
        r_ratio = float(r2 - r1) / height
        g_ratio = float(g2 - g1) / height
        b_ratio = float(b2 - b1) / height

        for i in range(height):
            nr = int(r1 + (r_ratio * i))
            ng = int(g1 + (g_ratio * i))
            nb = int(b1 + (b_ratio * i))
            color = f"#{nr//256:02x}{ng//256:02x}{nb//256:02x}"
            self.create_line(0, i, width, i, tags=("gradient",), fill=color)

class App(ttk.Window):
    def __init__(self, themename='darkly'):
        super().__init__(themename=themename)
        self.title("Fir-Fetch by firefly")
        self.geometry("1440x900")

        self.bg_color = self.style.colors.get('bg')
        self.style.configure('Transparent.TFrame', background=self.bg_color)
        self.style.configure('White.TLabel', foreground=self.style.colors.get('fg'), background=self.bg_color, font=('Microsoft YaHei UI', 10))
        self.style.configure('White.TLabelframe.Label', foreground=self.style.colors.get('fg'), background=self.bg_color, font=('Microsoft YaHei UI', 10))
        
        # --- MODIFICATION START: Added placeholder logic ---
        self.placeholder_text = "输入单个域名或浏览文件..."
        self.placeholder_color = 'grey'
        self.default_fg_color = self.style.lookup('TEntry', 'foreground')
        # --- MODIFICATION END ---

        self.create_widgets()
        self.setup_logging()
        self.scan_thread = None
        self.scan_loop = None


    def create_widgets(self):
        bg_frame = GradientFrame(self, colors=("#2E3B55", "#1C2833"))
        bg_frame.pack(fill=BOTH, expand=True)

        main_frame = ttk.Frame(bg_frame, padding="15", style='Transparent.TFrame')
        main_frame.pack(fill=BOTH, expand=True)
        main_frame.grid_rowconfigure(1, weight=1)
        main_frame.grid_columnconfigure(0, weight=1)

        controls_frame = ttk.Labelframe(main_frame, text="扫描配置", padding="10", style='White.TLabelframe')
        controls_frame.grid(row=0, column=0, sticky="ew", pady=(0, 10))
        
        controls_frame.grid_columnconfigure(1, weight=1)
        
        ttk.Label(controls_frame, text="目标:", style='White.TLabel').grid(row=0, column=0, sticky="w", padx=5, pady=5)
        
        self.target_var = tk.StringVar()
        self.target_entry = ttk.Entry(controls_frame, textvariable=self.target_var, font=('Microsoft YaHei UI', 10))
        self.target_entry.grid(row=0, column=1, sticky="ew", padx=(0, 5), pady=5)
        
        # --- MODIFICATION START: Placeholder setup and event binding ---
        self.target_entry.insert(0, self.placeholder_text)
        self.target_entry.config(foreground=self.placeholder_color)
        self.target_entry.bind('<FocusIn>', self.on_target_focus_in)
        self.target_entry.bind('<FocusOut>', self.on_target_focus_out)
        # --- MODIFICATION END ---

        self.browse_button = ttk.Button(controls_frame, text="浏览文件", command=self.browse_file, bootstyle="light-outline")
        self.browse_button.grid(row=0, column=2, padx=5, pady=5)
        
        self.start_button = ttk.Button(controls_frame, text="开始扫描", command=self.start_scan, bootstyle="success")
        self.start_button.grid(row=0, column=3, padx=5, pady=5)

        self.settings_button = ttk.Button(controls_frame, text="设置", command=self.open_settings, bootstyle="secondary")
        self.settings_button.grid(row=0, column=4, padx=5, pady=5)
        
        self.open_folder_button = ttk.Button(controls_frame, text="打开结果文件夹", command=self.open_results_folder, bootstyle="info")
        self.open_folder_button.grid(row=0, column=5, padx=5, pady=5)

        ttk.Label(controls_frame, text="选项:", style='White.TLabel').grid(row=1, column=0, sticky="w", padx=5, pady=5)
        
        options_frame = ttk.Frame(controls_frame, style='Transparent.TFrame')
        options_frame.grid(row=1, column=1, columnspan=5, sticky="ew", padx=0, pady=5)
        
        options_frame.grid_columnconfigure(3, weight=1) 
        
        ttk.Label(options_frame, text="搜索页数:", style='White.TLabel').grid(row=0, column=0, sticky='w')
        self.pages_var = tk.IntVar(value=3)
        self.pages_spinbox = ttk.Spinbox(options_frame, from_=1, to=20, textvariable=self.pages_var, width=5)
        self.pages_spinbox.grid(row=0, column=1, padx=(5, 15), sticky='w')
        
        ttk.Label(options_frame, text="代理:", style='White.TLabel').grid(row=0, column=2, sticky='w')
        self.proxy_var = tk.StringVar(value="")
        self.proxy_entry = ttk.Entry(options_frame, textvariable=self.proxy_var)
        self.proxy_entry.grid(row=0, column=3, padx=(5, 15), sticky='ew')
        
        self.show_browser_var = tk.BooleanVar(value=False)
        self.show_browser_check = ttk.Checkbutton(options_frame, text="显示浏览器", variable=self.show_browser_var, bootstyle="round-toggle")
        self.show_browser_check.grid(row=0, column=4, padx=(0, 5))

        self.verbose_var = tk.BooleanVar(value=False)
        self.verbose_check = ttk.Checkbutton(options_frame, text="显示详细信息", variable=self.verbose_var, bootstyle="round-toggle")
        self.verbose_check.grid(row=0, column=5, padx=(0, 15))

        self.collect_contacts_var = tk.BooleanVar(value=False)
        self.collect_contacts_check = ttk.Checkbutton(options_frame, text="收集联系方式", variable=self.collect_contacts_var, bootstyle="round-toggle")
        self.collect_contacts_check.grid(row=0, column=6, padx=(0, 15))

        log_frame = ttk.Labelframe(main_frame, text="日志输出", padding="10", style='White.TLabelframe')
        log_frame.grid(row=1, column=0, sticky="nsew", pady=(10, 0))
        log_frame.grid_rowconfigure(0, weight=1)
        log_frame.grid_columnconfigure(0, weight=1)
        self.log_text = scrolledtext.ScrolledText(log_frame, state='disabled', wrap=tk.WORD, font=("Courier New", 10), relief="solid", borderwidth=1, bg="#1C2833", fg="white", insertbackground="white")
        self.log_text.grid(row=0, column=0, sticky="nsew")
        self.log_text.tag_config('INFO', foreground='white')
        self.log_text.tag_config('WARNING', foreground='#F39C12')
        self.log_text.tag_config('ERROR', foreground='#E74C3C')
        self.log_text.tag_config('CRITICAL', foreground='#C0392B', font=("Courier New", 10, "bold"))
        self.log_text.tag_config('DEBUG', foreground='#7F8C8D')

    # --- MODIFICATION START: New methods for placeholder handling ---
    def on_target_focus_in(self, event):
        """当用户点击输入框时调用"""
        if self.target_entry.get() == self.placeholder_text:
            self.target_entry.delete(0, "end")
            self.target_entry.config(foreground=self.default_fg_color)

    def on_target_focus_out(self, event):
        """当用户点击输入框以外区域时调用"""
        if not self.target_entry.get():
            self.target_entry.insert(0, self.placeholder_text)
            self.target_entry.config(foreground=self.placeholder_color)
    # --- MODIFICATION END ---

    def open_settings(self):
        SettingsWindow(self)

    def open_results_folder(self):
        results_path = Path.home() / "Desktop" / "sfz_scan" / "sensitive_files"
        if not results_path.exists():
            results_path.mkdir(parents=True, exist_ok=True)
            messagebox.showinfo("提示", f"结果文件夹已创建于:\n{results_path}", parent=self)
        try:
            if sys.platform == "win32":
                os.startfile(results_path)
            elif sys.platform == "darwin":
                subprocess.Popen(["open", str(results_path)])
            else:
                subprocess.Popen(["xdg-open", str(results_path)])
        except Exception as e:
            messagebox.showerror("错误", f"无法打开文件夹: {e}", parent=self)

    def browse_file(self):
        filepath = filedialog.askopenfilename(title="选择域名文件", filetypes=(("Text files", "*.txt"), ("All files", "*.*")), parent=self)
        if filepath:
            self.on_target_focus_in(None) # Manually trigger focus in to clear placeholder
            self.target_var.set(f"file://{filepath}")

    def setup_logging(self):
        self.log_queue = queue.Queue()
        self.queue_handler = QueueHandler(self.log_queue)
        formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s', datefmt='%H:%M:%S')
        self.queue_handler.setFormatter(formatter)
        logger.addHandler(self.queue_handler)
        logger.setLevel(logging.DEBUG)
        self.after(100, self.poll_log_queue)

    def poll_log_queue(self):
        try:
            while True:
                record = self.log_queue.get(block=False)
                self.display_log(record)
        except queue.Empty:
            pass
        finally:
            self.after(100, self.poll_log_queue)

    def display_log(self, record):
        self.log_text.configure(state='normal')
        level_tag = 'INFO'
        if 'WARNING' in record or '🚨' in record or '🎯' in record or '🔄️' in record:
            level_tag = 'WARNING'
        elif 'ERROR' in record:
            level_tag = 'ERROR'
        elif 'CRITICAL' in record:
            level_tag = 'CRITICAL'
        elif 'DEBUG' in record:
            level_tag = 'DEBUG'
        self.log_text.insert(tk.END, record + '\n', level_tag)
        self.log_text.configure(state='disabled')
        self.log_text.yview(tk.END)

    def get_targets(self):
        target_str = self.target_var.get().strip()
        # --- MODIFICATION: Use placeholder variable for check ---
        if not target_str or target_str == self.placeholder_text:
            return None
        if target_str.startswith("file://"):
            filepath = target_str[7:]
            try:
                with open(filepath, 'r', encoding='utf-8') as f:
                    return [line.strip() for line in f if line.strip() and not line.startswith('#')]
            except FileNotFoundError:
                messagebox.showerror("错误", f"域名文件未找到: {filepath}", parent=self)
                return None
        else:
            return [target_str]
    
    def start_scan(self):
        target_domains = self.get_targets()
        if not target_domains:
            messagebox.showwarning("输入错误", "请输入一个域名或选择一个目标文件。", parent=self)
            return

        if self.verbose_var.get():
            self.queue_handler.setLevel(logging.DEBUG)
        else:
            self.queue_handler.setLevel(logging.INFO)

        self.start_button.config(text="取消扫描", command=self.cancel_scan, bootstyle="danger")
        
        self.log_text.config(state="normal")
        self.log_text.delete(1.0, tk.END)
        self.log_text.config(state="disabled")
        global domain_reports, ssl_failed_domains
        domain_reports = {}
        ssl_failed_domains = set()

        self.scan_thread = threading.Thread(
            target=self.run_async_scan,
            args=(
                target_domains,
                self.pages_var.get(),
                self.show_browser_var.get(),
                self.proxy_var.get().strip(),
                self.collect_contacts_var.get()
            ),
            daemon=True
        )
        self.scan_thread.start()

    def cancel_scan(self):
        self.start_button.config(text="正在取消...", state="disabled")
        logger.info("用户请求取消扫描...")
        if self.scan_loop and self.scan_loop.is_running():
            self.scan_loop.call_soon_threadsafe(self.shutdown_async_tasks)

    def shutdown_async_tasks(self):
        if not self.scan_loop or not self.scan_loop.is_running():
            return
        for task in asyncio.all_tasks(loop=self.scan_loop):
            task.cancel()

    def run_async_scan(self, domains, pages, show_browser, proxy, collect_contacts):
        was_cancelled = False
        self.scan_loop = asyncio.new_event_loop()
        asyncio.set_event_loop(self.scan_loop)
        try:
            self.scan_loop.run_until_complete(async_main_logic(domains, pages, show_browser, proxy, collect_contacts))
        except asyncio.CancelledError:
            was_cancelled = True
            logger.info("扫描任务已被成功取消。")
        except Exception as e:
            logger.critical(f"扫描线程中发生严重错误: {e}")
        finally:
            self.scan_loop.close()
            self.scan_loop = None
            self.after(0, self.on_scan_complete, was_cancelled)

    def on_scan_complete(self, was_cancelled):
        self.start_button.config(text="开始扫描", command=self.start_scan, state="normal", bootstyle="success")
        logger.info("=" * 20 + " 扫描任务已结束 " + "=" * 20)
        
        if was_cancelled:
            messagebox.showinfo("已取消", "扫描任务已被用户取消。", parent=self)
        else:
            messagebox.showinfo("完成", "所有扫描任务已完成！请查看日志和结果文件夹。", parent=self)
    
    def show_playwright_install_prompt(self):
        response = messagebox.askyesno("Playwright依赖缺失", "Playwright Edge浏览器依赖似乎未安装。\n是否要尝试自动安装？ (这可能需要一些时间)", parent=self)
        if response:
            self.start_button.config(text="正在安装...", state="disabled")
            self.update()
            install_thread = threading.Thread(target=self.run_playwright_install, daemon=True)
            install_thread.start()

    def run_playwright_install(self):
        try:
            logger.info("执行: playwright install msedge")
            subprocess.run([sys.executable, "-m", "playwright", "install", "msedge"], check=True, capture_output=True, text=True, encoding='utf-8')
            logger.info("执行: playwright install-deps msedge")
            subprocess.run([sys.executable, "-m", "playwright", "install-deps", "msedge"], check=True, capture_output=True, text=True, encoding='utf-8')
            logger.info("依赖安装成功！请重新启动程序并开始扫描。")
            self.after(0, lambda: messagebox.showinfo("成功", "依赖安装成功！\n请重新启动程序。"))
        except subprocess.CalledProcessError as e:
            logger.error(f"自动安装失败: {e}\nOutput: {e.stdout}\nError: {e.stderr}")
            self.after(0, lambda: messagebox.showerror("安装失败", "自动安装失败，请查看日志或手动执行安装命令。"))
        except Exception as install_e:
            logger.error(f"自动安装时发生未知错误: {install_e}")
            self.after(0, lambda: messagebox.showerror("安装失败", f"发生未知错误: {install_e}"))
        finally:
            self.after(0, lambda: self.start_button.config(text="开始扫描", state="normal"))


if __name__ == "__main__":
    app = App()
    globals()['app_instance'] = app
    try:
        app.mainloop()
    except KeyboardInterrupt:
        logger.info("\n用户手动退出程序。")
