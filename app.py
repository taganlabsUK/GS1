import os
import time
import threading
import smtplib
import uuid  # Added for secure unique session IDs
from datetime import datetime, timedelta
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
import requests
from bs4 import BeautifulSoup
from urllib.parse import urlparse, urljoin, urldefrag
import socket
import ipaddress
from flask import Flask, request, jsonify, render_template, session, send_file
from flask_limiter import Limiter
from flask_limiter.util import get_remote_address
from werkzeug.middleware.proxy_fix import ProxyFix
import io
# The reportlab library is not available in this environment.  Previously,
# these imports were used to generate PDF reports.  PDF generation is now
# handled via LibreOffice in export_pdf(), so the reportlab imports have
# been removed to avoid import errors.
import logging
import random
import redis
from celery import Celery
import re
import difflib  # For fuzzy slug vs title matching
from difflib import SequenceMatcher  # Used in Shopify alt text checks
import json
import tempfile  # For creating temporary files/directories when exporting PDFs
import subprocess  # For running external commands (LibreOffice)
import shutil  # For checking availability of system commands (e.g. soffice)
import pickle
import hashlib
from collections import deque
# Include Optional for type annotations.  Without importing Optional, using it
# in type hints (e.g. fetch_shopify_products) will raise a NameError at runtime.
from typing import List, Set, Optional, Dict  # For type annotations used in image scanning

# -----------------------------------------------------------------------------
# CAPTCHA utilities
#
# To mitigate automated spam and abusive crawlers, we provide a simple
# arithmetic CAPTCHA.  Each call to `/captcha` will generate a new question
# (for example "3 + 4?" or "9 - 2?") and store the corresponding answer in
# the user's session under the key `captcha_answer`.  Clients must include
# this answer in their subsequent `/crawl` POST request in a JSON field
# named `captcha_answer`.  If the provided answer does not match the stored
# value, the crawl request will be rejected.

def generate_captcha():
    """Generate a simple arithmetic CAPTCHA question and answer.

    Returns a tuple of (question, answer).  The answer is returned as a
    string to simplify comparison later.
    """
    # Randomly pick two numbers between 1 and 9 and an operator (+ or -).
    a = random.randint(1, 9)
    b = random.randint(1, 9)
    op = random.choice(['+', '-'])
    if op == '+':
        question = f"What is {a} + {b}?"
        answer = str(a + b)
    else:
        # Ensure non-negative answer for subtraction
        if b > a:
            a, b = b, a
        question = f"What is {a} - {b}?"
        answer = str(a - b)
    return question, answer

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# Allow log level to be overridden via the LOG_LEVEL environment variable.
# If LOG_LEVEL is set (e.g. "DEBUG", "INFO", "WARNING"), adjust both
# the module logger and the root logger accordingly.  This enables debug
# statements to appear in production when LOG_LEVEL=DEBUG is configured.
_env_log_level = os.environ.get('LOG_LEVEL')
if _env_log_level:
    # Normalize the level name and validate it exists in the logging module
    _level_name = _env_log_level.strip().upper()
    _level = getattr(logging, _level_name, None)
    if isinstance(_level, int):
        logger.setLevel(_level)
        logging.getLogger().setLevel(_level)

# Log environment variables (safely)
logger.info("Starting GMC Scout V1")
logger.info(f"Python version: {os.sys.version}")
logger.info(f"Environment: {os.environ.get('FLASK_ENV', 'not set')}")
logger.info(f"SECRET_KEY configured: {'Yes' if os.environ.get('SECRET_KEY') else 'No'}")
logger.info(f"Port: {os.environ.get('PORT', 'not set')}")
logger.info(f"Working directory: {os.getcwd()}")
logger.info(f"Temp directory writable: {os.access('/tmp', os.W_OK)}")

# Create the Flask application.  We explicitly specify the template and
# static folders to ensure that Flask looks up templates and static
# assets in the directories shipped with this application.  Without
# specifying these arguments, Flask may search for templates relative
# to the installation location of the package/module, which can lead
# to stale templates being used when the application is installed via
# pip.  By setting template_folder and static_folder here, we force
# Flask to use the current repository's `templates` and `static`
# directories.
app = Flask(__name__, template_folder='templates', static_folder='static')
app.secret_key = os.environ.get('SECRET_KEY', 'your-secret-key-change-this-in-production')

# CRITICAL: Check if secret key is properly set
if app.secret_key == 'your-secret-key-change-this-in-production':
    logger.warning("WARNING: Using default SECRET_KEY - sessions will not work properly in production!")
else:
    logger.info("SECRET_KEY properly configured")

# Configure Flask sessions properly
app.config['SESSION_COOKIE_SECURE'] = True if os.environ.get('FLASK_ENV') == 'production' else False
app.config['SESSION_COOKIE_HTTPONLY'] = True
app.config['SESSION_COOKIE_SAMESITE'] = 'Lax'
app.config['PERMANENT_SESSION_LIFETIME'] = 7200  # 2 hours
app.config['SESSION_COOKIE_NAME'] = 'linkchecker_session'

# Handle proxy headers for rate limiting
app.wsgi_app = ProxyFix(app.wsgi_app, x_for=1, x_proto=1, x_host=1, x_prefix=1)

# Rate limiting with explicit storage backend
limiter = Limiter(
    app=app,
    key_func=get_remote_address,
    default_limits=["200 per day", "50 per hour"],
    storage_uri="memory://"
)

# Configuration
EXCLUDED_DOMAINS = [
    'g.co', 'facebook.com', 'instagram.com', 'x.com', 'twitter.com',
    'pinterest.com', 'shopify.com', 'edpb.europa.eu', 'linkedin.com',
    'youtube.com', 'tiktok.com', 'snapchat.com', 'discord.com', 'google.com',
    'whatsapp.com', 'telegram.org', 'reddit.com'
]

# List of banned keywords to check in product titles and descriptions.
# These terms are not allowed to appear on product pages.  The crawler will
# scan each product page (title and description) for any of these phrases.
BANNED_KEYWORDS = [
    "100%", "100% Satisfaction", "Absolute", "Act", "Addiction", "Alcohol",
    "Alcoholic", "Amazing", "Ammonia", "Ammunition", "Anti-aging", "Apply",
    "Arms", "Attached", "Authentic", "Beer", "Best", "Beverage", "Bomb",
    "Breathable", "Business", "Catch", "Chemicals", "Cigarettes", "Cigars",
    "Clinical", "Clinically proven", "Cocaine", "Comfort", "Comfortable",
    "C4", "Cooling", "Curing", "Cure", "Cures", "Desirable", "Designer",
    "Detonators", "Detoxify", "Diagnosis", "Direct", "Doctor", "Dynamite",
    "Earn", "Ecstasy", "Eco-friendly", "Erotic", "Essential", "Exclusive",
    "Explode", "Explosives", "Exceptional", "Exquisite", "Fit", "Free",
    "Guarantee", "Guaranteed", "Gun", "Handguns", "Handmade", "Heal",
    "Healing", "Heals", "Health", "Healthy", "Heroin", "Hidden",
    "Highest quality", "High quality", "Hormone", "Hydrochloric",
    "Immediately", "Immediate", "Immediate Result", "Immunity Booster",
    "Improves", "Innovative", "Instant", "Intimate", "LSD", "Lightweight",
    "Liquor", "Luxury", "Lustful", "Magic", "Magical", "Marijuana",
    "Materials", "Medical", "Medicine", "Medication", "Memory",
    "Methamphetamine", "Miracle", "Money Back Guarantee", "Mushrooms",
    "Must-have", "Natural", "NoSideEffects", "Obligation", "Only",
    "Operation", "Opioids", "Organic", "Orthopedic", "Outstanding",
    "Pain", "Pain relief", "Passionate", "Pharmaceutical", "Pill",
    "Potential", "Premium", "Prevent", "Prize", "Purchase", "Pyrotechnics",
    "Range", "Recovery", "Recyclable / Recycled", "Relief", "Remedy",
    "Resolving", "Revolutionary", "Rifles", "Risk-Free", "Safe", "Sales",
    "Save", "Scratch-resistant", "Seamless", "Secret", "Seductive",
    "Seen", "Sensual", "Sex", "Sexy", "Shooting", "Shop", "Shockproof",
    "ShortGirlProblems", "Social", "Solution", "Soft", "Stain-resistant",
    "StayConnected", "SteamCleaner", "Stress", "Stressed", "Stronger",
    "Sulfuric", "Sultry", "Surgery", "Sustainable", "Superior",
    "Therapeutic", "Therapy", "™", "Tobacco", "Top choice", "Toxic",
    "Trade", "Treatment", "Trial", "TV", "Unique", "UV-protection",
    "Vegan", "Water-resistant", "Waterproof", "Wellbeing", "Win"
]

# Default crawling parameters.  Environment variables can override these,
# but we now default to larger values to accommodate deeper crawls.  The
# defaults are:
#   MAX_PAGES = 5000          (maximum pages to scan per crawl)
#   HARD_LIMIT_PAGES = 6000   (absolute safety cap)
#   CRAWL_TIMEOUT = 1800      (30 minutes in seconds)
#   CRAWL_DELAY = 0.3         (300ms between requests)

MAX_PAGES = int(os.environ.get('MAX_PAGES', 5000))
HARD_LIMIT_PAGES = int(os.environ.get('HARD_LIMIT_PAGES', 6000))
CRAWL_TIMEOUT = int(os.environ.get('CRAWL_TIMEOUT', 1800))  # seconds
CRAWL_DELAY = float(os.environ.get('CRAWL_DELAY', 0.3))  # seconds
MAX_OUTBOUND_CHECKS = 100

# Concurrency limits
# Limit the number of simultaneous crawls to avoid resource exhaustion.  This
# value can be overridden via the `MAX_CONCURRENT_CRAWLS` environment
# variable.  When the server is under heavy load and the limit is reached,
# new crawl requests will be rejected with a descriptive error.  By default,
# allow up to 50 concurrent crawls to support moderate traffic.
MAX_CONCURRENT_CRAWLS = int(os.environ.get('MAX_CONCURRENT_CRAWLS', 50))
active_crawl_semaphore = threading.Semaphore(MAX_CONCURRENT_CRAWLS)

# Email configuration
SMTP_SERVER = os.environ.get('SMTP_SERVER', 'smtp.gmail.com')
SMTP_PORT = int(os.environ.get('SMTP_PORT', 587))
SMTP_USERNAME = os.environ.get('SMTP_USERNAME')
SMTP_PASSWORD = os.environ.get('SMTP_PASSWORD')
FEEDBACK_EMAIL = os.environ.get('FEEDBACK_EMAIL', 'terry@terryecom.com')

# Configure Redis for shared state and Celery broker
REDIS_URL = os.environ.get('REDIS_URL', 'redis://localhost:6379/0')
redis_client = redis.Redis.from_url(REDIS_URL, decode_responses=False)

# Celery configuration: use Redis as both broker and backend
celery_app = Celery('link_checker', broker=REDIS_URL, backend=REDIS_URL)

# Global in-memory storage for crawl sessions (fallback if Redis unavailable)
crawl_sessions = {}

class CrawlResult:
    """Stores crawl results"""
    def __init__(self, domain):
        self.domain = domain
        self.start_time = datetime.now()
        self.end_time = None
        self.pages_scanned = 0
        self.outbound_links = set()
        self.broken_links = set()
        # Track details of each broken link: (source_page, broken_link)
        self.broken_links_details = []

        # Track details of each outbound link: (source_page, outbound_link)
        # This allows us to show where each external link was found, even if it
        # isn’t broken.  Only the first occurrence of an outbound link is
        # recorded; subsequent occurrences are ignored.
        self.outbound_links_details = []
        self.is_complete = False
        self.error = None
        self.cancelled = False
        self.current_url = ""
        self.recent_urls = deque(maxlen=10)  # Store last 10 URLs
        self.lock = threading.Lock()  # Thread safety
        # Unique session identifier (set externally) used for Redis storage
        self.session_id = None
        # Track last reported progress percentage (0-100).  This value is
        # updated in crawl_status() to ensure progress never decreases when
        # retrieving state from different workers or Redis snapshots.
        self.last_progress = 0.0
        # Store mismatches between product page slugs and their titles.  Each entry
        # is a tuple of (url, slug, title, similarity) where similarity is
        # between 0 and 1.  A lower similarity indicates a bigger mismatch.
        self.title_mismatches = []

        # Store pages where banned keywords are found.  Each entry is a tuple of
        # (url, banned_keywords_found, ratio) where banned_keywords_found is a
        # list of the banned words detected on the page and ratio is
        # len(found_words) / len(BANNED_KEYWORDS).  This allows us to
        # summarise how many of the prohibited terms appeared on a product page.
        self.banned_keyword_pages = []

        # Track pages checked for each specific validation.  Counters allow
        # the front‑end to display ratios of issues to pages checked.  We
        # increment these counters whenever a product page is scanned for
        # mismatches or banned keywords.  The alt text checker has been
        # removed, so we no longer track alt text specific counters.
        self.title_check_pages = 0
        self.banned_check_pages = 0
        # Note: alt_check_pages and alt_checks_total are intentionally
        # omitted since the alt text checker has been removed.

        # Debug logging: store human‑readable log entries describing
        # each check performed during the crawl.  Entries are appended
        # chronologically and may be displayed live in the UI or
        # downloaded at the end of the crawl.
        self.debug_logs: List[str] = []

        # ---------------------------------------------------------------------
        # Trust signals and policy checks
        #
        # trust_signal_issues stores tuples of the form
        # (url, contact_issues, policy_issues, ssl_issues) where each list
        # contains human‑readable strings describing missing or invalid trust
        # signals on a page.  For example, contact_issues might include
        # "missing email" or "no phone number".  policy_issues might list
        # missing Terms, Shipping, Returns or Privacy pages.  ssl_issues will
        # flag pages served over HTTP or sites with invalid TLS certificates.
        self.trust_signal_issues = []
        # Count how many pages were scanned for trust signals.  This allows the
        # UI to display a ratio of issues to pages checked.
        self.trust_check_pages = 0

        # ---------------------------------------------------------------------
        # Restricted content and crawl blocking checks
        #
        # restricted_content_pages stores tuples of the form (url, categories)
        # where categories is a list of prohibited themes detected on the page
        # (e.g. ["weapons", "tobacco"]).  robots_disallowed records
        # directives parsed from robots.txt that could block product pages
        # from Google’s crawlers.  meta_robots_pages records pages that set
        # restrictive meta robots tags such as noindex or nofollow.
        self.restricted_content_pages = []
        self.robots_disallowed = []
        self.meta_robots_pages = []
        # Counter for pages scanned for restricted content and meta robots tags
        self.restricted_check_pages = 0

        # ---------------------------------------------------------------------
        # Structured data validation checks
        #
        # structured_data_issues stores tuples of the form (url, errors) where
        # errors is a list of strings describing missing or invalid fields
        # in schema.org Product markup on a page.  This helps merchants fix
        # structured data so that Google can generate rich product snippets.
        self.structured_data_issues = []
        # Counter for pages scanned for structured data
        self.structured_check_pages = 0

        # Placeholder to maintain backward compatibility when loading from
        # serialized sessions.  Initialize alt text issue structures.
        self.alt_text_issues = []
        # Number of alt text issues found across all product images.  This
        # corresponds to the length of alt_text_issues and is returned
        # explicitly to the frontend to avoid issues serialising large arrays.
        self.alt_text_count = 0
        # Total number of images scanned when validating alt text via the
        # Shopify products JSON feed.  The UI uses this value as the
        # denominator when displaying the ratio of issues/images scanned.
        self.alt_checks_total = 0
    
    def update_current_url(self, url):
        """Thread-safe update of current URL"""
        with self.lock:
            self.current_url = url
            self.recent_urls.append(url)
    
    def get_status(self):
        """Thread-safe status retrieval"""
        with self.lock:
            # Always include the list of title/slug mismatches so that
            # the front‑end can display them while the crawl is in progress.
            return {
                'current_url': self.current_url,
                'recent_urls': list(self.recent_urls),
                'pages_scanned': self.pages_scanned,
                'outbound_count': len(self.outbound_links),
                'broken_count': len(self.broken_links),
                # Provide mismatches for real‑time updates
                'title_mismatches': list(self.title_mismatches),
                'is_complete': self.is_complete,
                'error': self.error
                , 'banned_keyword_pages': list(self.banned_keyword_pages)
                , 'title_check_pages': self.title_check_pages
                , 'banned_check_pages': self.banned_check_pages
                # Provide alt text issues and counters to the UI.  When no alt
                # checks have been run yet, alt_text_issues will be an empty list
                # and the counters will be zero.  alt_text_count is explicitly
                # included so that the frontend does not need to count the
                # issues array, which may be large.
                , 'alt_text_issues': list(self.alt_text_issues)
                , 'alt_text_count': self.alt_text_count
                , 'alt_checks_total': self.alt_checks_total
                # Trust signals and policies
                , 'trust_signal_issues': list(self.trust_signal_issues)
                , 'trust_check_pages': self.trust_check_pages
                # Restricted content and crawl blocking
                , 'restricted_content_pages': list(self.restricted_content_pages)
                , 'robots_disallowed': list(self.robots_disallowed)
                , 'meta_robots_pages': list(self.meta_robots_pages)
                , 'restricted_check_pages': self.restricted_check_pages
                # Structured data validation
                , 'structured_data_issues': list(self.structured_data_issues)
                , 'structured_check_pages': self.structured_check_pages
                , 'debug_logs': list(self.debug_logs)
            }
    
    def to_dict(self):
        """Convert to dictionary for serialization"""
        with self.lock:
            # Persist all relevant fields, including the current page being crawled
            # and the recent URLs list, so that progress can be restored across
            # workers via Redis.
            return {
                'domain': self.domain,
                'start_time': self.start_time.isoformat(),
                'end_time': self.end_time.isoformat() if self.end_time else None,
                'pages_scanned': self.pages_scanned,
                'outbound_links': list(self.outbound_links),
                'broken_links': list(self.broken_links),
                'broken_links_details': list(self.broken_links_details),
            'outbound_links_details': list(self.outbound_links_details),
                'is_complete': self.is_complete,
                'error': self.error,
                'cancelled': self.cancelled,
                'current_url': self.current_url,
                'recent_urls': list(self.recent_urls)
            , 'last_progress': self.last_progress
            , 'title_mismatches': list(self.title_mismatches)
            , 'banned_keyword_pages': list(self.banned_keyword_pages)
            , 'title_check_pages': self.title_check_pages
            , 'banned_check_pages': self.banned_check_pages
            # Store alt text issues and counters.  Use explicit counts to
            # avoid serialising large arrays when not needed.
            , 'alt_text_issues': list(self.alt_text_issues)
            , 'alt_text_count': self.alt_text_count
            , 'alt_checks_total': self.alt_checks_total
            # Trust signals and policies
            , 'trust_signal_issues': list(self.trust_signal_issues)
            , 'trust_check_pages': self.trust_check_pages
            # Restricted content and crawl blocking
            , 'restricted_content_pages': list(self.restricted_content_pages)
            , 'robots_disallowed': list(self.robots_disallowed)
            , 'meta_robots_pages': list(self.meta_robots_pages)
            , 'restricted_check_pages': self.restricted_check_pages
            # Structured data validation
            , 'structured_data_issues': list(self.structured_data_issues)
            , 'structured_check_pages': self.structured_check_pages
            , 'debug_logs': list(self.debug_logs)
            }

    def save_to_redis(self):
        """Persist the current state to Redis under self.session_id."""
        if not self.session_id:
            return
        try:
            data = pickle.dumps(self.to_dict())
            # Store with an expiry of 3 hours to free space automatically
            redis_client.set(self.session_id, data, ex=3 * 60 * 60)
        except Exception as e:
            logger.error(f"Failed to save session {self.session_id} to Redis: {e}")
    
    @classmethod
    def from_dict(cls, data):
        """Create from dictionary"""
        result = cls(data['domain'])
        result.start_time = datetime.fromisoformat(data['start_time'])
        result.end_time = datetime.fromisoformat(data['end_time']) if data['end_time'] else None
        result.pages_scanned = data['pages_scanned']
        result.outbound_links = set(data['outbound_links'])
        result.broken_links = set(data['broken_links'])
        # Restore broken links details if present
        result.broken_links_details = data.get('broken_links_details', [])
        result.outbound_links_details = data.get('outbound_links_details', [])
        result.is_complete = data['is_complete']
        result.error = data['error']
        result.cancelled = data['cancelled']
        # Restore live progress fields if present
        result.current_url = data.get('current_url', '')
        result.recent_urls = deque(data.get('recent_urls', []), maxlen=10)
        result.last_progress = data.get('last_progress', 0.0)
        result.title_mismatches = data.get('title_mismatches', [])
        result.banned_keyword_pages = data.get('banned_keyword_pages', [])
        # Restore counters for product and alt text checks.  These may be
        # absent in older serialized sessions.  Use 0 as a sensible default.
        result.title_check_pages = data.get('title_check_pages', 0)
        result.banned_check_pages = data.get('banned_check_pages', 0)
        # Restore alt text issues and counters if present.  For older
        # serialized sessions these fields may be absent, so fallback
        # to sensible defaults.  When alt_text_count is missing, derive
        # it from the length of alt_text_issues.
        result.alt_text_issues = data.get('alt_text_issues', [])
        result.alt_text_count = data.get('alt_text_count', len(result.alt_text_issues))
        result.alt_checks_total = data.get('alt_checks_total', 0)

        # Restore trust signals and policies
        result.trust_signal_issues = data.get('trust_signal_issues', [])
        result.trust_check_pages = data.get('trust_check_pages', 0)
        # Restore restricted content and crawl blocking
        result.restricted_content_pages = data.get('restricted_content_pages', [])
        result.robots_disallowed = data.get('robots_disallowed', [])
        result.meta_robots_pages = data.get('meta_robots_pages', [])
        result.restricted_check_pages = data.get('restricted_check_pages', 0)
        # Restore structured data validation
        result.structured_data_issues = data.get('structured_data_issues', [])
        result.structured_check_pages = data.get('structured_check_pages', 0)
        result.debug_logs = data.get('debug_logs', [])
        return result

class LinkCrawler:
    """Web crawler implementation"""
    def __init__(self, start_url, result_obj, session_id):
        self.start_url = start_url
        self.result = result_obj
        self.session_id = session_id
        self.visited = set()
        self.to_visit = [start_url]
        self.should_cancel = False
        self.outbound_checked = 0

        # Store full image source URLs already processed for alt text. This set helps
        # de-duplicate alt text checks across the entire crawl so the same image
        # encountered on multiple pages is only counted once.
        self.alt_seen_src = set()

        # Track image basenames seen across all product pages if we need to
        # de‑duplicate images globally.  Currently unused but kept for
        # potential future enhancements.
        self.global_image_basenames: Set[str] = set()

        # Track policy pages that have already been analysed.  This set
        # prevents redundant network requests and duplicate issue reports
        # when multiple pages link to the same shipping or return/refund
        # policy.  Each entry is the absolute URL of the policy page.
        self.analyzed_policy_pages: Set[str] = set()

        # Parse robots.txt once at the start of the crawl.  This helps
        # identify any disallowed sections that could prevent Google
        # Merchant Center from accessing product or policy pages.  Results
        # are stored on the CrawlResult so they can be reported via the UI.
        try:
            parsed = urlparse(start_url)
            robots_domain = parsed.netloc.replace('www.', '')
            robots_url = f"https://{robots_domain}/robots.txt"
            headers = {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) '
                              'AppleWebKit/537.36 (KHTML, like Gecko) '
                              'Chrome/122.0.0.0 Safari/537.36'
            }
            resp = requests.get(robots_url, headers=headers, timeout=10)
            if resp.status_code == 200:
                disallowed = []
                for line in resp.text.splitlines():
                    try:
                        line_stripped = line.strip()
                        if not line_stripped or line_stripped.startswith('#'):
                            continue
                        parts = line_stripped.split(':', 1)
                        if len(parts) == 2 and parts[0].lower() == 'disallow':
                            path = parts[1].strip()
                            if path:
                                disallowed.append(path)
                    except Exception:
                        continue
                if disallowed:
                    with self.result.lock:
                        self.result.robots_disallowed.extend(disallowed)
        except Exception:
            # Fail silently; robots.txt may be missing or inaccessible
            pass

        # Maintain a mapping from discovered URLs to the page where they were found.
        # This allows us to report the source page when a broken internal link is
        # encountered.  When scanning links, we will record parent-child
        # relationships in this dictionary; the root page will have no parent.
        self.link_parents = {}

        # Determine the normalized root domain for this crawl.  We normalise
        # the start URL’s netloc once so that internal vs external checks in
        # _crawl_page can simply compare against this value.  This avoids
        # repeated parsing on every link and prevents substring matches.
        try:
            parsed = urlparse(start_url)
            self.domain = self.normalize_domain(parsed.netloc)
        except Exception:
            # Fallback to empty string; domain validation occurs elsewhere
            self.domain = ''

        # -----------------------------------------------------------------
        # Alt text tracking for product images
        #
        # When scanning product pages, we extract image information from
        # embedded JSON contained in Shopify product pages.  To avoid
        # counting the same image multiple times (many products reuse the
        # same gallery images), we keep a set of unique image URLs that
        # have already been processed.  Each time we encounter a new image
        # not seen before, we increment result.alt_checks_total.  This
        # per‑crawl set is maintained here on the crawler instance.
        self.alt_seen_src: Set[str] = set()
        
    def normalize_domain(self, domain):
        """Normalize domain for comparison"""
        return domain.lower().replace("www.", "")
    
    def is_private_ip(self, hostname):
        """Check if hostname resolves to private IP"""
        try:
            # Get all IPs for the hostname
            ips = socket.getaddrinfo(hostname, None)
            for ip_info in ips:
                ip = ip_info[4][0]
                if ipaddress.ip_address(ip).is_private:
                    return True
            return False
        except Exception as e:
            logger.warning(f"Could not resolve hostname {hostname}: {e}")
            return True  # Assume private if can't resolve
    
    def is_valid_url(self, url):
        """Validate URL format"""
        try:
            parsed = urlparse(url)
            if not parsed.scheme or not parsed.netloc:
                return False
            if parsed.scheme not in ['http', 'https']:
                return False
            # Check for valid TLD
            if '.' not in parsed.netloc:
                return False
            return True
        except:
            return False
    
    def crawl_site(self):
        """Main crawl method"""
        try:
            parsed = urlparse(self.start_url)
            domain = self.normalize_domain(parsed.netloc)
            
            logger.info(f"Starting crawl for domain: {domain} (session: {self.session_id})")
            
            # Security check: Verify not private IP
            if self.is_private_ip(parsed.netloc):
                self.result.error = "Cannot crawl private or internal domains"
                logger.error(f"Private IP detected for {parsed.netloc}")
                return

            # DNS resolution check: ensure the domain can be resolved.  If not,
            # provide a user-friendly error instead of treating it as private.
            try:
                # Mark incomplete so that the UI waits for alt checks to finish.
                try:
                    with result.lock:
                        result.is_complete = False
                        result.save_to_redis()
                except Exception:
                    pass
                # Attempt to resolve the hostname; we don't use the result here.
                socket.gethostbyname(parsed.netloc)
            except socket.gaierror:
                self.result.error = f"Domain could not be resolved: {parsed.netloc}"
                logger.error(f"Could not resolve domain {parsed.netloc}")
                return
            
            start_time = time.time()
            pages_crawled_this_batch = 0
            batch_size = 10
            
            # Create session for connection pooling
            req_session = requests.Session()
            req_session.headers.update({
                'User-Agent': 'TerryEcomLinkChecker/1.0 (+https://terryecom.com/)',
                'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
                'Accept-Language': 'en-US,en;q=0.5',
                'Accept-Encoding': 'gzip, deflate',
                'Connection': 'keep-alive',
            })
            
            # Configure session limits
            adapter = requests.adapters.HTTPAdapter(
                pool_connections=10,
                pool_maxsize=10,
                max_retries=3
            )
            req_session.mount('http://', adapter)
            req_session.mount('https://', adapter)
            
            try:
                while self.to_visit and not self.should_cancel:
                    current_time = time.time()
                    
                    # Check timeout
                    if current_time - start_time > CRAWL_TIMEOUT:
                        self.result.error = f"Crawl timeout exceeded ({CRAWL_TIMEOUT}s)"
                        logger.warning(f"Crawl timeout after {self.result.pages_scanned} pages")
                        break
                    
                    # Check page limit
                    if self.result.pages_scanned >= MAX_PAGES:
                        logger.info(f"Reached page limit: {MAX_PAGES}")
                        break
                    
                    # Get next URL
                    if self.to_visit:
                        url = self.to_visit.pop(0)
                        if url not in self.visited and self.is_valid_url(url):
                            # Determine the page that linked to this URL, if any
                            source_page = self.link_parents.get(url)
                            # Update current URL for live display
                            self.result.update_current_url(url)
                            
                            logger.debug(f"Crawling page {self.result.pages_scanned + 1}: {url}")
                            # Pass the source_page so we can report it on 404s
                            self._crawl_page(url, domain, req_session, source_page)
                            pages_crawled_this_batch += 1

                            # Polite crawl delay
                            if not self.should_cancel:
                                time.sleep(CRAWL_DELAY)
                    
                    # Save state after each page crawl to provide near
                    # real-time updates.  Persist intermediate progress to
                    # Redis so that other workers can access up-to-date
                    # status.  If persisting fails, log the error but
                    # continue.  We reset the counter to avoid multiple
                    # saves per batch.
                    if pages_crawled_this_batch >= 1:
                        # Use debug-level logging for per-page progress to reduce
                        # log noise in production.  Logs at this level can
                        # still be enabled for detailed debugging via the
                        # logging configuration.
                        logger.debug(f"Progress: {self.result.pages_scanned} pages, "
                                     f"{len(self.result.outbound_links)} outbound, "
                                     f"{len(self.result.broken_links)} broken")
                        pages_crawled_this_batch = 0
                        try:
                            self.result.save_to_redis()
                        except Exception as e:
                            logger.debug(f"Failed to persist progress: {e}")
                        
            finally:
                req_session.close()
                
        except Exception as e:
            logger.error(f"Error in crawl_site: {e}")
            self.result.error = f"Crawl error: {str(e)}"
        finally:
            # Record end time and mark completion
            self.result.end_time = datetime.now()
            self.result.is_complete = True
            self.result.current_url = ""  # Clear current URL

            # Persist final state so that it can be retrieved by any worker
            try:
                self.result.save_to_redis()
            except Exception as e:
                logger.debug(f"Failed to persist final state: {e}")

            # Log completion
            duration = (self.result.end_time - self.result.start_time).total_seconds()
            logger.info(f"Crawl completed for {self.result.domain} in {duration:.1f}s. "
                       f"Pages: {self.result.pages_scanned}, "
                       f"Outbound: {len(self.result.outbound_links)}, "
                       f"Broken: {len(self.result.broken_links)}")
    
    def _crawl_page(self, url, domain, req_session, source_page=None):
        """Crawl a single page"""
        if self.should_cancel:
            return
        
        try:
            # Request with timeout
            response = req_session.get(url, timeout=10, allow_redirects=True)
            
            # Check status.  We treat HTTP 404 as a broken link and record
            # the source page.  Other HTTP errors (>=400) are logged but
            # not counted as broken to avoid false positives for pages
            # returning 401/403/500 etc.  Non‑200 responses that are not
            # 404 cause the crawler to skip processing the page.
            if response.status_code == 404:
                with self.result.lock:
                    self.result.broken_links.add(url)
                    if source_page:
                        self.result.broken_links_details.append((source_page, url))
                    else:
                        self.result.broken_links_details.append((url, url))
                logger.info(f"Found 404: {url}")
                return
            elif response.status_code >= 400 or response.status_code < 200:
                # Log and skip other non‑200 responses
                logger.debug(f"Skipping {url} (HTTP {response.status_code})")
                return
            
            # Verify content type
            content_type = response.headers.get('content-type', '').lower()
            if not any(ct in content_type for ct in ['text/html', 'application/xhtml']):
                logger.debug(f"Skipping non-HTML: {url}")
                return
            
            # Parse HTML
            soup = BeautifulSoup(response.text, "html.parser")
            self.visited.add(url)
            
            with self.result.lock:
                self.result.pages_scanned += 1

            # Determine if this page is considered a product page.  Product
            # pages typically have "/products/" in their path and belong to
            # the same domain.  We track how many product pages we check for
            # specific validations (title vs slug, banned keywords and alt
            # text) so that the UI can display ratios like 6/49.
            try:
                parsed_url_overall = urlparse(url)
                is_product_page = (
                    "/products/" in parsed_url_overall.path and
                    (
                        parsed_url_overall.netloc == domain or
                        parsed_url_overall.netloc.endswith('.' + domain)
                    )
                )
            except Exception:
                is_product_page = False
            if is_product_page:
                with self.result.lock:
                    self.result.title_check_pages += 1
                    self.result.banned_check_pages += 1
                    # Alt check pages are no longer tracked since the alt text
                    # checker has been removed.  Do not increment alt_check_pages.

            # -----------------------------------------------------------------
            # Product title vs slug similarity check
            #
            # If the URL looks like a product page (contains '/products/') we
            # attempt to compare the slug in the URL to the page's product
            # title.  Many e‑commerce platforms like Shopify use the URL
            # structure `/products/<slug>` for product pages.  To perform the
            # check, we:
            #   1. Extract the slug from the URL path, removing any trailing
            #      query string or fragment.
            #   2. Extract the product title from the page, preferring the
            #      `og:title` meta tag, then <h1>, then <title>.
            #   3. Normalize both strings (lowercase, remove punctuation, and
            #      replace hyphens with spaces), then compute the similarity
            #      using difflib.SequenceMatcher.
            #   4. If the similarity is below a threshold (e.g. 0.6), record
            #      the mismatch in result.title_mismatches.  This allows
            #      downstream reporting on product pages whose slugs do not
            #      closely match their titles.
            try:
                # Only perform check on product pages.  Ensure this is an
                # internal product URL by checking the path and domain.
                parsed_url = urlparse(url)
                if "/products/" in parsed_url.path and (
                    parsed_url.netloc == domain or parsed_url.netloc.endswith('.' + domain)
                ):
                    # Extract slug from the last segment of the path
                    slug_part = parsed_url.path.rstrip('/').split('/')[-1]
                    slug_clean = slug_part.split('?')[0].split('#')[0]
                    # Replace hyphens with spaces for comparison
                    slug_normalized = re.sub(r'[^a-z0-9]+', ' ', slug_clean.lower())
                    # Extract product title from common locations
                    product_title = None
                    # Prefer Open Graph title if available
                    meta_tag = soup.find('meta', attrs={'property': 'og:title'})
                    if meta_tag and meta_tag.get('content'):
                        product_title = meta_tag['content']
                    if not product_title:
                        # Try Twitter title
                        meta_tag = soup.find('meta', attrs={'name': 'twitter:title'})
                        if meta_tag and meta_tag.get('content'):
                            product_title = meta_tag['content']
                    if not product_title:
                        # Try first H1 tag
                        h1_tag = soup.find('h1')
                        if h1_tag:
                            product_title = h1_tag.get_text(strip=True)
                    if not product_title:
                        # Fallback to page title
                        title_tag = soup.find('title')
                        if title_tag:
                            product_title = title_tag.get_text(strip=True)
                    if product_title:
                        # Normalise title: lowercase, remove punctuation
                        title_normalized = re.sub(r'[^a-z0-9]+', ' ', product_title.lower())
                        # Compute similarity between slug and title
                        similarity = difflib.SequenceMatcher(
                            None, slug_normalized.strip(), title_normalized.strip()
                        ).ratio()
                        # Record mismatch if similarity below threshold (0.6)
                        if similarity < 0.6:
                            with self.result.lock:
                                self.result.title_mismatches.append(
                                    (url, slug_clean, product_title, similarity)
                                )
                            # Persist mismatch to Redis for cross-worker visibility
                            try:
                                self.result.save_to_redis()
                            except Exception:
                                pass
            except Exception as e:
                # Log at debug level; do not interrupt crawling
                logger.debug(f"Error checking product slug/title for {url}: {e}")

            # -----------------------------------------------------------------
            # Banned keyword scanning
            #
            # If this is a product page (contains '/products/' and belongs to the
            # same domain), check the product title and description for any
            # banned keywords.  We build a text string from common title and
            # description tags (og:title, twitter:title, h1, title and og:description,
            # twitter:description, meta description), then search for any of the
            # banned keywords in that text.  If any banned words are found, we
            # record the page along with the list of detected keywords and a
            # ratio representing the fraction of banned words found.
            try:
                # Use previously parsed URL if available
                parsed_url_banned = None
                try:
                    parsed_url_banned = parsed_url
                except Exception:
                    parsed_url_banned = urlparse(url)
                if parsed_url_banned and "/products/" in parsed_url_banned.path:
                    # Normalise the netloc for comparison against the crawl domain
                    page_netloc = self.normalize_domain(parsed_url_banned.netloc)
                    if page_netloc == self.domain or page_netloc.endswith('.' + self.domain):
                        text_fragments = []
                        # Get product title from various meta tags or page elements
                        product_title_local = None
                        tag = soup.find('meta', attrs={'property': 'og:title'})
                        if tag and tag.get('content'):
                            product_title_local = tag['content']
                        if not product_title_local:
                            tag = soup.find('meta', attrs={'name': 'twitter:title'})
                            if tag and tag.get('content'):
                                product_title_local = tag['content']
                        if not product_title_local:
                            h1_tag_local = soup.find('h1')
                            if h1_tag_local:
                                product_title_local = h1_tag_local.get_text(strip=True)
                        if not product_title_local:
                            title_tag_local = soup.find('title')
                            if title_tag_local:
                                product_title_local = title_tag_local.get_text(strip=True)
                        if product_title_local:
                            text_fragments.append(product_title_local)
                        # Get product description from og:description, twitter:description, or meta description
                        meta_desc = None
                        for attr_name, attr_value in [("property", "og:description"), ("name", "twitter:description"), ("name", "description")]:
                            tag = soup.find('meta', attrs={attr_name: attr_value})
                            if tag and tag.get('content'):
                                meta_desc = tag['content']
                                break
                        if meta_desc:
                            text_fragments.append(meta_desc)
                        if text_fragments:
                            combined_text = " ".join(text_fragments).lower()
                            found_words = []
                            for banned in BANNED_KEYWORDS:
                                try:
                                    if banned.lower() in combined_text:
                                        found_words.append(banned)
                                except Exception:
                                    continue
                            if found_words:
                                ratio = len(found_words) / len(BANNED_KEYWORDS) if len(BANNED_KEYWORDS) > 0 else 0.0
                                with self.result.lock:
                                    self.result.banned_keyword_pages.append((url, found_words, ratio))
                                try:
                                    self.result.save_to_redis()
                                except Exception:
                                    pass
            except Exception as e:
                logger.debug(f"Error scanning banned keywords for {url}: {e}")

            # -----------------------------------------------------------------
            # Alt text validation
            #
            # Historically the crawler delegated all alt text checks to a
            # secondary pass against Shopify’s product JSON feed.  However
            # some storefronts block access to `/products.json` or product
            # sitemaps altogether (returning HTTP 403), which means no
            # images are ever counted and the denominator falls back to the
            # number of pages scanned.  To provide a more reliable and
            # immediate measure of accessibility, we perform a lightweight
            # alt text scan directly on each product page.  This scan
            # inspects every `<img>` tag, deduplicates images across the
            # entire crawl, counts the total number of unique images seen
            # and flags missing, generic or irrelevant alt attributes.
            try:
                # Determine if the current page is a product page under the
                # crawled domain.  We reuse parsed_url if available; fall back
                # to parsing the URL directly.
                parsed_url_alt = None
                try:
                    parsed_url_alt = parsed_url
                except Exception:
                    parsed_url_alt = urlparse(url)
                if parsed_url_alt and "/products/" in parsed_url_alt.path:
                    page_netloc_alt = self.normalize_domain(parsed_url_alt.netloc)
                    if (page_netloc_alt == self.domain or
                            page_netloc_alt.endswith('.' + self.domain)):
                        # Attempt to extract a representative product title.  This
                        # value is used to compute similarity with the image
                        # alt attribute.  We try multiple meta tags and
                        # fall back to <h1> or <title> elements.
                        product_title_for_alt = None
                        tag = soup.find('meta', attrs={'property': 'og:title'})
                        if tag and tag.get('content'):
                            product_title_for_alt = tag['content']
                        if not product_title_for_alt:
                            tag = soup.find('meta', attrs={'name': 'twitter:title'})
                            if tag and tag.get('content'):
                                product_title_for_alt = tag['content']
                        if not product_title_for_alt:
                            h1_tag_for_alt = soup.find('h1')
                            if h1_tag_for_alt:
                                product_title_for_alt = h1_tag_for_alt.get_text(strip=True)
                        if not product_title_for_alt:
                            title_tag_for_alt = soup.find('title')
                            if title_tag_for_alt:
                                product_title_for_alt = title_tag_for_alt.get_text(strip=True)
                        title_norm = (product_title_for_alt.lower().replace('-', ' ').strip()
                                      if product_title_for_alt else '')
                        # Iterate over all image tags on the page.  For each
                        # unique image (deduplicated across the crawl), count
                        # it and evaluate its alt attribute.
                        for img_tag in soup.find_all('img'):
                            try:
                                src_attr = img_tag.get('src') or ''
                                if not src_attr:
                                    continue
                                # Resolve relative URLs to absolute.  Use
                                # urljoin to build a full image URL based on
                                # the current page.  Remove fragments from
                                # the URL to ensure consistent deduplication.
                                full_src = urljoin(url, src_attr)
                                full_src = urldefrag(full_src)[0]
                                # Only process each unique image once across
                                # the entire crawl.  This avoids inflating
                                # denominators when the same image appears
                                # on multiple product pages.
                                if full_src in self.alt_seen_src:
                                    continue
                                self.alt_seen_src.add(full_src)
                                # Increment total images scanned for alt text.
                                with self.result.lock:
                                    self.result.alt_checks_total += 1
                                # Retrieve alt attribute if present.
                                alt_attr = img_tag.get('alt')
                                if not alt_attr or not alt_attr.strip():
                                    # Missing alt attribute
                                    with self.result.lock:
                                        self.result.alt_text_issues.append((url, full_src, '(missing)', 'missing', None))
                                        self.result.alt_text_count = len(self.result.alt_text_issues)
                                    continue
                                alt_clean = alt_attr.strip()
                                # Generic alt if fewer than two words
                                if len(alt_clean.split()) < 2:
                                    with self.result.lock:
                                        self.result.alt_text_issues.append((url, full_src, alt_clean, 'generic', None))
                                        self.result.alt_text_count = len(self.result.alt_text_issues)
                                    continue
                                # Similarity check with the product title
                                if title_norm:
                                    try:
                                        sim_val = difflib.SequenceMatcher(None, alt_clean.lower(), title_norm).ratio()
                                    except Exception:
                                        sim_val = 0.0
                                    if sim_val < 0.4:
                                        with self.result.lock:
                                            self.result.alt_text_issues.append((url, full_src, alt_clean, 'low similarity', sim_val))
                                            self.result.alt_text_count = len(self.result.alt_text_issues)
                            except Exception:
                                # Continue scanning other images even if one fails
                                continue
                        # Persist updated alt text counts so the UI can
                        # reflect progress in near real time.  Errors during
                        # persistence are logged at debug level but do not
                        # interrupt crawling.
                        try:
                            self.result.save_to_redis()
                        except Exception as e:
                            logger.debug(f"Failed to persist alt text progress: {e}")
            except Exception as e:
                logger.debug(f"Error performing alt text scan for {url}: {e}")

            # -----------------------------------------------------------------
            # Trust signals & policies check
            #
            # Examine the current page for evidence of contact information,
            # required legal/policy pages, and HTTPS enforcement.  Contact
            # information (email, phone number, physical address) and
            # policies (Terms, Shipping, Returns, Privacy) are essential for
            # Merchant Center compliance.  This check records missing items
            # in result.trust_signal_issues and increments a page counter.
            try:
                self._check_trust_policies(url, soup)
            except Exception as e:
                logger.debug(f"Error checking trust signals for {url}: {e}")

            # -----------------------------------------------------------------
            # Restricted content & blocking directives check
            #
            # Scan for prohibited categories, robots meta tags and update
            # restricted content issues.  This check helps identify pages
            # containing content that could violate Google policies or pages
            # inadvertently blocked from crawling via meta robots tags.
            try:
                self._check_restricted_content(url, soup)
            except Exception as e:
                logger.debug(f"Error checking restricted content for {url}: {e}")

            # -----------------------------------------------------------------
            # Structured data validation check
            #
            # Validate schema.org Product markup on product pages.  Only run
            # this check for pages identified as product pages (contains
            # '/products/' and belongs to the same domain).  Issues are
            # recorded in result.structured_data_issues.
            try:
                # Reuse earlier determination of product page if available
                is_prod = False
                try:
                    is_prod = is_product_page
                except Exception:
                    # Fallback: simple check
                    is_prod = "/products/" in url
                if is_prod:
                    self._check_structured_data(url, soup)
            except Exception as e:
                logger.debug(f"Error validating structured data for {url}: {e}")

            # Extract all links
            links_found = 0
            for a_tag in soup.find_all("a", href=True):
                if self.should_cancel:
                    break
                
                href = a_tag['href'].strip()
                
                # Skip invalid hrefs
                if not href or href == "#":
                    continue
                
                # Skip javascript and tel links
                if href.lower().startswith(("javascript:", "tel:")):
                    continue
                
                # Handle mailto links.  We treat mailto links as outbound and
                # record the page where they were found.  Only the first
                # occurrence of a given mailto link is stored in both
                # outbound_links and outbound_links_details.
                if href.startswith("mailto:"):
                    # Exclude mailto links to the same domain (should rarely happen)
                    if domain not in href.lower():
                        with self.result.lock:
                            if href not in self.result.outbound_links:
                                self.result.outbound_links.add(href)
                                # Record where this mailto link was found
                                self.result.outbound_links_details.append((url, href))
                    continue
                
                try:
                    # Resolve relative URLs
                    full_url = urljoin(url, href)
                    # Remove fragment
                    clean_url = urldefrag(full_url)[0]
                    
                    if not self.is_valid_url(clean_url):
                        continue
                    
                    parsed = urlparse(clean_url)
                    netloc = self.normalize_domain(parsed.netloc)
                    
                    # Check if internal or external.  Treat a link as internal
                    # if its normalised netloc exactly matches the root domain
                    # or is a subdomain of it (endswith ".<domain>").  This
                    # avoids false positives where the domain string appears
                    # inside an unrelated hostname (e.g. example.com in
                    # notexample.com).
                    if netloc == self.domain or netloc.endswith('.' + self.domain):
                        # Internal link
                        if (
                            clean_url not in self.visited and
                            clean_url not in self.to_visit and
                            self.result.pages_scanned + len(self.to_visit) < MAX_PAGES
                        ):
                            self.to_visit.append(clean_url)
                            # Record the parent page so we can report which
                            # page contained a broken link if this target
                            # ultimately resolves to a 404.
                            self.link_parents[clean_url] = url
                            links_found += 1
                    else:
                        # External link
                        if not any(excluded in netloc for excluded in EXCLUDED_DOMAINS):
                            with self.result.lock:
                                if clean_url not in self.result.outbound_links:
                                    self.result.outbound_links.add(clean_url)
                                    # Record the page where this outbound link was found
                                    self.result.outbound_links_details.append((url, clean_url))
                                    # Check if external link is broken (limited)
                                    if self.outbound_checked < MAX_OUTBOUND_CHECKS:
                                        # Pass the current page URL so we know where the broken link was found
                                        self._check_outbound_link(clean_url, req_session, source_page=url)
                                        self.outbound_checked += 1
                                    
                except Exception as e:
                    logger.debug(f"Error processing link {href}: {e}")
                    continue
            
            logger.debug(f"Found {links_found} internal links on {url}")
            
        except requests.exceptions.Timeout:
            logger.warning(f"Timeout crawling {url}")
        except requests.exceptions.RequestException as e:
            logger.warning(f"Request error crawling {url}: {e}")
        except Exception as e:
            logger.error(f"Error crawling {url}: {e}")
    
    def _check_outbound_link(self, url, req_session, source_page=None):
        """Check if outbound link is broken (404) and record the source page."""
        try:
            # Use HEAD request first (faster)
            response = req_session.head(url, timeout=5, allow_redirects=True)

            # Some servers don't support HEAD
            if response.status_code == 405:
                response = req_session.get(url, timeout=5, allow_redirects=True, stream=True)
                response.close()

            # Treat any 4xx/5xx as broken
            if response.status_code >= 400:
                with self.result.lock:
                    if url not in self.result.broken_links:
                        self.result.broken_links.add(url)
                    # Record the source page if provided
                    if source_page:
                        self.result.broken_links_details.append((source_page, url))
                    else:
                        self.result.broken_links_details.append((url, url))
                # Persist the updated broken links list to Redis
                try:
                    self.result.save_to_redis()
                except Exception as e:
                    logger.debug(f"Failed to persist broken link update: {e}")
                if response.status_code == 404:
                    logger.info(f"Found broken outbound link (404): {url}")
                else:
                    logger.warning(f"Broken outbound link (HTTP {response.status_code}): {url}")

        except Exception as e:
            logger.debug(f"Could not check outbound link {url}: {e}")

    # -------------------------------------------------------------------------
    # New check functions for GMC Scout V1
    #
    def _check_trust_policies(self, url: str, soup: BeautifulSoup) -> None:
        """
        Check for trust signals and required policy pages on the current page.

        This method inspects the page content for contact information
        (email, phone, physical address), links to legal pages (Terms,
        Shipping, Returns/Refunds, Privacy) and verifies that the page is
        served over HTTPS.  Any missing items are recorded on the
        CrawlResult.trust_signal_issues list along with the URL.

        Args:
            url: The URL of the page being checked.
            soup: BeautifulSoup object for the page HTML.
        """
        # Increment page counter
        with self.result.lock:
            self.result.trust_check_pages += 1
        contact_issues: list[str] = []
        policy_issues: list[str] = []
        ssl_issues: list[str] = []
        try:
            text = soup.get_text(separator=' ', strip=True)
        except Exception:
            text = ''
        # Email detection
        try:
            if not re.search(r"[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}", text):
                contact_issues.append('missing email')
        except Exception:
            pass
        # Phone detection (simple pattern for digits, spaces, dashes, brackets)
        try:
            if not re.search(r"\+?\d[\d\s\-()]{7,}", text):
                contact_issues.append('missing phone number')
        except Exception:
            pass
        # Physical address detection: search for common street keywords
        try:
            address_keywords = ['street', 'st.', 'road', 'rd', 'avenue', 'ave', 'lane', 'ln', 'drive', 'dr', 'boulevard', 'blvd']
            found_address = any(kw in text.lower() for kw in address_keywords)
            if not found_address:
                contact_issues.append('missing physical address')
        except Exception:
            pass
        # Legal pages detection: search for anchor tags containing policy keywords
        try:
            policy_keywords = {
                'terms': ['terms', 'conditions', 'terms of service', 'terms & conditions'],
                'shipping': ['shipping', 'delivery'],
                'returns': ['return', 'refund', 'exchange'],
                'privacy': ['privacy']
            }
            # Normalize anchor text and capture policy links when found
            found_policies = {k: False for k in policy_keywords.keys()}
            policy_links: Dict[str, str] = {}
            for a in soup.find_all('a'):
                try:
                    anchor_text = a.get_text(strip=True).lower()
                    href = a.get('href') or ''
                    for key, variants in policy_keywords.items():
                        if found_policies[key]:
                            continue
                        for variant in variants:
                            if variant in anchor_text:
                                found_policies[key] = True
                                # Record the first encountered link for this policy
                                if href:
                                    try:
                                        abs_link = urljoin(url, href)
                                        policy_links.setdefault(key, abs_link)
                                    except Exception:
                                        pass
                                break
                    # early exit if all found
                    if all(found_policies.values()):
                        break
                except Exception:
                    continue
            # For each required policy not found, append to issues
            for key, present in found_policies.items():
                if not present:
                    policy_issues.append(f'missing {key} policy')
            # Analyse shipping and return/refund policy pages for compliance
            # only once per unique URL to avoid redundant requests
            # Analyse shipping policy
            ship_url = policy_links.get('shipping')
            if ship_url and ship_url not in self.analyzed_policy_pages:
                try:
                    ship_issues = self._analyze_shipping_policy(ship_url)
                    if ship_issues:
                        policy_issues.extend([f'shipping policy: {msg}' for msg in ship_issues])
                    self.analyzed_policy_pages.add(ship_url)
                except Exception:
                    pass
            # Analyse returns/refund policy
            ret_url = policy_links.get('returns')
            if ret_url and ret_url not in self.analyzed_policy_pages:
                try:
                    ret_issues = self._analyze_return_policy(ret_url)
                    if ret_issues:
                        policy_issues.extend([f'return policy: {msg}' for msg in ret_issues])
                    self.analyzed_policy_pages.add(ret_url)
                except Exception:
                    pass
        except Exception:
            pass
        # SSL/HTTPS check: require HTTPS scheme
        try:
            if not url.lower().startswith('https://'):
                ssl_issues.append('page not served over HTTPS')
        except Exception:
            pass
        # Additional Merchant Center compliance heuristics
        try:
            # Lowercase text for searching
            text_lower = text.lower()
            # Flag unrealistic or prohibited promotional claims.  Do not flag
            # common marketing phrases such as "free shipping" or "free returns",
            # which are allowed.  Terms like "best price", "lowest price",
            # "100%" or "guaranteed" are considered unrealistic under
            # misrepresentation guidelines.
            banned_claims = [
                # Flag marketing language that implies unrealistic promises.  Do
                # not include generic numeric phrases like "100%" or "100 percent"
                # since these can legitimately refer to product materials (e.g.,
                # "100% cotton").
                'best price', 'lowest price', 'guaranteed', 'no risk', 'money back guarantee'
            ]
            for claim in banned_claims:
                try:
                    if claim in text_lower:
                        policy_issues.append(f'unrealistic claim: {claim}')
                        break
                except Exception:
                    continue
        except Exception:
            pass

        # Additional checks specific to product pages.  If the URL indicates a
        # product page, verify that key elements are present: price, a purchase
        # button and availability information.  This helps catch cases where
        # products are not directly purchasable or have incomplete data.
        try:
            parsed_url_local = urlparse(url)
            if '/products/' in parsed_url_local.path:
                # Check for price pattern (currency symbols followed by numbers)
                has_price = False
                try:
                    # Look for common currency symbols followed by digits, e.g. $49 or £30
                    if re.search(r'[\$£€]\s?\d+', text_lower):
                        has_price = True
                except Exception:
                    pass
                if not has_price:
                    policy_issues.append('product page missing price')
                # Check for purchase button keywords
                if not any(keyword in text_lower for keyword in ['add to cart', 'add to basket', 'buy now', 'add-to-cart']):
                    policy_issues.append('product page missing purchase button')
                # Check for availability information (in stock / out of stock)
                if not any(keyword in text_lower for keyword in ['in stock', 'out of stock', 'available']):
                    policy_issues.append('product availability not specified')
        except Exception:
            pass
        # Summarise results and add to debug log
        try:
            summary_parts = []
            if contact_issues:
                summary_parts.append('contact issues: ' + ', '.join(contact_issues))
            if policy_issues:
                summary_parts.append('policy issues: ' + ', '.join(policy_issues))
            if ssl_issues:
                summary_parts.append('ssl issues: ' + ', '.join(ssl_issues))
            if not summary_parts:
                summary = f"{url} - Trust check: PASS"
            else:
                summary = f"{url} - Trust check: FAIL - " + '; '.join(summary_parts)
            with self.result.lock:
                self.result.debug_logs.append(summary)
        except Exception:
            pass
        # Record issues if any exist
        if contact_issues or policy_issues or ssl_issues:
            with self.result.lock:
                self.result.trust_signal_issues.append((url, contact_issues, policy_issues, ssl_issues))

    def _check_restricted_content(self, url: str, soup: BeautifulSoup) -> None:
        """
        Scan the page for restricted content categories and meta robots tags.

        This method looks for keywords associated with prohibited categories
        such as weapons, tobacco, explosives, adult content and counterfeits.
        It also examines meta robots directives to identify pages that block
        indexing or following.  Results are stored on the CrawlResult.

        Args:
            url: The page URL.
            soup: BeautifulSoup instance.
        """
        # Increment restricted content page counter
        with self.result.lock:
            self.result.restricted_check_pages += 1
        categories_found: list[str] = []
        try:
            page_text = soup.get_text(separator=' ', strip=True).lower()
        except Exception:
            page_text = ''
        # Define prohibited keyword categories.  Each entry is a tuple of
        # (category_name, list of keywords)
        prohibited_categories = [
            ('weapons', ['weapon', 'firearm', 'gun', 'rifle', 'pistol', 'ammo', 'ammunition']),
            ('tobacco', ['tobacco', 'cigarette', 'cigar', 'vape', 'nicotine']),
            ('explosives', ['explosive', 'bomb', 'grenade', 'dynamite']),
            ('alcohol', ['alcohol', 'beer', 'wine', 'whiskey', 'vodka']),
            ('adult', ['porn', 'adult', 'xxx', 'erotic', 'sex toy']),
            ('counterfeit', ['counterfeit', 'fake', 'replica']),
            ('controlled', ['opioid', 'marijuana', 'cocaine', 'heroin', 'methamphetamine'])
        ]
        try:
            for category, keywords in prohibited_categories:
                for kw in keywords:
                    if kw in page_text:
                        categories_found.append(category)
                        break
        except Exception:
            pass
        # Meta robots detection
        meta_issues: list[str] = []
        try:
            for meta in soup.find_all('meta'):
                try:
                    name_attr = (meta.get('name') or meta.get('property') or '').lower()
                    content_attr = (meta.get('content') or '').lower()
                    if name_attr in ['robots', 'googlebot'] and content_attr:
                        # record content of meta robots tag
                        meta_issues.append(content_attr)
                except Exception:
                    continue
        except Exception:
            pass
        # Record meta robots restrictions
        if meta_issues:
            with self.result.lock:
                self.result.meta_robots_pages.append((url, meta_issues))
        # Record restricted categories
        if categories_found:
            with self.result.lock:
                self.result.restricted_content_pages.append((url, categories_found))
        # Add to debug log summarising restricted content check
        try:
            summary_parts = []
            if categories_found:
                summary_parts.append('restricted categories: ' + ', '.join(categories_found))
            if meta_issues:
                summary_parts.append('meta robots: ' + ', '.join(meta_issues))
            # robots.txt disallows recorded separately; they are global and logged elsewhere
            if not summary_parts:
                summary = f"{url} - Restricted check: PASS"
            else:
                summary = f"{url} - Restricted check: FAIL - " + '; '.join(summary_parts)
            with self.result.lock:
                self.result.debug_logs.append(summary)
        except Exception:
            pass

    def _check_structured_data(self, url: str, soup: BeautifulSoup) -> None:
        """
        Validate schema.org Product structured data on the page.

        This method searches for JSON‑LD scripts and microdata representing
        Product entities.  It then verifies that required fields (name,
        description, image, price, availability) are present and well
        formatted.  Any missing or invalid fields are recorded on the
        CrawlResult.

        Args:
            url: URL of the page being validated.
            soup: Parsed HTML.
        """
        # Increment structured data page counter
        with self.result.lock:
            self.result.structured_check_pages += 1
        errors: list[str] = []
        # Helper to validate a Product object
        def validate_product_schema(product_data: dict, container_label: str = ''):
            local_errors: list[str] = []
            # Required fields and simple type checks
            required_fields = ['name', 'description', 'image', 'price', 'availability']
            for field in required_fields:
                if field not in product_data or not product_data[field]:
                    local_errors.append(f"missing {field}")
            # If price is present, ensure it contains digits and optionally currency symbol
            price_val = product_data.get('price')
            if price_val:
                try:
                    # Accept formats like 9.99, 9, 9.99 USD
                    price_str = str(price_val)
                    if not re.search(r"\d", price_str):
                        local_errors.append('invalid price')
                except Exception:
                    local_errors.append('invalid price')
            # Availability: check against known statuses
            avail_val = product_data.get('availability')
            if avail_val:
                valid_avail = ['instock', 'in stock', 'outofstock', 'out of stock', 'preorder', 'backorder']
                if str(avail_val).lower() not in valid_avail:
                    local_errors.append('invalid availability')
            if local_errors:
                for err in local_errors:
                    errors.append(f"{container_label}{err}")

        # JSON-LD detection
        try:
            for script in soup.find_all('script', type='application/ld+json'):
                try:
                    json_text = script.string or ''
                    data = json.loads(json_text)
                    # JSON-LD may be a list or dict
                    items = data if isinstance(data, list) else [data]
                    for item in items:
                        try:
                            if isinstance(item, dict):
                                item_type = item.get('@type') or item.get('type')
                                # Some implementations wrap Product in '@graph'
                                if not item_type and '@graph' in item:
                                    for subitem in item['@graph']:
                                        try:
                                            sub_type = subitem.get('@type') or subitem.get('type')
                                            if sub_type and 'product' in str(sub_type).lower():
                                                validate_product_schema(subitem, '')
                                        except Exception:
                                            continue
                                    continue
                                if item_type and 'product' in str(item_type).lower():
                                    validate_product_schema(item, '')
                        except Exception:
                            continue
                except Exception:
                    continue
        except Exception:
            pass
        # Microdata detection: look for itemscope/itemtype
        try:
            for tag in soup.find_all(attrs={'itemscope': True, 'itemtype': True}):
                try:
                    item_type = tag.get('itemtype')
                    if item_type and 'product' in item_type.lower():
                        # Collect itemprops from children
                        data = {}
                        for child in tag.find_all(attrs={'itemprop': True}):
                            try:
                                prop = child.get('itemprop')
                                value = child.get('content') or child.get_text(strip=True)
                                if prop and value:
                                    data[prop] = value
                            except Exception:
                                continue
                        validate_product_schema(data, '')
                except Exception:
                    continue
        except Exception:
            pass
        # Record errors
        if errors:
            with self.result.lock:
                self.result.structured_data_issues.append((url, errors))
        # Log structured data results
        try:
            if errors:
                summary = f"{url} - Structured data: FAIL - " + '; '.join(errors)
            else:
                summary = f"{url} - Structured data: PASS"
            with self.result.lock:
                self.result.debug_logs.append(summary)
        except Exception:
            pass

    # ---------------------------------------------------------------------
    # Policy page analysis helpers
    #
    def _analyze_shipping_policy(self, page_url: str) -> List[str]:
        """Download and analyse a shipping policy page for required content.

        Returns a list of human‑readable issue descriptions when required
        information is missing.  This function does not raise exceptions on
        network errors; instead, it returns a single issue explaining the
        failure.
        """
        issues: List[str] = []
        try:
            headers = {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) '
                              'AppleWebKit/537.36 (KHTML, like Gecko) '
                              'Chrome/122.0.0.0 Safari/537.36'
            }
            resp = requests.get(page_url, headers=headers, timeout=10)
            if resp.status_code != 200:
                issues.append('inaccessible (HTTP ' + str(resp.status_code) + ')')
                return issues
            soup = BeautifulSoup(resp.text, 'html.parser')
            text = soup.get_text(separator=' ', strip=True).lower()
            # Ensure the page talks about shipping or delivery
            if not any(word in text for word in ['shipping', 'delivery']):
                issues.append('missing shipping/delivery information')
            # Check for estimated delivery time (looks for numbers with days/weeks)
            if not re.search(r'\b\d+\s*(business\s*)?(day|days|week|weeks)\b', text):
                issues.append('missing estimated delivery time')
            # Check for cost information (mentions cost, fee, charge, price or free)
            if not any(word in text for word in ['free', 'cost', 'fee', 'charge', 'price']):
                issues.append('missing shipping cost information')
        except Exception:
            issues.append('failed to fetch shipping policy')
        return issues

    def _analyze_return_policy(self, page_url: str) -> List[str]:
        """Download and analyse a return/refund policy page for required content.

        Returns a list of issue descriptions if essential elements are missing.
        """
        issues: List[str] = []
        try:
            headers = {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) '
                              'AppleWebKit/537.36 (KHTML, like Gecko) '
                              'Chrome/122.0.0.0 Safari/537.36'
            }
            resp = requests.get(page_url, headers=headers, timeout=10)
            if resp.status_code != 200:
                issues.append('inaccessible (HTTP ' + str(resp.status_code) + ')')
                return issues
            soup = BeautifulSoup(resp.text, 'html.parser')
            text = soup.get_text(separator=' ', strip=True).lower()
            # Ensure the policy mentions returns, refunds or exchanges
            if not any(word in text for word in ['return', 'refund', 'exchange']):
                issues.append('missing returns/refunds section')
            # Check for return period (number with days/weeks)
            if not re.search(r'\b\d+\s*(business\s*)?(day|days|week|weeks)\b', text):
                issues.append('missing return period')
            # Check for condition requirements (unused, original, packaging)
            if not any(word in text for word in ['unused', 'original', 'packaging', 'receipt', 'condition']):
                issues.append('missing condition requirements')
            # Check for instructions or contact details
            if not any(word in text for word in ['contact', 'email', 'support', 'address', 'phone']):
                issues.append('missing return instructions or contact information')
        except Exception:
            issues.append('failed to fetch return policy')
        return issues

def normalize_url(url):
    """Normalize and validate URL input.

    This function accepts a user‑provided domain or URL, trims whitespace,
    ensures a scheme is present, validates the domain format and TLD, and
    returns a normalised URL. Unlike the previous implementation which
    stripped any existing scheme and forced HTTPS, this version preserves
    the user‑supplied scheme if present and only prepends ``https://`` when
    no scheme is provided. It also validates the domain without the ``www.``
    prefix but does not remove it from the returned URL.
    """
    if not url:
        raise ValueError("URL cannot be empty")

    url = url.strip()

    # If the URL does not start with http:// or https://, default to https://
    if not re.match(r'^https?://', url, re.IGNORECASE):
        # Remove a leading www. when adding a scheme to avoid double slashes
        url_no_scheme = re.sub(r'^(www\.)?', '', url, flags=re.IGNORECASE)
        url = f"https://{url_no_scheme}"

    parsed = urlparse(url)

    # Extract the network location for validation (lowercase for comparison)
    netloc = parsed.netloc.lower()

    # Remove a leading www. for validation only
    domain = netloc.replace('www.', '', 1)

    # Validate presence of domain
    if not domain:
        raise ValueError("Invalid domain")

    # Check for valid TLD (must contain a dot)
    if '.' not in domain:
        raise ValueError("Domain must have a valid TLD")

    # Validate domain format using RFC‑compliant pattern
    # Domain labels must start and end with an alphanumeric and can contain hyphens in between.
    domain_pattern = r'^[a-zA-Z0-9]([a-zA-Z0-9\-]{0,61}[a-zA-Z0-9])?(\.[a-zA-Z0-9]([a-zA-Z0-9\-]{0,61}[a-zA-Z0-9])?)*\.[a-zA-Z]{2,}$'
    if not re.match(domain_pattern, domain):
        raise ValueError("Invalid domain format")

    # Return the fully qualified URL (preserves path/query/fragment)
    return parsed.geturl()

# -----------------------------------------------------------------------------
# Celery task to perform the crawl asynchronously
#
# When a crawl is requested, the /crawl endpoint enqueues this task.  The task
# retrieves or initialises a CrawlResult object, runs the crawler, and
# periodically persists progress to Redis.  Upon completion, it saves the
# final state.
@celery_app.task
def run_crawl(session_id, start_url):
    """Celery task to perform a crawl asynchronously."""
    # Attempt to retrieve existing result from Redis; otherwise create new
    try:
        existing = redis_client.get(session_id)
        if existing:
            try:
                result_dict = pickle.loads(existing)
                result = CrawlResult.from_dict(result_dict)
            except Exception:
                # If unpickling fails, fall back to new result
                result = None
        else:
            result = None
    except Exception:
        result = None

    if result is None:
        # Determine domain and create new CrawlResult
        parsed = urlparse(start_url)
        domain = parsed.netloc.replace('www.', '')
        result = CrawlResult(domain)
    result.session_id = session_id
    # Save initial state to Redis
    result.save_to_redis()
    # Create and run crawler
    crawler = LinkCrawler(start_url, result, session_id)
    # Store crawler in-memory for this worker to support cancellation
    crawl_sessions[session_id] = {'result': result, 'crawler': crawler}
    try:
        # Run the crawl; it will update result as it goes
        crawler.crawl_site()
        # After crawl completes, perform alt text validation via Shopify's
        # products JSON feed.  This check runs once at the end of the crawl
        # and populates alt_text_issues, alt_text_count, and alt_checks_total
        # for the current session.  Wrap in a separate try/except so that
        # failures do not interrupt saving the crawl state.
        try:
            # Perform a secondary alt text validation using product JSON.  This
            # fallback runs when no images were processed during the page‑level
            # crawl (alt_checks_total == 0).  It uses the sitemap to discover
            # product handles and fetches each product's JSON individually,
            # extracting alt attributes from the product images.  If no
            # handles are discovered or JSON endpoints fail, the existing
            # check via /products.json is attempted as a secondary fallback.
            try:
                issues, alt_total = _check_alt_text_via_product_json(result.domain)
                # Always update the alt text results, regardless of whether
                # previous alt checks were recorded.  This ensures that
                # alt_checks_total and alt_text_count are persisted for the UI.
                if alt_total > 0:
                    # When product JSON returns alt text data, update the result
                    # inside the lock to prevent concurrent writes from other threads.
                    with result.lock:
                        result.alt_text_issues.extend(issues)
                        result.alt_text_count = len(result.alt_text_issues)
                        result.alt_checks_total += alt_total
                        # Mark progress complete when alt checks finish so the UI waits
                        result.last_progress = 100.0
                        # Mark crawl as complete now that alt checks finished
                        result.is_complete = True
                        result.save_to_redis()
                else:
                    # As a fallback, attempt to use the /products.json feed.
                    legacy_issues = check_alt_text_shopify(result.domain)
                    products = fetch_shopify_products(result.domain)
                    seen_srcs: set = set()
                    if products:
                        for product in products:
                            try:
                                for image in product.get('images', []):
                                    src = image.get('src') or ''
                                    if src:
                                        seen_srcs.add(src)
                            except Exception:
                                continue
                    # The alt_total_legacy value counts unique image sources from the fallback
                    alt_total_legacy = len(seen_srcs)
                    with result.lock:
                        result.alt_text_issues.extend(legacy_issues)
                        result.alt_text_count = len(result.alt_text_issues)
                        result.alt_checks_total += alt_total_legacy
                        # Ensure progress is marked as complete when fallback finishes
                        result.last_progress = 100.0
                        # Mark crawl as complete now that alt checks finished
                        result.is_complete = True
                        result.save_to_redis()
            except Exception as alt_exc:
                logger.debug(f"Product JSON alt text check failed: {alt_exc}")
        except Exception as exc:
            logger.warning(f"Alt text check failed for {result.domain}: {exc}")
    finally:
        # Persist final state to Redis (including alt text results)
        result.save_to_redis()
        # Only remove the session from the in-memory store if Celery is enabled.
        # When running synchronously (USE_CELERY=false), keep the session in memory
        # so that the UI can fetch the final status after the crawl completes.
        # A periodic cleanup thread will eventually remove old sessions.
        use_celery_cleanup = os.environ.get('USE_CELERY', 'true').lower() == 'true'
        if use_celery_cleanup and session_id in crawl_sessions:
            del crawl_sessions[session_id]

def send_feedback_email(email, message, ip, user_agent):
    """Send feedback email or log to file"""
    try:
        if not SMTP_USERNAME or not SMTP_PASSWORD:
            # Log to file if email not configured
            logger.info(f"Feedback from {email or 'anonymous'} ({ip}): {message[:100]}...")
            return True
        
        msg = MIMEMultipart()
        msg['From'] = SMTP_USERNAME
        msg['To'] = FEEDBACK_EMAIL
        msg['Subject'] = "GMC Scout V1 - Feedback"
        
        body = f"""
        New feedback received:
        
        Email: {email or 'Not provided'}
        IP: {ip}
        User Agent: {user_agent}
        Timestamp: {datetime.now().isoformat()}
        
        Message:
        {message}
        """
        
        msg.attach(MIMEText(body, 'plain'))
        
        with smtplib.SMTP(SMTP_SERVER, SMTP_PORT) as server:
            server.starttls()
            server.login(SMTP_USERNAME, SMTP_PASSWORD)
            server.send_message(msg)
        
        return True
    except Exception as e:
        logger.error(f"Failed to send feedback email: {e}")
        return False

@app.route('/')
def index():
    """Home page with crawl form"""
    return render_template('index.html')

# -----------------------------------------------------------------------------
# Debug log download endpoint
#
# Returns the accumulated debug log for a given session ID as a plain text file.
# Call with /debug_log?session_id=<id>.  If the session does not exist or has
# no logs, returns an error.
@app.route('/debug_log')
def download_debug_log():
    session_id = request.args.get('session_id')
    if not session_id:
        return jsonify({'error': 'session_id required'}), 400
    # Get the CrawlResult from in‑memory storage.  When using Celery,
    # crawl_sessions may not have the session; we could also attempt to
    # retrieve it from Redis or return an error.
    result = crawl_sessions.get(session_id)
    if not result:
        return jsonify({'error': 'session not found'}), 404
    # Join logs with newline.  If no logs, return a message.
    log_lines = result.debug_logs or ['No debug logs recorded.']
    log_text = '\n'.join(log_lines)
    file_bytes = io.BytesIO(log_text.encode('utf-8'))
    filename = f"debug_log_{result.domain}_{session_id}.txt"
    return send_file(
        file_bytes,
        as_attachment=True,
        download_name=filename,
        mimetype='text/plain'
    )

# -----------------------------------------------------------------------------
# CAPTCHA endpoint
#
# This endpoint returns a freshly generated CAPTCHA question.  The answer is
# stored in the session so that it can be validated on the next crawl
# request.  It returns JSON of the form {"question": "What is 3 + 4?"}.
@app.route('/captcha')
def get_captcha():
    question, answer = generate_captcha()
    # Store the answer in the user's session.  We keep only the latest
    # generated CAPTCHA answer so that each new request invalidates the
    # previous one.
    session['captcha_answer'] = answer
    return jsonify({'question': question})

@app.route('/crawl', methods=['POST'])
@limiter.limit("1 per minute")
def start_crawl():
    """Start a new crawl"""
    try:
        data = request.get_json()
        if not data:
            return jsonify({'error': 'No data provided'}), 400
        

        url = data.get('url', '').strip()
        # Validate CAPTCHA: the frontend must provide the user's answer under
        # the "captcha_answer" key.  Compare it to the answer stored in the
        # session by /captcha.  If it does not match, reject the request.
        provided_captcha = str(data.get('captcha_answer', '')).strip()
        expected_captcha = session.get('captcha_answer')
        # We treat an empty expected CAPTCHA as missing (should not happen
        # normally unless /captcha has not been called).
        if not expected_captcha:
            return jsonify({'error': 'CAPTCHA required. Please refresh the page.'}), 400
        if not provided_captcha or provided_captcha != expected_captcha:
            return jsonify({'error': 'Invalid CAPTCHA answer'}), 400
        # Invalidate the used CAPTCHA to prevent reuse
        session.pop('captcha_answer', None)
        
        # Validate inputs
        if not url:
            return jsonify({'error': 'URL is required'}), 400
        
        # Normalize and validate URL
        try:
            normalized_url = normalize_url(url)
            logger.info(f"Crawl request for: {normalized_url}")
        except ValueError as e:
            return jsonify({'error': str(e)}), 400
        
        # Extract domain
        parsed = urlparse(normalized_url)
        domain = parsed.netloc.replace('www.', '')
        
        # Generate a secure, random session ID using UUID4.  This avoids
        # collisions and makes session identifiers hard to guess.
        session_id = uuid.uuid4().hex
        
        # Store session ID
        session['crawl_session_id'] = session_id
        session.permanent = True
        
        logger.info(f"Created session ID: {session_id}")
        
        # Create crawl result
        result = CrawlResult(domain)
        result.session_id = session_id
        # Save initial state to Redis
        result.save_to_redis()
        # Also keep in-memory for the current worker (optional)
        crawl_sessions[session_id] = {'result': result}

        # Depending on configuration, either enqueue the task via Celery or run it
        # synchronously in a background thread.  Using Celery requires a separate
        # worker and broker.  For simpler deployments or troubleshooting, set
        # USE_CELERY=false in your environment to execute crawls in‑process.
        use_celery = os.environ.get('USE_CELERY', 'true').lower() == 'true'
        if use_celery:
            # Enqueue background crawl task via Celery
            try:
                run_crawl.delay(session_id, normalized_url)
                logger.info(f"Enqueued crawl task for {domain} (session: {session_id})")
            except Exception as e:
                logger.error(f"Failed to enqueue crawl task: {e}")
                return jsonify({'error': 'Failed to start crawl'}), 500
        else:
            # Limit concurrent crawls.  Acquire a permit; if none available,
            # reject the request with an informative error.  This prevents
            # unbounded thread creation when the service is under heavy load.
            if not active_crawl_semaphore.acquire(blocking=False):
                logger.warning("Concurrent crawl limit reached; rejecting new crawl request")
                return jsonify({'error': 'Service is busy. Please try again later.'}), 429

            # Run crawl synchronously in a background thread.  Release the
            # semaphore when the crawl finishes so another crawl can begin.
            logger.info(f"Starting synchronous crawl for {domain} (session: {session_id})")
            crawler = LinkCrawler(normalized_url, result, session_id)
            crawl_sessions[session_id]['crawler'] = crawler
            def crawl_and_release():
                try:
                    # Run the site crawl
                    crawler.crawl_site()
                    # After the crawl completes, perform the alt text validation.
                    try:
                        # Mark incomplete so that the UI waits for alt checks to finish.
                        try:
                            with result.lock:
                                result.is_complete = False
                                result.save_to_redis()
                        except Exception:
                            pass
                        # Attempt to scan product JSON endpoints via sitemap.
                        try:
                            issues, alt_total = _check_alt_text_via_product_json(result.domain)
                            if alt_total > 0:
                                with result.lock:
                                    result.alt_text_issues.extend(issues)
                                    result.alt_text_count = len(result.alt_text_issues)
                                    result.alt_checks_total += alt_total
                                    # Mark progress complete so the UI waits until alt checks finish
                                    result.last_progress = 100.0
                                    # Mark crawl as complete now that alt checks finished
                                    result.is_complete = True
                                    result.save_to_redis()
                            else:
                                # Fallback to /products.json feed
                                legacy_issues = check_alt_text_shopify(result.domain)
                                products = fetch_shopify_products(result.domain)
                                seen_srcs: set = set()
                                if products:
                                    for product in products:
                                        try:
                                            for image in product.get('images', []):
                                                src = image.get('src') or ''
                                                if src:
                                                    seen_srcs.add(src)
                                        except Exception:
                                            continue
                                alt_total_legacy = len(seen_srcs)
                                with result.lock:
                                    result.alt_text_issues.extend(legacy_issues)
                                    result.alt_text_count = len(result.alt_text_issues)
                                    result.alt_checks_total += alt_total_legacy
                                    # Ensure progress is marked as complete when fallback finishes
                                    result.last_progress = 100.0
                                    # Mark crawl as complete now that alt checks finished
                                    result.is_complete = True
                                    result.save_to_redis()
                        except Exception as alt_exc:
                            logger.debug(f"Product JSON alt text check failed: {alt_exc}")
                    except Exception as exc:
                        logger.warning(f"Alt text check failed for {result.domain}: {exc}")
                finally:
                    active_crawl_semaphore.release()
            thread = threading.Thread(target=crawl_and_release, daemon=True)
            thread.start()

        return jsonify({
            'success': True,
            'session_id': session_id,
            'message': 'Crawl started successfully'
        })
        
    except Exception as e:
        logger.error(f"Error starting crawl: {e}")
        return jsonify({'error': 'An error occurred starting the crawl'}), 500

@app.route('/status')
def crawl_status():
    """Get crawl status with live URL updates"""
    # Prefer session_id provided via query parameter for reliability.  Fallback
    # to server‑side session cookie if not provided.
    session_id = request.args.get('session_id') or session.get('crawl_session_id')
    
    logger.debug(f"Status request - Session ID: {session_id}")
    
    if not session_id:
        logger.warning("No session ID found in session")
        return jsonify({'error': 'No active crawl found'}), 404
    
    # Attempt to load the crawl result from Redis first.  Using Redis ensures
    # that progress is shared across multiple Gunicorn workers.  If Redis
    # doesn’t contain the session (e.g. just started), fall back to the
    # in-memory store for this worker.  This ordering prevents stale or
    # missing data from causing the progress bar to reset.
    result = None
    try:
        stored = redis_client.get(session_id)
        if stored:
            try:
                result_dict = pickle.loads(stored)
                result = CrawlResult.from_dict(result_dict)
            except Exception:
                logger.error(f"Failed to decode stored crawl session {session_id}")
                result = None
    except Exception:
        # Redis unavailable; ignore and fall back to memory
        result = None

    # If not found in Redis, check local in-memory store
    if result is None:
        mem_data = crawl_sessions.get(session_id)
        if mem_data:
            result = mem_data['result']

    if result is None:
        logger.warning(f"Session {session_id} not found in Redis or memory")
        return jsonify({'error': 'Crawl session not found'}), 404

    # Ensure the result knows its session ID.  This is critical so that when
    # we later call result.save_to_redis(), the result is saved back to
    # Redis under the correct key.  Without setting session_id here,
    # result.save_to_redis() would return early and not persist updates such
    # as last_progress, causing progress resets when status is handled by
    # different worker processes.
    result.session_id = session_id
    
    # Get thread-safe status
    status = result.get_status()

    # If alt checks have completed but the total count was not persisted
    # (e.g. due to a race condition), derive the alt checks total from
    # available data.  Prefer the explicit alt_text_count if present;
    # otherwise fall back to the length of alt_text_issues.  Only set
    # alt_checks_total when we have a non-zero count.
    try:
        if status.get('alt_checks_total', 0) == 0:
            # Determine how many alt issues were reported (from count or issues array)
            alt_issue_count = 0
            if isinstance(status.get('alt_text_count'), int) and status['alt_text_count'] > 0:
                alt_issue_count = status['alt_text_count']
            elif status.get('alt_text_issues'):
                try:
                    alt_issue_count = len(status['alt_text_issues'])
                except Exception:
                    alt_issue_count = 0
            if alt_issue_count > 0:
                status['alt_checks_total'] = alt_issue_count
                # Ensure alt_text_count is also populated for consistency
                status.setdefault('alt_text_count', alt_issue_count)
    except Exception:
        pass
    
    # Estimate progress using the number of pages scanned and the number of
    # pages remaining in the crawl queue (if available).  When a crawler
    # object exists in this worker, we compute progress as scanned / (scanned + pending).
    # If we don't have a live crawler in this process, we simply reuse the
    # previously recorded last_progress value.  This avoids regressions when
    # status requests are handled by different workers that do not know about
    # the in-memory crawl state.
    mem_data = crawl_sessions.get(session_id)
    current_progress = result.last_progress
    if mem_data and 'crawler' in mem_data:
        crawler_obj = mem_data.get('crawler')
        try:
            pending = len(getattr(crawler_obj, 'to_visit', []))
            scanned = status['pages_scanned']
            total_estimate = scanned + pending
            if total_estimate > 0:
                current_progress = (scanned / total_estimate) * 100
        except Exception:
            # If any error computing dynamic progress, leave current_progress
            pass
        # Ensure progress is monotonic.  Only update if the new estimate is
        # greater than the previous last_progress.  This prevents the bar
        # from moving backwards due to newly discovered pages or out-of-order
        # updates across workers.
        if current_progress < result.last_progress:
            progress = result.last_progress
        else:
            progress = current_progress
            result.last_progress = progress
            try:
                result.save_to_redis()
                if session_id in crawl_sessions:
                    crawl_sessions[session_id]['result'] = result
            except Exception:
                pass
    else:
        # Without a live crawler, we return the last known progress.  This
        # ensures the progress bar never regresses when polling hits a
        # different worker process.
        progress = result.last_progress
    
    # Always include current title mismatch list.  The front‑end will update
    # its display of mismatches even while a crawl is ongoing.  Without
    # returning this here, mismatches would only be available after the
    # crawl completes.
    # Compute a compliance percentage based on the number of pages scanned and
    # the number of errors across all checks.  As additional checks are added
    # (e.g. banned keywords, title mismatches, broken links), include their
    # error counts in this calculation.  The formula distributes the weight
    # evenly across all check categories so that each category contributes
    # equally to the overall score.  If there are no pages scanned yet, or
    # there are zero check categories, compliance defaults to 0.
    # Compute compliance using weighted error rates.  Each category has its own
    # denominator and weight.  Outbound and broken link checks run on every
    # scanned page, so their denominators are the number of pages.  Product
    # title mismatches and banned keyword checks use the number of product
    # pages scanned (title_check_pages and banned_check_pages).  Alt text
    # checks use the number of images scanned (alt_checks_total).  Weights
    # reduce the impact of certain categories, especially alt text issues.
    pages_scanned = status.get('pages_scanned', 0)
    outbound_total = pages_scanned
    broken_total = pages_scanned
    title_total = status.get('title_check_pages', 0) or pages_scanned
    banned_total = status.get('banned_check_pages', 0) or pages_scanned
    # Alt text checks use the number of images scanned.  If unavailable, fall
    # back to pages scanned so that alt issues still contribute to the score.
    alt_total = status.get('alt_checks_total', 0) or pages_scanned
    # Extract error counts for each category
    outbound_err = status['outbound_count']
    broken_err = status['broken_count']
    mismatch_err = len(status.get('title_mismatches', []))
    banned_err = len(status.get('banned_keyword_pages', []))
    alt_err = status.get('alt_text_count', 0)
    # Compute denominators and errors for new check categories.  If a
    # category has no explicit count, fall back to the total pages scanned so
    # that the ratio still yields meaningful values.  The restricted
    # category combines pages flagged for prohibited content, meta robots
    # directives and robots.txt disallows.
    trust_total = status.get('trust_check_pages', 0) or pages_scanned
    restricted_total = status.get('restricted_check_pages', 0) or pages_scanned
    structured_total = status.get('structured_check_pages', 0) or pages_scanned
    trust_err = len(status.get('trust_signal_issues', []))
    restricted_err = (len(status.get('restricted_content_pages', [])) +
                      len(status.get('meta_robots_pages', [])) +
                      len(status.get('robots_disallowed', [])))
    structured_err = len(status.get('structured_data_issues', []))
    # Define weights: assign a lower weight to alt text and structured data so
    # they have less impact on the overall compliance score compared to other checks.
    weights = {
        'outbound': 1.0,
        'broken': 1.0,
        'mismatch': 1.0,
        'banned': 1.0,
        'alt': 0.5,
        'trust': 1.0,
        'restricted': 1.0,
        'structured': 0.5
    }
    weighted_error_sum = 0.0
    total_weight = 0.0
    # Outbound
    if outbound_total > 0:
        weighted_error_sum += weights['outbound'] * (outbound_err / outbound_total)
        total_weight += weights['outbound']
    # Broken
    if broken_total > 0:
        weighted_error_sum += weights['broken'] * (broken_err / broken_total)
        total_weight += weights['broken']
    # Mismatch
    if title_total > 0:
        weighted_error_sum += weights['mismatch'] * (mismatch_err / title_total)
        total_weight += weights['mismatch']
    # Banned
    if banned_total > 0:
        weighted_error_sum += weights['banned'] * (banned_err / banned_total)
        total_weight += weights['banned']
    # Alt text
    if alt_total > 0:
        weighted_error_sum += weights['alt'] * (alt_err / alt_total)
        total_weight += weights['alt']
    # Trust signals
    if trust_total > 0:
        weighted_error_sum += weights['trust'] * (trust_err / trust_total)
        total_weight += weights['trust']
    # Restricted content and blocking
    if restricted_total > 0:
        weighted_error_sum += weights['restricted'] * (restricted_err / restricted_total)
        total_weight += weights['restricted']
    # Structured data
    if structured_total > 0:
        weighted_error_sum += weights['structured'] * (structured_err / structured_total)
        total_weight += weights['structured']
    # Compute quality: 1 minus weighted average of error rates
    if total_weight > 0:
        quality = 1.0 - (weighted_error_sum / total_weight)
    else:
        quality = 1.0
    # Clamp quality
    if quality < 0.0:
        quality = 0.0
    elif quality > 1.0:
        quality = 1.0
    # Determine which progress value to use when computing compliance.
    progress_for_compliance = 100.0 if status['is_complete'] else progress
    # Compliance is progress times quality
    compliance = progress_for_compliance * quality
    # If the crawl has completed, ensure the progress value sent to the client
    # reflects completion.  Without this override, the `last_progress` value
    # may remain below 100%, causing the progress bar to display 0% even
    # when the scan is finished.  Set progress to 100 when is_complete is
    # true.
    progress_value = 100.0 if status['is_complete'] else round(progress, 1)
    response_data = {
        'is_complete': status['is_complete'],
        'pages_scanned': status['pages_scanned'],
        'outbound_count': status['outbound_count'],
        'broken_count': status['broken_count'],
        'progress': progress_value,
        'error': status['error'],
        'current_url': status['current_url'],
        'recent_urls': status['recent_urls'],
        'title_mismatches': status.get('title_mismatches', []),
        'banned_keyword_pages': status.get('banned_keyword_pages', []),
        # Include the number of pages checked for each product-specific
        # validation.  These counts allow the front‑end to display
        # denominators for mismatch and banned checks separately from
        # the overall pages scanned.  Alt text counters have been removed.
        'title_check_pages': status.get('title_check_pages', 0),
        'banned_check_pages': status.get('banned_check_pages', 0),
        # Alt text counters for live progress.  These allow the front‑end
        # to display the ratio of alt issues to images scanned in the
        # progress tiles.
        'alt_checks_total': status.get('alt_checks_total', 0),
        'alt_text_count': status.get('alt_text_count', 0),
        'alt_text_issues': status.get('alt_text_issues', []),
        'compliance': round(compliance, 1),
        # Include the domain being scanned in all responses so that the
        # front‑end can display it in the final results header.  The
        # `result` object always holds the current domain.
        'domain': result.domain
                , 'trust_signal_issues': status.get('trust_signal_issues', [])
                , 'trust_check_pages': status.get('trust_check_pages', 0)
                , 'restricted_content_pages': status.get('restricted_content_pages', [])
                , 'robots_disallowed': status.get('robots_disallowed', [])
                , 'meta_robots_pages': status.get('meta_robots_pages', [])
                , 'restricted_check_pages': status.get('restricted_check_pages', 0)
                , 'structured_data_issues': status.get('structured_data_issues', [])
                , 'structured_check_pages': status.get('structured_check_pages', 0)
                , 'debug_logs': status.get('debug_logs', [])
    }
    
    if status['is_complete']:
        # Add complete data
        result_dict = result.to_dict()
        response_data.update({
            'outbound_links': sorted(result_dict['outbound_links']),
            'broken_links': sorted(result_dict['broken_links']),
            'broken_links_details': result_dict.get('broken_links_details', []),
            'outbound_links_details': result_dict.get('outbound_links_details', []),
            'start_time': result_dict['start_time'],
            'end_time': result_dict['end_time'],
            'duration': str(datetime.fromisoformat(result_dict['end_time']) - 
                          datetime.fromisoformat(result_dict['start_time'])) if result_dict['end_time'] else None
            , 'title_mismatches': result_dict.get('title_mismatches', [])
            , 'banned_keyword_pages': result_dict.get('banned_keyword_pages', [])
            , 'alt_text_issues': result_dict.get('alt_text_issues', [])
            , 'alt_text_count': result_dict.get('alt_text_count', 0)
            , 'alt_checks_total': result_dict.get('alt_checks_total', 0)
            , 'compliance': round(compliance, 1)
            , 'domain': result_dict.get('domain', result.domain)
        })
    
    return jsonify(response_data)

@app.route('/cancel', methods=['POST'])
def cancel_crawl():
    """Cancel active crawl"""
    session_id = request.args.get('session_id') or session.get('crawl_session_id')
    if not session_id:
        return jsonify({'error': 'No active crawl found'}), 404
    
    crawl_data = crawl_sessions.get(session_id)
    if crawl_data:
        crawler = crawl_data['crawler']
        if crawler:
            crawler.should_cancel = True
        
        result = crawl_data['result']
        result.cancelled = True
        result.is_complete = True
        result.end_time = datetime.now()
        
        logger.info(f"Cancelled crawl: {session_id}")
        return jsonify({'success': True, 'message': 'Crawl cancelled'})
    
    return jsonify({'error': 'No active crawl to cancel'}), 404

@app.route('/export/<format>')
def export_results(format):
    """Export crawl results"""
    session_id = request.args.get('session_id') or session.get('crawl_session_id')
    if not session_id:
        return jsonify({'error': 'No crawl results found'}), 404
    
    crawl_data = crawl_sessions.get(session_id)
    if not crawl_data:
        return jsonify({'error': 'No crawl results found'}), 404
    
    result = crawl_data['result']
    # Allow exporting even if the crawl has not fully completed.  Previously,
    # exports were restricted to completed scans only, which prevented users
    # from downloading results when a crawl finished but the front‑end state
    # lost track of completion.  By removing this check, the server will
    # generate a report based on whatever data is available at the time of
    # request.
    #
    # if not result.is_complete:
    #     return jsonify({'error': 'Crawl not yet complete'}), 400
    
    # Validate format.  Only PDF exports are supported.  TXT exports have
    # been removed per user request.  If any other format is requested,
    # return an error to the client.
    if format != 'pdf':
        return jsonify({'error': 'Invalid export format. Only PDF is supported.'}), 400

    timestamp = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
    domain_clean = re.sub(r'[^\w\-_]', '_', result.domain)

    # Always export as PDF.  TXT export has been removed.
    return export_pdf(result, domain_clean, timestamp)

def export_txt(result, domain_clean, timestamp):
    """Export as TXT file"""
    content = []
    content.append("=" * 60)
    content.append("GMC SCOUT V1 - CRAWL RESULTS")
    content.append("=" * 60)
    content.append(f"Generated: {timestamp}")
    content.append(f"Scanned Domain: {result.domain}")
    content.append(f"Crawl Started: {result.start_time.strftime('%Y-%m-%d %H:%M:%S')}")
    if result.end_time:
        content.append(f"Crawl Finished: {result.end_time.strftime('%Y-%m-%d %H:%M:%S')}")
        duration = result.end_time - result.start_time
        content.append(f"Duration: {duration}")
    content.append(f"Pages Scanned: {result.pages_scanned}")
    # Compute a compliance score for the TXT report using the same weighted
    # formula as the API.  Each category has its own denominator and
    # weight.  Alt text issues are given a lower weight so they don't
    # overwhelm the score when many images are scanned.
    pages_scanned = result.pages_scanned
    # Determine denominators
    outbound_total = pages_scanned
    broken_total = pages_scanned
    title_total = getattr(result, 'title_check_pages', 0) or pages_scanned
    banned_total = getattr(result, 'banned_check_pages', 0) or pages_scanned
    # Alt text checks have been removed; there is no denominator for alt
    # text errors in the compliance calculation
    alt_total = 0
    # Error counts
    outbound_err = len(result.outbound_links)
    broken_err = len(result.broken_links)
    mismatch_err = len(getattr(result, 'title_mismatches', []))
    banned_err = len(getattr(result, 'banned_keyword_pages', []))
    # Alt text errors are zero because the alt text checker has been removed
    alt_err = 0
    # New denominators and error counts for trust, restricted and structured checks
    trust_total = getattr(result, 'trust_check_pages', 0) or pages_scanned
    restricted_total = getattr(result, 'restricted_check_pages', 0) or pages_scanned
    structured_total = getattr(result, 'structured_check_pages', 0) or pages_scanned
    trust_err = len(getattr(result, 'trust_signal_issues', []))
    restricted_err = (len(getattr(result, 'restricted_content_pages', [])) +
                      len(getattr(result, 'meta_robots_pages', [])) +
                      len(getattr(result, 'robots_disallowed', [])))
    structured_err = len(getattr(result, 'structured_data_issues', []))
    # Weights (alt text category weight is zero because the checker has been removed)
    weights = {
        'outbound': 1.0,
        'broken': 1.0,
        'mismatch': 1.0,
        'banned': 1.0,
        # Alt text checker removed; alt errors are assigned zero weight
        'alt': 0.0,
        'trust': 1.0,
        'restricted': 1.0,
        'structured': 0.5
    }
    weighted_error_sum = 0.0
    total_weight = 0.0
    if outbound_total > 0:
        weighted_error_sum += weights['outbound'] * (outbound_err / outbound_total)
        total_weight += weights['outbound']
    if broken_total > 0:
        weighted_error_sum += weights['broken'] * (broken_err / broken_total)
        total_weight += weights['broken']
    if title_total > 0:
        weighted_error_sum += weights['mismatch'] * (mismatch_err / title_total)
        total_weight += weights['mismatch']
    if banned_total > 0:
        weighted_error_sum += weights['banned'] * (banned_err / banned_total)
        total_weight += weights['banned']
    if alt_total > 0:
        weighted_error_sum += weights['alt'] * (alt_err / alt_total)
        total_weight += weights['alt']
    # Trust signals
    if trust_total > 0:
        weighted_error_sum += weights['trust'] * (trust_err / trust_total)
        total_weight += weights['trust']
    # Restricted content and blocking
    if restricted_total > 0:
        weighted_error_sum += weights['restricted'] * (restricted_err / restricted_total)
        total_weight += weights['restricted']
    # Structured data
    if structured_total > 0:
        weighted_error_sum += weights['structured'] * (structured_err / structured_total)
        total_weight += weights['structured']
    if total_weight > 0:
        quality = 1.0 - (weighted_error_sum / total_weight)
    else:
        quality = 1.0
    if quality < 0.0:
        quality = 0.0
    elif quality > 1.0:
        quality = 1.0
    # For the TXT export, treat progress as 100% since the crawl is complete
    compliance = 100.0 * quality
    content.append(f"Compliance: {round(compliance, 1)}%")
    content.append(f"Banned Keyword Pages: {len(getattr(result, 'banned_keyword_pages', []))}")
    # New summary lines for trust signals, restricted content and structured data
    try:
        content.append(f"Trust Signal Issues: {len(getattr(result, 'trust_signal_issues', []))}")
    except Exception:
        content.append("Trust Signal Issues: 0")
    try:
        content.append(f"Restricted Content Pages: {len(getattr(result, 'restricted_content_pages', []))}")
    except Exception:
        content.append("Restricted Content Pages: 0")
    try:
        content.append(f"Structured Data Issues: {len(getattr(result, 'structured_data_issues', []))}")
    except Exception:
        content.append("Structured Data Issues: 0")
    content.append("")
    
    content.append("SUMMARY")
    content.append("-" * 20)
    content.append(f"Total Outbound Links: {len(result.outbound_links)}")
    content.append(f"Broken Links (404s): {len(result.broken_links)}")
    # Also include the number of product title mismatches in the summary
    content.append(f"Title Mismatches: {len(getattr(result, 'title_mismatches', []))}")
    # Include the number of pages that violated banned keyword rules in the summary
    content.append(f"Banned Keyword Pages: {len(getattr(result, 'banned_keyword_pages', []))}")
    content.append("")
    
    if result.outbound_links:
        content.append("OUTBOUND LINKS")
        content.append("-" * 20)
        # Build a lookup for first occurrence of each outbound link's source page
        details_map = {}
        for source, link in result.outbound_links_details:
            if link not in details_map:
                details_map[link] = source
        for link in sorted(result.outbound_links):
            if details_map.get(link):
                content.append(f"{link} (found on {details_map[link]})")
            else:
                content.append(link)
        content.append("")
    
    if result.broken_links:
        content.append("BROKEN LINKS / HTTP ERRORS")
        content.append("-" * 20)
        # Include the source page for each broken link when available
        if result.broken_links_details:
            for source_page, link in result.broken_links_details:
                content.append(f"{link} (found on {source_page})")
        else:
            for link in sorted(result.broken_links):
                content.append(link)
        content.append("")

    # Include product title & URL slug mismatches if any were recorded.  Each
    # mismatch entry is a four‑tuple: [url, slug, title, similarity].  We
    # convert the similarity to a percentage and display the page title,
    # slug and URL together for easy reference.
    if getattr(result, 'title_mismatches', None):
        content.append("PRODUCT TITLE & URL SLUG MISMATCHES")
        content.append("-" * 20)
        for url, slug, title, similarity in result.title_mismatches:
            try:
                similarity_pct = int(float(similarity) * 100)
            except Exception:
                similarity_pct = 0
            content.append(f"{title} | Slug: {slug} | Similarity: {similarity_pct}% | URL: {url}")
        content.append("")

    # Include pages where banned keywords were found.  Each entry is a
    # three‑tuple: [url, banned_words, ratio].  We display the URL
    # alongside the list of banned words that were detected on that page.
    if getattr(result, 'banned_keyword_pages', None):
        content.append("PAGES WITH BANNED KEYWORDS")
        content.append("-" * 20)
        for page_url, banned_words, ratio in result.banned_keyword_pages:
            # Convert ratio to percentage for readability
            try:
                ratio_pct = int(float(ratio) * 100)
            except Exception:
                ratio_pct = 0
            words_str = ", ".join(banned_words)
            content.append(f"{page_url} | Keywords: {words_str} | Match: {ratio_pct}%")
        content.append("")

    # Include trust signal & policy issues
    if getattr(result, 'trust_signal_issues', None):
        content.append("TRUST SIGNAL & POLICY ISSUES")
        content.append("-" * 20)
        for page_url, contact_issues, policy_issues, ssl_issues in result.trust_signal_issues:
            try:
                parts = []
                if contact_issues:
                    parts.append("Contact: " + ", ".join(contact_issues))
                if policy_issues:
                    parts.append("Policies: " + ", ".join(policy_issues))
                if ssl_issues:
                    parts.append("SSL: " + ", ".join(ssl_issues))
                summary = " | ".join(parts) if parts else ""
                content.append(f"{page_url} | {summary}")
            except Exception:
                continue
        content.append("")

    # Include restricted content pages
    if getattr(result, 'restricted_content_pages', None):
        content.append("PAGES WITH RESTRICTED CONTENT")
        content.append("-" * 20)
        for page_url, cats in result.restricted_content_pages:
            try:
                content.append(f"{page_url} | Categories: {', '.join(cats)}")
            except Exception:
                continue
        content.append("")

    # Include pages with meta robots restrictions
    if getattr(result, 'meta_robots_pages', None):
        content.append("META ROBOTS RESTRICTIONS")
        content.append("-" * 20)
        for page_url, directives in result.meta_robots_pages:
            try:
                content.append(f"{page_url} | Directives: {', '.join(directives)}")
            except Exception:
                continue
        content.append("")

    # Include disallowed paths from robots.txt
    if getattr(result, 'robots_disallowed', None):
        content.append("ROBOTS.TXT DISALLOWED PATHS")
        content.append("-" * 20)
        try:
            for path in result.robots_disallowed:
                content.append(path)
        except Exception:
            pass
        content.append("")

    # Include structured data issues
    if getattr(result, 'structured_data_issues', None):
        content.append("STRUCTURED DATA ISSUES")
        content.append("-" * 20)
        for page_url, errs in result.structured_data_issues:
            try:
                content.append(f"{page_url} | " + "; ".join(errs))
            except Exception:
                continue
        content.append("")

    # Do not include a section for image alt text issues since the
    # alt text checker has been removed.
    
    content.append("=" * 60)
    content.append("Generated by GMC Scout V1")
    content.append("Visit: https://gmcscout.com")
    content.append("")
    content.append("DISCLAIMER: This report is for informational purposes only.")
    content.append("No data from this scan is stored or shared.")
    content.append("=" * 60)
    
    txt_content = "\n".join(content)
    file_bytes = io.BytesIO(txt_content.encode('utf-8'))
    filename = f"crawl_results_{domain_clean}_{timestamp}.txt"
    
    return send_file(
        file_bytes,
        as_attachment=True,
        download_name=filename,
        mimetype='text/plain'
    )

def export_pdf(result, domain_clean, timestamp):
    """
    Export crawl results as a PDF.  This implementation attempts to
    generate a PDF using the reportlab library, which is widely used
    for creating PDFs in Python.  If reportlab is not available in
    the environment, the function falls back to a matplotlib-based
    approach, and finally to a plain text file if all else fails.
    """
    # Build the content lines similar to the TXT export
    lines = []
    lines.append("=" * 60)
    lines.append("GMC SCOUT V1 - CRAWL RESULTS")
    lines.append("=" * 60)
    lines.append(f"Generated: {timestamp}")
    lines.append(f"Scanned Domain: {result.domain}")
    lines.append(f"Crawl Started: {result.start_time.strftime('%Y-%m-%d %H:%M:%S')}")
    if result.end_time:
        lines.append(f"Crawl Finished: {result.end_time.strftime('%Y-%m-%d %H:%M:%S')}")
        duration = result.end_time - result.start_time
        lines.append(f"Duration: {duration}")
    lines.append(f"Pages Scanned: {result.pages_scanned}")
    # Compute compliance for the PDF report using the same weighted formula
    # as the TXT export.  Assign a lower weight to alt text issues so
    # that many image-related errors do not dominate the final score.
    pages_scanned = result.pages_scanned
    outbound_total = pages_scanned
    broken_total = pages_scanned
    title_total = getattr(result, 'title_check_pages', 0) or pages_scanned
    banned_total = getattr(result, 'banned_check_pages', 0) or pages_scanned
    # Alt text checks have been removed; there is no denominator for alt
    # text errors in the compliance calculation for PDF export
    alt_total = 0
    outbound_err = len(result.outbound_links)
    broken_err = len(result.broken_links)
    mismatch_err = len(getattr(result, 'title_mismatches', []))
    banned_err = len(getattr(result, 'banned_keyword_pages', []))
    # Alt text errors are zero because the alt text checker has been removed
    alt_err = 0
    # Additional denominators and error counts for new checks
    trust_total = getattr(result, 'trust_check_pages', 0) or pages_scanned
    restricted_total = getattr(result, 'restricted_check_pages', 0) or pages_scanned
    structured_total = getattr(result, 'structured_check_pages', 0) or pages_scanned
    trust_err = len(getattr(result, 'trust_signal_issues', []))
    restricted_err = (len(getattr(result, 'restricted_content_pages', [])) +
                      len(getattr(result, 'meta_robots_pages', [])) +
                      len(getattr(result, 'robots_disallowed', [])))
    structured_err = len(getattr(result, 'structured_data_issues', []))
    weights = {
        'outbound': 1.0,
        'broken': 1.0,
        'mismatch': 1.0,
        'banned': 1.0,
        # Alt text checker removed; alt errors do not contribute to the weighted score
        'alt': 0.0,
        'trust': 1.0,
        'restricted': 1.0,
        'structured': 0.5
    }
    weighted_error_sum = 0.0
    total_weight = 0.0
    if outbound_total > 0:
        weighted_error_sum += weights['outbound'] * (outbound_err / outbound_total)
        total_weight += weights['outbound']
    if broken_total > 0:
        weighted_error_sum += weights['broken'] * (broken_err / broken_total)
        total_weight += weights['broken']
    if title_total > 0:
        weighted_error_sum += weights['mismatch'] * (mismatch_err / title_total)
        total_weight += weights['mismatch']
    if banned_total > 0:
        weighted_error_sum += weights['banned'] * (banned_err / banned_total)
        total_weight += weights['banned']
    if alt_total > 0:
        weighted_error_sum += weights['alt'] * (alt_err / alt_total)
        total_weight += weights['alt']
    # Trust signals
    if trust_total > 0:
        weighted_error_sum += weights['trust'] * (trust_err / trust_total)
        total_weight += weights['trust']
    # Restricted content and blocking
    if restricted_total > 0:
        weighted_error_sum += weights['restricted'] * (restricted_err / restricted_total)
        total_weight += weights['restricted']
    # Structured data
    if structured_total > 0:
        weighted_error_sum += weights['structured'] * (structured_err / structured_total)
        total_weight += weights['structured']
    if total_weight > 0:
        quality = 1.0 - (weighted_error_sum / total_weight)
    else:
        quality = 1.0
    if quality < 0.0:
        quality = 0.0
    elif quality > 1.0:
        quality = 1.0
    compliance = 100.0 * quality
    lines.append(f"Compliance: {round(compliance, 1)}%")
    lines.append("")
    lines.append("SUMMARY")
    lines.append("-" * 20)
    lines.append(f"Total Outbound Links: {len(result.outbound_links)}")
    lines.append(f"Broken Links (404s): {len(result.broken_links)}")
    lines.append(f"Title Mismatches: {len(getattr(result, 'title_mismatches', []))}")
    lines.append(f"Banned Keyword Pages: {len(getattr(result, 'banned_keyword_pages', []))}")
    # Include a count of images that failed the alt text check.  This allows
    # merchants to quickly see how many product images need improved alt
    # descriptions for accessibility and SEO.
    # Remove Image Alt Text Issues from the summary as the alt text checker
    # has been removed.
    lines.append("")
    # Outbound links with source page if available
    if result.outbound_links:
        lines.append("OUTBOUND LINKS")
        lines.append("-" * 20)
        details_map = {}
        for source, link in result.outbound_links_details:
            if link not in details_map:
                details_map[link] = source
        for link in sorted(result.outbound_links):
            if details_map.get(link):
                lines.append(f"{link} (found on {details_map[link]})")
            else:
                lines.append(link)
        lines.append("")
    # Broken links with source page if available
    if result.broken_links:
        lines.append("BROKEN LINKS / HTTP ERRORS")
        lines.append("-" * 20)
        if result.broken_links_details:
            for source_page, link in result.broken_links_details:
                lines.append(f"{link} (found on {source_page})")
        else:
            for link in sorted(result.broken_links):
                lines.append(link)
        lines.append("")
    # Title mismatches
    if getattr(result, 'title_mismatches', None):
        lines.append("PRODUCT TITLE & URL SLUG MISMATCHES")
        lines.append("-" * 20)
        for url, slug, title, similarity in result.title_mismatches:
            try:
                similarity_pct = int(float(similarity) * 100)
            except Exception:
                similarity_pct = 0
            lines.append(f"{title} | Slug: {slug} | Similarity: {similarity_pct}% | URL: {url}")
        lines.append("")
    # Banned keywords
    if getattr(result, 'banned_keyword_pages', None):
        lines.append("PAGES WITH BANNED KEYWORDS")
        lines.append("-" * 20)
        for page_url, banned_words, ratio in result.banned_keyword_pages:
            try:
                ratio_pct = int(float(ratio) * 100)
            except Exception:
                ratio_pct = 0
            words_str = ", ".join(banned_words)
            lines.append(f"{page_url} | Keywords: {words_str} | Match: {ratio_pct}%")
        lines.append("")
    # Alt text issues have been removed from the export.

    lines.append("=" * 60)
    lines.append("Generated by GMC Scout V1")
    lines.append("Visit: https://gmcscout.com")
    lines.append("")
    lines.append("DISCLAIMER: This report is for informational purposes only.")
    lines.append("No data from this scan is stored or shared.")
    lines.append("=" * 60)

    # Compose the text content for fallback use
    txt_content = "\n".join(lines)

    filename = f"crawl_results_{domain_clean}_{timestamp}.pdf"
    # First, try to generate the PDF with reportlab
    try:
        from reportlab.lib.pagesizes import letter
        from reportlab.pdfgen import canvas
        buffer = io.BytesIO()
        c = canvas.Canvas(buffer, pagesize=letter)
        width, height = letter
        x_margin = 40
        y = height - 40
        line_height = 12
        # Use a monospaced font
        c.setFont("Courier", 9)
        for line in lines:
            c.drawString(x_margin, y, line)
            y -= line_height
            if y < 40:
                c.showPage()
                c.setFont("Courier", 9)
                y = height - 40
        c.save()
        buffer.seek(0)
        return send_file(
            buffer,
            as_attachment=True,
            download_name=filename,
            mimetype='application/pdf'
        )
    except Exception:
        # If reportlab fails, try matplotlib
        try:
            import matplotlib
            matplotlib.use('Agg')
            import matplotlib.pyplot as plt
            from matplotlib.backends.backend_pdf import PdfPages
            with tempfile.NamedTemporaryFile(delete=False, suffix='.pdf') as tmp_pdf:
                fig = plt.figure(figsize=(8.5, 11))
                fig.patch.set_facecolor('white')
                plt.axis('off')
                fontdict = {'family': 'monospace', 'size': 8}
                y_position = 0.99
                line_height_fraction = 0.02
                for line in lines:
                    if y_position < 0.02:
                        break
                    fig.text(0.01, y_position, line, va='top', ha='left', fontdict=fontdict)
                    y_position -= line_height_fraction
                pdf = PdfPages(tmp_pdf.name)
                pdf.savefig(fig, bbox_inches='tight')
                pdf.close()
                plt.close(fig)
                with open(tmp_pdf.name, 'rb') as f:
                    pdf_data = f.read()
            os.unlink(tmp_pdf.name)
            return send_file(
                io.BytesIO(pdf_data),
                as_attachment=True,
                download_name=filename,
                mimetype='application/pdf'
            )
        except Exception:
            # Ultimately fall back to plain text if PDF cannot be generated
            file_bytes = io.BytesIO(txt_content.encode('utf-8'))
            return send_file(
                file_bytes,
                as_attachment=True,
                download_name=f"crawl_results_{domain_clean}_{timestamp}.txt",
                mimetype='text/plain'
            )

@app.route('/feedback', methods=['POST'])
@limiter.limit("3 per hour")
def submit_feedback():
    """Submit feedback/bug report"""
    try:
        data = request.get_json()
        email = data.get('email', '').strip()
        message = data.get('message', '').strip()
        
        # Validate message
        if not message:
            return jsonify({'error': 'Message is required'}), 400
        
        if len(message) > 1000:
            return jsonify({'error': 'Message too long (max 1000 characters)'}), 400
        
        # Validate email if provided
        if email and not re.match(r'^[^@]+@[^@]+\.[^@]+$', email):
            return jsonify({'error': 'Invalid email format'}), 400
        
        # Get request info
        ip = get_remote_address()
        user_agent = request.headers.get('User-Agent', '')
        
        # Send feedback
        success = send_feedback_email(email, message, ip, user_agent)
        
        if success:
            return jsonify({'success': True, 'message': 'Feedback submitted successfully'})
        else:
            return jsonify({'error': 'Failed to submit feedback'}), 500
            
    except Exception as e:
        logger.error(f"Error submitting feedback: {e}")
        return jsonify({'error': 'An error occurred submitting feedback'}), 500

@app.route('/healthz')
def health_check():
    """Health check endpoint"""
    return jsonify({
        'status': 'healthy',
        'timestamp': datetime.now().isoformat(),
        'version': '1.0.0'
    })

# Cleanup old crawl sessions periodically
def cleanup_old_sessions():
    """Clean up old crawl sessions"""
    try:
        current_time = datetime.now()
        to_remove = []
        
        for session_id, crawl_data in crawl_sessions.items():
            result = crawl_data['result']
            if result.start_time < current_time - timedelta(hours=2):
                to_remove.append(session_id)
        
        for session_id in to_remove:
            del crawl_sessions[session_id]
            logger.info(f"Cleaned up old session: {session_id}")
            
    except Exception as e:
        logger.error(f"Error cleaning up sessions: {e}")

# Periodic cleanup timer
cleanup_timer = None

def run_periodic_cleanup():
    """Run cleanup periodically"""
    global cleanup_timer
    cleanup_old_sessions()
    # Schedule next cleanup in 30 minutes
    cleanup_timer = threading.Timer(1800.0, run_periodic_cleanup)
    cleanup_timer.daemon = True
    cleanup_timer.start()

# Start cleanup on app start
run_periodic_cleanup()

# Cleanup on exit
import atexit

def cleanup_on_exit():
    """Cleanup on app exit"""
    global cleanup_timer
    if cleanup_timer:
        cleanup_timer.cancel()
    logger.info("Application shutting down")

atexit.register(cleanup_on_exit)

# -----------------------------------------------------------------------------
# Shopify product JSON checks
#
# These helpers and API endpoint allow scanning of Shopify product data via
# the `/products.json` endpoint to perform additional checks such as
# alt text validation.  This feature operates independently of the main
# crawl workflow, so adding or testing new checks here will not affect
# existing functionality.

def fetch_shopify_products(domain: str) -> Optional[list]:
    """
    Fetch product data from a Shopify store's `/products.json` endpoint.
    Returns a list of product objects or an empty list on failure.
    """
    if not domain:
        return []
    # Ensure requests is available
    if 'requests' not in globals() or requests is None:
        logger.warning("Requests library not available; cannot fetch products.json")
        return []
    # If the caller provides a Shopify admin API key and password via
    # environment variables, attempt to use the private admin REST API.
    # This avoids 403 errors on stores that block public access to
    # products.json.  Only the fields needed for alt text checking are
    # requested to minimise payload size.  The version can be overridden
    # via SHOPIFY_API_VERSION; default to 2023-07.
    # Prepare default headers for all requests.  Use a realistic
    # User‑Agent and accept JSON to reduce the chance of being blocked.
    headers = {
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) '
                      'AppleWebKit/537.36 (KHTML, like Gecko) '
                      'Chrome/122.0.0.0 Safari/537.36',
        'Accept': 'application/json',
    }

    api_key = os.environ.get('SHOPIFY_API_KEY')
    api_pass = os.environ.get('SHOPIFY_API_PASSWORD')
    if api_key and api_pass:
        version = os.environ.get('SHOPIFY_API_VERSION', '2023-07')
        admin_url = (f"https://{api_key}:{api_pass}@{domain}/admin/api/{version}/products.json"
                     "?fields=title,handle,images&limit=250")
        try:
            resp = requests.get(admin_url, headers=headers, timeout=20)
            if resp.status_code == 200:
                try:
                    data = resp.json() or {}
                except Exception:
                    data = {}
                products = data.get('products', []) or []
                if products:
                    return products
            else:
                logger.debug(f"Admin API request failed for {domain}: status {resp.status_code}")
        except Exception as exc:
            logger.debug(f"Error accessing admin API for {domain}: {exc}")
    # Attempt to fetch product data from multiple potential endpoints.  Some
    # Shopify stores block the bare /products.json endpoint or require
    # specific query parameters.  Try a series of URLs until a successful
    # response (HTTP 200) is obtained.  Use a realistic User‑Agent and
    # accept JSON to minimise 403 responses.
    # headers were defined earlier.  Do not redeclare here.
    # Construct candidate endpoints
    domain_no_www = domain.lstrip('www.')
    endpoints = [
        f"https://{domain_no_www}/products.json?limit=250",
        f"https://{domain_no_www}/products.json",
        f"https://www.{domain_no_www}/products.json?limit=250",
    ]
    # If the domain is not already a myshopify.com domain, add a fallback to
    # the canonical myshopify address.  Many Shopify stores redirect to
    # their branded domain but still expose /products.json on the myshopify
    # subdomain.
    if not domain_no_www.endswith('.myshopify.com'):
        base = domain_no_www.split(':')[0]
        endpoints.append(f"https://{base}.myshopify.com/products.json?limit=250")
    for url in endpoints:
        try:
            resp = requests.get(url, headers=headers, timeout=20)
            # Log all attempts to assist debugging when products cannot be fetched
            if resp.status_code != 200:
                logger.debug(f"products.json request to {url} returned status {resp.status_code}")
                continue
            try:
                data = resp.json() or {}
            except Exception:
                logger.debug(f"products.json request to {url} returned non‑JSON data")
                continue
            products = data.get('products', []) or []
            if products:
                return products
        except Exception as exc:
            logger.debug(f"Exception requesting products.json from {url}: {exc}")
            continue
    # If all endpoints failed, return empty list
    return []


# -----------------------------------------------------------------------------
# Shopify product page JSON and sitemap helpers
#
# To perform alt‑text validation without relying on the store's public
# ``/products.json`` feed (which is often disabled or blocked), we provide
# additional helper functions.  These functions parse the store's sitemap to
# discover individual product handles and then fetch each product's JSON
# representation (``/products/<handle>.json``).  This approach works on any
# Shopify store because product JSON endpoints are publicly accessible and
# include image alt attributes.  The functions below deduplicate images across
# products and extract alt‑text issues using the same criteria as the
# ``check_alt_text_shopify`` function.

def _fetch_product_handles_from_sitemap(domain: str, limit: int = 200) -> list:
    """
    Discover product handles from a Shopify store's sitemaps.

    Shopify exposes a ``/sitemap.xml`` index which references product sitemap
    files (e.g. ``sitemap_products_1.xml``).  Each product URL in these
    sitemaps contains the handle of a product.  This function fetches the
    index and product sitemaps, extracts up to ``limit`` unique product
    handles and returns them as a list.  A realistic User‑Agent header is
    used to minimise the chance of being blocked.

    Args:
        domain: The store domain (e.g. ``example.com``) without protocol.
        limit: Maximum number of product handles to discover to avoid
            excessively long scans on very large stores.  Defaults to 200.

    Returns:
        A list of unique product handles (slugs).  May be empty if sitemaps
        are not accessible or parsing fails.
    """
    if not domain:
        return []
    handles: set = set()
    # Use a queue of sitemap URLs to visit.  Start with the root sitemap
    # index.  Normalise domain by stripping leading ``www.``.
    root_domain = domain.lstrip('www.')
    queue: list[str] = [f"https://{root_domain}/sitemap.xml"]
    visited: set[str] = set()
    headers = {
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) '
                      'AppleWebKit/537.36 (KHTML, like Gecko) '
                      'Chrome/122.0.0.0 Safari/537.36',
        'Accept': 'application/xml',
    }
    while queue and len(handles) < limit:
        sitemap_url = queue.pop(0)
        if sitemap_url in visited:
            continue
        visited.add(sitemap_url)
        try:
            resp = requests.get(sitemap_url, headers=headers, timeout=15)
            if resp.status_code != 200 or not resp.text:
                continue
            xml_text = resp.text
            # Parse XML.  Use ElementTree because it handles namespaces.
            try:
                import xml.etree.ElementTree as ET
                root = ET.fromstring(xml_text)
            except Exception:
                # Skip malformed XML
                continue
            # Determine namespace if present
            namespace = ''
            if root.tag.startswith('{'):
                namespace = root.tag.split('}')[0] + '}'
            # Iterate over <loc> elements in sitemap
            for loc_elem in root.iter(f'{namespace}loc'):
                loc = (loc_elem.text or '').strip()
                if not loc:
                    continue
                # If this loc points to another sitemap (e.g. sitemap_products_1.xml),
                # enqueue it for later processing.  Otherwise, extract product handle.
                # Shopify product sitemap URLs typically contain ``sitemap_products_``
                # but other sitemaps (e.g. pages, collections) can be ignored.
                if 'sitemap_products_' in loc and loc not in visited:
                    queue.append(loc)
                    continue
                # Identify product URLs.  A product URL contains ``/products/`` and
                # ends with the handle.  Extract the segment after ``/products/``.
                if '/products/' in loc:
                    try:
                        handle_part = loc.split('/products/', 1)[1]
                        # Remove query params or trailing slashes
                        handle = handle_part.split('?', 1)[0].split('/', 1)[0]
                        if handle:
                            handles.add(handle)
                            if len(handles) >= limit:
                                break
                    except Exception:
                        continue
            # Stop if we've collected enough handles
            if len(handles) >= limit:
                break
        except Exception:
            continue
    return list(handles)


def _check_alt_text_via_product_json(domain: str, limit: int = 200) -> tuple[list, int]:
    """
    Perform alt‑text validation by fetching each product's JSON
    representation individually.  This avoids relying on the global
    ``/products.json`` feed which many Shopify stores disable.

    The function obtains product handles via ``_fetch_product_handles_from_sitemap``
    and then requests ``/products/<handle>.json`` for each.  It extracts
    image alt attributes and flags missing, generic (fewer than two words)
    or low‑similarity alt text compared to the product title.  Duplicate
    image URLs across products are ignored so each image is checked only
    once.

    Args:
        domain: Store domain without protocol.
        limit: Maximum number of products to scan.  Defaults to 200.

    Returns:
        A tuple ``(issues, total_images)`` where ``issues`` is a list of
        five‑tuples matching the format of ``check_alt_text_shopify`` and
        ``total_images`` is the number of unique images inspected.
    """
    issues: list = []
    # Count of all images processed (per‑product).  We no longer deduplicate
    # across all products so that repeated images on different products are
    # counted separately.
    total_images_count: int = 0
    if not domain:
        return issues, 0
    # Fetch product handles via sitemap
    handles = _fetch_product_handles_from_sitemap(domain, limit=limit)
    if not handles:
        logger.debug(f"No product handles found in sitemap for {domain}")
        return issues, 0
    headers = {
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) '
                      'AppleWebKit/537.36 (KHTML, like Gecko) '
                      'Chrome/122.0.0.0 Safari/537.36',
        'Accept': 'application/json',
    }
    for handle in handles:
        product_url = f"https://{domain.lstrip('www.')}/products/{handle}.json"
        try:
            resp = requests.get(product_url, headers=headers, timeout=15)
            # Log the status code for each product JSON request to aid debugging.
            if resp.status_code != 200:
                logger.debug(f"{product_url} returned status {resp.status_code}")
                continue
            try:
                data = resp.json() or {}
            except Exception:
                logger.debug(f"Failed to parse JSON from {product_url}")
                continue
            # Shopify product JSON may wrap product data in a 'product' key
            # or return the product directly.  Handle both cases.
            product = data.get('product') if isinstance(data, dict) else None
            if not product:
                # Some themes may wrap in 'product' or 'products'
                product = data.get('product') or data.get('products') or data
            if not isinstance(product, dict):
                continue
            title = product.get('title', '') or ''
            handle_verified = product.get('handle', handle)
            title_norm = (title.lower().replace('-', ' ').strip() if title else '')
            # Collect images from both the legacy ``images`` array and the newer
            # ``media`` array.  The ``media`` array can contain additional
            # gallery images (with ``media_type`` set to "image").  Each item
            # should provide ``src`` and ``alt`` fields similar to those in
            # ``images``.  If ``src`` is nested under ``preview_image``, use
            # that as a fallback.  Use a per‑product deduplication set to avoid
            # counting duplicate images within a single product.
            combined: list = []
            try:
                combined.extend(product.get('images', []) or [])
            except Exception:
                pass
            try:
                for media_item in product.get('media', []) or []:
                    try:
                        # Only consider media entries that are images.  Some
                        # entries represent video or 3D models.
                        m_type = media_item.get('media_type') or media_item.get('type')
                        if m_type and 'image' not in str(m_type).lower():
                            continue
                        combined.append(media_item)
                    except Exception:
                        continue
            except Exception:
                pass
            seen_srcs_product: set = set()
            # Track how many issues were found for this product for debugging
            product_issue_count: int = 0
            for item in combined:
                try:
                    # Some media objects nest the actual image details under
                    # ``preview_image``.  Fall back to that if ``src`` is not
                    # present.
                    src = item.get('src') or item.get('preview_image', {}).get('src') or ''
                    if not src or src in seen_srcs_product:
                        continue
                    seen_srcs_product.add(src)
                    total_images_count += 1
                    alt = item.get('alt') or item.get('preview_image', {}).get('alt') or ''
                    page_url = f"https://{domain}/products/{handle_verified}" if handle_verified else f"https://{domain}"
                    # Missing alt
                    if not alt or not alt.strip():
                        issues.append((page_url, src, '(missing)', 'missing', None))
                        product_issue_count += 1
                        continue
                    alt_clean = alt.strip()
                    # Generic alt
                    if len(alt_clean.split()) < 2:
                        issues.append((page_url, src, alt_clean, 'generic', None))
                        product_issue_count += 1
                        continue
                    # Similarity check
                    try:
                        sim = difflib.SequenceMatcher(None, alt_clean.lower(), title_norm).ratio()
                    except Exception:
                        sim = 0.0
                    if sim < 0.4:
                        issues.append((page_url, src, alt_clean, 'low similarity', sim))
                        product_issue_count += 1
                except Exception:
                    continue
            # Log per-product summary at debug level
            try:
                logger.debug(
                    f"Alt check for product '{handle_verified}': processed {len(seen_srcs_product)} images, "
                    f"found {product_issue_count} issues")
            except Exception:
                pass
        except Exception:
            continue
    if total_images_count == 0:
        logger.debug(f"No images found in product JSON for {domain}; all requests may have failed")
    else:
        # Log overall summary of images and issues
        try:
            logger.debug(
                f"Alt check summary for {domain}: processed {total_images_count} images, "
                f"found {len(issues)} issues")
        except Exception:
            pass
    return issues, total_images_count


def check_alt_text_shopify(domain: str) -> list:
    """
    Perform alt text validation using Shopify's product JSON feed.  Each
    product's images are checked for missing, generic or irrelevant alt
    attributes.  The function returns a list of five‑tuples:

        (page_url, image_src, alt_text, reason, similarity)

    where:
        • page_url   – full URL to the product page (constructed as
          "https://<domain>/products/<handle>") for context.
        • image_src  – absolute URL of the image.
        • alt_text   – the alt text if present, or "(missing)".
        • reason     – one of "missing", "generic", or "low similarity".
        • similarity – a float between 0 and 1 indicating how closely the
          alt text matches the product title (only set for the low
          similarity case; otherwise None).

    This structure aligns with the front‑end expectations so that
    alt‑text issues can be displayed consistently alongside other
    compliance checks.
    """
    products = fetch_shopify_products(domain)
    issues: list = []
    if not products:
        return issues
    # Use a set to avoid scanning the same image across multiple products.  Some
    # Shopify stores reuse identical images on many products; counting each
    # instance separately results in duplicate issue reports and inflated
    # denominators.  Track unique image URLs to ensure each image is checked
    # only once.
    seen_srcs: set = set()
    for product in products:
        title = product.get('title', '') or ''
        handle = product.get('handle', '') or ''
        # Normalise the product title for similarity comparisons
        title_norm = title.lower().replace('-', ' ').strip()
        for image in product.get('images', []):
            src = image.get('src') or ''
            # Skip duplicate images
            if src in seen_srcs:
                continue
            seen_srcs.add(src)
            alt = image.get('alt') or ''
            page_url = f"https://{domain}/products/{handle}" if handle else f"https://{domain}"
            # Missing alt
            if not alt or not alt.strip():
                issues.append((page_url, src, '(missing)', 'missing', None))
                continue
            alt_clean = alt.strip()
            # Generic alt (fewer than two words)
            if len(alt_clean.split()) < 2:
                issues.append((page_url, src, alt_clean, 'generic', None))
                continue
            # Relevance check using difflib.SequenceMatcher
            try:
                sim = difflib.SequenceMatcher(None, alt_clean.lower(), title_norm).ratio()
            except Exception:
                sim = 0.0
            if sim < 0.4:
                issues.append((page_url, src, alt_clean, 'low similarity', sim))
    return issues


@app.route('/api/shopify_alt_check')
def shopify_alt_check():
    """
    Public API endpoint to test alt text compliance via Shopify's products JSON.
    Pass a `domain` query parameter to fetch products and return any alt text
    issues detected.  This route is for testing purposes and does not
    interfere with the primary crawl logic.
    """
    domain = request.args.get('domain', '').strip()
    if not domain:
        return jsonify({'error': 'Missing domain parameter'}), 400
    issues = check_alt_text_shopify(domain)
    return jsonify({'domain': domain, 'alt_text_issues': issues, 'issue_count': len(issues)})

if __name__ == '__main__':
    # Development mode only
    app.run(debug=True, host='0.0.0.0', port=int(os.environ.get('PORT', 5000)))