import re
import urllib.request
import urllib.error
import ssl

# Ignore SSL certificate errors
ctx = ssl.create_default_context()
ctx.check_hostname = False
ctx.verify_mode = ssl.CERT_NONE

def check_url(url):
    try:
        req = urllib.request.Request(url, headers={'User-Agent': 'Mozilla/5.0'})
        with urllib.request.urlopen(req, timeout=10, context=ctx) as response:
            return response.getcode()
    except urllib.error.HTTPError as e:
        return e.code
    except Exception as e:
        return str(e)

with open('references.bib', 'r') as f:
    content = f.read()

urls = re.findall(r'url\s*=\s*{(.*?)}', content)

print(f"Found {len(urls)} URLs.")

for url in urls:
    status = check_url(url)
    if status != 200:
        print(f"{status}: {url}")
