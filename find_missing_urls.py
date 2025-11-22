import re

def find_missing_urls(bib_file):
    with open(bib_file, 'r') as f:
        content = f.read()

    # Split by entry start @type{
    # We capture the key in the split if we use capturing group, but let's just split and process
    # A better way is to iterate over matches of the entry pattern
    
    entries = []
    # Regex to match an entry: @type{key, body}
    # This is a simple parser, assuming standard formatting
    entry_pattern = re.compile(r'@\w+\s*{\s*([^,]+),', re.MULTILINE)
    
    # We can iterate through the file line by line to be safer about boundaries
    current_entry = None
    current_key = None
    entry_lines = []
    
    all_entries = []

    for line in content.splitlines():
        line = line.strip()
        if line.startswith('@'):
            if current_entry:
                all_entries.append((current_key, entry_lines))
            
            # Start new entry
            match = re.match(r'@\w+\s*{\s*([^,]+),?', line)
            if match:
                current_key = match.group(1)
                current_entry = True
                entry_lines = []
            else:
                current_entry = False # Skip preamble or weird lines
        elif current_entry:
            if line == '}': # End of entry (heuristic)
                all_entries.append((current_key, entry_lines))
                current_entry = None
                current_key = None
                entry_lines = []
            else:
                entry_lines.append(line)
    
    # Process last entry if any
    if current_entry and current_key:
        all_entries.append((current_key, entry_lines))

    missing_url_info = []

    for key, lines in all_entries:
        has_url = False
        has_doi = False
        has_isbn = False
        
        for l in lines:
            # Check for fields with regex to handle spacing
            if re.search(r'^\s*url\s*=', l, re.IGNORECASE):
                has_url = True
            if re.search(r'^\s*doi\s*=', l, re.IGNORECASE):
                has_doi = True
            if re.search(r'^\s*isbn\s*=', l, re.IGNORECASE):
                has_isbn = True
        
        if not has_url:
            missing_url_info.append({
                'key': key,
                'has_doi': has_doi,
                'has_isbn': has_isbn
            })

    return missing_url_info

missing = find_missing_urls('references.bib')
print(f"Found {len(missing)} entries without URLs.")

# Prioritize: No DOI and No ISBN
critical = [x for x in missing if not x['has_doi'] and not x['has_isbn']]
print(f"\nCRITICAL (No DOI, No ISBN): {len(critical)}")
for item in critical:
    print(f"{item['key']}")

# Secondary: Has DOI or ISBN
secondary = [x for x in missing if x['has_doi'] or x['has_isbn']]
print(f"\nSECONDARY (Has DOI/ISBN): {len(secondary)}")
for item in secondary:
    extra = []
    if item['has_doi']: extra.append("DOI")
    if item['has_isbn']: extra.append("ISBN")
    print(f"{item['key']} ({', '.join(extra)})")
