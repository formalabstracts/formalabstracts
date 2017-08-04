import xml.etree.ElementTree as ET
import urllib
import sys

def concat_if_not_none(s, sep, dic, ls):
    return s + sep.join([l + ' := "' + dic[l] + '"' for l in ls if l in dic])

def format_author(dic):
    return concat_if_not_none("{ ", ", ", dic, ["name", "institution"]) + " }"

def format_authors(ldic):
    return "[" + ", ".join([format_author(d) for d in ldic]) + "]"

def format_document(dic):
    s = "{ authors := " + format_authors(dic["authors"]) + ", \n  "
    s = concat_if_not_none(s, ", \n  ", dic, ["title", "doi", "arxiv", "reference"])
    return s + " }"

def parse_author(author):
    rv = dict()
    nm = author.find('{http://www.w3.org/2005/Atom}name')
    if nm is not None:
        rv["name"] = nm.text
    af = author.find('{http://arxiv.org/schemas/atom}affiliation')
    if af is not None:
        rv["institution"] = af.text
    return rv
    

def parse_dict_from_entry(entry):
    rv = dict()
    ats = [parse_author(at) for at in entry.findall('{http://www.w3.org/2005/Atom}author')]
    rv["authors"] = ats
    title = entry.find('{http://www.w3.org/2005/Atom}title')
    if title is not None:
        rv["title"] = title.text
    summary = entry.find('{http://www.w3.org/2005/Atom}summary')
    if summary is not None:
        rv["abstract"] = summary.text
    journal = entry.find('{http://arxiv.org/schemas/atom}journal_ref')
    if journal is not None:
        rv["reference"] = journal.text
    doi = entry.find('{http://www.w3.org/2005/Atom}doi')
    if doi is not None:
        rv["doi"] = doi.text
    link = entry.find('{http://www.w3.org/2005/Atom}id')
    if link is not None:
        rv["arxiv"] = link.text
    return rv

def parse_entries(feed):
    entries = [format_document(parse_dict_from_entry(e)) for e in feed.findall('{http://www.w3.org/2005/Atom}entry')]
    entries = "\n---\n".join(entries)
    print ''.join([i if ord(i) < 128 else ' ' for i in entries])

if __name__ == '__main__':
    search = sys.argv[1]
    numres = sys.argv[2]
    quer = 'http://export.arxiv.org/api/query?search_query=all:{0}&start=0&max_results={1}'.format(search, numres)
    data = urllib.urlopen(quer).read()
    root = ET.fromstring(data)
    parse_entries(root)
