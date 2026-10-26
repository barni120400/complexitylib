#!/usr/bin/env python3
"""Static Lean tactic-token census; never invokes Lean/Lake or reads build outputs."""
import argparse, bisect, collections, csv, io, json, pathlib, re, subprocess, tarfile
ROOTS = ('Complexity', 'ComplexityTests', 'abstracts', 'guide')
TOKENS = re.compile(r"(?<![\w.'])\b(polytime|fun_prop|ppt)\b(?![\w'])")
DECL = re.compile(r'^\s*(?:(?:public|private|protected|noncomputable|unsafe|partial|local)\s+)*(theorem|lemma|example|def|instance|abbrev)\b([^\n]*)', re.M)
OPTIONS = re.compile(r'\bset_option\s+(maxHeartbeats|maxRecDepth|synthInstance\.maxHeartbeats|maxSteps)\s+([^\s;]+)(\s+in\b)?')
SIGNALS = {
 'explicit_composition':r'\.(?:comp|trans|prod|pair)\b',
 'fallback_syntax':r'\b(?:first|try|orelse)\b|<\|>',
 'negative_control':r'\bfail_if_success\b|\bguard_msgs\b',
 'search_controls':r'\b(?:maxSteps|maxDepth|maxTransitionDepth|maxRecDepth|maxHeartbeats)\b',
 'unfolding':r'\b(?:unfold|simp_all|dsimp)\b',
 'explicit_certificate_term':r'\b(?:exact|apply|refine|have)\b.*(?:computableIn|isPolyTime|isPPT|unary_|binary_)',
}
def mask_lean(s):
    """Mask nested /- -/, -- comments and double-quoted strings, retaining coordinates.
    This is lexical, not Lean parsing: quotations/antiquotations and option scopes are approximate.
    """
    out=list(s); i=0; depth=0; string=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i): out[i:i+2]='  ';depth+=1;i+=2
            elif s.startswith('-/',i):out[i:i+2]='  ';depth-=1;i+=2
            else:
                if s[i]!='\n':out[i]=' '
                i+=1
        elif string:
            if s[i]=='\\':
                out[i]=' ';i+=1
                if i<len(s) and s[i]!='\n':out[i]=' '
                i+=1
            else:
                if s[i]=='"':string=False
                if s[i]!='\n':out[i]=' '
                i+=1
        elif (raw := re.match(r'r(#+)"',s[i:])):
            end=s.find('"'+raw[1],i+raw.end());end=len(s) if end<0 else end+1+len(raw[1])
            for j in range(i,end):
                if s[j]!='\n':out[j]=' '
            i=end
        elif s.startswith('/-',i):out[i:i+2]='  ';depth=1;i+=2
        elif s.startswith('--',i):
            end=s.find('\n',i);end=len(s) if end<0 else end
            out[i:end]=' '*(end-i);i=end
        elif s[i]=='"':out[i]=' ';string=True;i+=1
        else:i+=1
    return ''.join(out)
def classify(code,pos):
    line=code[code.rfind('\n',0,pos)+1:pos]
    prefix=code[max(0,pos-350):pos]
    if prefix.endswith('`'):return 'quoted_identifier_reference'
    if re.search(r'(?:name|tacticName)\s*:=\s*$',line):return 'declaration_metadata'
    bracket=prefix.rfind('[')
    if bracket>prefix.rfind(']'):
        context=prefix[max(0,bracket-100):]
        if re.search(r'@\s*\[|\battribute\s*\[',context):return 'attribute_registration'
        if re.search(r'rule_sets|declare_aesop_rule_sets|aesop',context):return 'ruleset_reference'
    if re.search(r'`\([^\n]*tactic\s*\|',prefix):return 'quoted_tactic_candidate'
    if re.search(r'\b(?:namespace|open|export|attribute)\s*$',line):return 'name_reference'
    return 'tactic_call_candidate'
def signals(text):return [k for k,p in SIGNALS.items() if re.search(p,text,re.S if k=='explicit_certificate_term' else 0)]
def write_csv(path,rows,fields):
    with path.open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=fields,extrasaction='ignore',lineterminator='\n');w.writeheader()
        for r in rows:w.writerow({k:(json.dumps(v,ensure_ascii=False) if isinstance(v,(dict,list)) else v) for k,v in r.items()})
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--revision',required=True);ap.add_argument('--output',type=pathlib.Path,required=True);args=ap.parse_args()
    pin=subprocess.check_output(['git','rev-parse',args.revision],text=True).strip()
    archive=subprocess.check_output(['git','archive','--format=tar',pin,*ROOTS])
    rows=[];docs=[];files=collections.Counter();totals=collections.Counter()
    with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
      for item in sorted(tar.getmembers(),key=lambda x:x.name):
        if not item.isfile():continue
        name=item.name
        if not name.endswith(('.lean','.md')):continue
        text=tar.extractfile(item).read().decode('utf-8');area=name.split('/')[0]
        if not name.endswith('.lean'):
          for m in TOKENS.finditer(text):docs.append(dict(path=name,line=text.count('\n',0,m.start())+1,tactic=m.group(),classification='non_lean_text_token'))
          continue
        files[area]+=1;code=mask_lean(text);lines=text.splitlines();starts=[0]+[m.end() for m in re.finditer('\n',text)]
        decls=list(DECL.finditer(code));declpos=[m.start() for m in decls];opts=list(OPTIONS.finditer(code))
        for m in TOKENS.finditer(code):
          line=bisect.bisect_right(starts,m.start());di=bisect.bisect_right(declpos,m.start())-1
          decl=decls[di] if di>=0 else None;end=declpos[di+1] if 0<=di+1<len(declpos) else len(code)
          scope=code[decl.start():end] if decl else code[:end]
          prior=[o for o in opts if o.start()<m.start()]
          setters=[dict(line=bisect.bisect_right(starts,o.start()),option=o[1],value=o[2],has_in=bool(o[3]),scope='not_resolved_statically') for o in prior[-3:]]
          cls=classify(code,m.start());totals[(area,m[1],cls)]+=1
          rows.append(dict(path=name,line=line,column=m.start()-starts[line-1]+1,tactic=m[1],classification=cls,
            declaration=(decl[1]+' '+decl[2].strip())[:220] if decl else None,
            declaration_line=bisect.bisect_right(starts,decl.start()) if decl else None,
            source_line=lines[line-1].strip()[:420],prior_option_directives=setters,
            nearby_signals=signals('\n'.join(code.splitlines()[max(0,line-4):line+3])),
            declaration_signals=signals(scope),effective_heartbeat_budget=None,
            elapsed_ms=None,heartbeats=None,rules_fired=None,
            url=f'https://github.com/cslib-community/complexitylib/blob/{pin}/{name}#L{line}'))
    calls=[r for r in rows if r['classification'] in ('tactic_call_candidate','quoted_tactic_candidate')]
    excluded=[r for r in rows if r['classification'] not in ('tactic_call_candidate','quoted_tactic_candidate')]
    summary={'revision':pin,'method':'lexical static candidates; comments/strings masked; no Lean parsing/elaboration/build/cache access',
      'source_roots':list(ROOTS),'lean_files_scanned':dict(files),'total_lean_files':sum(files.values()),
      'all_code_tokens':len(rows),'call_candidates':len(calls),'ordinary_call_candidates':sum(r['classification']=='tactic_call_candidate' for r in calls),
      'quoted_tactic_candidates':sum(r['classification']=='quoted_tactic_candidate' for r in calls),'excluded_code_tokens':len(excluded),'non_lean_text_tokens':len(docs),
      'by_area_tactic_classification':[dict(area=a,tactic=t,classification=c,count=n) for (a,t,c),n in sorted(totals.items())],
      'call_candidate_signal_counts':dict(collections.Counter(s for r in calls for s in r['declaration_signals'])),
      'measured_by_this_census':0,'limitations':['Not an AST-verified invocation count; quotations/antiquotations and name references require spot checks.', 'Option setters are prior textual directives, NOT established effective budgets; section/local/in scopes are not resolved.', 'Manual composition/fallback signals record lexical presence, not motivation or successful paths.', 'No per-call dynamic time/heartbeat/rule trace, success/failure or syntax-directed coverage measurement. Published historical evidence is separate.']}
    args.output.mkdir(parents=True,exist_ok=True)
    (args.output/'summary.json').write_text(json.dumps(summary,indent=2,ensure_ascii=False)+'\n')
    (args.output/'callsites.json').write_text(json.dumps({'revision':pin,'entries':calls},indent=2,ensure_ascii=False)+'\n')
    fields=['path','line','column','tactic','classification','declaration','declaration_line','source_line','prior_option_directives','nearby_signals','declaration_signals','effective_heartbeat_budget','elapsed_ms','heartbeats','rules_fired','url']
    write_csv(args.output/'callsites.csv',calls,fields);write_csv(args.output/'excluded-code-tokens.csv',excluded,fields)
    write_csv(args.output/'non-lean-text-tokens.csv',docs,['path','line','tactic','classification'])
    print(json.dumps({k:v for k,v in summary.items() if k not in ('by_area_tactic_classification','limitations')},indent=2))
if __name__=='__main__':main()
