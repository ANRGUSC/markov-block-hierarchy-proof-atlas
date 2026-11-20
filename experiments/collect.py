"""Collect completed proof-authoring races and render the separate experiment report."""
import argparse
import json
import re
import statistics
from pathlib import Path

def read(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))

def checked(folder, stem):
    text=(folder/(stem+".output")).read_text(encoding="utf8")
    reports=re.findall(r"depends on axioms:\s*\[([^\]]*)\]",text)
    if len(reports)!=1 or set(reports[0].split(", "))-{"propext","Classical.choice","Quot.sound"}:
        raise ValueError("Unexpected axiom report for "+stem)
    return {"source":(folder/(stem+".lean")).read_text(encoding="utf8"),"axioms":reports[0].split(", ")}

def worker(folder,stem):
    claim=read(folder/(stem+".claim.json"))
    attempts=[json.loads(x) for x in (folder/(stem+".attempts.jsonl")).read_text().splitlines()]
    accepted=read(folder/(stem+".pass.json"))
    stages={s:checked(folder,s) for s in sorted({a.get("unit",stem) for a in attempts if a["ok"]})}
    strategy=folder/(stem+".strategy.txt")
    return {"claim":claim,"attempts":attempts,"pass":accepted,"checked":stages,
            "strategy_log":strategy.read_text(encoding="utf-8-sig") if strategy.exists() else None}

def arm(workers, release, certificate, assembly=None):
    starts=[w['claim']['start'] for w in workers]
    finish=certificate['end']
    drafts=[w['attempts'][0]['start']-w['claim']['start'] for w in workers]
    waits=[sum(a['elapsed'] for a in w['attempts']) for w in workers]
    occupied=[w['pass']['end']-w['claim']['start'] for w in workers]
    return {"release_to_certificate_s":finish-release,"claim_offsets_s":[s-release for s in starts],
            "first_drafts_s":drafts,"nonchecker_s":[t-c for t,c in zip(occupied,waits)],
            "checker_s_per_worker":waits,"total_occupied_worker_s":sum(occupied),
            "extra_join_check_s":assembly['elapsed'] if assembly else 0,
            "attempts":sum(len(w['attempts']) for w in workers)+(1 if assembly else 0),
            "workers":workers,"certificate":certificate}

def collect(src):
    rows=[]
    for n,s in enumerate(read(src/'contracts.json'),1):
        stems=[f'R{n}Merged',f'R{n}A',f'R{n}B',f'Join{n}']
        if not all((src/(x+'.pass.json')).exists() for x in stems):continue
        start=read(src/f'round-{n}.json')['start']
        m,a,b=[worker(src,x) for x in stems[:3]]
        join=read(src/(stems[3]+'.pass.json'))
        rows.append(dict(id=f'D{n}',series='Parallel split vs combined',topic=s['topic'],contract=s,release=start,
          common=(src/f'Common{n}.lean').read_text(encoding='utf8'),join=checked(src,stems[3]),
          arms={'combined':arm([m],start,m['pass']),'parallel split':arm([a,b],start,join,join)}))
    specs=read(src/'same-author-contracts.json')+read(src/'paired-contracts.json')+read(src/'lamport-contracts.json')
    for n,s in enumerate(specs,1):
        stems=[f'P{n}A',f'P{n}B']
        if not all((src/(x+'.pass.json')).exists() for x in stems):continue
        start=read(src/f'pair-{n}.start.json')['start']
        arms={}
        for x in stems:
            w=worker(src,x);arms[w['claim']['mode']]=arm([w],start,w['pass'])
        rows.append(dict(id=f'P{n}',series=s.get('series','Sequential split vs combined'),topic=s['topic'],contract=s,
                    common=(src/f'PairCommon{n}.lean').read_text(encoding='utf8'),release=start,arms=arms))
    return rows

def report(rows):
    lines=['# Experiments in Lean proof writing','',
        'The metric is elapsed time from the release of an unseen obligation until Lean accepts the entire contract. The split arm includes the check that joins both lemmas. Each arm checks the same proposition with the same pinned Lean installation. The paper-wide study is ongoing.','',
        '## Findings by experiment','','| Experiment | Completed pairs | First complete certificate | Working decision |',
        '|---|---:|---|---|']
    for series in dict.fromkeys(r['series'] for r in rows):
        group=[r for r in rows if r['series']==series]
        winners=[min(r['arms'],key=lambda a:r['arms'][a]['release_to_certificate_s']) for r in group]
        tally=', '.join(str(winners.count(w))+' '+w for w in dict.fromkeys(winners))
        if series=='Parallel split vs combined':
            decision='Keep short algebraic pairs together when adding an agent would add a join or queue delay. Test harder goals separately.'
        else:
            decision='Pilot evidence. Review the individual drafting intervals, retries and integration cost before changing the skill.'
        lines.append(f'| {series} | {len(group)} | {tally} | {decision} |')
    lines+=['','## Matched trials','','| Pair and paper obligation | Approach | Complete (s) | First draft per author (s) | Outside Lean per author (s) | Lean per author (s) | Extra join (s) | Checks |',
      '|---|---|---:|---:|---:|---:|---:|---:|']
    fmt=lambda seq:' / '.join(f'{x:.1f}' for x in seq)
    for r in rows:
        for mode,v in r['arms'].items():
            lines.append(f"| {r['id']} · {r['topic']} | {mode} | {v['release_to_certificate_s']:.1f} | {fmt(v['first_drafts_s'])} | {fmt(v['nonchecker_s'])} | {fmt(v['checker_s_per_worker'])} | {v['extra_join_check_s']:.1f} | {v['attempts']} |")
    lines+=['','## Interpretation','',
      'In D1 all three agents claimed the task together. In D2 and D3, the next pair opened when the first proof finished. One split worker was still finishing the preceding pair and claimed the new task about 88 and 91 seconds after release. These two comparisons measure pipeline throughput with a busy worker. They cannot establish the effect of splitting for two authors who start together. The equal-author series uses a synchronized gate and alternates which author receives the intervention.','',
      'First draft ends when the author submits their first attempt. Outside-Lean time includes reasoning, editing, reading diagnostics and tool or scheduling delays. These are wall-clock measurements. Checker time covers Lean process startup, elaboration and kernel verification. The raw event data includes individual attempt times, author occupancy, accepted source text and axiom reports. Small samples from this paper support conditional working rules.','',
      'The study protocol records the remaining comparisons and how the evidence will inform the reusable skill. [Study protocol](PROTOCOL.md) · [Machine-readable trial records](trials.json)']
    return '\n'.join(lines)+'\n'

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('workspace',type=Path)
    args=parser.parse_args()
    rows=collect(args.workspace)
    dest=Path(__file__).resolve().parent
    (dest/'trials.json').write_text(json.dumps(rows,indent=2,ensure_ascii=False)+'\n',encoding='utf8')
    (dest/'REPORT.md').write_text(report(rows),encoding='utf8')
    print(len(rows),'completed matched pairs')
