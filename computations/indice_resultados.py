"""Índice de todas as branches de resultados: o que cada execução gravou e onde está cada versão de cada arquivo.

    python3 computations/indice_resultados.py > computations/RESULTADOS.md

Lê `git log` de cada `origin/resultados-*` (faça `git fetch origin 'refs/heads/resultados-*:refs/remotes/origin/resultados-*'`
antes). Para cada commit: o run do GitHub Actions, a data e os arquivos que ele criou, mudou ou apagou. Versões
antigas que execuções posteriores substituíram ou apagaram ficam também em `historico/run-<id>/` na própria branch
(pasta criada pela restauração de 2026-11-03), e qualquer versão sai com `git show COMMIT:ARQUIVO`.
"""
import re
import subprocess


def git(*a):
    return subprocess.run(["git", *a], capture_output=True, text=True, check=True).stdout


ramos = sorted(r.strip() for r in git("branch", "-r", "--list", "origin/resultados-*").split())
print("# Onde estão os resultados dos cálculos\n")
print("Cada workflow grava numa branch própria (`resultados-*`). Desde 2026-11-03 nenhuma execução apaga o que outra")
print("gravou (`computations/grava_resultados.py`): arquivos com o mesmo nome são substituídos e o resto fica; cada branch")
print("tem um `INDICE.md` com uma linha por execução. As versões anteriores estão no histórico do git e, para as que")
print("execuções antigas tinham apagado ou substituído, também em `historico/run-<id>/`.\n")
print("Para ler um arquivo sem trocar de branch:\n")
print("    git fetch origin resultados-alturas")
print("    git show origin/resultados-alturas:alturas.json")
print("    git show COMMIT:varreduras/varre_18_0.json      # uma versão antiga, pelo commit da tabela\n")
print("Gerado por `python3 computations/indice_resultados.py`.\n")
for r in ramos:
    b = r.split("/", 1)[1]
    print(f"## `{b}`\n")
    atuais = git("ls-tree", "-r", "--name-only", r).split("\n")
    hist = sorted({a.split("/")[1] for a in atuais if a.startswith("historico/")})
    print(f"Arquivos na ponta: {len([a for a in atuais if a and not a.startswith('historico/')])}"
          + (f"; versões antigas em `historico/` ({', '.join(hist)})" if hist else "") + ".\n")
    print("| commit | data (UTC) | execução | criados | mudados | apagados |")
    print("|---|---|---|---|---|---|")
    for linha in git("log", "--reverse", "--format=%H|%cI|%s", r).strip().split("\n"):
        c, d, s = linha.split("|", 2)
        run = re.search(r"run (\d+)", s)
        pais = git("rev-list", "--parents", "-n", "1", c).split()[1:]
        if pais:
            mud = git("diff", "--name-status", pais[0], c).strip().split("\n")
        else:
            mud = ["A\t" + a for a in git("ls-tree", "-r", "--name-only", c).strip().split("\n")]
        grupos = {"A": [], "M": [], "D": []}
        for m in mud:
            if m:
                k, nome = m.split("\t", 1)
                grupos.setdefault(k[0], []).append(nome)

        def fmt(v):
            v = [x for x in v if not x.startswith("historico/")]
            return (", ".join(f"`{x}`" for x in v[:6]) + (f" e mais {len(v) - 6}" if len(v) > 6 else "")) or "—"
        exe = f"[{run.group(1)}](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/{run.group(1)})" if run else s[:40]
        print(f"| `{c[:9]}` | {d[:16].replace('T', ' ')} | {exe} | {fmt(grupos['A'])} | {fmt(grupos['M'])} | "
              f"{fmt(grupos['D'])} |")
    print()
