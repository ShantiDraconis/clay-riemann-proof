"""Grava os arquivos de uma execução numa branch de resultados SEM apagar o que já estava lá.

    python3 computations/grava_resultados.py BRANCH PASTA --run RUN_ID --sha SHA [--titulo TITULO]

Antes, cada workflow apagava a branch inteira e punha só o que a execução nova tinha produzido: rodar de novo uma
altura tirava da ponta da branch as outras (os dados ficavam só no histórico do git, difíceis de achar). Agora:

* os arquivos de PASTA vão para a raiz da branch e substituem só os que têm o mesmo nome; o resto fica;
* `INDICE.md` ganha uma linha por execução (data, run, commit do código, arquivos gravados) e a receita para tirar
  da história qualquer versão anterior (`git log --grep "run RUN_ID"`);
* o push tenta de novo (busca, rebase) se outra tarefa gravou na mesma branch nesse meio tempo.

Roda dentro do checkout do repositório (o workflow já fez `actions/checkout`). Não toca na branch main.
"""
import argparse
import shutil
import subprocess
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path


def git(*a, check=True):
    return subprocess.run(["git", *a], check=check, capture_output=True, text=True)


ap = argparse.ArgumentParser()
ap.add_argument("branch")
ap.add_argument("pasta")
ap.add_argument("--run", default="local")
ap.add_argument("--sha", default="")
ap.add_argument("--titulo", default="")
a = ap.parse_args()

orig = Path(a.pasta).resolve()
tmp = Path(tempfile.mkdtemp(prefix="grava-"))
arquivos = []
if orig.is_dir():
    for p in sorted(orig.rglob("*")):
        if p.is_file():
            rel = p.relative_to(orig)
            (tmp / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(p, tmp / rel)
            arquivos.append(str(rel))
if not arquivos:
    print(f"nada para gravar em {a.branch} (pasta {a.pasta} vazia ou ausente)")
    raise SystemExit(0)

git("config", "user.name", "github-actions[bot]")
git("config", "user.email", "41898282+github-actions[bot]@users.noreply.github.com")
titulo = a.titulo or a.branch.replace("resultados-", "")
agora = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")

for tentativa in range(6):
    existe = git("fetch", "-q", "origin", f"{a.branch}:refs/remotes/origin/{a.branch}", check=False).returncode == 0
    git("reset", "-q", "--hard", check=False)
    git("clean", "-fdxq", check=False)
    if existe:
        git("checkout", "-q", "-f", "-B", a.branch, f"origin/{a.branch}")
    else:
        git("checkout", "-q", "--orphan", a.branch)
        git("rm", "-rqf", ".", check=False)
        for p in Path(".").iterdir():
            if p.name != ".git":
                shutil.rmtree(p) if p.is_dir() else p.unlink()
    for rel in arquivos:
        (Path(rel)).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(tmp / rel, rel)
    ind = Path("INDICE.md")
    if not ind.exists():
        ind.write_text(
            f"# {a.branch}\n\n"
            "Cada execução substitui só os arquivos com o mesmo nome; nada é apagado. Uma versão anterior de qualquer\n"
            f"arquivo: `git log --grep \"run RUN_ID\" origin/{a.branch}` dá o commit, e `git show COMMIT:ARQUIVO` o arquivo.\n\n"
            "| data | run | código | arquivos gravados |\n|---|---|---|---|\n")
    lista = ", ".join(arquivos[:40]) + (f" e mais {len(arquivos) - 40}" if len(arquivos) > 40 else "")
    with ind.open("a") as f:
        f.write(f"| {agora} | {a.run} | {a.sha[:7]} | {lista} |\n")
    git("add", "-A")
    if git("commit", "-q", "-m", f"{titulo}: run {a.run} ({a.sha})", check=False).returncode != 0:
        print("nada mudou")
        break
    if git("push", "-q", "origin", a.branch, check=False).returncode == 0:
        print(f"gravado em {a.branch}: {len(arquivos)} arquivos")
        break
    time.sleep(5 + 10 * tentativa)  # outra tarefa gravou antes: busca de novo e reaplica
else:
    raise SystemExit(f"não consegui gravar em {a.branch}")
