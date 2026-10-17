#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Servidor da loja PODEROSA — com banco de dados na NUVEM (Turso) e Checkout Pro (Mercado Pago)
"""
import hashlib
import hmac
import json
import mimetypes
import os
import re
import secrets
import sqlite3
import sys
import queue
import threading
import time
import urllib.error
import urllib.request
from datetime import datetime, timedelta
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, unquote

try:
    import libsql
    TURSO_BIBLIOTECA_OK = True
except ImportError:
    TURSO_BIBLIOTECA_OK = False
    libsql = None

try:
    import mercadopago
    MP_BIBLIOTECA_OK = True
except ImportError:
    MP_BIBLIOTECA_OK = False
    mercadopago = None

for _e, _t in ((".jfif", "image/jpeg"), (".avif", "image/avif"), (".webp", "image/webp"), (".svg", "image/svg+xml")):
    mimetypes.add_type(_t, _e)

BASE_DIR = os.path.realpath(os.path.dirname(os.path.abspath(__file__)))
INDEX_FILE = os.path.join(BASE_DIR, "index.html")
DB_PATH = os.environ.get("DB_PATH", os.path.join(BASE_DIR, "pow.db"))
PORT = int(os.environ.get("PORT", "8000"))
HOST = os.environ.get("HOST", "0.0.0.0")
ADMIN_FILE = os.path.join(BASE_DIR, ".admin_token")
TOKEN_ME_FILE = os.path.join(BASE_DIR, "token_melhorenvio.txt")
TOKEN_TURSO_FILE = os.path.join(BASE_DIR, "token_turso.txt")
TOKEN_MP_FILE = os.path.join(BASE_DIR, "token_mercadopago.txt")

CEP_ORIGEM = os.environ.get("CEP_ORIGEM", "41925-715")
MELHOR_ENVIO_API = os.environ.get("MELHOR_ENVIO_API",
                             "https://melhorenvio.com.br/api/v2/me/shipment/calculate")
MELHOR_ENVIO_USER_AGENT = "Poderosa Hair Store (contato@poderosa.com.br)"

EMBALAGENS = {
    "par":     {"peso": 0.80, "altura": 22, "largura": 14, "comprimento": 7},
    "tonico":  {"peso": 0.35, "altura": 20, "largura": 6,  "comprimento": 6},
    "frasco":  {"peso": 0.40, "altura": 20, "largura": 7,  "comprimento": 7},
    "pote":    {"peso": 0.60, "altura": 10, "largura": 12, "comprimento": 12},
}
EMBALAGEM_PRODUTO = {
    1: "par", 2: "par", 3: "tonico", 4: "frasco", 5: "frasco", 6: "par",
    7: "par", 8: "pote", 9: "frasco", 10: "pote", 11: "pote", 49: "frasco",
}

FRETE_GRATIS_MINIMO = 199.00
FRETE_SALVADOR_VALOR = 19.00
FRETE_SALVADOR_PRAZO = 2
DESCONTO_PIX = 0.05
SESSAO_DIAS = 30
PAGAMENTOS_OK = ("pix", "cartão", "cartao", "boleto")

CUPONS_INICIAIS = [
    ("BEMVINDO10", "percentual", 10.0, 0.0),
    ("PODEROSA5", "percentual", 5.0, 0.0),
    ("FRETE20", "fixo", 20.0, 150.0),
]

db_lock = threading.Lock()
tentativas = {}


def ler_token_me():
    # Em hospedagem use a variável de ambiente MELHORENVIO_TOKEN; localmente vale o arquivo.
    if os.environ.get("MELHORENVIO_TOKEN"):
        return os.environ["MELHORENVIO_TOKEN"].strip()
    if os.path.exists(TOKEN_ME_FILE):
        return open(TOKEN_ME_FILE, encoding="utf-8").read().strip()
    return ""

TOKEN_ME = ler_token_me()


def ler_token_turso():
    # Em hospedagem use as variáveis TURSO_URL e TURSO_TOKEN; localmente vale o arquivo.
    if os.environ.get("TURSO_URL") and os.environ.get("TURSO_TOKEN"):
        return os.environ["TURSO_URL"].strip(), os.environ["TURSO_TOKEN"].strip()
    if not os.path.exists(TOKEN_TURSO_FILE):
        return None, None
    url, tok = None, None
    with open(TOKEN_TURSO_FILE, encoding="utf-8") as f:
        for linha in f:
            linha = linha.strip()
            if not linha:
                continue
            if linha.upper().startswith("URL:"):
                url = linha.split(":", 1)[1].strip()
            elif linha.upper().startswith("TOKEN:"):
                tok = linha.split(":", 1)[1].strip()
    return url, tok

TURSO_URL, TURSO_TOKEN = ler_token_turso()
USANDO_TURSO = bool(TURSO_URL and TURSO_TOKEN and TURSO_BIBLIOTECA_OK)


def ler_token_mp():
    # Em hospedagem use a variável MP_TOKEN; localmente vale o arquivo.
    if os.environ.get("MP_TOKEN"):
        return os.environ["MP_TOKEN"].strip()
    if not os.path.exists(TOKEN_MP_FILE):
        return ""
    with open(TOKEN_MP_FILE, encoding="utf-8") as f:
        for linha in f:
            if linha.upper().startswith("TOKEN:"):
                return linha.split(":", 1)[1].strip()
    return ""

TOKEN_MP = ler_token_mp()
USANDO_MP = bool(TOKEN_MP and MP_BIBLIOTECA_OK)


# ============================================================
# Wrappers do libsql (compatibilidade com sqlite3.Row)
# ============================================================
class _RowLibsql:
    __slots__ = ("_cols", "_vals", "_dict")
    def __init__(self, colunas, valores=None):
        if valores is None and isinstance(colunas, dict):
            self._dict = dict(colunas)
            self._cols = tuple(colunas.keys())
            self._vals = tuple(colunas.values())
            return
        self._cols = tuple(colunas or ())
        self._vals = tuple(valores or ())
        try:
            self._dict = dict(zip(self._cols, self._vals))
        except Exception:
            self._dict = {}
    def __getitem__(self, k):
        if isinstance(k, str):
            if k in self._dict:
                return self._dict[k]
            return self._vals[self._cols.index(k)]
        return self._vals[k]
    def __iter__(self):
        return iter(self._vals)
    def __len__(self):
        return len(self._vals)
    def __contains__(self, k):
        if isinstance(k, str):
            return k in self._dict or k in self._cols
        return k in self._vals
    def keys(self):
        return list(self._cols)
    def values(self):
        return list(self._vals)
    def items(self):
        return list(zip(self._cols, self._vals))
    def get(self, k, default=None):
        try:
            return self[k]
        except Exception:
            return default
    def __eq__(self, other):
        if isinstance(other, _RowLibsql):
            return self._dict == other._dict
        if isinstance(other, dict):
            return self._dict == other
        if isinstance(other, (tuple, list)):
            return self._vals == tuple(other)
        return NotImplemented
    def __repr__(self):
        return "Row(%r)" % (self._dict,)


class _CursorLibsql:
    def __init__(self, cur):
        self._cur = cur
        self._cols = None
        self.lastrowid = None
        self.rowcount = 0
    def _atualiza_cols(self):
        try:
            desc = getattr(self._cur, "description", None)
            if desc:
                self._cols = [d[0] for d in desc]
        except Exception:
            self._cols = None
        try:
            self.lastrowid = getattr(self._cur, "lastrowid", None)
        except Exception:
            self.lastrowid = None
        try:
            self.rowcount = getattr(self._cur, "rowcount", 0) or 0
        except Exception:
            self.rowcount = 0
    def execute(self, *a, **k):
        r = self._cur.execute(*a, **k)
        self._atualiza_cols()
        return self
    def executemany(self, *a, **k):
        self._cur.executemany(*a, **k)
        return self
    def executescript(self, *a, **k):
        r = self._cur.executescript(*a, **k)
        self._atualiza_cols()
        return r
    def _wrap(self, linha):
        if linha is None:
            return None
        if isinstance(linha, _RowLibsql):
            return linha
        if isinstance(linha, dict):
            return _RowLibsql(linha)
        try:
            if hasattr(linha, "keys"):
                d = {k: linha[k] for k in linha.keys()}
                return _RowLibsql(d)
        except Exception:
            pass
        if self._cols is None:
            self._atualiza_cols()
        try:
            if self._cols:
                return _RowLibsql(self._cols, tuple(linha))
        except Exception:
            pass
        return linha
    def fetchone(self):
        return self._wrap(self._cur.fetchone())
    def fetchall(self):
        try:
            linhas = self._cur.fetchall()
        except Exception:
            return []
        return [self._wrap(l) for l in linhas]
    def __iter__(self):
        self._atualiza_cols()
        try:
            for l in self._cur:
                yield self._wrap(l)
        except Exception:
            return
    def __getattr__(self, nome):
        return getattr(self._cur, nome)
    def close(self):
        try:
            self._cur.close()
        except Exception:
            pass


class _ConnLibsql:
    def __init__(self, conn):
        self._conn = conn
    def execute(self, *a, **k):
        return _CursorLibsql(self._conn.execute(*a, **k))
    def executemany(self, *a, **k):
        return _CursorLibsql(self._conn.executemany(*a, **k))
    def executescript(self, *a, **k):
        return self._conn.executescript(*a, **k)
    def commit(self):
        try:
            self._conn.commit()
        except Exception:
            pass
    def rollback(self):
        try:
            self._conn.rollback()
        except Exception:
            pass
    def close(self):
        try:
            self._conn.close()
        except Exception:
            pass
    def __enter__(self):
        return self
    def __exit__(self, *a):
        try:
            self.commit()
        except Exception:
            pass
        try:
            self.close()
        except Exception:
            pass
# ============================================================


def agora():
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")

def moeda(v):
    return round(float(v) + 1e-9, 2)

def hash_senha(senha, salt=None):
    salt = salt or secrets.token_hex(16)
    h = hashlib.pbkdf2_hmac("sha256", senha.encode("utf-8"), bytes.fromhex(salt), 200_000)
    return salt, h.hex()

def confere_senha(senha, salt, hash_guardado):
    _, h = hash_senha(senha, salt)
    return hmac.compare_digest(h, hash_guardado)

EMAIL_RE = re.compile(r"^[^@\s]+@[^@\s]+\.[^@\s]+$")


def _colunas_tabela(c, tabela):
    try:
        cur = c.execute("PRAGMA table_info(%s)" % tabela)
    except Exception:
        return []
    linhas = None
    try:
        linhas = list(cur)
    except TypeError:
        try:
            linhas = cur.fetchall()
        except Exception:
            linhas = []
    except Exception:
        linhas = []
    if linhas is None:
        try:
            linhas = cur.fetchall()
        except Exception:
            linhas = []
    cols = []
    for r in linhas or []:
        try:
            cols.append(r[1])
        except (TypeError, IndexError):
            try:
                cols.append(r["name"])
            except Exception:
                pass
    return cols


def conectar():
    if USANDO_TURSO:
        base = libsql.connect(database=TURSO_URL, auth_token=TURSO_TOKEN)
        try:
            base.execute("PRAGMA foreign_keys = ON")
        except Exception:
            pass
        return _ConnLibsql(base)
    c = sqlite3.connect(DB_PATH, timeout=30)
    c.row_factory = sqlite3.Row
    c.execute("PRAGMA foreign_keys = ON")
    return c


def eh_salvador(cep):
    try:
        d = _cep(cep)[1]
    except ApiErro:
        return False
    cidade = (d.get("cidade") or "").strip().lower()
    return cidade == "salvador" and (d.get("estado") or "").upper() == "BA"


def calcular_frete_me(cep_destino, itens, subtotal):
    cep_dest = re.sub(r"\D", "", cep_destino or "")
    cep_orig = re.sub(r"\D", "", CEP_ORIGEM or "")
    if len(cep_dest) == 8 and eh_salvador(cep_dest):
        return [{
            "chave": "salvador", "nome": "Entrega em Salvador",
            "valor": moeda(FRETE_SALVADOR_VALOR), "prazo": FRETE_SALVADOR_PRAZO,
            "empresa": "Poderosa",
        }]
    if len(cep_dest) != 8 or len(cep_orig) != 8 or not TOKEN_ME:
        return None

    produtos_env = []
    for it in itens:
        pid = int(it.get("id", 0))
        qtd = max(1, int(it.get("quantidade", 1)))
        tipo = EMBALAGEM_PRODUTO.get(pid, "frasco")
        e = EMBALAGENS[tipo]
        for _ in range(qtd):
            produtos_env.append({
                "id": str(pid), "width": e["largura"], "height": e["altura"],
                "length": e["comprimento"], "weight": e["peso"],
                "insurance_value": 0, "quantity": 1,
            })

    payload = json.dumps({
        "from": {"postal_code": cep_orig},
        "to": {"postal_code": cep_dest},
        "products": produtos_env,
        "options": {"receipt": False, "own_hand": False},
        "services": "1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30",
    }).encode("utf-8")

    req = urllib.request.Request(MELHOR_ENVIO_API, data=payload, method="POST")
    req.add_header("Authorization", "Bearer " + TOKEN_ME)
    req.add_header("Content-Type", "application/json")
    req.add_header("Accept", "application/json")
    req.add_header("User-Agent", MELHOR_ENVIO_USER_AGENT)

    try:
        with urllib.request.urlopen(req, timeout=15) as r:
            dados = json.loads(r.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        corpo_erro = e.read().decode("utf-8", "ignore")[:300]
        sys.stderr.write("Erro Melhor Envio %s: %s\n" % (e.code, corpo_erro))
        return None
    except Exception as e:
        sys.stderr.write("Erro Melhor Envio: %r\n" % (e,))
        return None

    if not isinstance(dados, list) or not dados:
        return None

    opcoes = []
    for d in dados:
        if d.get("error"):
            continue
        try:
            preco = float(d.get("custom_price") or d.get("price") or 0)
            prazo = int(d.get("custom_delivery_time") or d.get("delivery_time") or 0)
        except (TypeError, ValueError):
            continue
        if preco <= 0:
            continue
        nome = d.get("name") or d.get("company", {}).get("name") or "Frete"
        empresa = (d.get("company") or {}).get("name", "")
        label = nome if nome.lower().startswith(empresa.lower()) else (empresa + " " + nome).strip()
        chave = re.sub(r"[^a-z0-9]+", "-", nome.lower())[:30]
        opcoes.append({"chave": chave, "nome": label, "valor": moeda(preco),
                       "prazo": prazo, "empresa": empresa})

    if subtotal >= FRETE_GRATIS_MINIMO and opcoes:
        mais_barato = min(opcoes, key=lambda o: o["valor"])
        opcoes.append({
            "chave": "gratis",
            "nome": "Frete Grátis (%s, %d dias úteis)" % (mais_barato["nome"], mais_barato["prazo"]),
            "valor": 0.0, "prazo": mais_barato["prazo"],
            "empresa": mais_barato["empresa"],
            "custo_loja": mais_barato["valor"],
            "servico_chave": mais_barato["chave"],
        })

    return opcoes if opcoes else None


def criar_banco():
    with db_lock, conectar() as c:
        c.executescript("""
            CREATE TABLE IF NOT EXISTS usuarios(
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                nome TEXT NOT NULL, email TEXT NOT NULL UNIQUE,
                salt TEXT NOT NULL, senha_hash TEXT NOT NULL, criado_em TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS sessoes(
                token TEXT PRIMARY KEY, usuario_id INTEGER NOT NULL, expira_em TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS favoritos(
                usuario_id INTEGER NOT NULL, produto_id INTEGER NOT NULL,
                PRIMARY KEY(usuario_id, produto_id)
            );
            CREATE TABLE IF NOT EXISTS carrinho(
                usuario_id INTEGER NOT NULL, produto_id INTEGER NOT NULL,
                quantidade INTEGER NOT NULL, PRIMARY KEY(usuario_id, produto_id)
            );
            CREATE TABLE IF NOT EXISTS produtos(
                id INTEGER PRIMARY KEY, nome TEXT NOT NULL, categoria TEXT,
                preco REAL NOT NULL, estoque INTEGER NOT NULL
            );
            CREATE TABLE IF NOT EXISTS pedidos(
                id INTEGER PRIMARY KEY AUTOINCREMENT, codigo TEXT NOT NULL UNIQUE,
                usuario_id INTEGER NOT NULL, subtotal REAL, frete REAL, frete_nome TEXT,
                desconto_pix REAL, desconto_cupom REAL, cupom TEXT,
                total REAL, pagamento TEXT,
                cep TEXT, rua TEXT, numero TEXT, complemento TEXT, cidade TEXT, estado TEXT,
                status TEXT NOT NULL DEFAULT 'Aguardando pagamento', criado_em TEXT NOT NULL,
                preference_id TEXT, -- NOVO CAMPO
                codigo_rastreio TEXT NOT NULL DEFAULT ''
            );
            CREATE TABLE IF NOT EXISTS pedido_itens(
                pedido_id INTEGER NOT NULL, produto_id INTEGER NOT NULL,
                nome TEXT, preco REAL, quantidade INTEGER
            );
            CREATE TABLE IF NOT EXISTS avaliacoes(
                id INTEGER PRIMARY KEY AUTOINCREMENT, produto_id INTEGER NOT NULL,
                usuario_id INTEGER, nome TEXT NOT NULL, nota INTEGER NOT NULL,
                texto TEXT NOT NULL, data TEXT NOT NULL, criado_em TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS cupons(
                codigo TEXT PRIMARY KEY, tipo TEXT NOT NULL, valor REAL NOT NULL,
                minimo REAL NOT NULL DEFAULT 0, ativo INTEGER NOT NULL DEFAULT 1
            );
        """)
        try:
            c.execute("ALTER TABLE pedidos ADD COLUMN custo_frete_loja REAL DEFAULT 0")
        except Exception:
            pass
        try:
            c.execute("ALTER TABLE pedidos ADD COLUMN preference_id TEXT")
        except Exception:
            pass
        for tabela, coluna, ddl in (
            ("usuarios", "telefone", "TEXT NOT NULL DEFAULT ''"),
            ("usuarios", "cpf", "TEXT NOT NULL DEFAULT ''"),
            ("usuarios", "nascimento", "TEXT NOT NULL DEFAULT ''"),
            ("usuarios", "endereco_json", "TEXT NOT NULL DEFAULT ''"),
            ("pedidos", "codigo_rastreio", "TEXT NOT NULL DEFAULT ''"),
        ):
            cols = _colunas_tabela(c, tabela)
            if cols and coluna not in cols:
                try:
                    c.execute("ALTER TABLE %s ADD COLUMN %s %s" % (tabela, coluna, ddl))
                except Exception:
                    pass
        for cod, tipo, valor, minimo in CUPONS_INICIAIS:
            c.execute("INSERT OR IGNORE INTO cupons(codigo,tipo,valor,minimo) VALUES(?,?,?,?)",
                      (cod, tipo, valor, minimo))
        c.commit()


def produtos_do_index():
    if not os.path.exists(INDEX_FILE):
        return []
    s = open(INDEX_FILE, encoding="utf-8").read()
    achados = {}
    pat = r'^\s*\{ id: (\d+), nome: "([^"]+)", categoria: "([^"]*)", estoque: (\d+), preco: ([\d.]+)'
    for i, nome, cat, est, preco in re.findall(pat, s, re.M):
        achados[int(i)] = (int(i), nome, cat, float(preco), int(est))
    m = re.search(r"const NOVOS_PRODUTOS = (\[.*?\]);\n", s, re.S)
    if m:
        try:
            for p in json.loads(m.group(1)):
                achados[int(p["id"])] = (int(p["id"]), p["nome"], p.get("categoria", ""),
                                         float(p["preco"]), int(p.get("estoque", 0)))
        except Exception as e:
            print("Aviso NOVOS_PRODUTOS:", e)
    g = re.search(r"const ESTOQUE_GOLD = \{(.*?)\};", s, re.S)
    if g:
        for i, q, v in re.findall(r"(\d+):\s*\[\s*(\d+)\s*,\s*([\d.]+)\s*\]", g.group(1)):
            i = int(i)
            if i in achados:
                _, nome, cat, _, _ = achados[i]
                achados[i] = (i, nome, cat, float(v), int(q))
    return list(achados.values())


def sincronizar_produtos():
    prods = produtos_do_index()
    with db_lock, conectar() as c:
        for i, nome, cat, preco, est in prods:
            existe = c.execute("SELECT id FROM produtos WHERE id=?", (i,)).fetchone()
            if existe and os.environ.get("RESETAR_ESTOQUE") == "1":
                c.execute("UPDATE produtos SET nome=?, categoria=?, preco=?, estoque=? WHERE id=?",
                          (nome, cat, preco, est, i))
            elif existe:
                c.execute("UPDATE produtos SET nome=?, categoria=?, preco=? WHERE id=?",
                          (nome, cat, preco, i))
            else:
                c.execute("INSERT INTO produtos(id,nome,categoria,preco,estoque) VALUES(?,?,?,?,?)",
                          (i, nome, cat, preco, est))
        c.commit()
    return len(prods)


class ApiErro(Exception):
    def __init__(self, msg, status=400):
        super().__init__(msg)
        self.msg, self.status = msg, status


def usuario_publico(u):
    return {"id": u["id"], "nome": u["nome"], "email": u["email"]}


def criar_sessao(c, uid):
    if uid is None:
        raise ApiErro("Erro interno: usuário sem ID.", 500)
    try:
        uid = int(uid)
    except (TypeError, ValueError):
        raise ApiErro("Erro interno: ID inválido.", 500)
    token = secrets.token_urlsafe(32)
    exp = (datetime.now() + timedelta(days=SESSAO_DIAS)).strftime("%Y-%m-%d %H:%M:%S")
    c.execute("INSERT INTO sessoes(token,usuario_id,expira_em) VALUES(?,?,?)", (token, uid, exp))
    return token


def usuario_do_token(c, token):
    if not token:
        return None
    return c.execute(
        "SELECT u.* FROM sessoes s JOIN usuarios u ON u.id=s.usuario_id "
        "WHERE s.token=? AND s.expira_em>?", (token, agora())).fetchone()


def validar_cupom(c, codigo, subtotal):
    codigo = (codigo or "").strip().upper()
    if not codigo:
        raise ApiErro("Digite um código de desconto.")
    cp = c.execute("SELECT * FROM cupons WHERE codigo=? AND ativo=1", (codigo,)).fetchone()
    if not cp:
        raise ApiErro("Cupom inválido ou expirado.", 404)
    if subtotal < cp["minimo"]:
        raise ApiErro("Este cupom vale a partir de R$ %.2f." % cp["minimo"])
    desc = subtotal * cp["valor"] / 100 if cp["tipo"] == "percentual" else cp["valor"]
    return cp["codigo"], moeda(min(desc, subtotal))


def montar_itens(c, itens):
    if not isinstance(itens, list) or not itens:
        raise ApiErro("Carrinho vazio.")
    juntos = {}
    for it in itens:
        try:
            pid, q = int(it.get("id")), int(it.get("quantidade", 1))
        except Exception:
            raise ApiErro("Item inválido no carrinho.")
        if q < 1 or q > 99:
            raise ApiErro("Quantidade inválida.")
        juntos[pid] = juntos.get(pid, 0) + q
    lista, subtotal = [], 0.0
    for pid, q in juntos.items():
        p = c.execute("SELECT * FROM produtos WHERE id=?", (pid,)).fetchone()
        if not p:
            raise ApiErro("Produto %s não existe." % pid, 404)
        if p["estoque"] < q:
            raise ApiErro("Estoque insuficiente de “%s” (restam %d)." % (p["nome"], p["estoque"]), 409)
        lista.append({"id": pid, "nome": p["nome"], "preco": p["preco"], "quantidade": q})
        subtotal += p["preco"] * q
    return lista, moeda(subtotal)


def pedido_json(c, p):
    itens = c.execute("SELECT produto_id id, nome, preco, quantidade FROM pedido_itens WHERE pedido_id=?",
                      (p["id"],)).fetchall()
    out_itens = []
    for i in itens:
        try:
            out_itens.append(dict(i))
        except Exception:
            out_itens.append({"id": i[0], "nome": i[1], "preco": i[2], "quantidade": i[3]})
    return {
        "codigo": p["codigo"], "status": p["status"], "criado_em": p["criado_em"],
        "subtotal": p["subtotal"], "frete": p["frete"], "frete_nome": p["frete_nome"],
        "desconto_pix": p["desconto_pix"], "desconto_cupom": p["desconto_cupom"], "cupom": p["cupom"],
        "total": p["total"], "pagamento": p["pagamento"], "codigo_rastreio": p["codigo_rastreio"] or "",
        "endereco": {"cep": p["cep"], "rua": p["rua"], "numero": p["numero"],
                     "complemento": p["complemento"], "cidade": p["cidade"], "estado": p["estado"]},
        "itens": out_itens,
    }


def texto(v, maximo, obrigatorio=True, nome="campo"):
    v = (v or "").strip() if isinstance(v, str) else ""
    if obrigatorio and not v:
        raise ApiErro("Preencha: %s." % nome)
    return v[:maximo]


def cpf_valido(d):
    if len(d) != 11 or d == d[0] * 11:
        return False
    for n in (9, 10):
        soma = sum(int(d[i]) * (n + 1 - i) for i in range(n))
        if int(d[n]) != (soma * 10 % 11) % 10:
            return False
    return True


def fmt_tel(d):
    if len(d) == 11:
        return "(%s) %s-%s" % (d[:2], d[2:7], d[7:])
    if len(d) == 10:
        return "(%s) %s-%s" % (d[:2], d[2:6], d[6:])
    return d


def fmt_cpf(d):
    return "%s.%s.%s-%s" % (d[:3], d[3:6], d[6:9], d[9:]) if len(d) == 11 else d


def perfil_json(u):
    try:
        end = json.loads(u["endereco_json"] or "{}")
    except Exception:
        end = {}
    return {"telefone": u["telefone"] or "", "cpf": u["cpf"] or "",
            "nascimento": u["nascimento"] or "", "endereco": end, "desde": u["criado_em"]}


def devolver_estoque(c, pedido_id):
    for it in c.execute("SELECT produto_id, quantidade FROM pedido_itens WHERE pedido_id=?",
                        (pedido_id,)).fetchall():
        c.execute("UPDATE produtos SET estoque=estoque+? WHERE id=?",
                  (it["quantidade"], it["produto_id"]))


def cancelado(status):
    return (status or "").lower().startswith("cancel")


MESES = ["jan", "fev", "mar", "abr", "mai", "jun", "jul", "ago", "set", "out", "nov", "dez"]


def data_br(d=None):
    d = d or datetime.now()
    return "%02d %s. %d" % (d.day, MESES[d.month - 1], d.year)


# ============================================================
# TEMPO REAL (Server-Sent Events)
# O servidor mantém uma conexão aberta com cada cliente logado e com o painel
# admin, e avisa na hora quando um pedido muda.
# ============================================================
assinantes = {}              # chave (id do usuário ou "admin") -> conjunto de filas
assin_lock = threading.Lock()
_pend = threading.local()


def publicar(uid=None):
    """Avisa o dono do pedido e o painel admin que algo mudou."""
    with assin_lock:
        filas = list(assinantes.get("admin", ()))
        if uid is not None:
            filas += list(assinantes.get(uid, ()))
    for q in filas:
        q.put("pedidos")


def notificar(uid=None):
    """Agenda o aviso para depois do commit no banco (evita ler dado antigo)."""
    if not hasattr(_pend, "lista"):
        _pend.lista = []
    _pend.lista.append(uid)


def _disparar_avisos():
    lista = getattr(_pend, "lista", [])
    _pend.lista = []
    for uid in set(lista):
        publicar(uid)


def rota_api(h, metodo, caminho, corpo):
    partes = [p for p in caminho.split("/") if p][1:]
    rota = partes[0] if partes else ""
    token = None
    auth = h.headers.get("Authorization", "")
    if auth.startswith("Bearer "):
        token = auth[7:].strip()
    if rota == "cep" and metodo == "GET" and len(partes) > 1:
        return _cep(partes[1])
    # Webhook do Mercado Pago (não exige login)
    if rota == "webhook" and metodo == "POST":
        return _webhook_mp(corpo)
    try:
        with db_lock:
            c = conectar()
            try:
                return _rotas(c, h, metodo, rota, partes, corpo, token)
            finally:
                try:
                    c.commit()
                except Exception:
                    pass
                c.close()
    finally:
        _disparar_avisos()


def _cep(valor):
    cep = re.sub(r"\D", "", valor)
    if len(cep) != 8:
        raise ApiErro("CEP inválido.")
    try:
        with urllib.request.urlopen("https://viacep.com.br/ws/%s/json/" % cep, timeout=6) as r:
            d = json.loads(r.read().decode("utf-8"))
    except Exception:
        raise ApiErro("Não consegui consultar o CEP agora. Preencha o endereço manualmente.", 503)
    if d.get("erro"):
        raise ApiErro("CEP não encontrado.", 404)
    return 200, {"rua": d.get("logradouro", ""), "cidade": d.get("localidade", ""),
                 "estado": d.get("uf", ""), "bairro": d.get("bairro", "")}


def exigir_login(c, token):
    u = usuario_do_token(c, token)
    if not u:
        raise ApiErro("Faça login para continuar.", 401)
    return u


def exigir_admin(h):
    t = h.headers.get("X-Admin-Token", "")
    if not t or not hmac.compare_digest(t, ADMIN_TOKEN):
        raise ApiErro("Acesso negado.", 403)


# ============================================================
# MERCADO PAGO - WEBHOOK (confirmação de pagamento)
# ============================================================
def verificar_pagamento_mp(c, ped):
    """Consulta o Mercado Pago pelo código do pedido. Se houver pagamento aprovado,
    muda o status para 'Pagamento aprovado'. Devolve o status atual do pedido."""
    atual = ped["status"] or ""
    if not atual.lower().startswith("aguardando") or not TOKEN_MP:
        return atual
    try:
        import mercadopago
        sdk = mercadopago.SDK(TOKEN_MP)
        ref = "%s|%s" % (ped["usuario_id"], ped["codigo"])
        r = sdk.payment().search({"external_reference": ref, "sort": "date_created", "criteria": "desc"})
        resultados = (r.get("response") or {}).get("results") or []
        if any(x.get("status") == "approved" for x in resultados):
            c.execute("UPDATE pedidos SET status=? WHERE id=?", ("Pagamento aprovado", ped["id"]))
            notificar(ped["usuario_id"])
            return "Pagamento aprovado"
    except Exception as e:
        sys.stderr.write("Erro ao verificar pagamento: %r\n" % (e,))
    return atual


def _webhook_mp(corpo):
    """Recebe a notificação do Mercado Pago e salva o pedido no banco."""
    if not USANDO_MP:
        return 200, {"ok": True}
    
    payment_id = None
    if "data" in corpo and isinstance(corpo["data"], dict):
        payment_id = corpo["data"].get("id")
    
    if not payment_id:
        return 200, {"ok": True}

    try:
        sdk = mercadopago.SDK(TOKEN_MP)
        payment_info = sdk.payment().get(payment_id)
        payment = payment_info.get("response", {})
        
        status = payment.get("status")
        preference_id = payment.get("order", {}).get("id") or payment.get("preference_id")
        external_reference = payment.get("external_reference")
        
        if status in ("approved", "pending", "in_process") and external_reference:
            # external_reference contém o ID do usuário e o código do pedido
            # Formato: "USER_ID|CODIGO_PEDIDO"
            partes = external_reference.split("|")
            if len(partes) == 2:
                uid = int(partes[0])
                codigo = partes[1]
                with db_lock:
                    c = conectar()
                    try:
                        ped = c.execute("SELECT * FROM pedidos WHERE codigo=?", (codigo,)).fetchone()
                        if ped:
                            if (ped["status"] or "").lower().startswith("aguardando") and status == "approved":
                                c.execute("UPDATE pedidos SET status=? WHERE codigo=?", ("Pagamento aprovado", codigo))
                                c.commit()
                                publicar(uid)
                    finally:
                        c.close()
    except Exception as e:
        sys.stderr.write("Erro Webhook MP: %r\n" % (e,))
    
    return 200, {"ok": True}
# ============================================================


def _rotas(c, h, metodo, rota, partes, corpo, token):
    if rota == "saude" and metodo == "GET":
        info = {"ok": True, "hora": agora(), "frete_real": bool(TOKEN_ME),
                "banco": "turso" if USANDO_TURSO else "sqlite_local",
                "turso_url": TURSO_URL or "", "libsql_ok": TURSO_BIBLIOTECA_OK,
                "mercadopago": USANDO_MP}
        try:
            tabelas = c.execute("SELECT name FROM sqlite_master WHERE type='table'").fetchall()
            info["tabelas"] = [t[0] for t in tabelas]
        except Exception as e:
            info["tabelas_erro"] = repr(e)
        return 200, info

    if rota == "frete" and metodo == "POST":
        cep = corpo.get("cep") or ""
        itens = corpo.get("itens") or []
        if not re.sub(r"\D", "", cep):
            raise ApiErro("Informe o CEP para calcular o frete.")
        _, subtotal = montar_itens(c, itens)
        opcoes = calcular_frete_me(cep, itens, subtotal)
        if not opcoes:
            raise ApiErro("Não consegui calcular o frete agora. Confira o CEP e tente de novo.", 503)
        return 200, {"opcoes": opcoes, "cep_origem": CEP_ORIGEM, "subtotal": subtotal}

    # ==================== MERCADO PAGO ====================
    if rota == "pagamento" and metodo == "POST":
        if not TOKEN_MP:
            raise ApiErro("Pagamento via Mercado Pago não configurado.", 503)
        
        import mercadopago
        sdk = mercadopago.SDK(TOKEN_MP)
        
        u = exigir_login(c, token)
        lista, subtotal = montar_itens(c, corpo.get("itens"))
        
        end = corpo.get("endereco") or {}
        cep = re.sub(r"\D", "", end.get("cep") or "")
        frete_chave = corpo.get("frete") or "pac"
        frete_valor = float(corpo.get("frete_valor") or 0)
        frete_nome = corpo.get("frete_nome") or "Frete"
        
        opcoes_me = calcular_frete_me(cep, corpo.get("itens"), subtotal)
        if not opcoes_me:
            raise ApiErro("Erro ao calcular frete.", 503)
        
        escolhida = None
        for o in opcoes_me:
            if o["chave"] == frete_chave or o["nome"] == frete_nome:
                escolhida = o
                break
        if not escolhida:
            raise ApiErro("Escolha uma opção de frete válida.")
        
        frete_valor = escolhida["valor"]
        frete_nome = escolhida["nome"]
        custo_loja = float(escolhida.get("custo_loja") or 0)
        
        pag = corpo.get("pagamento") or ""
        pix = moeda(subtotal * DESCONTO_PIX) if pag.lower().startswith("pix") else 0.0
        cupom_cod, desc_cupom = (None, 0.0)
        if corpo.get("cupom"):
            cupom_cod, desc_cupom = validar_cupom(c, corpo.get("cupom"), subtotal)
        total = moeda(max(subtotal - pix - desc_cupom, 0) + frete_valor)
        
        # Gera um código de pedido provisório
        codigo = None
        for _ in range(20):
            cand = "PD-%06d" % (100000 + secrets.randbelow(900000))
            if not c.execute("SELECT 1 FROM pedidos WHERE codigo=?", (cand,)).fetchone():
                codigo = cand
                break
        
        # Cria o pedido no banco como "Aguardando pagamento" (para ter um ID)
        c.execute(
            "INSERT INTO pedidos(codigo,usuario_id,subtotal,frete,frete_nome,desconto_pix,desconto_cupom,cupom,"
            "total,pagamento,cep,rua,numero,complemento,cidade,estado,criado_em,custo_frete_loja,status) "
            "VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
            (codigo, u["id"], subtotal, frete_valor, frete_nome, pix, desc_cupom,
             cupom_cod, total, pag, "%s-%s" % (cep[:5], cep[5:]), end.get("rua", ""),
             end.get("numero", ""), end.get("complemento", ""), end.get("cidade", ""),
             end.get("estado", ""), agora(), custo_loja, "Aguardando pagamento"))
        
        ped = c.execute("SELECT * FROM pedidos WHERE codigo=?", (codigo,)).fetchone()
        ped_id = ped["id"] if ped else None
        
        if ped_id:
            for it in lista:
                c.execute("INSERT INTO pedido_itens VALUES(?,?,?,?,?)",
                          (ped_id, it["id"], it["nome"], it["preco"], it["quantidade"]))
                c.execute("UPDATE produtos SET estoque=estoque-? WHERE id=?",
                          (it["quantidade"], it["id"]))
        
        # Cria a preferência no Mercado Pago
        # URL pública da loja. Em produção use https (ex.: set BASE_URL=https://sualoja.com.br).
        base_url = (os.environ.get("BASE_URL") or "http://localhost:8000").rstrip("/")
        publico = base_url.startswith("https://")

        preference_data = {
            "items": [{
                "title": f"Pedido {codigo} - Loja Poderosa",
                "quantity": 1,
                "unit_price": float(total),
                "currency_id": "BRL"
            }],
            "payer": {"name": u["nome"], "email": u["email"]},
            "external_reference": f"{u['id']}|{codigo}",
            "back_urls": {
                "success": base_url + "/?pagamento=sucesso",
                "failure": base_url + "/?pagamento=falha",
                "pending": base_url + "/?pagamento=pendente"
            }
        }
        # auto_return e notification_url exigem URL pública (https).
        # Com localhost o Mercado Pago recusa a preferência (erro 400).
        if publico:
            preference_data["auto_return"] = "approved"
            preference_data["notification_url"] = base_url + "/api/webhook"

        def _falhar(msg):
            if ped_id:
                devolver_estoque(c, ped_id)
                c.execute("DELETE FROM pedidos WHERE id=?", (ped_id,))
            raise ApiErro(msg, 500)

        try:
            preference_response = sdk.preference().create(preference_data)
        except Exception as e:
            sys.stderr.write("Erro Mercado Pago (conexão): %r\n" % (e,))
            _falhar("Erro ao comunicar com o Mercado Pago.")

        status_mp = preference_response.get("status")
        preference = preference_response.get("response", {}) or {}
        init_point = preference.get("init_point")
        preference_id = preference.get("id")

        if not init_point:
            # Mostra o motivo real devolvido pelo Mercado Pago
            sys.stderr.write("Erro Mercado Pago: HTTP %s -> %r\n" % (status_mp, preference))
            _falhar("Mercado Pago recusou o pagamento: %s" % (preference.get("message") or "veja o terminal do servidor."))

        c.execute("UPDATE pedidos SET preference_id=? WHERE id=?", (preference_id, ped_id))
        c.execute("DELETE FROM carrinho WHERE usuario_id=?", (u["id"],))
        notificar(u["id"])
        return 200, {"init_point": init_point, "codigo": codigo}
    # ==================== FIM MERCADO PAGO ====================

    if rota == "registrar" and metodo == "POST":
        nome = texto(corpo.get("nome"), 80, nome="nome")
        email = texto(corpo.get("email"), 120, nome="e-mail").lower()
        senha = corpo.get("senha") or ""
        if not EMAIL_RE.match(email):
            raise ApiErro("E-mail inválido.")
        if len(senha) < 4:
            raise ApiErro("A senha precisa ter pelo menos 4 caracteres.")
        if c.execute("SELECT 1 FROM usuarios WHERE email=?", (email,)).fetchone():
            raise ApiErro("E-mail já cadastrado.", 409)
        salt, h_ = hash_senha(senha)
        c.execute("INSERT INTO usuarios(nome,email,salt,senha_hash,criado_em) VALUES(?,?,?,?,?)",
                  (nome, email, salt, h_, agora()))
        u = c.execute("SELECT * FROM usuarios WHERE email=?", (email,)).fetchone()
        if not u:
            raise ApiErro("Erro ao criar conta. Tente novamente.", 500)
        try:
            uid = u["id"]
        except Exception:
            uid = u[0]
        tk = criar_sessao(c, uid)
        return 201, {"token": tk, "usuario": usuario_publico(u)}

    if rota == "login" and metodo == "POST":
        email = (corpo.get("email") or "").strip().lower()
        senha = corpo.get("senha") or ""
        chave = (h.client_address[0], email)
        t = tentativas.get(chave, [])
        t = [x for x in t if time.time() - x < 600]
        if len(t) >= 8:
            raise ApiErro("Muitas tentativas. Aguarde alguns minutos.", 429)
        u = c.execute("SELECT * FROM usuarios WHERE email=?", (email,)).fetchone()
        if not u or not confere_senha(senha, u["salt"], u["senha_hash"]):
            t.append(time.time())
            tentativas[chave] = t
            raise ApiErro("E-mail ou senha inválidos.", 401)
        tentativas.pop(chave, None)
        return 200, {"token": criar_sessao(c, u["id"]), "usuario": usuario_publico(u)}

    if rota == "logout" and metodo == "POST":
        if token:
            c.execute("DELETE FROM sessoes WHERE token=?", (token,))
        return 200, {"ok": True}

    if rota == "me" and metodo == "GET":
        return 200, {"usuario": usuario_publico(exigir_login(c, token))}

    if rota == "senha" and metodo == "PUT":
        u = exigir_login(c, token)
        if not confere_senha(corpo.get("atual") or "", u["salt"], u["senha_hash"]):
            raise ApiErro("Senha atual incorreta.", 403)
        nova = corpo.get("nova") or ""
        if len(nova) < 4:
            raise ApiErro("A nova senha precisa ter pelo menos 4 caracteres.")
        salt, h_ = hash_senha(nova)
        c.execute("UPDATE usuarios SET salt=?, senha_hash=? WHERE id=?", (salt, h_, u["id"]))
        c.execute("DELETE FROM sessoes WHERE usuario_id=? AND token<>?", (u["id"], token))
        return 200, {"ok": True}

    if rota == "perfil":
        u = exigir_login(c, token)
        if metodo == "GET":
            return 200, {"perfil": perfil_json(u)}
        if metodo == "PUT":
            sets, vals = [], []
            if "telefone" in corpo:
                tel = re.sub(r"\D", "", str(corpo.get("telefone") or ""))
                if tel and len(tel) not in (10, 11):
                    raise ApiErro("Telefone inválido. Use DDD + número.")
                sets.append("telefone=?"); vals.append(fmt_tel(tel))
            if "cpf" in corpo:
                cpf = re.sub(r"\D", "", str(corpo.get("cpf") or ""))
                if cpf and not cpf_valido(cpf):
                    raise ApiErro("CPF inválido.")
                sets.append("cpf=?"); vals.append(fmt_cpf(cpf))
            if "nascimento" in corpo:
                nasc = texto(corpo.get("nascimento"), 10, obrigatorio=False)
                if nasc:
                    try:
                        d = datetime.strptime(nasc, "%Y-%m-%d")
                        if d > datetime.now() or d.year < 1900:
                            raise ValueError
                    except ValueError:
                        raise ApiErro("Data de nascimento inválida.")
                sets.append("nascimento=?"); vals.append(nasc)
            if "endereco" in corpo:
                e = corpo.get("endereco") or {}
                if not isinstance(e, dict):
                    raise ApiErro("Endereço inválido.")
                cep = re.sub(r"\D", "", str(e.get("cep") or ""))
                if cep and len(cep) != 8:
                    raise ApiErro("CEP inválido.")
                end = {"cep": "%s-%s" % (cep[:5], cep[5:]) if cep else "",
                       "rua": texto(e.get("rua"), 120, False),
                       "numero": texto(e.get("numero"), 15, False),
                       "cidade": texto(e.get("cidade"), 80, False),
                       "estado": texto(e.get("estado"), 2, False).upper(),
                       "complemento": texto(e.get("complemento"), 80, False)}
                sets.append("endereco_json=?"); vals.append(json.dumps(end, ensure_ascii=False))
            if sets:
                c.execute("UPDATE usuarios SET %s WHERE id=?" % ", ".join(sets), vals + [u["id"]])
            u = c.execute("SELECT * FROM usuarios WHERE id=?", (u["id"],)).fetchone()
            return 200, {"perfil": perfil_json(u)}

    if rota == "produtos" and metodo == "GET":
        rows = c.execute("SELECT id,nome,categoria,preco,estoque FROM produtos ORDER BY id").fetchall()
        out = []
        for r in rows:
            try:
                out.append(dict(r))
            except Exception:
                out.append({"id": r[0], "nome": r[1], "categoria": r[2], "preco": r[3], "estoque": r[4]})
        return 200, {"produtos": out}

    if rota == "favoritos":
        u = exigir_login(c, token)
        if metodo == "GET":
            rows = c.execute("SELECT produto_id FROM favoritos WHERE usuario_id=?", (u["id"],)).fetchall()
            return 200, {"favoritos": [r[0] for r in rows]}
        if metodo == "PUT":
            ids = {int(x) for x in corpo.get("favoritos", []) if str(x).lstrip("-").isdigit()}
            c.execute("DELETE FROM favoritos WHERE usuario_id=?", (u["id"],))
            c.executemany("INSERT INTO favoritos(usuario_id,produto_id) VALUES(?,?)",
                          [(u["id"], i) for i in ids])
            return 200, {"favoritos": sorted(ids)}

    if rota == "carrinho":
        u = exigir_login(c, token)
        if metodo == "GET":
            rows = c.execute(
                "SELECT p.id, p.nome, p.preco, k.quantidade FROM carrinho k "
                "JOIN produtos p ON p.id=k.produto_id WHERE k.usuario_id=?", (u["id"],)).fetchall()
            out = []
            for r in rows:
                try:
                    out.append(dict(r))
                except Exception:
                    out.append({"id": r[0], "nome": r[1], "preco": r[2], "quantidade": r[3]})
            return 200, {"carrinho": out}
        if metodo == "PUT":
            c.execute("DELETE FROM carrinho WHERE usuario_id=?", (u["id"],))
            for it in corpo.get("carrinho", []):
                try:
                    pid, q = int(it["id"]), max(1, min(99, int(it.get("quantidade", 1))))
                except Exception:
                    continue
                if c.execute("SELECT 1 FROM produtos WHERE id=?", (pid,)).fetchone():
                    c.execute("INSERT OR REPLACE INTO carrinho(usuario_id,produto_id,quantidade) VALUES(?,?,?)",
                              (u["id"], pid, q))
            return 200, {"ok": True}

    if rota == "cupom" and metodo == "POST":
        _, subtotal = montar_itens(c, corpo.get("itens"))
        cod, desc = validar_cupom(c, corpo.get("cupom"), subtotal)
        return 200, {"codigo": cod, "desconto": desc, "subtotal": subtotal}

    if rota == "frete" and metodo == "GET":
        return 200, {"gratis_a_partir_de": FRETE_GRATIS_MINIMO,
                     "cep_origem": CEP_ORIGEM, "opcoes": []}

    if rota == "pedidos":
        u = exigir_login(c, token)
        # Conferir se o pagamento foi aprovado: POST /api/pedidos/<codigo>/verificar
        if metodo == "POST" and len(partes) > 2 and partes[2] == "verificar":
            ped = c.execute("SELECT * FROM pedidos WHERE codigo=? AND usuario_id=?",
                            (partes[1], u["id"])).fetchone()
            if not ped:
                raise ApiErro("Pedido não encontrado.", 404)
            return 200, {"status": verificar_pagamento_mp(c, ped)}
        # Retomar pagamento de um pedido "Aguardando pagamento": POST /api/pedidos/<codigo>/pagar
        if metodo == "POST" and len(partes) > 2 and partes[2] == "pagar":
            if not TOKEN_MP:
                raise ApiErro("Pagamento via Mercado Pago não configurado.", 503)
            import mercadopago
            sdk = mercadopago.SDK(TOKEN_MP)
            ped = c.execute("SELECT * FROM pedidos WHERE codigo=? AND usuario_id=?",
                            (partes[1], u["id"])).fetchone()
            if not ped:
                raise ApiErro("Pedido não encontrado.", 404)
            if not (ped["status"] or "").lower().startswith("aguardando"):
                raise ApiErro("Este pedido não está aguardando pagamento.", 409)
            init_point = None
            # 1) tenta reaproveitar o link que já foi gerado
            if ped["preference_id"]:
                try:
                    r = sdk.preference().get(ped["preference_id"])
                    init_point = (r.get("response") or {}).get("init_point")
                except Exception as e:
                    sys.stderr.write("Erro MP (get preference): %r\n" % (e,))
            # 2) se não deu, cria um link novo para o mesmo pedido
            if not init_point:
                base_url = (os.environ.get("BASE_URL") or "http://localhost:8000").rstrip("/")
                pref = {
                    "items": [{"title": "Pedido %s - Loja Poderosa" % ped["codigo"], "quantity": 1,
                               "unit_price": float(ped["total"]), "currency_id": "BRL"}],
                    "payer": {"name": u["nome"], "email": u["email"]},
                    "external_reference": "%s|%s" % (u["id"], ped["codigo"]),
                    "back_urls": {"success": base_url + "/?pagamento=sucesso",
                                  "failure": base_url + "/?pagamento=falha",
                                  "pending": base_url + "/?pagamento=pendente"}
                }
                if base_url.startswith("https://"):
                    pref["auto_return"] = "approved"
                    pref["notification_url"] = base_url + "/api/webhook"
                try:
                    r = sdk.preference().create(pref)
                except Exception as e:
                    sys.stderr.write("Erro MP (create preference): %r\n" % (e,))
                    raise ApiErro("Erro ao comunicar com o Mercado Pago.", 500)
                resp = r.get("response") or {}
                init_point = resp.get("init_point")
                if not init_point:
                    sys.stderr.write("Erro Mercado Pago: HTTP %s -> %r\n" % (r.get("status"), resp))
                    raise ApiErro("Mercado Pago recusou o pagamento: %s" % (resp.get("message") or "veja o terminal."), 500)
                c.execute("UPDATE pedidos SET preference_id=? WHERE id=?", (resp.get("id"), ped["id"]))
            return 200, {"init_point": init_point, "codigo": ped["codigo"]}
        if metodo == "GET":
            rows = c.execute("SELECT * FROM pedidos WHERE usuario_id=? ORDER BY id DESC", (u["id"],)).fetchall()
            return 200, {"pedidos": [pedido_json(c, p) for p in rows]}
        if metodo == "POST":
            lista, subtotal = montar_itens(c, corpo.get("itens"))
            pag = texto(corpo.get("pagamento"), 60, nome="forma de pagamento")
            if not pag.lower().startswith(PAGAMENTOS_OK):
                raise ApiErro("Forma de pagamento inválida.")
            end = corpo.get("endereco") or {}
            cep = re.sub(r"\D", "", end.get("cep") or "")
            if len(cep) != 8:
                raise ApiErro("CEP inválido.")
            rua = texto(end.get("rua"), 120, nome="rua")
            numero = texto(end.get("numero"), 15, nome="número")
            cidade = texto(end.get("cidade"), 80, nome="cidade")
            estado = texto(end.get("estado"), 2, nome="estado").upper()
            comp = texto(end.get("complemento"), 80, obrigatorio=False)

            frete_chave = corpo.get("frete") or "pac"
            frete_valor = float(corpo.get("frete_valor") or 0)
            frete_nome = texto(corpo.get("frete_nome") or "Frete", 60, nome="frete")

            opcoes_me = calcular_frete_me(cep, itens, subtotal)
            if not opcoes_me:
                raise ApiErro("Não consegui calcular o frete agora. Tente de novo em instantes.", 503)
            escolhida = None
            for o in opcoes_me:
                if o["chave"] == frete_chave or o["nome"] == frete_nome:
                    escolhida = o
                    break
            if not escolhida:
                raise ApiErro("Escolha uma opção de frete válida.")
            frete_valor = escolhida["valor"]
            frete_nome = escolhida["nome"]
            custo_loja = float(escolhida.get("custo_loja") or 0)

            pix = moeda(subtotal * DESCONTO_PIX) if pag.lower().startswith("pix") else 0.0
            cupom_cod, desc_cupom = (None, 0.0)
            if corpo.get("cupom"):
                cupom_cod, desc_cupom = validar_cupom(c, corpo.get("cupom"), subtotal)
            total = moeda(max(subtotal - pix - desc_cupom, 0) + frete_valor)

            codigo = None
            for _ in range(20):
                cand = "PD-%06d" % (100000 + secrets.randbelow(900000))
                if not c.execute("SELECT 1 FROM pedidos WHERE codigo=?", (cand,)).fetchone():
                    codigo = cand
                    break
            c.execute(
                "INSERT INTO pedidos(codigo,usuario_id,subtotal,frete,frete_nome,desconto_pix,desconto_cupom,cupom,"
                "total,pagamento,cep,rua,numero,complemento,cidade,estado,criado_em,custo_frete_loja) "
                "VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                (codigo, u["id"], subtotal, frete_valor, frete_nome, pix, desc_cupom,
                 cupom_cod, total, pag, "%s-%s" % (cep[:5], cep[5:]), rua, numero, comp,
                 cidade, estado, agora(), custo_loja))
            p = c.execute("SELECT * FROM pedidos WHERE codigo=?", (codigo,)).fetchone()
            if p:
                try:
                    pid = p["id"]
                except Exception:
                    pid = p[0]
            else:
                pid = None
            if pid:
                for it in lista:
                    c.execute("INSERT INTO pedido_itens VALUES(?,?,?,?,?)",
                              (pid, it["id"], it["nome"], it["preco"], it["quantidade"]))
                    c.execute("UPDATE produtos SET estoque=estoque-? WHERE id=?",
                              (it["quantidade"], it["id"]))
            c.execute("DELETE FROM carrinho WHERE usuario_id=?", (u["id"],))
            p = c.execute("SELECT * FROM pedidos WHERE codigo=?", (codigo,)).fetchone()
            notificar(u["id"])
            return 201, {"pedido": pedido_json(c, p)}

    if rota == "avaliacoes" and len(partes) > 1 and partes[1].isdigit():
        pid = int(partes[1])
        if metodo == "GET":
            rows = c.execute("SELECT nome n, data d, nota s, texto t FROM avaliacoes "
                             "WHERE produto_id=? ORDER BY id DESC", (pid,)).fetchall()
            out = []
            for r in rows:
                try:
                    out.append(dict(r))
                except Exception:
                    out.append({"n": r[0], "d": r[1], "s": r[2], "t": r[3]})
            return 200, {"avaliacoes": out}
        if metodo == "POST":
            if not c.execute("SELECT 1 FROM produtos WHERE id=?", (pid,)).fetchone():
                raise ApiErro("Produto não existe.", 404)
            u = usuario_do_token(c, token)
            nome = texto(corpo.get("nome") or (u["nome"] if u else ""), 60, nome="nome")
            txt = texto(corpo.get("texto"), 1000, nome="comentário")
            try:
                nota = int(corpo.get("nota", 5))
            except Exception:
                nota = 5
            nota = max(1, min(5, nota))
            c.execute("INSERT INTO avaliacoes(produto_id,usuario_id,nome,nota,texto,data,criado_em) "
                      "VALUES(?,?,?,?,?,?,?)",
                      (pid, u["id"] if u else None, nome, nota, txt, data_br(), agora()))
            return 201, {"avaliacao": {"n": nome, "d": data_br(), "s": nota, "t": txt}}

    if rota == "admin":
        exigir_admin(h)
        sub = partes[1] if len(partes) > 1 else ""
        if sub == "pedidos" and metodo == "GET":
            rows = c.execute("SELECT p.*, u.nome cliente, u.email, u.telefone FROM pedidos p "
                             "JOIN usuarios u ON u.id=p.usuario_id ORDER BY p.id DESC").fetchall()
            out = []
            for p in rows:
                j = pedido_json(c, p)
                try:
                    j["cliente"], j["email"] = p["cliente"], p["email"]
                    j["telefone"] = p["telefone"] or ""
                except Exception:
                    pass
                out.append(j)
            return 200, {"pedidos": out}
        if sub == "pedidos" and metodo == "POST" and len(partes) > 3 and partes[3] == "verificar":
            ped = c.execute("SELECT * FROM pedidos WHERE codigo=?", (partes[2],)).fetchone()
            if not ped:
                raise ApiErro("Pedido não encontrado.", 404)
            return 200, {"status": verificar_pagamento_mp(c, ped)}
        if sub == "pedidos" and metodo == "PUT" and len(partes) > 2:
            ped = c.execute("SELECT * FROM pedidos WHERE codigo=?", (partes[2],)).fetchone()
            if not ped:
                raise ApiErro("Pedido não encontrado.", 404)
            status = texto(corpo.get("status") or ped["status"], 40, nome="status")
            rastreio = (texto(corpo.get("rastreio"), 40, obrigatorio=False)
                        if "rastreio" in corpo else ped["codigo_rastreio"])
            if cancelado(status) and not cancelado(ped["status"]):
                devolver_estoque(c, ped["id"])
            c.execute("UPDATE pedidos SET status=?, codigo_rastreio=? WHERE id=?",
                      (status, rastreio, ped["id"]))
            notificar(ped["usuario_id"])
            return 200, {"ok": True}
        if sub == "estoque" and metodo == "PUT" and len(partes) > 2 and partes[2].isdigit():
            try:
                novo = max(0, int(corpo.get("estoque", 0)))
            except (TypeError, ValueError):
                raise ApiErro("Estoque inválido.")
            c.execute("UPDATE produtos SET estoque=? WHERE id=?", (novo, int(partes[2])))
            return 200, {"ok": True}
        if sub == "cupons" and metodo == "GET":
            rows = c.execute("SELECT * FROM cupons").fetchall()
            out = []
            for r in rows:
                try:
                    out.append(dict(r))
                except Exception:
                    out.append({"codigo": r[0], "tipo": r[1], "valor": r[2],
                                "minimo": r[3], "ativo": r[4]})
            return 200, {"cupons": out}
        if sub == "cupons" and metodo == "POST":
            cod = texto(corpo.get("codigo"), 30, nome="código").upper()
            tipo = corpo.get("tipo") if corpo.get("tipo") in ("percentual", "fixo") else "percentual"
            c.execute("INSERT OR REPLACE INTO cupons(codigo,tipo,valor,minimo,ativo) VALUES(?,?,?,?,?)",
                      (cod, tipo, float(corpo.get("valor", 0)),
                       float(corpo.get("minimo", 0)), 1 if corpo.get("ativo", True) else 0))
            return 201, {"ok": True}
        if sub == "usuarios" and metodo == "GET":
            rows = c.execute("SELECT id,nome,email,criado_em FROM usuarios ORDER BY id DESC").fetchall()
            out = []
            for r in rows:
                try:
                    out.append(dict(r))
                except Exception:
                    out.append({"id": r[0], "nome": r[1], "email": r[2], "criado_em": r[3]})
            return 200, {"usuarios": out}

    raise ApiErro("Rota não encontrada.", 404)


EXT_PERMITIDAS = {".jpg", ".jpeg", ".png", ".webp", ".gif", ".svg", ".ico",
                  ".avif", ".jfif", ".css", ".js", ".woff", ".woff2"}
PASTAS_BUSCA = ("static/images", "images", "static/img", "img", "static", "assets", ".")
EXT_IMAGEM = {".jpg", ".jpeg", ".png", ".webp", ".gif", ".svg", ".ico", ".avif", ".jfif"}


def achar_imagem(nome):
    base, ext = os.path.splitext(nome)
    if ext.lower() not in EXT_IMAGEM:
        return None
    for raiz in (BASE_DIR, os.path.dirname(BASE_DIR)):
        for pasta in PASTAS_BUSCA:
            d = os.path.join(raiz, pasta)
            try:
                arquivos = os.listdir(d)
            except OSError:
                continue
            for f in arquivos:
                if f.lower() == nome.lower() and os.path.isfile(os.path.join(d, f)):
                    return os.path.join(d, f)
            for f in arquivos:
                b, e = os.path.splitext(f)
                if b.lower() == base.lower() and e.lower() in EXT_IMAGEM and os.path.isfile(os.path.join(d, f)):
                    return os.path.join(d, f)
    return None


def avisar_logos_faltando():
    esperados = ["gold-logo", "goldspell-logo", "everk-logo", "extremegold-logo"]
    faltam = [b + ".jpg" for b in esperados if not achar_imagem(b + ".jpg")]
    if faltam:
        print(" ATENÇÃO: logos não encontradas:")
        for f in faltam:
            print("    -", f)


class Handler(BaseHTTPRequestHandler):
    server_version = "PoderosaServer/5.0"

    def log_message(self, fmt, *args):
        sys.stderr.write("[%s] %s\n" % (datetime.now().strftime("%H:%M:%S"), fmt % args))

    def _cabecalhos(self, tipo, tamanho, extra=None):
        self.send_header("Content-Type", tipo)
        self.send_header("Content-Length", str(tamanho))
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Referrer-Policy", "same-origin")
        for k, v in (extra or {}).items():
            self.send_header(k, v)

    def _json(self, status, dados):
        b = json.dumps(dados, ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self._cabecalhos("application/json; charset=utf-8", len(b), {"Cache-Control": "no-store"})
        self.end_headers()
        if self.command != "HEAD":
            self.wfile.write(b)

    def _arquivo(self, caminho):
        try:
            with open(caminho, "rb") as f:
                dados = f.read()
        except OSError:
            self.send_error(404, "Arquivo não encontrado")
            return
        tipo = mimetypes.guess_type(caminho)[0] or "application/octet-stream"
        if tipo.startswith("text/") or tipo in ("application/javascript", "application/json"):
            tipo += "; charset=utf-8"
        cache = "no-cache" if caminho.endswith(".html") else "public, max-age=3600"
        self.send_response(200)
        self._cabecalhos(tipo, len(dados), {"Cache-Control": cache})
        self.end_headers()
        if self.command != "HEAD":
            self.wfile.write(dados)

    def _estatico(self, caminho_url):
        rel = unquote(caminho_url).lstrip("/")
        if rel in ("", "index.html"):
            return self._arquivo(INDEX_FILE)
        if rel == "produtos" or rel.startswith("produtos/"):
            return self._arquivo(INDEX_FILE)   # página de produto: /produtos/<nome>
        if rel.rstrip("/") == "admin":
            return self._arquivo(os.path.join(BASE_DIR, "admin.html"))
        alvo = os.path.realpath(os.path.join(BASE_DIR, rel))
        if not os.path.normcase(alvo).startswith(os.path.normcase(BASE_DIR + os.sep)):
            return self.send_error(403)
        if os.path.splitext(alvo)[1].lower() not in EXT_PERMITIDAS:
            return self.send_error(404)
        if os.path.isfile(alvo):
            return self._arquivo(alvo)
        achado = achar_imagem(os.path.basename(alvo))
        if achado:
            return self._arquivo(achado)
        self.send_error(404, "Arquivo não encontrado")

    def _eventos(self):
        """Conexão em tempo real (SSE). Autenticação por cabeçalho, nunca pela URL."""
        at = self.headers.get("X-Admin-Token", "")
        auth = self.headers.get("Authorization", "")
        token = auth[7:].strip() if auth.startswith("Bearer ") else None
        if at:
            if not hmac.compare_digest(at, ADMIN_TOKEN):
                return self._json(403, {"erro": "Acesso negado."})
            chave = "admin"
        else:
            u = None
            if token:
                with db_lock:
                    c = conectar()
                    try:
                        u = usuario_do_token(c, token)
                    finally:
                        c.close()
            if not u:
                return self._json(401, {"erro": "Faça login para continuar."})
            chave = u["id"]
        fila = queue.Queue()
        with assin_lock:
            assinantes.setdefault(chave, set()).add(fila)
        self.close_connection = True
        try:
            self.send_response(200)
            self.send_header("Content-Type", "text/event-stream; charset=utf-8")
            self.send_header("Cache-Control", "no-cache")
            self.send_header("X-Accel-Buffering", "no")
            self.end_headers()
            self.wfile.write(b"retry: 3000\n: conectado\n\n")
            self.wfile.flush()
            while True:
                try:
                    ev = fila.get(timeout=15)
                    self.wfile.write(("event: %s\ndata: {}\n\n" % ev).encode("utf-8"))
                except queue.Empty:
                    self.wfile.write(b": ping\n\n")
                self.wfile.flush()
        except (OSError, ValueError):
            pass
        finally:
            with assin_lock:
                conj = assinantes.get(chave)
                if conj is not None:
                    conj.discard(fila)
                    if not conj:
                        assinantes.pop(chave, None)

    def _tratar(self, metodo):
        url = urlparse(self.path)
        if metodo == "GET" and url.path == "/api/eventos":
            return self._eventos()
        if not url.path.startswith("/api/"):
            if metodo in ("GET", "HEAD"):
                return self._estatico(url.path)
            return self.send_error(405)
        corpo = {}
        if metodo in ("POST", "PUT", "PATCH"):
            try:
                n = int(self.headers.get("Content-Length") or 0)
                if n > 1_000_000:
                    return self._json(413, {"erro": "Requisição grande demais."})
                bruto = self.rfile.read(n) if n else b"{}"
                corpo = json.loads(bruto.decode("utf-8") or "{}")
                if not isinstance(corpo, dict):
                    raise ValueError
            except Exception:
                return self._json(400, {"erro": "JSON inválido."})
        try:
            status, dados = rota_api(self, "PUT" if metodo == "PATCH" else metodo, url.path, corpo)
        except ApiErro as e:
            return self._json(e.status, {"erro": e.msg})
        except Exception as e:
            sys.stderr.write("ERRO: %r\n" % (e,))
            return self._json(500, {"erro": "Erro interno do servidor."})
        self._json(status, dados)

    def do_GET(self): self._tratar("GET")
    def do_HEAD(self): self._tratar("HEAD")
    def do_POST(self): self._tratar("POST")
    def do_PUT(self): self._tratar("PUT")
    def do_PATCH(self): self._tratar("PATCH")


def carregar_admin_token():
    t = os.environ.get("ADMIN_TOKEN")
    if t:
        return t
    if os.path.exists(ADMIN_FILE):
        return open(ADMIN_FILE).read().strip()
    t = secrets.token_urlsafe(18)
    with open(ADMIN_FILE, "w") as f:
        f.write(t)
    try:
        os.chmod(ADMIN_FILE, 0o600)
    except OSError:
        pass
    return t


ADMIN_TOKEN = carregar_admin_token()


class ServidorLoja(ThreadingHTTPServer):
    """Igual ao servidor padrão, mas não despeja erro no terminal quando o navegador
    fecha a conexão no meio da resposta (acontece ao apertar F5 várias vezes)."""
    daemon_threads = True

    def handle_error(self, request, client_address):
        exc = sys.exc_info()[1]
        if isinstance(exc, (ConnectionAbortedError, ConnectionResetError, BrokenPipeError)):
            return
        super().handle_error(request, client_address)


def main():
    if not os.path.exists(INDEX_FILE):
        print("ATENÇÃO: index.html não encontrado em", BASE_DIR)
    criar_banco()
    n = sincronizar_produtos()
    with db_lock, conectar() as c:
        c.execute("DELETE FROM sessoes WHERE expira_em<=?", (agora(),))
        c.commit()
    srv = ServidorLoja((HOST, PORT), Handler)
    print("=" * 60)
    print(" Loja PODEROSA rodando!  (%d produtos carregados)" % n)
    print(" Abra:  http://localhost:%d" % PORT)
    if USANDO_TURSO:
        print(" Banco: TURSO (nuvem) -> %s" % TURSO_URL)
    else:
        print(" Banco: SQLite local -> %s" % DB_PATH)
    print(" CEP de origem (frete): %s" % CEP_ORIGEM)
    if TOKEN_ME:
        print(" Melhor Envio: TOKEN CARREGADO (frete REAL ativo)")
    else:
        print(" Melhor Envio: token nao encontrado")
    if USANDO_MP:
        print(" Mercado Pago: TOKEN CARREGADO (pagamento REAL ativo)")
    else:
        print(" Mercado Pago: token nao encontrado (pagamento desativado)")
    print(" Painel admin: http://localhost:%d/admin" % PORT)
    print(" Admin token: %s" % ADMIN_TOKEN)
    print("=" * 60)
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        print("\nEncerrando...")
    finally:
        srv.server_close()


if __name__ == "__main__":
    main()