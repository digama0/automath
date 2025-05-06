import Std.Internal.Parsec

open Std.Internal.Parsec String

namespace Automath
namespace AST

inductive Namespace where
  | current
  | super (s : String)
  | sub (parent : Namespace) (s : String)
  deriving Repr

inductive Symbol where
  | simple (s : String)
  | ns (s : String) (ns : Namespace)
  deriving Repr

inductive Expr where
  | type
  | prop
  | id (s : Symbol)
  | papp (fn arg : Expr)
  | app (fn arg : Expr)
  | lam (x : String) (ty : Expr) (body : Expr)
  deriving Repr

inductive Item where
  | comment
  | openSection (s : String)
  | reopenSection (s : String)
  | closeSection (s : String)
  | setContext (p : Option Symbol)
  | parameter (name : String) (ty : Expr)
  | axiom_ (id : String) (ty : Expr)
  | def_ (id : String) (ty : Expr) (v : Expr)
  deriving Repr

end AST

namespace Parser
open AST

def charsWhile (p : Char → Bool) : Parser String :=
  many1Chars <| attempt do
    let c ← any; guard (p c); return c

def ident : Parser String := attempt <| charsWhile fun c =>
  ('0' ≤ c ∧ c ≤ '9') ∨ ('a' ≤ c ∧ c ≤ 'z') ∨ ('A' ≤ c ∧ c ≤ 'Z') ∨
    c matches '_' | '\u0008' | '`' | '\''

def ns : Parser Namespace := do
  let id := match ← optional ident with
    | none => .current
    | some s => .super s
  return (← many (pchar '.' *> ident)).foldl (·.sub) id

def symbol : Parser Symbol := attempt do
  let id ← ident
  match ← optional (pchar '"' *> ns <* pchar '"') with
  | none => return .simple id
  | some ns => return .ns id ns

partial def expr : Parser Expr :=
  pstring "'type'" *> pure .type <|>
  pstring "'prop'" *> pure .prop <|>
  pchar '<' *> (flip .app <$> expr <*> (pchar '>' *> expr)) <|>
  pchar '[' *> (.lam <$> ident <*> (pchar ':' *> expr <* pchar ']') <*> expr) <|>
  (do
    let s ← symbol
    let args ← optional (pchar '(' *>
      Prod.mk <$> expr <*> many (pchar ',' *> expr) <* pchar ')')
    match args with
    | none => pure (.id s)
    | some (e1, args) => pure <| args.foldl (·.papp) (.papp (.id s) e1))

def item : Parser Item :=
  (pchar '%' *> charsWhile (· ≠ '\n') *> pure .comment) <|>
  pchar '+' *> (
    (fun | none => .openSection | some _ => .reopenSection)
      <$> optional (pchar '*') <*> ident) <|>
  pchar '-' *> (.closeSection <$> ident) <|>
  (pchar '@' *> pure (.setContext none)) <|>
  (.setContext ∘ some) <$> attempt (symbol <* pchar '@') <|>
  (.parameter <$> (pchar '[' *> ident) <*>
    (pchar ':' *> expr <* pchar ']')) <|>
  (do
    let id ← ident
    _ ← pstring ":="
    let val ← pstring "'prim'" *> pure none <|> (some <$> expr)
    let ty ← pchar ':' *> expr
    match val with
    | none => pure (.axiom_ id ty)
    | some v => pure (.def_ id ty v))

def items : Parser (Array Item) := many (item <* ws)
