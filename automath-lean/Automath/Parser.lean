import Std.Internal.Parsec

open Std.Internal.Parsec String

namespace Automath
namespace AST

inductive Namespace where
  | current
  | super (s : String)
  | sub (parent : Namespace) (s : String)
  deriving Repr

def Namespace.toString : Namespace → String
  | .current => ""
  | .super s => s
  | .sub p x => p.toString ++ "." ++ x

instance : ToString Namespace where toString n := n.toString
instance : Repr Namespace where reprPrec n _ := n.toString

inductive Symbol where
  | simple (s : String)
  | ns (s : String) (ns : Namespace)
  deriving Repr

instance : ToString Symbol where
  toString
  | .simple s => s
  | .ns s p => s!"{s}.{p}"

instance : Repr Symbol where reprPrec n _ := toString n

inductive Expr where
  | type
  | prop
  | id (s : Symbol)
  | papp (fn arg : Expr)
  | app (fn arg : Expr)
  | lam (x : String) (ty : Expr) (body : Expr)

mutual
partial def Expr.reprPrec : Expr → Nat → Std.Format
  | .type, _ => "TYPE"
  | .prop, _ => "PROP"
  | .id s, _ => repr s
  | .lam x ty body, _ => f!"λ{x}:{ty.reprPrec 0} ↦ {body.reprPrec 0}"
  | .papp fn arg, _ => Expr.reprApp fn [arg]
  | .app e1 e2, n =>
    let f := f!"{e1.reprPrec 0} {e2.reprPrec 1}"
    if n > 0 then f!"({f})" else f

partial def Expr.reprApp : Expr → List Expr → Std.Format
  | .papp fn arg, es => fn.reprApp (arg :: es)
  | e, [] => Expr.reprPrec e 0
  | e, es => Expr.reprPrec e 0 ++ f!"[{f!", ".joinSep (es.map (·.reprPrec 0))}]"
end

instance : Repr Expr where reprPrec := Expr.reprPrec

inductive Item where
  | comment
  | openSection (s : String)
  | reopenSection (s : String)
  | closeSection (s : String)
  | setContext (p : Option Symbol)
  | parameter (name : String) (ty : Expr)
  | def_ (id : String) (ty : Expr) (v : Option Expr)
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
    pure (.def_ id ty val))

def items : Parser (Array Item) := many (item <* ws)
