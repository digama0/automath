import Automath
import Lean

namespace Automath

deriving instance Lean.ToExpr for AST.Namespace
deriving instance Lean.ToExpr for AST.Symbol
deriving instance Lean.ToExpr for AST.Expr
deriving instance Lean.ToExpr for AST.Item

def grundlagen := by_elab
  let e :=
    match Parser.items.run (include_str "../aut-4.2/grundlagen.aut") with
    | .ok e => e.take 100
    | .error _ => #[]
  return Lean.toExpr e

def findAssoc (l : List (String × α)) (x : String) : Option α :=
  l.find? (·.1 == x) |>.map (·.2)

inductive Expr where
  | univ (isType : Bool)
  | var (i : Nat)
  | const (n : String) (ns : List String)
  | papp (fn arg : Expr)
  -- | app (fn arg : Expr)
  | lam (deg : Nat) (ty : Expr) (body : Expr)
  deriving Repr

instance : ToString Expr where
  toString e := toString (repr e)

structure LocalDecl where
  name : String
  id : Nat
  degree : Nat
  type : Expr
  deriving Repr

abbrev LocalCtx := List LocalDecl

def Expr.lift : Expr → Nat → Nat → Expr
  | e@(.univ _), _, _
  | e@(.const ..), _, _ => e
  | .lam d ty e, n, k => .lam d (ty.lift n k) (e.lift n (k+1))
  | .papp e1 e2, n, k => .papp (e1.lift n k) (e2.lift n k)
  | .var i, n, k => .var (if i < k then i else i + n)

def Expr.principalType (ctx : LocalCtx) : Expr → Option Expr
  | .univ _ => none
  | .lam d ty e => return .lam d ty (← e.principalType (⟨"", 0, d, ty⟩ :: ctx))
  | .var i => ctx[i]?.map (·.type.lift (i+1) 0)
  | .const ..
  | .papp .. => panic! "TODO"
  -- | _ => 0

structure Definition where
  ctx : LocalCtx
  degree : Nat
  type : Expr
  val : Option Expr
  deriving Repr

structure Namespace where
  ctx : LocalCtx := []
  children : List (String × Namespace) := []
  params : List (String × LocalCtx) := []
  defs : List (String × Definition) := []
  deriving Repr

structure Environment where
  stack : List (String × Namespace) := []
  ns : Namespace := {}
  deriving Repr

structure State where
  env : Environment := {}
  ngen : Nat := 1
  deriving Repr

abbrev M := StateT State (Except String)

def nextId : M Nat :=
  fun s => .ok (s.ngen, {s with ngen := s.ngen + 1})

def findSuper (stack : List (String × Namespace)) (ns : Namespace) (x : String) :
    Except String (List (String × Namespace) × Namespace) :=
  match stack with
  | [] => throw s!"unknown namespace {x}"
  | (a,ns')::stack' =>
    if a = x then pure (stack, ns) else findSuper stack' ns' x

def findNS (stack : List (String × Namespace)) (ns : Namespace) :
    AST.Namespace → Except String (List (String × Namespace) × Namespace)
  | .current => return (stack, ns)
  | .sub p x => do
    let (stack', ns') ← findNS stack ns p
    let .some ns'' := findAssoc ns'.children x | throw s!"unknown namespace {x}"
    pure ((x, ns) :: stack', ns'')
  | .super x => findSuper stack ns x

def findSimpleParam (stack : List (String × Namespace)) (ns : Namespace) (x : String) :
    Option LocalCtx :=
  match findAssoc ns.params x with
  | some ctx => pure ctx
  | none =>
    match stack with
    | [] => none
    | (_, ns) :: stack => findSimpleParam stack ns x

def findSimpleDef (stack : List (String × Namespace)) (ns : Namespace) (x : String) :
    Option (List (String × Namespace) × Definition) :=
  match findAssoc ns.defs x with
  | some d => pure (stack, d)
  | none =>
    match stack with
    | [] => none
    | (_, ns) :: stack => findSimpleDef stack ns x

def findSymbol (stack : List (String × Namespace)) (ns : Namespace) :
    AST.Symbol → Except String (LocalCtx ⊕ (String × List (String × Namespace) × Definition))
  | .simple x =>
    match findSimpleParam stack ns x with
    | some ns => .ok (.inl ns)
    | none =>
      match findSimpleDef stack ns x with
      | some d => .ok (.inr (x, d))
      | none => throw s!"unknown symbol {x}"
  | .ns x p => do
    let (stack', ns') ← findNS stack ns p
    match findAssoc ns'.params x with
    | some ctx => pure (.inl ctx)
    | none =>
      match findAssoc ns'.defs x with
      | some d => pure (.inr (x, stack', d))
      | none => throw s!"unknown symbol {x}"

def matchContext (ctx : LocalCtx) : LocalCtx → Option Nat
  | [] => pure ctx.length
  | {id, ..} :: _ => ctx.findIdx? (·.id == id)

def isSubtype (e1 e2 : Expr) : Bool :=
  match e1, e2 with
  | .univ t1, .univ t2 => t1 == t2
  | .var i, .var j => i == j
  | .lam d1 t1 e1, .lam d2 t2 e2 =>
    d1 == d2 && isSubtype t1 t2 && isSubtype e1 e2
  | .lam _ _ e1, .univ t2 => isSubtype e1 (.univ t2)
  | _, _ => false

def assertSubtype (e1 e2 : Expr) : Except String Unit :=
  if isSubtype e1 e2 then pure () else
    throw s!"{e1} <: {e2} failed"

def ensureType (env : Environment) (e ty : Expr) : Except String Unit := do
  let .some ety := e.principalType env.ns.ctx | throw s!"ensureType: value {e} has no type"
  assertSubtype ety ty

structure Typecheck where
  val : Expr
  type : Option Expr
  degree : Nat

structure ApplyDef where
  val : Expr
  lift : Nat

def applyDef (ctx : LocalCtx) (name : String) (stack : List (String × Namespace)) (d : Definition)
    (revArgs : List Typecheck) : M Typecheck := do
  -- unless d.ctx.length ≥ revArgs.length do throw "too many arguments"
  -- let some n := matchContext ctx (d.ctx.drop args.length) | throw "incompatible context"
  let { val, lift } ← loop d.ctx revArgs
  pure { val, type := d.type.lift lift 0, degree := d.degree }
where
  loop (dctx : LocalCtx) (revArgs : List Typecheck) : M ApplyDef := do
    match revArgs with
    | [] =>
      let some n := matchContext ctx dctx | throw "incompatible context"
      pure { val := .const name (stack.map (·.1)), lift := n }
    | { val := a, type := aty, .. } :: rest =>
      let d :: dctx := dctx | throw "too many arguments"
      let { val, lift } ← loop dctx rest
      let .some aty := aty | throw s!"ensureType: value {a} has no type"
      assertSubtype aty d.type
      return { val := .papp val a, lift }

mutual
def typecheck (ctx : LocalCtx) : AST.Expr → M Typecheck
  | .type => pure { val := .univ true, type := none, degree := 1 }
  | .prop => pure { val := .univ false, type := none, degree := 1 }
  | .lam name ty e => do
    let {val := ty, degree, ..} ← typecheck ctx ty
    let {val := e', degree := d, type} ← typecheck ({ name, id := ← nextId, degree, type := ty } :: ctx) e
    return {val := .lam degree ty e', type := .lam degree ty <$> type, degree := d}
  | .id x => do
    let s ← get
    match ← findSymbol s.env.stack s.env.ns x with
    | .inl xctx =>
      let d :: _ := xctx | throw "unreachable"
      let some n := matchContext ctx xctx | throw "incompatible context"
      return {val := .var n, type := d.type.lift (n+1) 0, degree := d.degree + 1}
    | .inr (x, stack, d) => applyDef ctx x stack d []
  | e@(.papp ..) => typecheckCall ctx e []
  | e => throw s!"typecheck {repr e}"
termination_by e => 2 * sizeOf e + 1

def typecheckCall (ctx : LocalCtx) : AST.Expr → List Typecheck → M Typecheck
  | .papp e1 e2, acc => do typecheckCall ctx e1 ((← typecheck ctx e2) :: acc)
  | .id x, acc => do
    let s ← get
    let .inr (x, stack', d) ← findSymbol s.env.stack s.env.ns x
      | throw "variables cannot have arguments"
    applyDef ctx x stack' d acc
  | _, _ => throw s!"invalid application"
termination_by e => 2 * sizeOf e
end

def typecheck' (e : AST.Expr) : M Typecheck := do
  typecheck (← get).env.ns.ctx e

def ensureType' (e ty : Expr) : M Unit := do
  ensureType (← get).env e ty

def processItem : AST.Item → M Unit
  | .comment => pure ()
  | .openSection n =>
    modify fun s => { s with env.stack := (n, s.env.ns) :: s.env.stack }
  | .reopenSection _ => throw "processItem reopenSection"
  | .closeSection _ => throw "processItem closeSection"
  | .setContext none =>
    modify ({· with env.ns.ctx := []})
  | .setContext (some _) => throw "processItem setContext"
  | .parameter x ty => do
    let {val := ty, degree := deg, ..} ← typecheck' ty
    let ctx := (← get).env.ns.ctx
    unless 1 ≤ deg ∧ deg ≤ 2 do throw "bad parameter degree"
    let n ← nextId
    modify fun s =>
      let ctx' := { name := x, id := n, degree := deg, type := ty } :: ctx
      { s with env.ns.ctx := ctx', env.ns.params := (x, ctx') :: s.env.ns.params }
  | .axiom_ _ _ => throw "processItem axiom_"
  | .def_ x ty val => do
    let {val := ty', degree := deg, ..} ← typecheck' ty
    let ctx := (← get).env.ns.ctx
    unless 1 ≤ deg ∧ deg ≤ 2 do throw "bad parameter degree"
    let {val := val', ..} ← typecheck' val
    ensureType' val' ty'
    let defn := {ctx, type := ty', val := some val', degree := deg}
    modify fun s => { s with env.ns.defs := (x, defn) :: s.env.ns.defs }

instance : MonadLift M (StateT State IO) where
  monadLift m s :=
    match m s with
    | .ok (s, a) => pure (s, a)
    | .error e => throw <| .userError e

def main : IO Unit := do
  -- let grundlagen ← IO.FS.readFile "../aut-4.2/grundlagen.aut"
  -- let items ← match items.run grundlagen with
  --   | .ok e => pure e
  --   | .error e => throw (.userError e)
  let (_, _s) ← StateT.run (s := ({} : State)) do
    for it in grundlagen do
      -- monadLift $ IO.println $ repr ((← get), it)
      processItem it

-- #eval main
