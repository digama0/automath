import Automath
import Lean

namespace Automath

deriving instance Lean.ToExpr for AST.Namespace
deriving instance Lean.ToExpr for AST.Symbol
deriving instance Lean.ToExpr for AST.Expr
deriving instance Lean.ToExpr for AST.Item

-- def grundlagen := by_elab
--   let e :=
--     match Parser.items.run (include_str "../aut-4.2/grundlagen.aut") with
--     | .ok e => e.take 500
--     | .error _ => #[]
--   return Lean.toExpr e

def findAssoc (l : List (String × α)) (x : String) : Option α :=
  l.find? (·.1 == x) |>.map (·.2)

def popAssoc (l : List (String × α)) (x : String) : Option (α × List (String × α)) :=
  match l with
  | [] => none
  | (a, v) :: l =>
    if a == x then
      some (v, l)
    else do
      let (v', l') ← popAssoc l x
      some (v', (a,v)::l')

inductive Expr where
  | univ (isType : Bool)
  | var (i : Nat)
  | const (n : String) (ns : List String) (seq : Nat) (args : List Expr)
  -- | papp (fn arg : Expr)
  | app (fn arg : Expr) -- arg.degree := 3
  | lam (n : String) (ty : Expr) (body : Expr) -- ty.degree := 2

partial def Expr.reprPrec : Expr → Nat → Std.Format
  | .univ true, _ => "TYPE"
  | .univ false, _ => "PROP"
  | .var i, _ => f!"#{i}"
  | .lam x ty body, _ => f!"λ{x}:{ty.reprPrec 0} ↦ {body.reprPrec 0}"
  | .const n ns _ es, _ =>
    Std.format (String.intercalate "." (ns ++ [n])) ++
    match es with | [] => f!"" | _ => f!"[{f!", ".joinSep (es.map (·.reprPrec 0))}]"
  | .app e1 e2, n =>
    let f := f!"{e1.reprPrec 0} {e2.reprPrec 1}"
    if n > 0 then f!"({f})" else f

instance : Repr Expr where reprPrec := Expr.reprPrec

instance : ToString Expr where
  toString e := toString (repr e)

structure LocalDecl where
  name : String
  id : Nat
  tyDeg : Nat
  type : Expr

instance : Repr LocalDecl where
  reprPrec
  | {name, type, tyDeg, ..}, _ => f!"{name}[{tyDeg+1}]: {repr type}"

abbrev LocalCtx := List LocalDecl

def LocalCtx.repr (ctx : LocalCtx) : Std.Format :=
  f!", ".joinSep (ctx.reverse.map _root_.repr)

def isToken : String → Bool
  | "if" => true
  | "in" => true
  | "class" => true
  | _ => false

def escape1 (x : String) : String := (Lean.Name.mkSimple x).toString (isToken := isToken)

def Expr.toLean (ctx : LocalCtx) : Expr → Bool → Std.Format
  | .univ false, _ => "Prop"
  | .univ true, _ => "Type"
  | .var i, _ => match ctx[i]? with | none => "!" | some d => (Lean.Name.mkSimple d.name).toString (isToken := isToken)
  | .const n ns _ es, _ =>
    let name := (ns ++ [n]).foldl .str Lean.Name.anonymous
    let name := if ctx.any (·.name == "l") then `_root_ ++ name else name
    let e := es.foldl (· ++ f!"{Std.Format.line}{·.toLean ctx false}") f!"{name}"
    f!"({e})".nest 2 |>.group
  | .lam x d b, false =>
    f!"(fun {escape1 x} : \
      {d.toLean ctx true} =>{Std.Format.line}{b.toLean (⟨x, 0, 2, d⟩::ctx) false})".nest 2 |>.group
  | .lam x d b, true =>
    f!"(∀ {escape1 x} : \
      {d.toLean ctx true}, {b.toLean (⟨x, 0, 2, d⟩::ctx) true})".nest 2 |>.group
  | .app f x, _ => f!"({f.toLean ctx false}{Std.Format.line}{x.toLean ctx false})".nest 2 |>.group

def LocalCtx.toLean : LocalCtx → Std.Format
  | [] => ""
  | a :: as => toLean as ++ .line ++ .group f!"({escape1 a.name} : {a.type.toLean as true})"

def Expr.lift : Expr → Nat → Nat → Expr
  | e@(.univ _), _, _ => e
  | .lam x ty e, n, k => .lam x (ty.lift n k) (e.lift n (k+1))
  | .const a ns i es, n, k => .const a ns i (es.map (·.lift n k))
  | .app e1 e2, n, k => .app (e1.lift n k) (e2.lift n k)
  | .var i, n, k => .var (if i < k then i else i + n)

def Expr.subst : Expr → Expr → Nat → Expr
  | e@(.univ _), _, _ => e
  | .lam x ty e, n, k => .lam x (ty.subst n k) (e.subst n (k+1))
  | .const a ns i es, n, k => .const a ns i (es.map (·.subst n k))
  | .app e1 e2, n, k => .app (e1.subst n k) (e2.subst n k)
  | .var i, n, k => if i < k then .var i else if i = k then n.lift k 0 else .var (i - 1)

def Expr.skips : Expr → Nat → Bool
  | .univ _, _ => true
  | .lam _ ty e, k => ty.skips k && e.skips (k+1)
  | .const _ _ _ es, k => allSkips es k
  | .app e1 e2, k => e1.skips k && e2.skips k
  | .var i, k => i != k
where
  allSkips : List Expr → Nat → Bool
  | [], _ => true
  | e :: es, k => e.skips k && allSkips es k

structure Definition where
  ctx : LocalCtx
  seq : Nat
  tyDeg : Nat
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

def Environment.head (env : Environment) : Namespace := toHead env.stack env.ns where
  toHead (stack : List (String × Namespace)) (ns : Namespace) : Namespace :=
    match stack with
    | [] => ns
    | (a, hd) :: stack => toHead stack { hd with children := (a, ns) :: hd.children }

def Namespace.findNS (ns : Namespace) (p : List String) : Option Namespace :=
  match p with
  | [] => ns
  | x :: p => do (← findAssoc ns.children x).findNS p

def Environment.findDef (env : Environment) (n : String) (ns : List String) :
    Option Definition := do findAssoc (← env.head.findNS ns).defs n

structure State where
  env : Environment := {}
  ngen : Nat := 1
  seq : Nat := 1
  out : IO.FS.Handle

abbrev M := StateT State (ExceptT String IO)

def nextId : M Nat :=
  fun s => return (s.ngen, {s with ngen := s.ngen + 1})

def nextSeq : M Nat :=
  fun s => return (s.seq, {s with seq := s.seq + 1})

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

def findSimple (stack : List (String × Namespace)) (ns : Namespace) (x : String) :
    Option (LocalCtx ⊕ (String × List (String × Namespace) × Definition)) :=
  if let some ctx := findAssoc ns.params x then pure (.inl ctx) else
  if let some d := findAssoc ns.defs x then pure (.inr (x, stack, d)) else
  match stack with
  | [] => none
  | (_, ns) :: stack => findSimple stack ns x

def LocalCtx.find (ctx : LocalCtx) (x : String) : Option LocalCtx :=
  match ctx with
  | [] => none
  | d :: ctx' => if d.name == x then some ctx else find ctx' x

def findSymbol (stack : List (String × Namespace)) (ns : Namespace) (ctx : LocalCtx) :
    AST.Symbol → Except String (LocalCtx ⊕ (String × List (String × Namespace) × Definition))
  | .simple x =>
    if let some ctx := LocalCtx.find ctx x then .ok (.inl ctx) else
    if let some res := findSimple stack ns x then .ok res else
    throw s!"unknown symbol {x}"
  | .ns x p => do
    let (stack', ns') ← findNS stack ns p
    if let some ctx := findAssoc ns'.params x then pure (.inl ctx) else
    if let some d := findAssoc ns'.defs x then pure (.inr (x, stack', d)) else
    throw s!"unknown symbol {x}"

def matchContext (ctx : LocalCtx) : LocalCtx → Option Nat
  | [] => pure ctx.length
  | {id, ..} :: _ => ctx.findIdx? (·.id == id)

variable (env : Environment) (ctx : LocalCtx)

variable (verbose := false)
def traceIf (s : String) (f : Unit → α) : α :=
  if verbose then dbgTrace s f else f ()

def delta : Expr → Option Expr
  | .const n ns _ es => do
    let {val := some val, ..} ← env.findDef n ns | none
    let rec loop (revArgs : List Expr) (k : Nat) : Option Expr :=
      match revArgs with
      | [] => do
        return val.lift ctx.length k
      | a :: rest => do
        let val ← loop rest (k+1)
        return val.subst a k
    let r ← loop es.reverse 0
    traceIf verbose "{ns}.{n}{es} := {r}" fun () =>
    pure r
  | _ => none

def whnf (fuel : Nat) : Expr → Option Expr
  | .univ .. | .lam .. | .var .. => none
  | e@(.const ..) => do
    let e ← delta env ctx verbose e
    return match fuel with | 0 => e | fuel+1 => (whnf fuel e).getD e
  | .app e1 e2 =>
    -- FIXME it shouldn't be necessary to consume fuel here
    let e1' := match fuel with | 0 => none | fuel+1 => whnf fuel e1
    match e1'.getD e1 with
    | .lam _ _ d =>
      match fuel with
      | 0 => return .app (← e1') e2
      | fuel+1 => let e := d.subst e2 0; (whnf fuel e).getD e
    | _ => return .app (← e1') e2

def whnfFuel := 100

def eta (fuel : Nat) (x : String) (dom e : Expr) : Option Expr := do
  let e' := whnf env ctx verbose fuel e
  match e'.getD e with
  | .app f (.var 0) =>
    unless f.skips 0 do return .lam x dom (← e')
    let e := f.subst (.var 0) 0
    return (whnf env ctx verbose fuel e).getD e
  | .lam y d b =>
    match fuel with
    | 0 => .lam x dom <$> e'
    | fuel+1 =>
      match eta fuel y d b with
      | none => .lam x dom <$> e'
      | some e' => return (eta fuel x dom e').getD (.lam x dom e')
  | _ => .lam x dom <$> e'

def isSubtype (fuel : Nat) (e1 e2 : Expr) : Bool := Id.run do
  let isSubtype a b := match fuel with | 0 => false | fuel+1 => isSubtype fuel a b
  traceIf verbose s!"{e1} <? {e2}" fun () => do
  if let .app .. := e1 then
    if let some e1' := whnf env ctx verbose fuel e1 then
      return isSubtype e1' e2
  if let .app .. := e2 then
    if let some e2' := whnf env ctx verbose fuel e2 then
      return isSubtype e1 e2'
  (match e1, e2 with
  | .univ t1, .univ t2 => t1 == t2
  | .var i, .var j => i == j
  | .lam _ t1 e1, .lam _ t2 e2 => isSubtype t1 t2 && isSubtype e1 e2
  | .lam _ _ e1, .univ t2 => isSubtype e1 (.univ t2)
  | .const _ _ seq1 es1, .const _ _ seq2 es2 =>
    seq1 == seq2 && es1.length == es2.length &&
    (es1.zip es2).all fun (a,b) => isSubtype a b
  | .app f1 a1, .app f2 a2 => isSubtype f1 f2 && isSubtype a1 a2
  | _, _ => false) ||
  (match e1, e2 with
  | .const _ _ seq1 _, .const _ _ seq2 _ =>
    if seq1 > seq2 then
      if let some e1' := delta env ctx verbose e1 then isSubtype e1' e2 else
      if let some e2' := delta env ctx verbose e2 then isSubtype e1 e2' else false
    else
      if let some e2' := delta env ctx verbose e2 then isSubtype e1 e2' else
      if let some e1' := delta env ctx verbose e1 then isSubtype e1' e2 else false
  | .const .., _ =>
    if let some e1' := delta env ctx verbose e1 then isSubtype e1' e2 else false
  | _, _ =>
    if let some e2' := delta env ctx verbose e2 then isSubtype e1 e2' else false) ||
  (match e1, e2 with
  | .lam x1 t1 e1, _ =>
    if let some e1' := eta env ctx verbose fuel x1 t1 e1 then isSubtype e1' e2 else false
  | _, .lam x2 t2 e2 =>
    if let some e2' := eta env ctx verbose fuel x2 t2 e2 then isSubtype e1 e2' else false
  | _, _ => false)

def assertSubtype (e1 e2 : Expr) : Except String Unit :=
  if isSubtype env ctx verbose whnfFuel e1 e2 then pure () else
    throw s!"{ctx.repr}\n⊢ {e1} <: {e2} failed"

structure Typecheck where
  val : Expr
  type : Option Expr
  degree : Nat
  deriving Repr

structure ApplyDef where
  subst : Nat → Expr → Expr

variable (check := true) in
def applyDef (name : String) (stack : List (String × Namespace)) (d : Definition)
    (args : List Typecheck) : M Typecheck := do
  let { subst } ← loop d.ctx args.reverse 0
  let rec mkArgs
    | 0, _, acc => acc
    | n+1, k, acc => mkArgs n (k+1) (.var k :: acc)
  let n := d.ctx.length - args.length
  let args' := mkArgs n (ctx.length - n) (args.map (·.val))
  pure {
    val := .const name (stack.map (·.1)).reverse d.seq args'
    type := subst 0 d.type, degree := d.tyDeg + 1 }
where
  loop (dctx : LocalCtx) (revArgs : List Typecheck) (k : Nat) : M ApplyDef := do
    match revArgs with
    | [] =>
      let some n := matchContext ctx dctx | throw s!"incompatible context 2: {repr ctx} <: {repr dctx}"
      pure { subst k e := e.lift n k }
    | { val := a, type := aty, .. } :: rest =>
      traceIf verbose s!"applyDef {ctx.repr} -> {dctx.repr}; {repr revArgs}" fun () => do
      let d :: dctx := dctx | throw "too many arguments"
      let { subst } ← loop dctx rest (k+1)
      if check then
        let .some aty := aty | throw s!"ensureType: value {a} has no type"
        assertSubtype env ctx verbose aty (subst 0 d.type)
      return { subst k e := (subst (k+1) e).subst a k }

def Expr.principalType (ctx : LocalCtx) : Expr → Option Expr
  | .univ _ => none
  | .lam x ty e => return .lam x ty (← e.principalType (⟨x, 0, 2, ty⟩ :: ctx))
  | .var i => ctx[i]?.map (·.type.lift (i+1) 0)
  | .const n ns _ es => do
    let {type, ..} ← env.findDef n ns
    let rec loop (revArgs : List Expr) (k : Nat) : Expr :=
      match revArgs with
      | [] => type.lift ctx.length k
      | a :: rest => (loop rest (k+1)).subst a k
    loop es.reverse 0
  | .app e1 e2 => return .app (← e1.principalType ctx) e2

variable (check := true) in
mutual
def typecheck (ctx : LocalCtx) : AST.Expr → M Typecheck
:= fun e =>
  traceIf verbose s!"typecheck {repr e}" fun () =>
  (fun res => do
    let a ← res
    traceIf verbose s!"typecheck {repr e} => {repr a}" fun () => pure a) <|
  match e with
  | .type => pure { val := .univ true, type := none, degree := 1 }
  | .prop => pure { val := .univ false, type := none, degree := 1 }
  | .lam name ty e => do
    let {val := ty, degree := d, ..} ← typecheck ctx ty
    if check && d != 2 then throw s!"bad type {repr ty}"
    let {val := e', degree := d, type} ← typecheck ({ name, id := ← nextId, tyDeg := 2, type := ty } :: ctx) e
    return {val := .lam name ty e', type := .lam name ty <$> type, degree := d}
  | .id x => do
    let s ← get
    match ← findSymbol s.env.stack s.env.ns ctx x with
    | .inl xctx =>
      let d :: _ := xctx | throw "unreachable"
      let some n := matchContext ctx xctx | throw s!"incompatible context 1: {repr ctx} <: {repr xctx}"
      return {val := .var n, type := d.type.lift (n+1) 0, degree := d.tyDeg + 1}
    | .inr (x, stack, d) => applyDef env ctx check verbose x stack d []
  | e@(.papp ..) => typecheckCall ctx e []
  | .app e1 e2 => do
    let {val := e1, type := some ty1, degree} ← typecheck ctx e1 | throw s!"not a function: {repr e1}"
    let {val := e2, type := some ty2, degree := d2} ← typecheck ctx e2 | throw s!"{ctx.repr}\n⊢ bad type {repr e2}"
    if check && d2 != 3 then throw s!"{ctx.repr}\n⊢ bad degree {degree} for {repr e2} : {repr ty2}"
    let some (dom, b) :=
        match (whnf env ctx verbose whnfFuel ty1).getD ty1 with
        | .lam _ dom b => pure (dom, b)
        | ty1 => do
          let univ ← ty1.principalType env ctx
          dbg_trace "trying univ: ({e1} : {ty1} : {univ})"
          let .lam _ dom _ := (whnf env ctx verbose whnfFuel univ).getD univ | none
          pure (dom, (ty1.lift 1 0).app (.var 0))
      | throw s!"not a function: ({e1} : {ty1})"
    traceIf verbose s!"applying ({e1} : {ty1} := λ_:{dom} => {b}) to ({e2} : {ty2})" fun () => do
    if check then assertSubtype env ctx verbose ty2 dom
    return {val := .app e1 e2, type := b.subst e2 0, degree}
  -- | e => throw s!"typecheck {repr e}"
termination_by e => 2 * sizeOf e + 1

def typecheckCall (ctx : LocalCtx) : AST.Expr → List Typecheck → M Typecheck
  | .papp e1 e2, acc => do typecheckCall ctx e1 ((← typecheck ctx e2) :: acc)
  | .id x, acc => do
    let s ← get
    let .inr (x, stack', d) ← findSymbol s.env.stack s.env.ns ctx x
      | throw "variables cannot have arguments"
    applyDef env ctx verbose check x stack' d acc
  | _, _ => throw s!"invalid application"
termination_by e => 2 * sizeOf e
end

def typecheck' (e : AST.Expr) (check := true) : M Typecheck := do
  let s ← get
  typecheck s.env verbose check s.env.ns.ctx e

def ensureType (e ty : Expr) : Except String Unit := do
  let .some ety := e.principalType env env.ns.ctx | throw s!"ensureType: value {e} has no type"
  assertSubtype env env.ns.ctx verbose ety ty

def ensureType' (e ty : Expr) : M Unit := do
  ensureType (← get).env verbose e ty

def processItem (check := true) : AST.Item → M Unit
  | .comment => pure ()
  | .openSection n => do
    (← get).out.putStrLn s!"namespace {escape1 n}"
    modify fun s => { s with
      env.stack := (n, s.env.ns) :: s.env.stack
      env.ns := { ctx := s.env.ns.ctx } }
  | .reopenSection n => do
    let ns := (← get).env.ns
    (← get).out.putStrLn s!"namespace {escape1 n}"
    let some (child, children) := popAssoc ns.children n | throw s!"unknown section {n}"
    let ns := { ns with children }
    modify fun s => { s with env.stack := (n, ns) :: s.env.stack, env.ns := child }
  | .closeSection n' => do
    let {stack := (n, ns) :: stack, ns := sec} := (← get).env | throw "no open section"
    unless n' == n do throw s!"expected {n}, got {n'}"
    (← get).out.putStrLn s!"end {escape1 n'}"
    let ns := { ns with children := (n, sec) :: ns.children }
    modify fun s => { s with env := {stack, ns} }
  | .setContext none =>
    modify ({· with env.ns.ctx := []})
  | .setContext (some x) => do
    let s ← get
    let .inl xctx ← findSymbol s.env.stack s.env.ns [] x | throw s!"unknown symbol {repr x}"
    modify ({· with env.ns.ctx := xctx})
  | .parameter x ty => do
    let {val := ty, degree := tyDeg, ..} ← typecheck' verbose ty check
    let ctx := (← get).env.ns.ctx
    if check then unless 1 ≤ tyDeg ∧ tyDeg ≤ 2 do throw "bad parameter degree"
    let n ← nextId
    modify fun s =>
      let ctx' := { name := x, id := n, tyDeg, type := ty } :: ctx
      { s with env.ns.ctx := ctx', env.ns.params := (x, ctx') :: s.env.ns.params }
  | .def_ x ty val => do
    let {val := ty', degree := deg, ..} ← typecheck' verbose ty check
    let ctx := (← get).env.ns.ctx
    if check then unless 1 ≤ deg ∧ deg ≤ 2 do throw "bad parameter degree"
    let val' ← if let some val := val then
      let {val := val', ..} ← typecheck' verbose val check
      if check then ensureType' verbose val' ty'
      pure (some val')
    else pure none
    let defn := {ctx, seq := ← nextSeq, type := ty', val := val', tyDeg := deg}
    traceIf verbose "def {ctx.repr} ⊢ {x}[{deg}] : {ty'} := {val'}" fun () => do
    let fmt := Id.run do
      let sctx := (ctx.toLean.group .fill).nest 4
      let sty := (Std.Format.line ++ (ty'.toLean ctx true).group).nest 4
      let mut sval := val'.map fun v =>
        (Std.Format.line ++ (v.toLean ctx (ty' matches .univ _)).group).nest 2
      -- if x == "all" then sval := some "∀ x, p x"
      match sval with
      | none => f!"axiom {escape1 x}{sctx} :{sty}".group
      | some val' => f!"def {escape1 x}{sctx} :{sty} :={val'}".group
    (← get).out.putStrLn <| fmt.pretty 100
    modify fun s => { s with env.ns.defs := (x, defn) :: s.env.ns.defs }

instance : MonadLift M (StateT State IO) where
  monadLift m s := do
    match ← m s with
    | .ok (s, a) => pure (s, a)
    | .error e => throw <| .userError e

def _root_.main (args : List String) : IO Unit := do
  let N := (·.toNat!) <$> args.head?
  let grundlagen ← match Parser.items.run (← IO.FS.readFile "../aut-4.2/grundlagen.aut") with
    | .ok e => pure e
    | .error e => throw (.userError e)
  let h ← IO.FS.Handle.mk "out.lean" .write
  h.putStrLn "\
    instance (α : Sort u) : CoeSort (α → Sort v) (Sort imax u v) := ⟨fun f => ∀ a, f a⟩\n\
    instance (α : Sort u) : CoeOut (α → Sort v) (Sort imax u v) := ⟨fun f => ∀ a, f a⟩\n\
    set_option linter.unusedVariables false\n\
    noncomputable section"
  let (_, _s) ← StateT.run (s := ({ out := h } : State)) do
    let mut n := 0
    let check := true
    for it in grundlagen do
      -- monadLift $ IO.println $ (← get).env.ns.ctx.repr
      monadLift $ h.putStrLn s!"#eval {n}" -- progress reporting for generated lean file
      monadLift $ IO.println s!"== item {n} =="
      -- monadLift $ IO.println $ repr it
      let s ← get
      try
        processItem (match N with | none => false | some N => n ≥ N) check it
      catch e =>
        monadLift $ IO.println s!"\n\n== FAILED item {n} =="
        monadLift $ println! s.env.ns.ctx.repr
        set s
        processItem false false it
        throw e
      n := n + 1
  h.flush

-- #eval main
