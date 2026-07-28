import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-!
# Axiom-audit commands

These commands turn Lean's transitive dependency and axiom collection into
enforcing checks.  They are shared by the focused final-deduction audit and
the exhaustive whole-project audit.
-/

open Lean Elab Command

private def sortedDifference
    (left right : NameSet) : Array Name := Id.run do
  let mut difference := #[]
  for name in left do
    unless right.contains name do
      difference := difference.push name
  return difference.qsort Name.lt

private def assertExactNames
    (subject : MessageData)
    (actual expected : NameSet) : CommandElabM Unit := do
  let unexpected := sortedDifference actual expected
  let missing := sortedDifference expected actual
  unless unexpected.isEmpty && missing.isEmpty do
    throwError
      "allowlist mismatch for {subject}\n\
       unexpected: {unexpected}\nmissing: {missing}"

private def resolveNameSet
    (names : Array (TSyntax `ident)) : CommandElabM NameSet := do
  let resolved ← names.mapM fun name =>
    liftCoreM <| realizeGlobalConstNoOverloadWithInfo name
  return NameSet.ofArray resolved

private partial def visitDependencies
    (env : Environment) (name : Name) : StateM NameSet Unit := do
  if (← get).contains name then
    return
  modify (·.insert name)
  let visitExpr (expr : Expr) : StateM NameSet Unit :=
    expr.getUsedConstants.forM (visitDependencies env)
  match env.find? name with
  | some (.axiomInfo value) =>
      visitExpr value.type
  | some (.defnInfo value) =>
      visitExpr value.type *> visitExpr value.value
  | some (.thmInfo value) =>
      visitExpr value.type *> visitExpr value.value
  | some (.opaqueInfo value) =>
      visitExpr value.type *> visitExpr value.value
  | some (.quotInfo _) =>
      pure ()
  | some (.ctorInfo value) =>
      visitExpr value.type
  | some (.recInfo value) =>
      visitExpr value.type
  | some (.inductInfo value) =>
      visitExpr value.type *> value.ctors.forM (visitDependencies env)
  | none =>
      pure ()

private def dependencyClosure
    (env : Environment) (root : Name) : NameSet :=
  ((visitDependencies env root).run {}).2

/--
Fail unless a declaration's complete axiom set is exactly the supplied
allowlist. Unlike `#print axioms`, this turns axiom-set drift into a
verification failure.
-/
elab "assert_axioms " decl:ident
    allowed:(ppSpace colGt ident)* : command => do
  let declName ←
    liftCoreM <| realizeGlobalConstNoOverloadWithInfo decl
  let actual ← Lean.collectAxioms declName
  let expected ← resolveNameSet allowed
  assertExactNames m!"{declName}" (NameSet.ofArray actual) expected

/--
Fail if any declaration from a module under the supplied prefix contains
`sorryAx`, or if the union of their axiom sets differs from the allowlist.
Declarations are selected by source module, so private helpers and
declarations outside the project's principal namespace remain covered.
-/
elab "assert_module_prefix_axioms " module:ident
    allowed:(ppSpace colGt ident)* : command => do
  let modulePrefix := module.getId
  let env ← getEnv
  let mut actual : NameSet := {}
  let mut sorryOffenders : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some moduleIdx := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[moduleIdx.toNat]!
      if modulePrefix.isPrefixOf moduleName then
        let axioms ← Lean.collectAxioms name
        if axioms.contains ``sorryAx then
          sorryOffenders := sorryOffenders.push (privateToUserName name)
        for axiomName in axioms do
          actual := actual.insert axiomName
  unless sorryOffenders.isEmpty do
    throwError
      "declarations containing sorry in modules under {modulePrefix}: \
       {sorryOffenders.qsort Name.lt}"
  let expected ← resolveNameSet allowed
  assertExactNames m!"modules under {modulePrefix}" actual expected

/--
Fail unless every listed declaration occurs in the transitive kernel
dependency closure of `root`.
-/
elab "assert_reachable_from " root:ident
    dependencies:(ppSpace colGt ident)* : command => do
  let rootName ←
    liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let dependencyNames ← dependencies.mapM fun dependency =>
    liftCoreM <| realizeGlobalConstNoOverloadWithInfo dependency
  let closure := dependencyClosure (← getEnv) rootName
  let missing :=
    dependencyNames.filter (fun name => !closure.contains name)
      |>.qsort Name.lt
  unless missing.isEmpty do
    throwError
      "declarations not reachable from {rootName}: {missing}"

/--
Fail if a source module under `modulePrefix` contributes declarations to the
environment but none to `root`'s transitive kernel dependency closure.
Modules listed after `except` are ignored; this is used for audit commands,
which inspect the proof but are not themselves part of it.
-/
elab "assert_module_prefix_reachable_from " root:ident
    modulePrefix:ident " except "
    excluded:(ppSpace colGt ident)* : command => do
  let rootName ←
    liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let modulePrefixName := modulePrefix.getId
  let excludedModules := NameSet.ofArray (excluded.map (·.getId))
  let env ← getEnv
  let closure := dependencyClosure env rootName
  let mut projectModules : NameSet := {}
  let mut reachedModules : NameSet := {}
  for (name, _) in env.constants.toList do
    if let some moduleIdx := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[moduleIdx.toNat]!
      if modulePrefixName.isPrefixOf moduleName &&
          !excludedModules.contains moduleName then
        projectModules := projectModules.insert moduleName
        if closure.contains name then
          reachedModules := reachedModules.insert moduleName
  let missing := sortedDifference projectModules reachedModules
  unless missing.isEmpty do
    throwError
      "modules under {modulePrefixName} with no declaration reachable from \
       {rootName}: {missing}"
