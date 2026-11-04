module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesULiftComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticFlatSubsiteCohomology

/-!
# Cohomology of a parasitic module vanishes, at the module universe of the schemes

Let `𝒳` be an algebraic stack and `ℱ` a parasitic sheaf of `𝒪_𝒳`-modules on the fppf site
(**Stacks 0773**), at the module universe `u` of the schemes, which is where
`AlgebraicGeometry.Stack.fppfModules` and the quasi-coherent theory live. Part (1) of
**Stacks 0775** asserts `H^i(𝒳, ℱ) = 0` for all `i`, with `H^i(𝒳, -) = Ext^i(𝒪_𝒳, -)`, the
functor `AlgebraicGeometry.Stack.FlatFppf.fppfModuleCohomology`. This file proves it.

The universe lift carries `H^i(𝒳, ℱ)` to `Ext^i` out of the lifted structure sheaf of the lift of
`ℱ` at the universe `u + 1` (`AlgebraicGeometry.Stack.fppfModuleCohomologyULiftIso`), the lift of
a parasitic module is parasitic, and at `u + 1` the vanishing is
`AlgebraicGeometry.Stack.isZero_ext_uliftUnit_of_isParasitic`.

## Main results

* `AlgebraicGeometry.Stack.isZero_fppfModuleCohomology_of_isParasitic_atSchemeUniverse`:
  **Stacks 0775** part (1) for the fppf topology, at the module universe `u`, for `Ext`-groups in
  any universe.

## References

* [Stacks Project, Tag 0775](https://stacks.math.columbia.edu/tag/0775)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u w t

namespace AlgebraicGeometry.Stack

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0775** part (1), for the fppf topology, at the module universe `u` of the schemes.
Let `𝒳` be an algebraic stack and `ℱ` a parasitic sheaf of `𝒪_𝒳`-modules (**Stacks 0773**).
Then `H^i(𝒳, ℱ) = 0` for every `i`, where `H^i(𝒳, -)` is
`AlgebraicGeometry.Stack.FlatFppf.fppfModuleCohomology`, `Ext^i` out of the structure sheaf, in
any universe `t` of `Ext`-groups.

The instance argument `HasExt.{t}` is not a hypothesis on `ℱ`: `fppfModuleCohomology.{u, w, t}`
is only defined in its presence. At `t = u` it is supplied by the Grothendieck abelian structure
(`AlgebraicGeometry.Stack.isGrothendieckAbelian_fppfModules`), which is
`AlgebraicGeometry.Stack.isZero_fppfModuleCohomology_of_isParasitic_ofGrothendieck`.

By `AlgebraicGeometry.Stack.fppfModuleCohomologyULiftIso` this is the vanishing of `Ext^i` out of
the lifted structure sheaf of the universe lift of `ℱ`, which is parasitic as `ℱ` is, and that
is `AlgebraicGeometry.Stack.isZero_ext_uliftUnit_of_isParasitic`. -/
@[stacks 0775 "part (1) for τ = fppf at the module universe u of the schemes: H^i(𝒳, ℱ) = 0 for \
a parasitic ℱ, with H^i = Ext^i(𝒪_𝒳, -) as in FlatFppf.fppfModuleCohomology"]
theorem isZero_fppfModuleCohomology_of_isParasitic_atSchemeUniverse
    {𝒳 : AlgebraicStacks.{u, w} B S hS} [HasExt.{t} (fppfModules B S hS 𝒳)]
    (N : fppfModules B S hS 𝒳) (hN : IsParasitic B S hS 𝒳 .fppf N.val) (i : ℕ) :
    IsZero ((FlatFppf.fppfModuleCohomology.{u, w, t} B S hS 𝒳 i).obj N) := by
  let := enoughInjectives_fppfModules B S hS 𝒳
  have : HasExt.{u + 1} (fppfModules B S hS 𝒳) := hasExt_of_enoughInjectives.{u + 1} _
  have h := ((fppfModuleCohomologyULiftIso 𝒳 i).app N).isZero_iff.2
    (isZero_ext_uliftUnit_of_isParasitic.{u, w, u + 1} (Or.inr rfl)
      ((fppfModulesULift B S hS 𝒳).obj N) (fun x hx =>
        @Equiv.subsingleton _ _ Equiv.ulift (hN x hx)) i)
  have : Subsingleton (Ext.{u + 1} (SheafOfModules.unit _) N i) :=
    AddCommGrpCat.subsingleton_of_isZero h
  have : Subsingleton (Ext.{t} (SheafOfModules.unit _) N i) :=
    Ext.chgUniv.{u + 1, t}.subsingleton
  exact @AddCommGrpCat.isZero_of_subsingleton _ this

/-- **Stacks 0775** part (1) for the fppf topology at the module universe `u`, with `Ext`-groups in
the universe `u` in which the Grothendieck abelian category `Mod(𝒪_𝒳)` has them, so with no
instance argument. -/
theorem isZero_fppfModuleCohomology_of_isParasitic_ofGrothendieck
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (N : fppfModules B S hS 𝒳)
    (hN : IsParasitic B S hS 𝒳 .fppf N.val) (i : ℕ) :
    haveI := isGrothendieckAbelian_fppfModules B S hS 𝒳
    IsZero ((FlatFppf.fppfModuleCohomology.{u, w, u} B S hS 𝒳 i).obj N) :=
  have := isGrothendieckAbelian_fppfModules B S hS 𝒳
  isZero_fppfModuleCohomology_of_isParasitic_atSchemeUniverse N hN i

section SiteKind

/-- **Stacks 0775** part (1), for `τ` the étale or the fppf topology, at the module universe `u` of
the schemes. Let `𝒳` be an algebraic stack and `ℱ` a parasitic sheaf of `𝒪_𝒳`-modules on `𝒳_τ`
(**Stacks 0773**). Then `H^i_τ(𝒳, ℱ) = Ext^i(𝒪_𝒳, ℱ) = 0` for every `i`, for `Ext`-groups in any
universe `t`.

The instance argument `HasExt.{t}` is not a hypothesis on `ℱ`: it is what makes `Ext`-groups in
the universe `t` exist at all, and it is always available at `t = u`, the category of modules
being Grothendieck abelian (`AlgebraicGeometry.Stack.isGrothendieckAbelian_moduleRingSheaf`, see
`AlgebraicGeometry.Stack.isZero_ext_unit_of_isParasitic_atSchemeUniverse_ofGrothendieck`).

By `AlgebraicGeometry.Stack.isZero_ext_unit_iff_isZero_ext_uliftUnit` this is the vanishing of
`Ext^i` out of the lifted structure sheaf of the universe lift of `ℱ`, which is parasitic as `ℱ`
is, and that is `AlgebraicGeometry.Stack.isZero_ext_uliftUnit_of_isParasitic`. -/
@[stacks 0775 "part (1) for τ the étale or the fppf topology, at the module universe u of the \
schemes: H^i_τ(𝒳, ℱ) = Ext^i(𝒪_𝒳, ℱ) = 0 for a parasitic ℱ"]
theorem isZero_ext_unit_of_isParasitic_atSchemeUniverse {τ : SiteKind}
    (hτ : τ = .etale ∨ τ = .fppf) {𝒳 : AlgebraicStacks.{u, w} B S hS}
    [HasExt.{t} (SheafOfModules.{u}
      (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ))]
    (N : SheafOfModules.{u}
      (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ))
    (hN : IsParasitic B S hS 𝒳 τ N.val) (i : ℕ) :
    IsZero ((extFunctorObj.{t} (SheafOfModules.unit _) i).obj N) :=
  (isZero_ext_unit_iff_isZero_ext_uliftUnit τ 𝒳 N i).2
    (isZero_ext_uliftUnit_of_isParasitic.{u, w, u + 1} hτ ((stackModuleULift B S hS τ 𝒳).obj N)
      (fun x hx => @Equiv.subsingleton _ _ Equiv.ulift (hN x hx)) i)

/-- **Stacks 0775** part (1) at the module universe `u`, with the `Ext`-groups in the universe `u`
in which the Grothendieck abelian category of modules has them
(`CategoryTheory.IsGrothendieckAbelian.hasExt`), so with no instance argument. This is
`AlgebraicGeometry.Stack.isZero_ext_unit_of_isParasitic_atSchemeUniverse` at `t = u`. -/
theorem isZero_ext_unit_of_isParasitic_atSchemeUniverse_ofGrothendieck {τ : SiteKind}
    (hτ : τ = .etale ∨ τ = .fppf) {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (N : SheafOfModules.{u}
      (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ))
    (hN : IsParasitic B S hS 𝒳 τ N.val) (i : ℕ) :
    haveI := isGrothendieckAbelian_moduleRingSheaf B S hS 𝒳 τ
    IsZero ((extFunctorObj.{u} (SheafOfModules.unit _) i).obj N) :=
  have := isGrothendieckAbelian_moduleRingSheaf B S hS 𝒳 τ
  isZero_ext_unit_of_isParasitic_atSchemeUniverse hτ N hN i

end SiteKind

end AlgebraicGeometry.Stack

end
