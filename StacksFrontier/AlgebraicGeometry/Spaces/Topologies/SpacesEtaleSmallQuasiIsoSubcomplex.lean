module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SmallQuasiIsoSubcomplex
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleModulePullbackComparison

/-!
# Small quasi-isomorphic subcomplexes on the spaces-étale site

Let `X` be an algebraic space. A complex of `𝒪_X`-modules on the spaces-étale site
`X_{spaces,étale}` (modules in the universe `u + 1`) whose cohomology sheaves have `u`-small
sections — that is, lie in the essential image of the transport from the small étale site
(`AlgebraicGeometry.Space.toSpacesEtaleModules_full_faithful_essImage`) — contains a subcomplex
with `u`-small sections whose inclusion is a quasi-isomorphism
(`AlgebraicGeometry.Space.spacesEtale_exists_small_quasiIso_subcomplex`).

This is `Stacks.SheafOfModules.exists_small_quasiIso_subcomplex_of_small_homology` for the
spaces-étale site, which is essentially `u`-small (`AlgebraicGeometry.Space.SpacesEtale`), with
`u`-small rings of sections (`AlgebraicGeometry.Space.small_globalFunctions`).

## Implementation notes

The abelian structure on sheaves of modules is Mathlib's `SheafOfModules.instAbelian`. This file
does not import `Stacks.Cohomology.SiteModules.moduleSheavesAbelian`; files that do, and use this
statement, switch that instance off (together with
`Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Small quasi-isomorphic subcomplexes on the spaces-étale site.** A complex of
`𝒪_X`-modules on `X_{spaces,étale}` whose cohomology sheaves have `u`-small sections contains a
subcomplex with `u`-small sections whose inclusion is a quasi-isomorphism. -/
theorem spacesEtale_exists_small_quasiIso_subcomplex (X : AlgebraicSpaces B S hS)
    (M : CochainComplex (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O)) ℤ)
    (hM : ∀ (n : ℤ) (V : (SpacesEtale B S hS X)ᵒᵖ), Small.{u} ((M.homology n).val.obj V)) :
    ∃ (M' : CochainComplex (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O)) ℤ)
      (i : M' ⟶ M), QuasiIso i ∧
      ∀ (n : ℤ) (V : (SpacesEtale B S hS X)ᵒᵖ), Small.{u} ((M'.X n).val.obj V) := by
  have : ∀ V, Small.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleRingedSite B S hS X).O).obj.obj V) := fun V =>
    small_globalFunctions B S hS _
  obtain ⟨M', i, -, hq, hs⟩ :=
    Stacks.SheafOfModules.exists_small_quasiIso_subcomplex_of_small_homology.{u, u + 1} M hM
  exact ⟨M', i, hq, hs⟩

end AlgebraicGeometry.Space

end
