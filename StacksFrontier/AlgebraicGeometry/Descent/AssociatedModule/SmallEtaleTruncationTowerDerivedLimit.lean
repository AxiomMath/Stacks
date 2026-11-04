module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffineHypercohomologyEdge
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorTriangleOfTower
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleModuleInjectives

/-!
# An object of `D_QCoh(S_étale, 𝒪)` is the derived limit of its truncation tower

Let `S` be a scheme contained in a big étale site `B` and let `E` be an object of the unbounded
derived category of `𝒪`-modules on the small étale site of [Stacks, Tag 021B] whose cohomology
sheaves are all quasi-coherent on the site.  Then `E` *is* a derived limit of the tower
`n ↦ τ_{≥ -n} E` of its canonical truncations from below.

This is [Stacks, Tag 0D6S] at the morphism `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` of [Stacks, Tag
070R] — equivalently [Stacks, Tag 0D6P] with `d = 0` on the small étale site — and it is the one
ingredient that the unbounded form of obligations (ii) and (iii) of [Stacks, Tag 071Q] was
missing.  Both of its inputs are already available at that site:

* the affine objects cover every object, which is
  `AlgebraicGeometry.SmallEtale.hasEnoughObjects_isAffine`;
* a quasi-coherent `𝒪`-module has no higher cohomology over an affine object, which is
  `AlgebraicGeometry.SmallEtale.isZero_rightDerived_evaluation_of_isQuasicoherentOnSite`.

So no `Stacks.Cohomology.OlssonLaszloSituation` has to be assembled: the convergence criterion
`Stacks.Cohomology.AcyclicCover.isIso_to_isDerivedLimit_truncGETower_of_acyclic` takes the
covering class and the vanishing directly, its own cofinal system of coverings being the one
built generically by `Stacks.Cohomology.CofinalCoveringSystem.ofHasEnoughObjects`.  This is the
same route the algebraic-space analogue
`AlgebraicGeometry.Space.isDerivedLimit_truncGETower_modules` takes.

## Main results

* `AlgebraicGeometry.SmallEtale.isIso_to_isDerivedLimit_truncGETower_of_isQuasicoherentOnSite`:
  the canonical map from `E` to a derived limit of its truncation tower is invertible.
* `AlgebraicGeometry.SmallEtale.isDerivedLimit_truncGETower`: the same fact in the form the
  limit arguments consume — `E` is a derived limit of the tower, the structural map being the
  canonical cone.

## Implementation notes

The derived category is the standard one, as in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleAffineHypercohomologyEdge.lean`
and for the same reason: the convergence criterion is stated at
`CategoryTheory.HasDerivedCategory.standard`.  Its universe is `u + 1`, and the instance is
named rather than synthesized, being
`AlgebraicGeometry.SmallEtale.hasDerivedCategoryStandard_structureSheaf`.

The product of the tower is not assumed: each of its stages is bounded below, so
`Stacks.Cohomology.HypercohomologyEdge.hasProduct_truncGETower` supplies it.

The step from "the canonical map into any derived limit is invertible" to "`E` is a derived
limit" is `Stacks.InverseSystem.exists_distTriang_milnor_of_isIso`, which is exactly that step:
a derived limit exists, the cone of truncation maps lifts through the triangle presenting it,
and the hypothesis says that lift is invertible, so the triangle transports to `E`.  The cone
condition is `Stacks.Cohomology.HypercohomologyEdge.truncGEπ_comp_truncGETower_map`.

No `@[stacks]` attribute is attached.  Both statements are the instance at the small étale site
of a tag proved in general — [Stacks, Tag 0D6P] is
`Stacks.Cohomology.AcyclicCover.isIso_to_isDerivedLimit_truncGETower_of_acyclic` and [Stacks,
Tag 0D6S] is `Stacks.Cohomology.isIso_to_isDerivedLimit_truncGETower_of_derivedCategoryB` — and
a tag is not restated at an instance.

## References

* [Stacks Project, Tag 0D6S](https://stacks.math.columbia.edu/tag/0D6S)
* [Stacks Project, Tag 0D6P](https://stacks.math.columbia.edu/tag/0D6P)
* [Stacks Project, Tag 0BK7](https://stacks.math.columbia.edu/tag/0BK7)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.SmallEtale

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] hasDerivedCategoryStandard_structureSheaf

/-- Former name of
`AlgebraicGeometry.SmallEtale.enoughInjectives_smallEtaleModules`, the instance that the
`𝒪`-modules on the small étale site of `S`, at module universe `u`, have enough injectives; that
instance is what the statements below use, the global
`Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives` being removed above. -/
alias enoughInjectives_structureSheafModules := enoughInjectives_smallEtaleModules

/-- The truncation tower from below of an object of `D(S_étale, 𝒪)` has a product in that derived
category: each of its stages is bounded below, which is
`Stacks.Cohomology.HypercohomologyEdge.hasProduct_truncGETower` ([Stacks, Tag 0BK7]).  It is
named here so that the derived-limit statement below needs no product hypothesis, as the generic
declaration is not an instance. -/
local instance hasProduct_truncGETower_structureSheaf
    (E : DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS))) :
    HasProduct fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
      (SheafOfModules.{u} (structureSheaf B S hS)) E).obj ⟨n⟩ :=
  Stacks.Cohomology.HypercohomologyEdge.hasProduct_truncGETower (structureSheaf B S hS) E

/-- **[Stacks, Tag 0D6S] at `ε`.**  Let `E` be an object of `D(S_étale, 𝒪)` whose cohomology
sheaves are all quasi-coherent on the site.  Then the canonical map from `E` to a derived limit
`L` of the tower `n ↦ τ_{≥ -n} E` of its canonical truncations from below is an isomorphism.

The derived limit is presented by its structural morphism `p` to the product of the tower
together with the distinguished triangle `hL` characterising it; the map `c` out of `E` is the
canonical one because its composites with the product projections are required to be the
truncation maps.

This is `Stacks.Cohomology.AcyclicCover.isIso_to_isDerivedLimit_truncGETower_of_acyclic`, Tag
0D6P with `d = 0`, at the class of affine objects of the small étale site: that class has enough
objects by `AlgebraicGeometry.SmallEtale.hasEnoughObjects_isAffine`, and the cohomology sheaves
of `E` are acyclic over every member of it by
`AlgebraicGeometry.SmallEtale.isZero_rightDerived_evaluation_of_isQuasicoherentOnSite`. -/
theorem isIso_to_isDerivedLimit_truncGETower_of_isQuasicoherentOnSite
    (E : DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS)))
    (hE : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheaf B S hS)) q).obj E).IsQuasicoherentOnSite)
    [HasProduct fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
      (SheafOfModules.{u} (structureSheaf B S hS)) E).obj ⟨n⟩]
    (L : DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS)))
    (c : E ⟶ L)
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
      (SheafOfModules.{u} (structureSheaf B S hS)) E).obj ⟨n⟩)
    (δ : (∏ᶜ fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
      (SheafOfModules.{u} (structureSheaf B S hS)) E).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧)
    (hL : Triangle.mk p (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
        (SheafOfModules.{u} (structureSheaf B S hS)) E).obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
          (SheafOfModules.{u} (structureSheaf B S hS)) E).obj ⟨n⟩) (n + 1) ≫
          (Stacks.DerivedLimit.truncGETower
            (SheafOfModules.{u} (structureSheaf B S hS)) E).map
              (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS))))
    (hc : ∀ n : ℕ, c ≫ p ≫ Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
      (SheafOfModules.{u} (structureSheaf B S hS)) E).obj ⟨n⟩) n =
        (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) :
    IsIso c :=
  Stacks.Cohomology.AcyclicCover.isIso_to_isDerivedLimit_truncGETower_of_acyclic
    (structureSheaf B S hS) E (SmallEtale.IsAffine B S hS)
    (SmallEtale.hasEnoughObjects_isAffine B S hS)
    (fun V hV r hr m =>
      isZero_rightDerived_evaluation_of_isQuasicoherentOnSite B S hS _ (hE m) V hV r hr)
    L c p δ hL hc

/-- **[Stacks, Tag 0D6S] at `ε`, as a derived limit.**  An object of `D(S_étale, 𝒪)` all of whose
cohomology sheaves are quasi-coherent on the site *is* a derived limit of the tower
`n ↦ τ_{≥ -n} E` of its canonical truncations from below.

This repackages `isIso_to_isDerivedLimit_truncGETower_of_isQuasicoherentOnSite` in the shape the
limit arguments consume, exactly as
`AlgebraicGeometry.Space.isDerivedLimit_truncGETower_modules` does for an algebraic space. -/
theorem isDerivedLimit_truncGETower
    (E : DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS)))
    (hE : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheaf B S hS)) q).obj E).IsQuasicoherentOnSite) :
    IsDerivedLimit (Stacks.DerivedLimit.truncGETower
      (SheafOfModules.{u} (structureSheaf B S hS)) E) E := by
  obtain ⟨δ, hδ⟩ := Stacks.InverseSystem.exists_distTriang_milnor_of_isIso
    (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} (structureSheaf B S hS)) E)
    (fun n : ℕ ↦ (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E)
    (fun n ↦ Stacks.Cohomology.HypercohomologyEdge.truncGEπ_comp_truncGETower_map E _)
    (fun L c p d hL hc ↦
      isIso_to_isDerivedLimit_truncGETower_of_isQuasicoherentOnSite B S hS E hE L c p d hL hc)
  exact ⟨_, δ, hδ⟩

end AlgebraicGeometry.SmallEtale

end
