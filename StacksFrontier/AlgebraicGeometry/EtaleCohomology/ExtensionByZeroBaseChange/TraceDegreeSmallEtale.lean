module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.TraceDegree
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence

/-!
# The trace of a finite étale morphism of constant degree, on Mathlib's small étale site

Let `f : T ⟶ S` be a finite étale morphism of schemes which is finite locally free of rank `d`,
and let `G` be an abelian sheaf on `S_étale`. The unit `G ⟶ f_* f^{-1} G` of the adjunction
`f^{-1} ⊣ f_*` has a left inverse up to `d`: there is `r : f_* f^{-1} G ⟶ G` whose composite
with the unit is multiplication by `d`. This is Section 03SH; the map `r` is the trace of
Proposition 03SE, transported from the size-bounded small étale site of Tag 021B, on which it is
`AlgebraicGeometry.unit_comp_abelianTrace_eq_nsmul`.

## Main results

* `Stacks.EtaleCohomology.exists_unit_comp_eq_nsmul_of_finiteEtale`.

## Implementation notes

The transport goes through `AlgebraicGeometry.SmallEtale.sheafEquiv` and the two comparisons of
`AlgebraicGeometry.SmallEtale.restrictionPullbackBaseChangeIso` (inverse images) and
`AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso` (direct images), which are
mates (`AlgebraicGeometry.SmallEtale.mateEquiv_restrictionPullbackBaseChange`); the mate relation
is exactly what carries the unit of one adjunction to the unit of the other
(`CategoryTheory.unit_mateEquiv`).

## References

* [Stacks Project, Tag 03SE](https://stacks.math.columbia.edu/tag/03SE)
* [Stacks Project, Tag 03SH](https://stacks.math.columbia.edu/tag/03SH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- **The unit of `f^{-1} ⊣ f_*` for a finite étale `f` of degree `d` has a left inverse up to
`d`** (the trace, Section 03SH): there is `r : f_* f^{-1} G ⟶ G` with `r ∘ unit = d`. -/
theorem exists_unit_comp_eq_nsmul_of_finiteEtale {S T : Scheme.{u}} (f : T ⟶ S) [IsFinite f]
    [Etale f] (d : ℕ) [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d]
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ∃ r : (etaleAbelianDirectImage.{u, 0} f).obj ((etaleAbelianInverseImage.{u, 0} f).obj G) ⟶ G,
      (etaleAbelianInverseImageDirectImageAdj.{u, 0} f).unit.app G ≫ r = d • 𝟙 G := by
  let S₀ : Set Scheme.{u} := {S, T}
  let B := BigEtaleSite.ofSet S₀
  have hS : B.Contains S := BigEtaleSite.contains_ofSet S₀ (by simp [S₀])
  have hT : B.Contains T := BigEtaleSite.contains_ofSet S₀ (by simp [S₀])
  let f₀ : B.obj T hT ⟶ B.obj S hS := ObjectProperty.homMk f
  have : IsFinite (B.inclusion.map f₀) := ‹IsFinite f›
  have : Etale (B.inclusion.map f₀) := ‹Etale f›
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (B.inclusion.map f₀) d :=
    ‹Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d›
  let A := AddCommGrpCat.{u + 1}
  let adjU := etaleAbelianInverseImageDirectImageAdj.{u, 0} f
  let adjB := smallEtalePostcomposePushforwardAdjunction B f₀ A
  let ρS := (SmallEtale.toEtaleSite B S hS).sheafPushforwardContinuous A
    (SmallEtale.topology B S hS) S.smallEtaleTopology
  have hff : ρS.FullyFaithful :=
    (SmallEtale.sheafEquiv B S hS A).fullyFaithfulInverse
  let α := SmallEtale.restrictionPullbackBaseChangeIso B A f₀ adjU adjB
  let β := SmallEtale.toEtaleSitePushforwardBaseChangeIso B f₀ A
  have hmate := SmallEtale.mateEquiv_restrictionPullbackBaseChange B A f₀ adjU adjB
  have hunit := unit_mateEquiv adjU adjB
    (SmallEtale.restrictionPullbackBaseChange B A f₀ adjU adjB) G
  have hβ : (mateEquiv adjU adjB (SmallEtale.restrictionPullbackBaseChange B A f₀ adjU adjB)).app
      ((etaleAbelianInverseImage.{u, 0} f).obj G) =
      β.hom.app ((etaleAbelianInverseImage.{u, 0} f).obj G) :=
    congrArg (fun t ↦ t.app ((etaleAbelianInverseImage.{u, 0} f).obj G)) hmate
  rw [hβ] at hunit
  let rB := (abelianTrace B S hS (SmallEtale.ofEtaleHom B f₀)).app (ρS.obj G)
  have htr := unit_comp_abelianTrace_eq_nsmul B f₀ d (ρS.obj G)
  have hαα : (SmallEtale.restrictionPullbackBaseChange B A f₀ adjU adjB).app G ≫ α.inv.app G =
      𝟙 _ := α.hom_inv_id_app G
  have h1 : ρS.map (adjU.unit.app G) ≫ β.hom.app ((etaleAbelianInverseImage.{u, 0} f).obj G) ≫
      (B.smallPushforward f₀ A).map (α.inv.app G) ≫ rB = d • 𝟙 _ := by
    rw [reassoc_of% hunit, ← Functor.map_comp_assoc, hαα]
    simpa using htr
  refine ⟨hff.preimage (β.hom.app ((etaleAbelianInverseImage.{u, 0} f).obj G) ≫
    (B.smallPushforward f₀ A).map (α.inv.app G) ≫ rB), hff.map_injective ?_⟩
  rw [Functor.map_comp, hff.map_preimage, h1, Functor.map_nsmul]
  simp

end Stacks.EtaleCohomology

end
