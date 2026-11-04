module

public import StacksFrontier.AlgebraicGeometry.DeRham.HigherDirectImageDifferentialAffineLocal
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.SmoothOfRelativeDimension
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive

/-!
# The top de Rham differential on higher direct images, from affine bases

In the situation of relative Poincaré duality ([Stacks, Tag 0G8G]) the map
`d : R^n f_*Ω^{n-1}_{X/S} ⟶ R^n f_*Ω^n_{X/S}` of [Stacks, Tag 0G8J] is affine-local on `S`: it
vanishes as soon as, for every ring `A` and every proper, surjective morphism `Y ⟶ Spec A` smooth
of relative dimension `n`, the de Rham differential `Ω^{n-1}_{Y/A} ⟶ Ω^n_{Y/A}` induces zero on
`H^n(Y, -)`. The restrictions `f⁻¹(V) ⟶ Spec Γ(S, V)` of `f` to affine opens of `S` are such
morphisms.

## Main results

* `AlgebraicGeometry.Scheme.Hom.higherDirectImage_map_deRham_d_top_eq_zero_of_affine`.
* `AlgebraicGeometry.RelativeDualitySituation.surjective`: the morphism of the situation is
  surjective.
* `AlgebraicGeometry.RelativeDualitySituation.higherDirectImage_map_deRham_d_eq_zero_of_affine`:
  the reduction of [Stacks, Tag 0G8J] to affine bases.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.Leray (sectionsFunctor)

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The restriction `f⁻¹(V) ⟶ Spec Γ(S, V)` of a morphism smooth of relative dimension `n` to
an affine open of the base is smooth of relative dimension `n`. -/
theorem smoothOfRelativeDimension_restrictAffine (n : ℕ) [SmoothOfRelativeDimension n f]
    {V : S.Opens} (hV : IsAffineOpen V) :
    SmoothOfRelativeDimension n (f.restrictAffine hV) := by
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := n)
  have : SmoothOfRelativeDimension n (f ∣_ V) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension n)
      (isPullback_morphismRestrict f V).flip inferInstance
  exact inferInstanceAs (SmoothOfRelativeDimension (n + 0) (f ∣_ V ≫ hV.isoSpec.hom))

/-- The restriction `f⁻¹(V) ⟶ Spec Γ(S, V)` of a surjective morphism to an affine open of the
base is surjective. -/
theorem surjective_restrictAffine [Surjective f] {V : S.Opens} (hV : IsAffineOpen V) :
    Surjective (f.restrictAffine hV) := by
  have : Surjective (f ∣_ V) := IsZariskiLocalAtTarget.restrict ‹_› V
  infer_instance

/-- **The top de Rham differential on higher direct images, from affine bases.** Let
`f : X ⟶ S` be proper, surjective and smooth of relative dimension `n`. If for every ring `A`
and every proper surjective `g : Y ⟶ Spec A` smooth of relative dimension `n` the differential
`Ω^{n-1}_{Y/A} ⟶ Ω^n_{Y/A}` induces zero on `H^n(Y, -)`, then
`d : R^n f_*Ω^{n-1}_{X/S} ⟶ R^n f_*Ω^n_{X/S}` is zero. -/
theorem higherDirectImage_map_deRham_d_top_eq_zero_of_affine (n : ℕ) [IsProper f]
    [SmoothOfRelativeDimension n f] [Surjective f]
    (hAff : ∀ (A : Type u) [CommRing A] (Y : Scheme.{u}) (g : Y ⟶ Spec (.of A)) [IsProper g]
      [SmoothOfRelativeDimension n g] [Surjective g],
      ((sectionsFunctor Y.carrier ⊤).rightDerived n).map
        ((SheafOfModules.toSheaf _).map (g.deRhamComplex.d (n - 1) n)) = 0) :
    (Stacks.Cohomology.AbelianSheaf.higherDirectImage f.base n).map
      ((SheafOfModules.toSheaf _).map (f.deRhamComplex.d (n - 1) n)) = 0 := by
  cases n with
  | zero =>
    rw [HomologicalComplex.shape _ _ _ (by simp), Functor.map_zero]
    unfold Stacks.Cohomology.AbelianSheaf.higherDirectImage
    have : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).Additive :=
      { map_add := by intros; rfl }
    exact Functor.map_zero _ _ _
  | succ e =>
    refine higherDirectImage_map_deRham_d_eq_zero_of_affine f e (e + 1) fun V hV => ?_
    have := f.smoothOfRelativeDimension_restrictAffine (e + 1) hV
    have := f.surjective_restrictAffine hV
    exact hAff Γ(S, V) _ (f.restrictAffine hV)

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.RelativeDualitySituation

variable (D : RelativeDualitySituation.{u})

/-- The morphism of the relative duality situation is surjective: every fibre has a point. -/
theorem surjective : Surjective D.f := by
  refine ⟨fun s => ?_⟩
  obtain ⟨x⟩ := D.fiber_nonempty s
  have h : D.f.fiberι s x ∈ D.f ⁻¹' {s} := D.f.range_fiberι s ▸ Set.mem_range_self x
  exact ⟨_, h⟩

/-- **The map `d : R^n f_*Ω^{n-1}_{X/S} ⟶ R^n f_*Ω^n_{X/S}` of [Stacks, Tag 0G8J], from affine
bases**: it is zero as soon as the top de Rham differential vanishes on top cohomology for every
proper surjective morphism to an affine scheme smooth of relative dimension `n`. -/
theorem higherDirectImage_map_deRham_d_eq_zero_of_affine
    (hAff : ∀ (A : Type u) [CommRing A] (Y : Scheme.{u}) (g : Y ⟶ Spec (.of A)) [IsProper g]
      [SmoothOfRelativeDimension D.n g] [Surjective g],
      ((sectionsFunctor Y.carrier ⊤).rightDerived D.n).map
        ((SheafOfModules.toSheaf _).map (g.deRhamComplex.d (D.n - 1) D.n)) = 0) :
    (Stacks.Cohomology.AbelianSheaf.higherDirectImage D.f.base D.n).map
      ((SheafOfModules.toSheaf _).map (D.f.deRhamComplex.d (D.n - 1) D.n)) = 0 :=
  have := D.surjective
  D.f.higherDirectImage_map_deRham_d_top_eq_zero_of_affine D.n hAff

end AlgebraicGeometry.RelativeDualitySituation
