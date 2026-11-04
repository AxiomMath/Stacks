module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.StalkSpecialization
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingRegular
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularAtGeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularCompletionClosedFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionFunction
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
public import StacksFrontier.RingTheory.RegularRing.Defs
public import StacksFrontier.RingTheory.RegularRing.GlobalDimension

/-!
# Regularity of a proper algebraic space and of its completed base change

Let `(A, 𝔪)` be a Noetherian local ring, let `X` be a decent algebraic space proper over
`Spec A` and let `Y = X ×_{Spec A} Spec A^` be its base change to the `𝔪`-adic completion.
Then `X` is regular if and only if `Y` is.

One direction is pointwise descent along the flat projection `Y ⟶ X`, which is surjective on
points because `A → A^` is faithfully flat. For the other direction the point is that every
point of `Y` is a generalization of a point of the closed fibre: properness makes the image of
a closed subset of `|Y|` closed in `|Spec A^|`, and every point of `|Spec A^|` specializes to
the closed point, so the closure of a point of `|Y|` already meets the closed fibre. Over the
closed fibre regularity is unchanged by the base change, and regularity propagates from a
point to its generalizations because the local ring at a generalization is a localization of
the local ring at the point, and a localization of a regular local ring is regular.

## Main results

* `AlgebraicGeometry.isRegularLocalRing_stalk_of_specializes`: the local ring of a scheme at a
  generalization of a point with regular local ring is regular.
* `AlgebraicGeometry.Space.isRegularAt_of_specializes`: regularity of a decent algebraic space
  at a point passes to the generalizations of that point.
* `AlgebraicGeometry.Space.hasEtaleLocalProperty_isRegular_iff_forall_isRegularAt`: a locally
  Noetherian algebraic space is regular exactly when it is regular at every point.
* `AlgebraicGeometry.Space.exists_specializes_mem_closedFibre_of_isProper`: every point of the
  completed base change of a proper algebraic space specializes to a point of the closed
  fibre.
* `AlgebraicGeometry.Space.hasEtaleLocalProperty_isRegular_completionSpace_iff_of_isProper`:
  **Stacks 0BHQ, part (3)**.

## Implementation notes

That the local ring at a generalization is a localization is
`Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes`; that a localization of a
regular local ring at a prime is again regular is Serre's theorem in the form
`IsLocalRing.isRegularRing_tfae`, whose third clause is Mathlib's `IsRegularRing`.

Lifting a specialization of points of a decent algebraic space to an étale scheme chart is
Stacks 03IL, `AlgebraicGeometry.Space.exists_specialization_lift_of_isDecentSpace`; the
lifted specialization is read on the chart scheme through the homeomorphism
`AlgebraicGeometry.Space.schemePointsHomeomorph` of clause (1) of Stacks 03BX.

Properness enters only through its universally closed conjunct, applied to the base change
along `Spec A^ ⟶ Spec A` itself. That conjunct is stated for the first projection of the
pullback, so the projection `Y ⟶ Spec A^` is identified with it by the pullback symmetry,
whose map on points is closed because it is an isomorphism.

## References

* [Stacks Project, Tag 0BHQ](https://stacks.math.columbia.edu/tag/0BHQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The local ring at a generalization of a regular point is regular.** If `y ⤳ x` and the
local ring of a scheme at `x` is a regular local ring, then so is its local ring at `y`: the
latter is a localization of the former at a prime, and all localizations of a regular local
ring at primes are regular. -/
theorem isRegularLocalRing_stalk_of_specializes {X : Scheme.{u}} {x y : X} (h : y ⤳ x)
    (hx : IsRegularLocalRing (X.presheaf.stalk x)) :
    IsRegularLocalRing (X.presheaf.stalk y) := by
  let : Algebra (X.presheaf.stalk x) (X.presheaf.stalk y) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  have : IsRegularRing (X.presheaf.stalk x) :=
    ((IsLocalRing.isRegularRing_tfae (R := X.presheaf.stalk x)).out 1 3).mp hx
  have := Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes h
  exact IsRegularRing.isRegularLocalRing_of_isLocalization
    ((IsLocalRing.maximalIdeal (X.presheaf.stalk y)).under (X.presheaf.stalk x))
    (X.presheaf.stalk y)

namespace Space

attribute [local instance] pointTopology

/-! ### Regularity at the generalizations of a point -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Regularity propagates to generalizations.** If a decent algebraic space is regular at a
point `x` and `x' ⤳ x`, then it is regular at `x'`. The specialization lifts to an étale
scheme chart by Stacks 03IL, and on the chart the local ring at the lifted generalization is a
localization of a regular local ring. -/
theorem isRegularAt_of_specializes {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hdec : IsDecentSpace B S hS F)
    {x x' : points B S hS F} (hs : x' ⤳ x) (hx : IsRegularAt B S hS F x) :
    IsRegularAt B S hS F x' := by
  obtain ⟨U, a, hsurj, haE⟩ := hF.exists_atlas
  obtain ⟨u, hu⟩ :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS F hF U a).mp hsurj x
  obtain ⟨u', hspec, hu'⟩ :=
    exists_specialization_lift_of_isDecentSpace B S hS F hF hdec x x' hs U a haE u hu
  obtain ⟨p, rfl⟩ := Quot.exists_rep u
  obtain ⟨p', rfl⟩ := Quot.exists_rep u'
  exact (isRegularAt_iff_exists_etale_chart B S hS F hF x').mpr
    ⟨U, a, haE, p', hu', isRegularLocalRing_stalk_of_specializes
      (hspec.map (schemePointsHomeomorph B S hS U).continuous) (hx U a haE p hu)⟩

/-! ### Regularity as a pointwise condition -/

/-- **A locally Noetherian algebraic space is regular exactly when it is regular at every
point.** Regularity of the space is the étale-local property `AlgebraicGeometry.IsRegular` of
its étale scheme charts, and for a locally Noetherian scheme that property is regularity of
all of its local rings. -/
theorem hasEtaleLocalProperty_isRegular_iff_forall_isRegularAt
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hN : HasEtaleLocalProperty B S hS F (fun T : Scheme.{u} ↦ IsLocallyNoetherian T)) :
    HasEtaleLocalProperty B S hS F (fun T : Scheme.{u} ↦ IsRegular T) ↔
      ∀ x : points B S hS F, IsRegularAt B S hS F x := by
  constructor
  · intro h x U a haE p hp
    have hU : IsRegular ((BigFppfOver.toScheme B S hS).obj U) :=
      (exists_atlas_iff_forall_etale B S hS F
        (fun T : Scheme.{u} ↦ IsRegular T) hF).mp h U a haE
    have hstalk : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) ∧
        ∀ z : (BigFppfOver.toScheme B S hS).obj U,
          IsRegularLocalRing (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk z) :=
      ((isRegular_tfae ((BigFppfOver.toScheme B S hS).obj U)).out 1 2).mp hU
    exact hstalk.2 _
  · intro h
    refine (isRegular_iff_etaleLocalRings_regular B S hS F hF hN).mpr fun xbar ↦ ?_
    have hall : ∀ xb : GeometricPoint B S hS F, xb.LiesOver xbar.image →
        IsRegularLocalRing (etaleLocalRing B S hS F xb) :=
      ((isRegularAt_tfae B S hS F hF xbar.image).out 1 2).mp (h xbar.image)
    exact hall xbar rfl

end Space

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The closed fibre of the completed base change -/

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
variable (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
variable (hAc : B.Contains (Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))))
variable {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
variable (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))

omit [IsNoetherianRing A] in
/-- For a proper `X` the projection `X ×_{Spec A} Spec A^ ⟶ Spec A^` is closed on points: it
is the base change of `X ⟶ Spec A` along `Spec A^ ⟶ Spec A`, up to the pullback symmetry,
whose map on points is a closed map because it is an isomorphism. -/
theorem isClosedMorphism_completionSpace_snd_of_isProper
    (hproper : IsProper B (Spec (.of A)) hA f) :
    IsClosedMorphism B (Spec (.of A)) hA
      (pullback.snd f (completionBaseMap A B hA hAc)) := by
  have hbase := hproper.2.2 (yoneda.obj (completionBase A B hA hAc))
    (isAlgebraicSpace_yoneda B (Spec (.of A)) hA (completionBase A B hA hAc))
    (completionBaseMap A B hA hAc)
  have hcomp := IsClosedMap.comp hbase (isClosedMap_pointsMap_of_isIso B (Spec (.of A)) hA
    (pullbackSymmetry f (completionBaseMap A B hA hAc)).hom)
  rwa [← pointsMap_comp, pullbackSymmetry_hom_comp_fst] at hcomp

/-- **Every point of the completed base change of a proper space specializes to the closed
fibre.** Properness makes the image in `|Spec A^|` of the closure of a point `y` closed, and
every point of `|Spec A^|` specializes to the closed point, so that closure contains a point
lying over the closed point of `Spec A^`. -/
theorem exists_specializes_mem_closedFibre_of_isProper
    (hproper : IsProper B (Spec (.of A)) hA f)
    (y : points B (Spec (.of A)) hA (completionSpace A B hA hAc f)) :
    ∃ y₀ : points B (Spec (.of A)) hA (completionSpace A B hA hAc f), y ⤳ y₀ ∧
      pointsToScheme B (Spec (.of A)) hA (completionBase A B hA hAc)
          (pointsMap B (Spec (.of A)) hA (completionSpace A B hA hAc f)
            (pullback.snd f (completionBaseMap A B hA hAc)) y₀) =
        (⟨IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A),
          inferInstance⟩ :
          PrimeSpectrum (AdicCompletion (IsLocalRing.maximalIdeal A) A)) := by
  set φ := pointsMap B (Spec (.of A)) hA (completionSpace A B hA hAc f)
    (pullback.snd f (completionBaseMap A B hA hAc))
  set e := schemePointsHomeomorph B (Spec (.of A)) hA (completionBase A B hA hAc)
  set c : PrimeSpectrum (AdicCompletion (IsLocalRing.maximalIdeal A) A) :=
    ⟨IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A), inferInstance⟩
  have hspec : φ y ⤳ e.symm c := by
    have h : e (φ y) ⤳ c := IsLocalRing.specializes_closedPoint (e (φ y))
    have := h.map e.symm.continuous
    rwa [e.symm_apply_apply] at this
  have hclosed : IsClosed (φ '' closure {y}) :=
    isClosedMorphism_completionSpace_snd_of_isProper A B hA hAc f hproper _ isClosed_closure
  obtain ⟨y₀, hy₀, hφy₀⟩ := hspec.mem_closed hclosed ⟨y, subset_closure rfl, rfl⟩
  exact ⟨y₀, specializes_iff_mem_closure.mpr hy₀,
    (congrArg e hφy₀).trans (e.apply_symm_apply c)⟩

/-! ### Part (3) of Stacks 0BHQ -/

/-- **Stacks 0BHQ, part (3).** Let `(A, 𝔪)` be a Noetherian local ring and let `X` be a decent
algebraic space proper over `Spec A`. Then `X` is regular if and only if its base change
`Y = X ×_{Spec A} Spec A^` to the `𝔪`-adic completion of `A` is regular. -/
@[stacks 0BHQ "part (3)"]
theorem hasEtaleLocalProperty_isRegular_completionSpace_iff_of_isProper
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (hXdec : IsDecentSpace B (Spec (.of A)) hA X)
    (hproper : IsProper B (Spec (.of A)) hA f) :
    HasEtaleLocalProperty B (Spec (.of A)) hA X (fun T : Scheme.{u} ↦ IsRegular T) ↔
      HasEtaleLocalProperty B (Spec (.of A)) hA (completionSpace A B hA hAc f)
        (fun T : Scheme.{u} ↦ IsRegular T) := by
  have hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f := hproper.2.1.1
  have hNX := hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType_base
    A B hA f hX hf
  have hNY := hasEtaleLocalProperty_isLocallyNoetherian_completionSpace A B hA hAc f hX hf
  rw [hasEtaleLocalProperty_isRegular_iff_forall_isRegularAt B (Spec (.of A)) hA hX hNX,
    hasEtaleLocalProperty_isRegular_iff_forall_isRegularAt B (Spec (.of A)) hA
      (isAlgebraicSpace_completionSpace A B hA hAc f hX) hNY]
  refine ⟨fun h y ↦ ?_, fun h x ↦ ?_⟩
  · obtain ⟨y₀, hspec, hy₀⟩ :=
      exists_specializes_mem_closedFibre_of_isProper A B hA hAc f hproper y
    exact isRegularAt_of_specializes B (Spec (.of A)) hA
      (isAlgebraicSpace_completionSpace A B hA hAc f hX)
      (isDecentSpace_completionSpace A B hA hAc f hX hXdec) hspec
      ((isRegularAt_completionSpace_iff_of_mem_closedFibre A B hA hAc f hX hf y₀ hy₀).mpr
        (h _))
  · obtain ⟨y, rfl⟩ := isSurjective_completionProjection A B hA hAc f x
    exact isRegularAt_completionSpace_descent A B hA hAc f hX hf y (h y)

end AlgebraicGeometry.Space

end
