module

public import StacksFrontier.AlgebraicGeometry.Flatness.GrothendieckExistence.LevelCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Quasi-compact opens in derived existence

In Situation [Stacks, Tag 0DIB] let `U ⊆ X` be a quasi-compact open. Then `U` is flat,
quasi-compact and quasi-separated over `A = lim Aₙ`, and `Uₙ = U ∩ Xₙ` — the inverse image of `U`
in `Xₙ` — is the base change of `U` along `Spec Aₙ ⟶ Spec A`. These are the inputs needed to
apply flat base change for derived global sections to `U` in [Stacks, Tag 0DIF].

## Main definitions

* `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.levelOpen`: the open
  `Uₙ = U ∩ Xₙ` of `Xₙ`.
* `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.openStructure`: the
  structure morphism `U ⟶ Spec A`.
* `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.levelOpenStructure`: the
  structure morphism `Uₙ ⟶ Spec Aₙ`.
* `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.levelOpenInclusion`: the
  closed immersion `Uₙ ⟶ U`.

## Main results

* `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.isPullback_levelOpen`:
  `Uₙ = U ×_{Spec A} Spec Aₙ`.

## References

* [Stacks Project, Tag 0DIF](https://stacks.math.columbia.edu/tag/0DIF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation

variable (S : DerivedExistenceSituation.{u}) (U : S.X.left.Opens) (n : ℕ)

/-- `Uₙ = U ∩ Xₙ`: the inverse image of an open `U` of `X` in the closed subscheme `Xₙ`. -/
abbrev levelOpen : (schemeAt S.system S.X n).Opens :=
  (schemeProjection S.system S.X n) ⁻¹ᵁ U

/-- The structure morphism `U ⟶ Spec A` of an open of `X`. -/
abbrev openStructure : (U : Scheme.{u}) ⟶ limitBase S.system :=
  U.ι ≫ S.X.hom

/-- The structure morphism `Uₙ ⟶ Spec Aₙ`. -/
abbrev levelOpenStructure : (S.levelOpen U n : Scheme.{u}) ⟶ baseAt S.system n :=
  (S.levelOpen U n).ι ≫ levelStructure S.system S.X n

/-- The inclusion `Uₙ ⟶ U`, the restriction of `Xₙ ⟶ X` to `U`. -/
abbrev levelOpenInclusion : (S.levelOpen U n : Scheme.{u}) ⟶ U :=
  schemeProjection S.system S.X n ∣_ U

/-- The inclusion `Uₙ ⟶ U` is a closed immersion. -/
instance : IsClosedImmersion (S.levelOpenInclusion U n) := by
  have := S.closedSchemeProjection n
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_morphismRestrict (schemeProjection S.system S.X n) U).flip inferInstance

/-- **`Uₙ = U ×_{Spec A} Spec Aₙ`.** The square formed by `Uₙ ⟶ U`, the two structure morphisms
and `Spec Aₙ ⟶ Spec A` is cartesian: it is the restriction to `U` of the cartesian square
defining `Xₙ`. -/
theorem isPullback_levelOpen :
    IsPullback (S.levelOpenInclusion U n) (S.levelOpenStructure U n) (S.openStructure U)
      (Spec.map (CommRingCat.ofHom (limit.π S.system (op n)).hom)) :=
  (isPullback_morphismRestrict (schemeProjection S.system S.X n) U).paste_vert
    (IsPullback.of_hasPullback S.X.hom (baseProjection S.system n))

/-- The commutativity of the square of `isPullback_levelOpen`. -/
theorem levelOpenInclusion_comp_openStructure :
    S.levelOpenInclusion U n ≫ S.openStructure U =
      S.levelOpenStructure U n ≫
        Spec.map (CommRingCat.ofHom (limit.π S.system (op n)).hom) :=
  (S.isPullback_levelOpen U n).w

/-- An open `U` of `X` is flat over `A`. -/
instance : Flat (S.openStructure U) := by
  have := S.flat
  infer_instance

/-- An open `U` of `X` is quasi-separated over `A`. -/
instance : QuasiSeparated (S.openStructure U) := by
  have := S.proper
  infer_instance

/-- A quasi-compact open of `X` is quasi-compact over `A`. -/
theorem quasiCompact_openStructure (hU : IsCompact (U : Set S.X.left)) :
    QuasiCompact (S.openStructure U) := by
  have : CompactSpace U := isCompact_iff_compactSpace.1 hU
  infer_instance

end AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation

end
