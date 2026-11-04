module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.TwoOutOfThree
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.AbsoluteUniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Twist

/-!
# The relative Frobenius is a finite dominant universal homeomorphism

For a scheme `X` over a scheme `S` of positive prime characteristic, the relative Frobenius from
`X` to its Frobenius twist is a universal homeomorphism, is integral, and induces purely
inseparable extensions of residue fields. When `X` is locally of finite type over `S` it is
moreover finite, and it is always dominant. Consequently a reduced Frobenius twist of a variety
over a field is again a variety.

## Main results

* `AlgebraicGeometry.relativeFrobenius_universalHomeomorphism` states that the relative
  Frobenius is a universal homeomorphism.
* `AlgebraicGeometry.relativeFrobenius_isIntegralHom` states that it is integral.
* `AlgebraicGeometry.relativeFrobenius_residueFieldMap_isPurelyInseparable` states that its
  induced maps on residue fields are purely inseparable.
* `AlgebraicGeometry.relativeFrobenius_isFinite` gives finiteness of the relative Frobenius of a
  scheme locally of finite type over the base.
* `AlgebraicGeometry.relativeFrobenius_isDominant` gives dominance.
* `AlgebraicGeometry.isVariety_frobeniusTwist_of_isReduced` shows that a reduced Frobenius twist
  of a variety is a variety.

## Implementation notes

The universal-homeomorphism and integrality conclusions are instances on the underlying scheme
morphism of the relative Frobenius in `Over S`, and the residue-field conclusion uses its
canonical residue-field map at each point. Both are obtained from the absolute Frobenius of the
base by the two-out-of-three property: the first projection of the Frobenius twist is a base
change of the absolute Frobenius of `S`, and composing with it gives the absolute Frobenius of
`X`.

Neither finiteness nor dominance requires the Frobenius twist to be reduced, so those two
statements apply more generally than to varieties. For the variety statement the characteristic
hypothesis on `k` supplies the characteristic hypothesis needed to form the absolute Frobenius
of `Spec k`, and reducedness of the twist is the only missing ingredient, since the relative
Frobenius is a homeomorphism and the remaining conditions are inherited from the base change.

## References

* [Stacks Project, Tag 0CCB](https://stacks.math.columbia.edu/tag/0CCB)
* [Stacks Project, Tag 0CCD](https://stacks.math.columbia.edu/tag/0CCD)
* [Stacks Project, Tag 0CCF](https://stacks.math.columbia.edu/tag/0CCF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-- The relative Frobenius is a universal homeomorphism. -/
@[stacks 0CCB, sga "5 XV 1.Proposition2" "a) univ. homeo"]
instance relativeFrobenius_universalHomeomorphism
    (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p)
    (X : Over S) :
    UniversalHomeomorphism (relativeFrobenius S p hS X).left := by
  apply (universalHomeomorphism_hasTwoOutOfThreeProperty
    |>.toHasOfPostcompProperty).of_postcomp
    (relativeFrobenius S p hS X).left (pullback.fst X.hom (absoluteFrobenius S p hS))
  · constructor
    exact (MorphismProperty.universally_isStableUnderBaseChange
      (topologically @IsHomeomorph)).of_isPullback
        (IsPullback.of_hasPullback X.hom (absoluteFrobenius S p hS)).flip
        (absoluteFrobenius_universalHomeomorphism S p hS).universally_isHomeomorph
  · rw [relativeFrobenius_fst]
    infer_instance

/-- The relative Frobenius is integral. -/
@[stacks 0CCB, sga "5 XV 1.Proposition2" "a) integral", sga "3 VIIA 7.4.2" "more general"]
instance relativeFrobenius_isIntegralHom
    (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p)
    (X : Over S) :
    IsIntegralHom (relativeFrobenius S p hS X).left :=
  (universalHomeomorphism_iff_integral_universallyInjective_surjective _).mp
    (relativeFrobenius_universalHomeomorphism S p hS X) |>.1

/-- Every residue-field extension induced by the relative Frobenius is purely inseparable. -/
@[stacks 0CCB, sga "5 XV 1.Proposition2" "a) radicial"]
theorem relativeFrobenius_residueFieldMap_isPurelyInseparable
    (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p)
    (X : Over S) (x : X.left) :
    (((relativeFrobenius S p hS X).left).residueFieldMap x).hom.IsPurelyInseparable := by
  let f := (relativeFrobenius S p hS X).left
  have h := ((AlgebraicGeometry.tfae_universallyInjective f).out 1 3).mp
    (((universalHomeomorphism_iff_integral_universallyInjective_surjective f).mp
      (relativeFrobenius_universalHomeomorphism S p hS X)).2.1)
  exact h.2 x

/-- **Stacks Project, Tag 0CCD.** The relative Frobenius of an `S`-scheme locally of finite type
over `S` is finite. -/
@[stacks 0CCD, sga "5 XV 1.Proposition2" "Clause a), special case"]
instance relativeFrobenius_isFinite (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (X : Over S) [LocallyOfFiniteType X.hom] :
    IsFinite (relativeFrobenius S p hS X).left :=
  (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).2 ⟨inferInstance,
    @locallyOfFiniteType_of_comp _ _ _ _ ((frobeniusTwist S p hS).obj X).hom
      (by rw [(relativeFrobenius S p hS X).w]; infer_instance)⟩

add_to_stacks 0CCF "finite_dominant" AlgebraicGeometry.relativeFrobenius_isFinite

/-- The relative Frobenius is dominant over a base of prime characteristic. -/
@[stacks 0CCF "finite_dominant"]
instance relativeFrobenius_isDominant (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (X : Over S) :
    IsDominant (relativeFrobenius S p hS X).left :=
  ⟨((relativeFrobenius_universalHomeomorphism S p hS X).universally_isHomeomorph
    _ _ _ IsPullback.of_id_snd).surjective.denseRange⟩

/-- A reduced Frobenius twist of a variety over a field is a variety. -/
@[stacks 0CCF "twist_variety"]
theorem isVariety_frobeniusTwist_of_isReduced
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsVariety k f] (p : ℕ) [Fact p.Prime] [CharP k p] :
    let hchar : IsInCharacteristic (Spec (.of k)) p := by
      let φ : k →+* Γ(Spec (.of k), ⊤) := (Scheme.ΓSpecIso (.of k)).inv.hom
      change (p : Γ(Spec (.of k), ⊤)) = 0
      rw [← map_natCast φ, CharP.cast_eq_zero k p]
      exact map_zero φ
    IsReduced (((frobeniusTwist (Spec (.of k)) p hchar).obj (Over.mk f)).left) →
      IsVariety k (((frobeniusTwist (Spec (.of k)) p hchar).obj (Over.mk f)).hom) := by
  intro hchar hred
  let S : Scheme.{u} := Spec (.of k)
  let U : Over S := Over.mk f
  let T : Over S := (frobeniusTwist S p hchar).obj U
  let r := relativeFrobenius S p hchar U
  have : IsIntegral T.left := (isIntegral_iff_irreducibleSpace_and_isReduced T.left).mpr
    ⟨(IsHomeomorph.homeomorph r.left
        ((relativeFrobenius_universalHomeomorphism S p hchar U).universally_isHomeomorph
          _ _ _ IsPullback.of_id_snd)).irreducibleSpace_iff.mp
      ((isIntegral_iff_irreducibleSpace_and_isReduced U.left).mp inferInstance).1, hred⟩
  have : IsSeparated T.hom := by dsimp [T, U, S]; infer_instance
  have : LocallyOfFiniteType T.hom := by dsimp [T, U, S]; infer_instance
  have : QuasiCompact T.hom := by dsimp [T, U, S]; infer_instance
  exact {}

end AlgebraicGeometry

end
