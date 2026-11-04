module

public import StacksFrontier.AlgebraicGeometry.RelativeWeakNormalizationAway.Hard

/-!
# The relative weak normalization commutes with localization of the base

Let `A → B` be an algebra inducing a dominant morphism on spectra, let `r` be an element of `A`,
and let `Af` and `Bf` be the localizations of `A` and `B` away from `r`. Writing `B'` for the
relative weak normalization of `A` in `B` of
[Stacks, Tag 0H3J](https://stacks.math.columbia.edu/tag/0H3J), this file proves that the relative
weak normalization of `Af` in `Bf` is the localization of `B'` away from `r`. This is
[Stacks, Tag 0H3K](https://stacks.math.columbia.edu/tag/0H3K).

The statement is in the `IsLocalization.Away` shape rather than as an equality of subalgebras of
`Bf`, because that is the shape
`AlgebraicGeometry.coequifibered_iff_forall_isLocalizationAway` consumes when gluing the affine
charts of a relative weak normalization into a scheme: the presheaf `U ↦ Γ(X, U)'` on the affine
Zariski site of the base is coequifibered precisely because its value on a basic open is the
localization of its value on the open. The same shape is used by Mathlib's
`IsLocalization.Away.integralClosure`, for the same purpose in the relative normalization.

## Main definitions

* `AlgebraicGeometry.relativeWeakNormalizationToLocalization` is the canonical map from the
  relative weak normalization to the relative weak normalization over the localized base.

## Main results

* `AlgebraicGeometry.isLocalizationAway_relativeWeakNormalization`: Stacks 0H3K, for an
  arbitrary compatible algebra structure.
* `AlgebraicGeometry.isLocalizationAway_relativeWeakNormalization'`: the same for the canonical
  algebra structure.

## Implementation notes

Following `IsLocalization.Away.integralClosure`, the algebra structure relating the two relative
weak normalizations is a parameter of the main statement, with the hypothesis that its structure
map is the restriction of `B → Bf`. That makes the statement applicable to whichever structure a
caller has, and `AlgebraicGeometry.relativeWeakNormalizationToLocalization` supplies the
canonical one, the existence of which is the easy inclusion of the tag.

## References

* [Stacks Project, Tag 0H3K](https://stacks.math.columbia.edu/tag/0H3K)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {A B Af Bf : Type u} [CommRing A] [CommRing B] [CommRing Af] [CommRing Bf]
  [Algebra A B] [Algebra A Af] [Algebra Af Bf] [Algebra A Bf] [Algebra B Bf]
  [IsScalarTower A B Bf] [IsScalarTower A Af Bf]

/-- The canonical map from the relative weak normalization of `A` in `B` to the relative weak
normalization of a localization `Af` of `A` in the corresponding localization `Bf` of `B`. Its
existence is the easy inclusion of Stacks 0H3K. -/
def relativeWeakNormalizationToLocalization (r : A) [IsLocalization.Away r Af]
    [IsLocalization.Away (algebraMap A B r) Bf]
    (hdom : IsDominant (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)) :
    relativeWeakNormalization A B →+* relativeWeakNormalization Af Bf where
  toFun b := ⟨algebraMap B Bf (b : B), algebraMap_mem_relativeWeakNormalization r hdom b⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

/-- **Stacks 0H3K.** Formation of the relative weak normalization commutes with localization of
the base: the relative weak normalization of `Af` in `Bf` is the localization away from `r` of
the relative weak normalization of `A` in `B`. -/
theorem isLocalizationAway_relativeWeakNormalization (r : A) [IsLocalization.Away r Af]
    [IsLocalization.Away (algebraMap A B r) Bf]
    (hdom : IsDominant (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op))
    [Algebra (relativeWeakNormalization A B) (relativeWeakNormalization Af Bf)]
    (hmap : ∀ b : relativeWeakNormalization A B,
      ((algebraMap (relativeWeakNormalization A B) (relativeWeakNormalization Af Bf) b :
        relativeWeakNormalization Af Bf) : Bf) = algebraMap B Bf (b : B)) :
    IsLocalization.Away (algebraMap A (relativeWeakNormalization A B) r)
      (relativeWeakNormalization Af Bf) := by
  refine IsLocalization.Away.of_subalgebra r (relativeWeakNormalization A B) _
    (relativeWeakNormalization Af Bf).val.toRingHom (fun x y h => Subtype.ext h) hmap ?_ ?_
  · have he : algebraMap (relativeWeakNormalization A B) (relativeWeakNormalization Af Bf)
        (algebraMap A (relativeWeakNormalization A B) r) =
        algebraMap Af (relativeWeakNormalization Af Bf) (algebraMap A Af r) := by
      apply Subtype.ext
      rw [hmap, show ((algebraMap A (relativeWeakNormalization A B) r :
          relativeWeakNormalization A B) : B) = algebraMap A B r from rfl,
        ← IsScalarTower.algebraMap_apply A B Bf, IsScalarTower.algebraMap_apply A Af Bf]
      rfl
    rw [he]
    exact (IsLocalization.map_units Af
      (⟨r, Submonoid.mem_powers r⟩ : Submonoid.powers r)).map
      (algebraMap Af (relativeWeakNormalization Af Bf))
  · exact exists_pow_mul_mem_relativeWeakNormalization r hdom

/-- **Stacks 0H3K**, for the canonical algebra structure of
`AlgebraicGeometry.relativeWeakNormalizationToLocalization`. -/
theorem isLocalizationAway_relativeWeakNormalization' (r : A) [IsLocalization.Away r Af]
    [IsLocalization.Away (algebraMap A B r) Bf]
    (hdom : IsDominant (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)) :
    letI : Algebra (relativeWeakNormalization A B) (relativeWeakNormalization Af Bf) :=
      (relativeWeakNormalizationToLocalization r hdom).toAlgebra
    IsLocalization.Away (algebraMap A (relativeWeakNormalization A B) r)
      (relativeWeakNormalization Af Bf) :=
  let : Algebra (relativeWeakNormalization A B) (relativeWeakNormalization Af Bf) :=
    (relativeWeakNormalizationToLocalization r hdom).toAlgebra
  isLocalizationAway_relativeWeakNormalization r hdom fun _ => rfl

end AlgebraicGeometry

end
