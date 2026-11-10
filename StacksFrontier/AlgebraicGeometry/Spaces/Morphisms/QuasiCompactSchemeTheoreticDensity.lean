module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticDensity
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Scheme-theoretic density of a quasi-compact open subspace

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let
`U ⊆ X` be an open subspace whose inclusion is quasi-compact. Then `U` is scheme-theoretically
dense in `X` if and only if its scheme-theoretic closure is all of `X`, and scheme-theoretic
density of such an open subspace is preserved under inverse image along flat morphisms.

## Main results

* `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_comp_of_epi`: precomposing a morphism
  of presheaves with an epimorphism does not change its scheme-theoretic image.
* `AlgebraicGeometry.Space.schemeTheoreticClosure_preimage_of_isEtale`: for a quasi-compact open
  subspace `U ⊆ X` and an étale `V ⟶ X`, the scheme-theoretic closure of `U ×_X V` in `V` is the
  inverse image of the scheme-theoretic closure of `U`.
* `AlgebraicGeometry.Space.isSchemeTheoreticallyDense_iff_schemeTheoreticClosure_eq_top`: an open
  subspace whose inclusion is quasi-compact is scheme-theoretically dense exactly when its
  scheme-theoretic closure is the whole space.
* `AlgebraicGeometry.Space.schemeTheoreticClosure_preimage_of_isFlat`: for a quasi-compact open
  subspace `V ⊆ Y` and a flat `X ⟶ Y`, the scheme-theoretic closure of `V ×_Y X` in `X` is the
  inverse image of the scheme-theoretic closure of `V`.
* `AlgebraicGeometry.Space.isSchemeTheoreticallyDense_preimage_of_isFlat_of_isQuasiCompact`: the
  inverse image of a quasi-compact scheme-theoretically dense open subspace along a flat
  morphism of algebraic spaces is scheme-theoretically dense.

## References

* [Stacks Project, Tag 0834](https://stacks.math.columbia.edu/tag/0834)
* [Stacks Project, Tag 0835](https://stacks.math.columbia.edu/tag/0835)
* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 089D](https://stacks.math.columbia.edu/tag/089D)
* [Stacks Project, Tag 089E](https://stacks.math.columbia.edu/tag/089E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- Precomposing with an epimorphism does not change the range of a morphism of presheaves of
types. -/
private theorem range_comp_eq_range_of_epi {C : Type*} [Category C] {F G H : C ⥤ Type u}
    (e : F ⟶ G) [Epi e] (f : G ⟶ H) :
    Subfunctor.range (e ≫ f) = Subfunctor.range f := by
  rw [Subfunctor.range_comp, Subfunctor.range_eq_top, Subfunctor.image_top]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
private instance (priority := high) hasPullback_presheaf_quasiCompactSchemeTheoreticDensity
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

section QuasiCompactDensity

variable {W X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The scheme-theoretic image of a morphism is unchanged by precomposition with an
epimorphism. -/
theorem schemeTheoreticImageSubfunctor_comp_of_epi (e : W ⟶ X) [Epi e] (f : X ⟶ Y) :
    schemeTheoreticImageSubfunctor B S hS (e ≫ f) =
      schemeTheoreticImageSubfunctor B S hS f := by
  unfold schemeTheoreticImageSubfunctor
  rw [range_comp_eq_range_of_epi e f]

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the `pullback` of presheaves on the big fppf site in the statement
/-- The scheme-theoretic closure of the preimage of a subfunctor `U` along `φ` is the
scheme-theoretic image of the second projection of the pullback of `U.ι` along `φ`. -/
private theorem schemeTheoreticClosure_preimage_eq_image_pullback_snd
    {V X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : Subfunctor X) (φ : V ⟶ X) :
    schemeTheoreticClosure B S hS (U.preimage φ) =
      schemeTheoreticImageSubfunctor B S hS (pullback.snd U.ι φ) := by
  rw [schemeTheoreticClosure, ← (Subfunctor.isPullback_preimage φ U).isoIsPullback_hom_snd _ _
    (IsPullback.of_hasPullback U.ι φ)]
  exact @schemeTheoreticImageSubfunctor_comp_of_epi B S hS _ _ _ _
    (IsIso.epi_of_iso ((Subfunctor.isPullback_preimage φ U).isoIsPullback _ _
      (IsPullback.of_hasPullback U.ι φ)).hom) _

/-- **The scheme-theoretic closure of a quasi-compact open subspace commutes with étale
localization.** Let `U ⊆ X` be an open subspace of an algebraic space over `S` whose inclusion
is quasi-compact, and let `φ : V ⟶ X` be an étale morphism of algebraic spaces over `S`. Then
the scheme-theoretic closure of `U ×_X V` in `V` is the inverse image along `φ` of the
scheme-theoretic closure of `U` in `X`. -/
theorem schemeTheoreticClosure_preimage_of_isEtale (hX : IsAlgebraicSpace B S hS X)
    (U : Subfunctor X) (hU : IsOpenSubspace B S hS U) (hqc : IsQuasiCompact B S hS U.ι)
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V) (φ : V ⟶ X)
    (hφ : IsEtale B S hS φ) :
    schemeTheoreticClosure B S hS (U.preimage φ) =
      (schemeTheoreticClosure B S hS U).preimage φ := by
  rw [schemeTheoreticClosure_preimage_eq_image_pullback_snd]
  exact schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_isQuasiCompact' B S hS U.ι φ
    hU.1 hX hV hqc hφ

/-- Let `S` be a scheme contained in a big fppf site `B`, let `X` be an algebraic space over `S`
and let `U ⊆ X` be an open subspace. If the inclusion `U ⟶ X` is quasi-compact, then `U` is
scheme-theoretically dense in `X` if and only if the scheme-theoretic closure of `U` in `X` is
`X`. -/
@[stacks 0835]
theorem isSchemeTheoreticallyDense_iff_schemeTheoreticClosure_eq_top
    (hX : IsAlgebraicSpace B S hS X) (U : Subfunctor X) (hU : IsOpenSubspace B S hS U)
    (hqc : IsQuasiCompact B S hS U.ι) :
    IsSchemeTheoreticallyDense B S hS U ↔ schemeTheoreticClosure B S hS U = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h V hV φ hφ ↦ ?_⟩
  · simpa only [Subfunctor.preimage_id] using h hX (𝟙 X) (isEtale_of_isIso B S hS (𝟙 X))
  · rw [schemeTheoreticClosure_preimage_of_isEtale B S hS hX U hU hqc hV φ hφ, h]
    exact (Subfunctor.preimage_eq_top_iff _ _).2 le_top

end QuasiCompactDensity

section FlatDensity

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The scheme-theoretic closure of a quasi-compact open subspace commutes with flat base
change.** Let `V ⊆ Y` be an open subspace of an algebraic space over `S` whose inclusion is
quasi-compact, and let `f : X ⟶ Y` be a flat morphism of algebraic spaces over `S`. Then the
scheme-theoretic closure of `V ×_Y X` in `X` is the inverse image along `f` of the
scheme-theoretic closure of `V` in `Y`. -/
@[ega "IV 2.3.2" "special case"]
theorem schemeTheoreticClosure_preimage_of_isFlat (hY : IsAlgebraicSpace B S hS Y)
    (V : Subfunctor Y) (hV : IsOpenSubspace B S hS V) (hqc : IsQuasiCompact B S hS V.ι)
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) (hf : IsFlat B S hS f) :
    schemeTheoreticClosure B S hS (V.preimage f) =
      (schemeTheoreticClosure B S hS V).preimage f := by
  rw [schemeTheoreticClosure_preimage_eq_image_pullback_snd]
  exact schemeTheoreticImageSubfunctor_pullback_snd_of_isFlat_of_isQuasiCompact' B S hS f V.ι
    hX hY hV.1 hf hqc

/-- Let `S` be a scheme contained in a big fppf site `B`, let `f : X ⟶ Y` be a flat morphism of
algebraic spaces over `S` and let `V ⊆ Y` be an open subspace whose inclusion is quasi-compact.
If `V` is scheme-theoretically dense in `Y`, then `f⁻¹V` is scheme-theoretically dense in
`X`. -/
@[stacks 089D]
theorem isSchemeTheoreticallyDense_preimage_of_isFlat_of_isQuasiCompact
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsFlat B S hS f) (V : Subfunctor Y) (hV : IsOpenSubspace B S hS V)
    (hqc : IsQuasiCompact B S hS V.ι)
    (hdense : IsSchemeTheoreticallyDense B S hS V) :
    IsSchemeTheoreticallyDense B S hS (V.preimage f) := by
  intro Z hZ φ hφ
  rw [← Subfunctor.preimage_comp V φ f,
    schemeTheoreticClosure_preimage_of_isFlat B S hS hY V hV hqc hZ (φ ≫ f)
      (isFlat_comp B S hS hZ hX hY φ f (isFlat_of_isEtale B S hS hφ) hf),
    (isSchemeTheoreticallyDense_iff_schemeTheoreticClosure_eq_top B S hS hY V hV hqc).1 hdense]
  exact (Subfunctor.preimage_eq_top_iff _ _).2 le_top

end FlatDensity

end AlgebraicGeometry.Space

end
