module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Checking that a restricted morphism is an isomorphism on an open cover

Let `f : X ⟶ Y` be a morphism of schemes and let `Ω : Y.Opens`. The property of the restriction
`f ∣_ Ω : (f ⁻¹ᵁ Ω).toScheme ⟶ Ω.toScheme` being an isomorphism is Zariski-local on `Ω`: it may be
checked on any family of opens whose supremum is `Ω`, with no quasi-compactness or affineness
assumption on `Ω` itself.

## Main results

* `Stacks.RestrictIso.isIso_morphismRestrict_of_le`: `IsIso (f ∣_ Ω)` descends to any smaller open.
* `Stacks.RestrictIso.isIso_morphismRestrict_of_iSup`: if `⨆ i, V i = Ω` and each `f ∣_ V i` is an
  isomorphism, then so is `f ∣_ Ω`.
* `Stacks.RestrictIso.isIso_restrict_of_isIso_app`: for a self-map `ψ` of an affine scheme `A` over
  `Spec R` and an affine open `Ω` of `Spec R`, the restriction `ψ ∣_ (a ⁻¹ᵁ Ω)` is an isomorphism
  as soon as the ring map `ψ.app (a ⁻¹ᵁ Ω)` is.
* `Stacks.RestrictIso.isIso_morphismRestrict_preimage_of_cover`: a self-map of `A` over `Spec R`
  restricts to an isomorphism over the preimage of an arbitrary open `Ω` of `Spec R` as soon as it
  does so, on sections, over each member of an affine open cover of `Ω`.

## Implementation notes

The locality statements are instances of the general machinery for properties that are local at the
target, applied to `MorphismProperty.isomorphisms Scheme`, which carries an
`AlgebraicGeometry.IsZariskiLocalAtTarget` instance from `Mathlib/AlgebraicGeometry/Gluing.lean`.
The only glue needed is the arrow isomorphism
`Stacks.RestrictIso.morphismRestrictRestrictLE`, identifying a double restriction
`f ∣_ Ω ∣_ (Ω.ι ⁻¹ᵁ V)` with the single restriction `f ∣_ V` when `V ≤ Ω`.
-/

@[expose] public section

namespace Stacks.RestrictIso

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

universe u

noncomputable section

/-! ### Double restrictions along an inclusion of opens -/

/-- If `V ≤ Ω` are opens of a scheme `X`, then the open `Ω.ι ⁻¹ᵁ V` of `Ω` has image `V` in `X`. -/
lemma ι_image_ι_preimage_of_le {X : Scheme.{u}} {V Ω : X.Opens} (hle : V ≤ Ω) :
    Ω.ι ''ᵁ (Ω.ι ⁻¹ᵁ V) = V := by
  simp [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hle]

/-- For `V ≤ Ω` opens of the target of `f : X ⟶ Y`, restricting `f` to `Ω` and then further to the
open `Ω.ι ⁻¹ᵁ V` of `Ω` gives the same arrow, up to isomorphism, as restricting `f` to `V`
directly. -/
def morphismRestrictRestrictLE {X Y : Scheme.{u}} (f : X ⟶ Y) {V Ω : Y.Opens} (hle : V ≤ Ω) :
    Arrow.mk (f ∣_ Ω ∣_ Ω.ι ⁻¹ᵁ V) ≅ Arrow.mk (f ∣_ V) :=
  morphismRestrictRestrict f Ω _ ≪≫ morphismRestrictEq f (ι_image_ι_preimage_of_le hle)

/-! ### Locality of `IsIso (f ∣_ Ω)` in `Ω` -/

/-- For `V ≤ Ω`, the double restriction `f ∣_ Ω ∣_ Ω.ι ⁻¹ᵁ V` is an isomorphism iff `f ∣_ V` is. -/
private theorem isIso_restrict_restrict_iff {X Y : Scheme.{u}} (f : X ⟶ Y) {V Ω : Y.Opens}
    (hle : V ≤ Ω) : IsIso (f ∣_ Ω ∣_ Ω.ι ⁻¹ᵁ V) ↔ IsIso (f ∣_ V) :=
  (MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff (morphismRestrictRestrictLE f hle)

/-- Being an isomorphism after restriction to an open `Ω` of the target passes to any smaller
open. -/
theorem isIso_morphismRestrict_of_le {X Y : Scheme.{u}} (f : X ⟶ Y) {V Ω : Y.Opens}
    (hle : V ≤ Ω) (h : IsIso (f ∣_ Ω)) : IsIso (f ∣_ V) :=
  (isIso_restrict_restrict_iff f hle).1
    (IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme) h _)

/-- Being an isomorphism after restriction to an open of the target is Zariski-local in that open:
if `Ω` is the supremum of a family `V` of opens of `Y` and `f ∣_ V i` is an isomorphism for every
`i`, then `f ∣_ Ω` is an isomorphism.

No quasi-compactness or affineness assumption is placed on `Ω` or on the `V i`, and the index type
`ι` is arbitrary. -/
theorem isIso_morphismRestrict_of_iSup {X Y : Scheme.{u}} (f : X ⟶ Y)
    {ι : Type*} (Ω : Y.Opens) (V : ι → Y.Opens) (hV : ⨆ i, V i = Ω)
    (h : ∀ i, IsIso (f ∣_ V i)) : IsIso (f ∣_ Ω) := by
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun i ↦ Ω.ι ⁻¹ᵁ V i) ?_ fun i ↦
      (isIso_restrict_restrict_iff f ((le_iSup V i).trans hV.le)).2 (h i)
  rw [← Scheme.Hom.preimage_iSup, hV, Scheme.Opens.ι_preimage_self]

/-! ### The affine criterion -/

variable {A : Scheme.{u}} {R : CommRingCat.{u}}

/-- If `ψ` is a self-map of a scheme `A` over `Spec R`, then the preimage in `A` of an open of
`Spec R` is `ψ`-stable. -/
lemma preimage_preimage_of_comp_eq (a : A ⟶ Spec R) {ψ : A ⟶ A} (hψ : ψ ≫ a = a)
    (Ω : (Spec R).Opens) : ψ ⁻¹ᵁ (a ⁻¹ᵁ Ω) = a ⁻¹ᵁ Ω := by
  rw [← Scheme.Hom.comp_preimage, hψ]

/-- The affine criterion: let `A` be an affine scheme over `Spec R` via `a`, let `ψ` be a self-map
of `A` over `Spec R`, and let `Ω` be an affine open of `Spec R`. If the induced map on sections
`ψ.app (a ⁻¹ᵁ Ω)` is an isomorphism, then `ψ` restricts to an isomorphism over `a ⁻¹ᵁ Ω`.

This is `AlgebraicGeometry.isIso_morphismRestrict_iff_isIso_app` together with the fact that the
preimage of an affine open under an affine morphism is affine. -/
theorem isIso_restrict_of_isIso_app (a : A ⟶ Spec R)
    [IsAffine A] (ψ : A ⟶ A) (Ω : (Spec R).Opens) (hΩ : IsAffineOpen Ω)
    (h : IsIso (ψ.app (a ⁻¹ᵁ Ω))) : IsIso (ψ ∣_ a ⁻¹ᵁ Ω) :=
  (isIso_morphismRestrict_iff_isIso_app ψ (hΩ.preimage a)).mpr h

/-- The affine criterion over a basic open of the base: specialisation of
`Stacks.RestrictIso.isIso_restrict_of_isIso_app` to `Ω = PrimeSpectrum.basicOpen g`, which is an
affine open of `Spec R` for every `g : R`. -/
theorem isIso_restrict_basicOpen_of_isIso_app (a : A ⟶ Spec R)
    [IsAffine A] (ψ : A ⟶ A) (g : R)
    (h : IsIso (ψ.app (a ⁻¹ᵁ (PrimeSpectrum.basicOpen g : (Spec R).Opens)))) :
    IsIso (ψ ∣_ a ⁻¹ᵁ (PrimeSpectrum.basicOpen g : (Spec R).Opens)) :=
  isIso_restrict_of_isIso_app a ψ _ (IsAffineOpen.Spec_basicOpen g) h

/-! ### The combined statement -/

/-- The form in which the two halves are used: let `A` be an affine scheme over `Spec R` via `a`,
let `ψ` be a self-map of `A` over `Spec R`, and let `Ω` be an arbitrary open of `Spec R` — neither
affine nor quasi-compact — covered by a family `V` of affine opens. If `ψ.app (a ⁻¹ᵁ V i)` is an
isomorphism for every `i`, then `ψ` restricts to an isomorphism over `a ⁻¹ᵁ Ω`. -/
theorem isIso_morphismRestrict_preimage_of_cover (a : A ⟶ Spec R)
    [IsAffine A] (ψ : A ⟶ A)
    {ι : Type*} (Ω : (Spec R).Opens) (V : ι → (Spec R).Opens) (hV : ⨆ i, V i = Ω)
    (haff : ∀ i, IsAffineOpen (V i))
    (h : ∀ i, IsIso (ψ.app (a ⁻¹ᵁ V i))) : IsIso (ψ ∣_ a ⁻¹ᵁ Ω) :=
  isIso_morphismRestrict_of_iSup ψ _ (fun i ↦ a ⁻¹ᵁ V i)
    (by rw [← Scheme.Hom.preimage_iSup, hV])
    fun i ↦ isIso_restrict_of_isIso_app a ψ (V i) (haff i) (h i)

end

end Stacks.RestrictIso
