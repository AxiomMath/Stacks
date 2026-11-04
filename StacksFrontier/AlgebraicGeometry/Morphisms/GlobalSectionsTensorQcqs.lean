module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Global sections of a fibre product over a field

Let `k` be a field and let `X` and `Y` be quasi-compact quasi-separated schemes over `Spec k`.
The canonical map `Γ(X, 𝒪_X) ⊗_k Γ(Y, 𝒪_Y) ⟶ Γ(X ×_k Y, 𝒪)` is an isomorphism.

## Main results

* `AlgebraicGeometry.isPushout_appTop_pullback_of_field`: the square of global sections of the
  fibre product `X ×_{Spec k} Y` is a pushout of commutative rings.
* `AlgebraicGeometry.isIso_globalSectionsTensorDesc` and
  `AlgebraicGeometry.bijective_globalSectionsTensorDesc`: for any `k`-algebra structures on
  `Γ(X, ⊤)` and `Γ(Y, ⊤)` given by the structure morphisms, the map
  `Γ(X, ⊤) ⊗[k] Γ(Y, ⊤) ⟶ Γ(X ×_k Y, ⊤)`, `a ⊗ b ↦ pr₁^* a · pr₂^* b`, is bijective.

## Implementation notes

This is Mathlib's
`AlgebraicGeometry.isIso_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat` at the top
opens: every morphism to the spectrum of a field is flat, and every ring is flat over a field.
The `k`-algebra structures are taken as instance arguments together with the equation identifying
them with the structure morphisms, so that a caller may use whichever instance it already has (for
instance Mathlib's on the global sections of an affine scheme over `Spec R`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of k)) (q : Y ⟶ Spec (CommRingCat.of k))
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- **The global sections of `X ×_{Spec k} Y` are the pushout of those of `X` and `Y` over those
of `Spec k`**, for `X` and `Y` quasi-compact and quasi-separated over a field `k`. -/
theorem isPushout_appTop_pullback_of_field :
    IsPushout p.appTop q.appTop (pullback.fst p q).appTop (pullback.snd p q).appTop := by
  have hfield : IsField Γ(Spec (CommRingCat.of k), ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k))
  have H := isIso_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat
    (IsPullback.of_hasPullback p q) (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤)
    (by simp) (by simp) (by simp) (isAffineOpen_top _) isCompact_univ
    (isQuasiSeparated_univ) isCompact_univ isQuasiSeparated_univ
    (RingHom.Flat.of_isField hfield _)
  have H' := (isIso_pushoutSection_iff _ _ _ _).mp H
  convert H' using 1 <;> exact Scheme.Hom.app_eq_appLE _

/-- The structure ring map `k ⟶ Γ(X, ⊤)` of a scheme over `Spec k`. -/
abbrev structureRingMap : CommRingCat.of k ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop

/-- The pushout square of global sections of `X ×_{Spec k} Y`, with `k` itself in the corner
in place of `Γ(Spec k, ⊤)`. -/
theorem isPushout_structureRingMap_pullback :
    IsPushout (structureRingMap p) (structureRingMap q) (pullback.fst p q).appTop
      (pullback.snd p q).appTop :=
  (isPushout_appTop_pullback_of_field p q).of_iso (Scheme.ΓSpecIso (CommRingCat.of k)) (Iso.refl _)
    (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)

variable [Algebra k Γ(X, ⊤)] [Algebra k Γ(Y, ⊤)]
  (hX : algebraMap k Γ(X, ⊤) = (structureRingMap p).hom)
  (hY : algebraMap k Γ(Y, ⊤) = (structureRingMap q).hom)

include hX hY in
/-- The two composites `k ⟶ Γ(X ×_k Y, ⊤)` through `Γ(X, ⊤)` and `Γ(Y, ⊤)` agree. -/
theorem globalSectionsTensor_w :
    CommRingCat.ofHom (algebraMap k Γ(X, ⊤)) ≫ (pullback.fst p q).appTop =
      CommRingCat.ofHom (algebraMap k Γ(Y, ⊤)) ≫ (pullback.snd p q).appTop := by
  rw [hX, hY, CommRingCat.ofHom_hom, CommRingCat.ofHom_hom]
  exact (isPushout_structureRingMap_pullback p q).w

/-- **The canonical map `Γ(X, ⊤) ⊗[k] Γ(Y, ⊤) ⟶ Γ(X ×_k Y, ⊤)`**, `a ⊗ b ↦ pr₁^* a · pr₂^* b`. -/
def globalSectionsTensorDesc :
    CommRingCat.of (Γ(X, ⊤) ⊗[k] Γ(Y, ⊤)) ⟶ Γ(pullback p q, ⊤) :=
  (CommRingCat.isPushout_tensorProduct k Γ(X, ⊤) Γ(Y, ⊤)).desc (pullback.fst p q).appTop
    (pullback.snd p q).appTop (globalSectionsTensor_w p q hX hY)

/-- The canonical map sends `a ⊗ b` to `pr₁^* a · pr₂^* b`. -/
@[simp]
theorem globalSectionsTensorDesc_tmul (a : Γ(X, ⊤)) (b : Γ(Y, ⊤)) :
    globalSectionsTensorDesc p q hX hY (a ⊗ₜ b) =
      (pullback.fst p q).appTop a * (pullback.snd p q).appTop b := by
  have h : a ⊗ₜ[k] b = (a ⊗ₜ 1) * (1 ⊗ₜ b) := by simp
  rw [h, map_mul]
  congr 1
  · exact congr($((CommRingCat.isPushout_tensorProduct k Γ(X, ⊤) Γ(Y, ⊤)).inl_desc _ _ _).hom a)
  · exact congr($((CommRingCat.isPushout_tensorProduct k Γ(X, ⊤) Γ(Y, ⊤)).inr_desc _ _ _).hom b)

/-- **Künneth for global sections over a field.**  For `X` and `Y` quasi-compact and
quasi-separated over a field `k`, the canonical map `Γ(X, ⊤) ⊗[k] Γ(Y, ⊤) ⟶ Γ(X ×_k Y, ⊤)` is an
isomorphism of rings. -/
instance isIso_globalSectionsTensorDesc : IsIso (globalSectionsTensorDesc p q hX hY) := by
  have hsq : IsPushout (CommRingCat.ofHom (algebraMap k Γ(X, ⊤)))
      (CommRingCat.ofHom (algebraMap k Γ(Y, ⊤))) (pullback.fst p q).appTop
      (pullback.snd p q).appTop := by
    rw [hX, hY, CommRingCat.ofHom_hom, CommRingCat.ofHom_hom]
    exact isPushout_structureRingMap_pullback p q
  have : globalSectionsTensorDesc p q hX hY =
      ((CommRingCat.isPushout_tensorProduct k Γ(X, ⊤) Γ(Y, ⊤)).isoIsPushout _ _ hsq).hom := by
    apply (CommRingCat.isPushout_tensorProduct k Γ(X, ⊤) Γ(Y, ⊤)).hom_ext <;>
      simp [globalSectionsTensorDesc]
  rw [this]
  infer_instance

/-- **Künneth for global sections over a field**, as bijectivity of the underlying map. -/
theorem bijective_globalSectionsTensorDesc :
    Function.Bijective (globalSectionsTensorDesc p q hX hY) :=
  ConcreteCategory.bijective_of_isIso _

end AlgebraicGeometry
