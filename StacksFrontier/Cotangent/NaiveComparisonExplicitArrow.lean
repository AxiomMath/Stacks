module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.Complex

/-!
# The explicit comparison with the naive cotangent complex

Let `P` be the standard resolution of a commutative `A`-algebra `B` and let `I` be the kernel
of the augmentation `P₀ = A[B] → B`. The comparison from the cotangent complex to the naive
cotangent complex is induced by the identity in degree zero and by `d f ⊗ b ↦ (d₀ f - d₁ f) b`
in degree one, the higher terms contributing zero.

## Main definitions

* `CommAlgCat.standardResolutionVar` and `CommAlgCat.standardResolutionSection`: the insertion
  of variables `Pₙ → Pₙ₊₁` and the resulting section `B → Pₙ` of the augmentation.
* `CommAlgCat.standardResolutionExtension`: the term `Pₙ → B` of the standard resolution as an
  extension of `B` over `A`, so that its conormal module `I/I²` and its cotangent space
  `Ω[Pₙ⁄A] ⊗[Pₙ] B` are available.
* `CommAlgCat.standardResolutionExtensionFace`: a face map as a morphism of extensions.
* `CommAlgCat.naiveCotangentComparison`: the downward arrow of the comparison diagram,
  `Ω[P₁⁄A] ⊗[P₁] B → I/I²`.

## Main results

* `CommAlgCat.naiveCotangentComparison_tmul`: the arrow sends `d f ⊗ b` to the class of
  `(d₀ f - d₁ f) b`.
* `CommAlgCat.naiveCotangentComparison_cotangentComplex`: it is compatible with the differential
  `Ω[P₁⁄A] ⊗[P₁] B → Ω[P₀⁄A] ⊗[P₀] B`, which is the lower commuting square of the diagram.
* `CommAlgCat.naiveCotangentComparison_faceSum`: it annihilates the differential coming from
  `Ω[P₂⁄A] ⊗[P₂] B`, which is the upper commuting square.
* `Algebra.Extension.cotangentSpace_hom_ext`: two maps out of a cotangent space agreeing on the
  pure differentials `1 ⊗ d x` are equal.

## Implementation notes

The degree-zero term of the diagram is the same object on both rows, namely the cotangent space
of `standardResolutionExtension A B 0`, so the comparison is the identity there and only the
degree-one arrow carries content; the two results above are exactly the two commuting squares,
hence the two conditions for a map of complexes into a complex concentrated in degrees `-1`
and `0`. The map of complexes itself is assembled from them as
`CommAlgCat.explicitNaiveComparison`.

Remark 08UP omits two verifications. The first is that the rule `d f ⊗ b ↦ (d₀ f - d₁ f) b` is
well defined — "We omit the verification that this rule is well defined" — which here needs no
verification at all, the arrow being built as `Algebra.Extension.Hom.sub` of two morphisms of
extensions rather than from a choice of representatives. The second is the agreement with the
comparison map of Lemma 08RB — "We omit the verification that this is the same as the map".
The remark omits the *proof* of that agreement, not the assertion, so the assertion is part of
Tag 08UP; it is not proved here but as
`Stacks.Cotangent.explicitNaiveComparison_comp_comparison`, the map of complexes itself being
assembled as `CommAlgCat.explicitNaiveComparison`. The comparison map of Lemma 08RB is
`Stacks.Cotangent.comparison`, at the object `A[B] → B`.

The extension attached to `Pₙ` needs a section of its augmentation, and the variables provide
one without any choice: `standardResolutionVar` inserts `p ∈ Pₙ` as the variable `[p]` of
`Pₙ₊₁ = A[Pₙ]`, the zeroth face evaluates `[p]` back to `p`, and the augmentations of adjacent
degrees differ by that face.

The cotangent space `Algebra.Extension.CotangentSpace` of
`standardResolutionExtension A B n` is the module `CommAlgCat.cotangentTerm A B (op ⦋n⦌)`
carrying degree `-n` of `CommAlgCat.cotangentComplex`, and the alternating sum of the faces
below is the differential of that complex; the results are stated for the extension's cotangent
spaces, where no transport is needed.

## References

* [Stacks Project, Tag 08UP](https://stacks.math.columbia.edu/tag/08UP)
-/

@[expose] public section

open CategoryTheory Opposite Simplicial TensorProduct

universe u v

/-- Two `S`-linear maps out of the cotangent space of an extension `P → S` which agree on every
pure differential `1 ⊗ d x` are equal. -/
theorem Algebra.Extension.cotangentSpace_hom_ext {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (P : Algebra.Extension R S) {M : Type*} [AddCommGroup M] [Module S M]
    (α β : P.CotangentSpace →ₗ[S] M)
    (h : ∀ x : P.Ring, α ((1 : S) ⊗ₜ KaehlerDifferential.D R P.Ring x) =
      β ((1 : S) ⊗ₜ KaehlerDifferential.D R P.Ring x)) : α = β := by
  apply LinearMap.ext
  intro z
  have hz : z ∈ Submodule.span S
      (Set.range fun x : P.Ring => (1 : S) ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring x) := by
    refine TensorProduct.inductionOn z ?_ ?_
    · intro s ω
      have hω : ω ∈ Submodule.span P.Ring
          (Set.range (KaehlerDifferential.D R P.Ring)) := by
        rw [KaehlerDifferential.span_range_derivation]
        exact Submodule.mem_top
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hω
      · rintro _ ⟨x, rfl⟩
        have hx : (1 : S) ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring x ∈
            Submodule.span S (Set.range fun y : P.Ring =>
              (1 : S) ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring y) :=
          Submodule.subset_span ⟨x, rfl⟩
        simpa [TensorProduct.smul_tmul'] using Submodule.smul_mem _ s hx
      · simp
      · intro x y _ _ hx hy
        simpa only [TensorProduct.tmul_add] using Submodule.add_mem _ hx hy
      · intro p y _ hy
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        have hs := Submodule.smul_mem (Submodule.span S (Set.range fun y : P.Ring =>
          (1 : S) ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring y)) (algebraMap P.Ring S p) hy
        convert hs using 1
        simp [TensorProduct.smul_tmul', Algebra.smul_def]
    · intro x y hx hy
      exact Submodule.add_mem _ hx hy
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨x, rfl⟩
    exact h x
  · simp
  · intro x y _ _ hx hy
    rw [map_add, map_add, hx, hy]
  · intro s x _ hx
    rw [map_smul, map_smul, hx]

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)

/-! ### The extension attached to a term of the standard resolution -/

/-- The variable `[p]` of `Pₙ₊₁ = A[Pₙ]` indexed by an element `p` of `Pₙ`. In degree zero this
is `CommAlgCat.standardResolutionVarOne`, which this generalizes to every degree. -/
noncomputable def standardResolutionVar (n : ℕ)
    (p : (standardResolution A B).left.obj (op ⦋n⦌)) :
    (standardResolution A B).left.obj (op ⦋n + 1⦌) :=
  eqToHom (standardResolution_obj_mvPolynomial_succ A B n).symm
    (MvPolynomial.X (eqToHom (standardResolution_obj_mvPolynomial A B n) p))

/-- The zeroth face evaluates the variable `[p]` at `p`. -/
theorem standardResolution_δ_zero_var (n : ℕ)
    (p : (standardResolution A B).left.obj (op ⦋n⦌)) :
    (standardResolution A B).left.δ (0 : Fin (n + 2)) (standardResolutionVar A B n p) = p := by
  rw [standardResolution_δ_zero_aeval, standardResolutionVar, CommAlgCat.comp_apply,
    CommAlgCat.comp_apply, eqToHom_eqToHom_symm_apply, CommAlgCat.ofHom_apply,
    MvPolynomial.aeval_X, id_eq, eqToHom_symm_eqToHom_apply]

/-- The section `B → Pₙ` of the augmentation obtained by iterating the insertion of variables
from the variable `[b]` of `P₀ = A[B]`. -/
noncomputable def standardResolutionSection :
    (n : ℕ) → B → (standardResolution A B).left.obj (op ⦋n⦌)
  | 0 => standardResolutionVarZero A B
  | n + 1 => fun b => standardResolutionVar A B n (standardResolutionSection n b)

/-- The iterated variables do section the augmentation. -/
theorem standardResolution_augmentation_section (n : ℕ) (b : B) :
    standardResolutionAugmentationHom A B (op ⦋n⦌) (standardResolutionSection A B n b) = b := by
  induction n with
  | zero => exact standardResolution_augmentation_varZero A B b
  | succ n ih =>
      have hnat := RingHom.congr_fun
        (standardResolutionAugmentationHom_naturality A B
          (SimplexCategory.δ (0 : Fin (n + 2))).op)
        (standardResolutionVar A B n (standardResolutionSection A B n b))
      refine hnat.symm.trans ?_
      change standardResolutionAugmentationHom A B (op ⦋n⦌)
        ((standardResolution A B).left.δ (0 : Fin (n + 2))
          (standardResolutionVar A B n (standardResolutionSection A B n b))) = b
      rw [standardResolution_δ_zero_var, ih]

/-- The term `Pₙ → B` of the standard resolution as an extension of `B` over `A`. Its conormal
module is `I/I²` for `I` the kernel of the augmentation, and its cotangent space is
`Ω[Pₙ⁄A] ⊗[Pₙ] B`. -/
noncomputable def standardResolutionExtension (n : ℕ) : Algebra.Extension.{max u v} A B := by
  letI : Algebra ((standardResolution A B).left.obj (op ⦋n⦌)) B :=
    (standardResolutionAugmentationHom A B (op ⦋n⦌)).toAlgebra
  haveI : IsScalarTower A ((standardResolution A B).left.obj (op ⦋n⦌)) B :=
    IsScalarTower.of_algebraMap_eq
      (fun a => (((standardResolution A B).hom.app (op ⦋n⦌)).hom.commutes a).symm)
  exact
    { Ring := (standardResolution A B).left.obj (op ⦋n⦌)
      σ := standardResolutionSection A B n
      algebraMap_σ := standardResolution_augmentation_section A B n }

/-- The underlying algebra of the extension is the term of the standard resolution. -/
theorem standardResolutionExtension_Ring (n : ℕ) :
    (standardResolutionExtension A B n).Ring =
      ((standardResolution A B).left.obj (op ⦋n⦌) : Type (max u v)) := rfl

/-- The structure map of the extension is the augmentation. -/
theorem standardResolutionExtension_algebraMap (n : ℕ) :
    (algebraMap (standardResolutionExtension A B n).Ring B) =
      (standardResolutionAugmentationHom A B (op ⦋n⦌) :
        (standardResolution A B).left.obj (op ⦋n⦌) →+* B) := rfl

/-- A simplicial operator of the standard resolution as a morphism of the attached extensions:
it commutes with the structure maps by naturality of the augmentation. -/
noncomputable def standardResolutionExtensionMap {i j : ℕ}
    (f : (op ⦋i⦌ : SimplexCategoryᵒᵖ) ⟶ op ⦋j⦌) :
    Algebra.Extension.Hom (standardResolutionExtension A B i)
      (standardResolutionExtension A B j) where
  toRingHom := ((standardResolution A B).left.map f).hom.toRingHom
  toRingHom_algebraMap x := ((standardResolution A B).left.map f).hom.commutes x
  algebraMap_toRingHom x :=
    RingHom.congr_fun (standardResolutionAugmentationHom_naturality A B f) x

/-- The `i`th face `Pₙ₊₁ → Pₙ` as a morphism of extensions. -/
noncomputable abbrev standardResolutionExtensionFace (n : ℕ) (i : Fin (n + 2)) :
    Algebra.Extension.Hom (standardResolutionExtension A B (n + 1))
      (standardResolutionExtension A B n) :=
  standardResolutionExtensionMap A B (SimplexCategory.δ i).op

/-- The morphism of extensions attached to a simplicial operator acts as that operator. -/
theorem standardResolutionExtensionMap_apply {i j : ℕ}
    (f : (op ⦋i⦌ : SimplexCategoryᵒᵖ) ⟶ op ⦋j⦌)
    (p : (standardResolution A B).left.obj (op ⦋i⦌)) :
    (standardResolutionExtensionMap A B f).toRingHom p =
      (standardResolution A B).left.map f p := rfl

/-- The morphism of extensions attached to a face acts as that face. -/
theorem standardResolutionExtensionFace_apply (n : ℕ) (i : Fin (n + 2))
    (p : (standardResolutionExtension A B (n + 1)).Ring) :
    (standardResolutionExtensionFace A B n i).toRingHom p =
      (standardResolution A B).left.δ i p := rfl

/-! ### The comparison arrow -/

/-- **Stacks Project, Tag 08UP.** The downward arrow of the comparison diagram in degree one:
the difference of the two faces `P₁ → P₀`, which lands in the kernel `I` of the augmentation,
read as a map `Ω[P₁⁄A] ⊗[P₁] B → I/I²`. -/
@[stacks 08UP "the explicit downward arrow of the diagram, `d f ⊗ b ↦ (d₀ f - d₁ f) b`, with no
hypothesis beyond the remark's own standard resolution of B over A; well defined by
construction, as the remark's two omitted verifications are discussed in this module's
implementation notes"]
noncomputable def naiveCotangentComparison :
    (standardResolutionExtension A B 1).CotangentSpace →ₗ[B]
      (standardResolutionExtension A B 0).Cotangent :=
  (standardResolutionExtensionFace A B 0 0).sub (standardResolutionExtensionFace A B 0 1)

/-- The arrow sends `d f ⊗ b` to `b` times the class of `d₀ f - d₁ f` in `I/I²`. -/
@[stacks 08UP "the value of the arrow on a pure differential"]
theorem naiveCotangentComparison_tmul (b : B)
    (f : (standardResolutionExtension A B 1).Ring) :
    naiveCotangentComparison A B
        (b ⊗ₜ KaehlerDifferential.D A (standardResolutionExtension A B 1).Ring f) =
      b • Algebra.Extension.Cotangent.mk
        ((standardResolutionExtensionFace A B 0 0).subToKer
          (standardResolutionExtensionFace A B 0 1) f) :=
  Algebra.Extension.Hom.sub_tmul _ _ _ _

/-- The element of `I` whose class the arrow takes: the difference of the two faces. -/
@[stacks 08UP "the difference of the two faces, which is the element of `I` the arrow uses"]
theorem naiveCotangentComparison_subToKer_coe
    (f : (standardResolutionExtension A B 1).Ring) :
    ((standardResolutionExtensionFace A B 0 0).subToKer
        (standardResolutionExtensionFace A B 0 1) f).val =
      (standardResolution A B).left.δ (0 : Fin 2) f -
        (standardResolution A B).left.δ (1 : Fin 2) f :=
  Algebra.Extension.Hom.subToKer_apply_coe _ _ _

/-- The lower commuting square of the diagram: following the arrow by the differential
`I/I² → Ω[P₀⁄A] ⊗[P₀] B` of the naive cotangent complex is the differential
`Ω[P₁⁄A] ⊗[P₁] B → Ω[P₀⁄A] ⊗[P₀] B`, the difference of the two faces. -/
@[stacks 08UP "the lower square: compatibility with the differential out of degree one"]
theorem naiveCotangentComparison_cotangentComplex :
    (standardResolutionExtension A B 0).cotangentComplex ∘ₗ naiveCotangentComparison A B =
      Algebra.Extension.CotangentSpace.map (standardResolutionExtensionFace A B 0 0) -
        Algebra.Extension.CotangentSpace.map (standardResolutionExtensionFace A B 0 1) :=
  (Algebra.Extension.CotangentSpace.map_sub_map (standardResolutionExtensionFace A B 0 0)
    (standardResolutionExtensionFace A B 0 1)).symm

/-- The upper commuting square of the diagram: the arrow annihilates the alternating sum of the
three faces `P₂ → P₁`, which is the differential of the cotangent complex out of degree two. -/
@[stacks 08UP "the upper square: the arrow annihilates the differential into degree one"]
theorem naiveCotangentComparison_faceSum :
    naiveCotangentComparison A B ∘ₗ
        (Algebra.Extension.CotangentSpace.map (standardResolutionExtensionFace A B 1 0) -
          Algebra.Extension.CotangentSpace.map (standardResolutionExtensionFace A B 1 1) +
          Algebra.Extension.CotangentSpace.map (standardResolutionExtensionFace A B 1 2)) = 0 := by
  refine Algebra.Extension.cotangentSpace_hom_ext (standardResolutionExtension A B 2) _ _ ?_
  intro x
  rw [LinearMap.zero_apply, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
    Algebra.Extension.CotangentSpace.map_tmul, Algebra.Extension.CotangentSpace.map_tmul,
    Algebra.Extension.CotangentSpace.map_tmul, map_one]
  rw [map_add, map_sub, naiveCotangentComparison_tmul, naiveCotangentComparison_tmul,
    naiveCotangentComparison_tmul, one_smul, one_smul, one_smul, ← map_sub, ← map_add]
  have hδ : ∀ (i j : Fin 2) (H : i ≤ j),
      (standardResolutionExtensionFace A B 0 i).toRingHom
        ((standardResolutionExtensionFace A B 1 j.succ).toRingHom x) =
      (standardResolutionExtensionFace A B 0 j).toRingHom
        ((standardResolutionExtensionFace A B 1 i.castSucc).toRingHom x) := fun i j H =>
    congrFun (congrArg (fun g => g.hom.toFun)
      ((standardResolution A B).left.δ_comp_δ H)) x
  have h₀ := hδ 0 0 le_rfl
  have h₁ := hδ 0 1 (by decide)
  have h₂ := hδ 1 1 le_rfl
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.castSucc_zero,
    Fin.castSucc_one] at h₀ h₁ h₂
  refine (congrArg Algebra.Extension.Cotangent.mk (Subtype.ext ?_)).trans (map_zero _)
  simp only [AddMemClass.coe_add, AddSubgroupClass.coe_sub, ZeroMemClass.coe_zero]
  rw [Algebra.Extension.Hom.subToKer_apply_coe, Algebra.Extension.Hom.subToKer_apply_coe,
    Algebra.Extension.Hom.subToKer_apply_coe]
  simp only [Algebra.Extension.Hom.toAlgHom_apply]
  linear_combination (norm := ring_nf) -h₀ + h₁ - h₂

end CommAlgCat

end
