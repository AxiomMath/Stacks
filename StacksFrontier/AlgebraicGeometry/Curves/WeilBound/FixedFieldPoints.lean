module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldValuedPointCount

/-!
# Field-valued points fixed by an automorphism of the field

Let `X` be a scheme over a field `k`, `Ω` an extension of `k` and `τ` a `k`-endomorphism of `Ω`.
Precomposition with `Spec τ` acts on the set `X(Ω)` of `Ω`-valued points. If `j : K → Ω` is a
`k`-embedding of a further extension whose image is exactly the set of elements fixed by `τ`,
then the points fixed by `τ` are exactly the points coming from `X(K)`:
`X(Ω)^τ ≃ X(K)`, by `t ↦ Spec j ≫ t`.

For a finite field `K` with `Q` elements, the image of any embedding `K → Ω` contains every
`a ∈ Ω` with `a ^ Q = a`, since `X ^ Q - X` has at most `Q` roots and the `Q` elements of the
image are among them. This is how the fixed points of a power of the Frobenius of an algebraic
closure of a finite field are identified with the points over a finite extension.

## Main results

* `AlgebraicGeometry.Scheme.SpecToEquivOfField_specMap_comp`: precomposing a field-valued point
  with `Spec φ` postcomposes its residue field embedding with `φ`.
* `AlgebraicGeometry.mem_range_of_pow_card_eq`: the image of a finite field with `Q` elements in a
  field contains every root of `a ^ Q = a`.
* `AlgebraicGeometry.fixedFieldValuedPointsEquiv`: `X(Ω)^τ ≃ X(K)`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

/-- Precomposing a field-valued point `t : Spec K ⟶ X` with `Spec φ` for a field map `φ : K → L`
keeps its point and postcomposes its residue field embedding with `φ`. -/
theorem Scheme.SpecToEquivOfField_specMap_comp {X : Scheme.{u}} {K L : Type u} [Field K]
    [Field L] (φ : K →+* L) (t : Spec (.of K) ⟶ X) :
    Scheme.SpecToEquivOfField L X (Spec.map (CommRingCat.ofHom φ) ≫ t) =
      ⟨(Scheme.SpecToEquivOfField K X t).1,
        (Scheme.SpecToEquivOfField K X t).2 ≫ CommRingCat.ofHom φ⟩ := by
  rw [← Equiv.eq_symm_apply]
  conv_lhs => rw [← (Scheme.SpecToEquivOfField K X).symm_apply_apply t]
  simp only [Scheme.SpecToEquivOfField_symm_apply, Spec.map_comp, Category.assoc]

/-- The image of a finite field with `Q` elements in a field `Ω` contains every `a ∈ Ω` with
`a ^ Q = a`: the polynomial `X ^ Q - X` has at most `Q` roots, and the `Q` elements of the image
are roots. -/
theorem mem_range_of_pow_card_eq {K Ω : Type u} [Field K] [Fintype K] [Field Ω] (j : K →+* Ω)
    {a : Ω} (ha : a ^ Fintype.card K = a) : a ∈ Set.range j := by
  classical
  by_contra hna
  set Q := Fintype.card K
  have hQ : 1 < Q := Fintype.one_lt_card
  set Z : Finset Ω := Finset.univ.image j
  have hZcard : Z.card = Q := Finset.card_image_of_injective _ j.injective
  have hP0 : (Polynomial.X ^ Q - Polynomial.X : Polynomial Ω) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero Ω hQ
  have hroot : ∀ b : Ω, b ^ Q = b → b ∈ (Polynomial.X ^ Q - Polynomial.X : Polynomial Ω).roots :=
    fun b hb => by
      rw [Polynomial.mem_roots hP0, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, hb, sub_self]
  have hsub : (insert a Z).val ⊆ (Polynomial.X ^ Q - Polynomial.X : Polynomial Ω).roots := by
    intro b hb
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact hroot b ha
    · obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hb
      exact hroot _ (by rw [← map_pow, FiniteField.pow_card])
  have hle := Polynomial.card_le_degree_of_subset_roots hsub
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq Ω hQ,
    Finset.card_insert_of_notMem (fun h => hna (by
      obtain ⟨c, -, hc⟩ := Finset.mem_image.1 h
      exact ⟨c, hc⟩)), hZcard] at hle
  omega

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The `Ω`-valued point `Spec τ ≫ t` for a `k`-endomorphism `τ` of `Ω`. -/
def fieldValuedPointsPrecomp {Ω : Type u} [Field Ω] [Algebra k Ω] (τ : Ω →ₐ[k] Ω)
    (t : fieldValuedPoints f Ω) : fieldValuedPoints f Ω :=
  ⟨Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ t.1, by
    rw [Category.assoc, t.2, ← Spec.map_comp]
    congr 2
    ext c
    exact τ.commutes c⟩

/-- The `Ω`-valued point `Spec j ≫ t` of a `K`-valued point `t`, for a `k`-embedding
`j : K → Ω`. -/
def fieldValuedPointsMap {K Ω : Type u} [Field K] [Field Ω] [Algebra k K] [Algebra k Ω]
    (j : K →ₐ[k] Ω) (t : fieldValuedPoints f K) : fieldValuedPoints f Ω :=
  ⟨Spec.map (CommRingCat.ofHom j.toRingHom) ≫ t.1, by
    rw [Category.assoc, t.2, ← Spec.map_comp]
    congr 2
    ext c
    exact j.commutes c⟩

/-- Ring maps into a field are cancelled by postcomposition with an injective ring map. -/
private theorem eq_of_comp_ofHom_eq {K Ω : Type u} [Field K] [Field Ω] {j : K →+* Ω}
    {R : CommRingCat.{u}} {x y : R ⟶ .of K}
    (h : x ≫ CommRingCat.ofHom j = y ≫ CommRingCat.ofHom j) : x = y :=
  CommRingCat.hom_ext (RingHom.ext fun c => j.injective (congrArg (fun φ => φ.hom c) h))

/-- Pushing forward along a field embedding is injective on field-valued points. -/
theorem fieldValuedPointsMap_injective {K Ω : Type u} [Field K] [Field Ω] [Algebra k K]
    [Algebra k Ω] (j : K →ₐ[k] Ω) : Function.Injective (fieldValuedPointsMap f j) := by
  intro a b hab
  have h := congrArg (fun t : fieldValuedPoints f Ω => Scheme.SpecToEquivOfField Ω X t.1) hab
  simp only [fieldValuedPointsMap, Scheme.SpecToEquivOfField_specMap_comp] at h
  obtain ⟨e, he⟩ := Scheme.SpecToEquivOfField_eq_iff.1 h
  apply Subtype.ext
  apply (Scheme.SpecToEquivOfField K X).injective
  refine Scheme.SpecToEquivOfField_eq_iff.2
    ⟨e, eq_of_comp_ofHom_eq (j := j.toRingHom) ?_⟩
  rwa [Category.assoc]

/-- If every element of `Ω` fixed by `τ` lies in the image of `j`, then every `Ω`-valued point
fixed by `τ` comes from a `K`-valued point. -/
private theorem exists_fieldValuedPointsMap_eq_of_precomp_eq {K Ω : Type u} [Field K] [Field Ω]
    [Algebra k K] [Algebra k Ω] (j : K →ₐ[k] Ω) (τ : Ω →ₐ[k] Ω)
    (hτ : ∀ a : Ω, τ a = a → a ∈ Set.range j) (t : fieldValuedPoints f Ω)
    (ht : fieldValuedPointsPrecomp f τ t = t) :
    ∃ s, fieldValuedPointsMap f j s = t := by
  have hfix : (Scheme.SpecToEquivOfField Ω X t.1).2 ≫ CommRingCat.ofHom τ.toRingHom =
      (Scheme.SpecToEquivOfField Ω X t.1).2 := by
    have h := congrArg (fun t : fieldValuedPoints f Ω => Scheme.SpecToEquivOfField Ω X t.1) ht
    simp only [fieldValuedPointsPrecomp, Scheme.SpecToEquivOfField_specMap_comp] at h
    obtain ⟨e, he⟩ := Scheme.SpecToEquivOfField_eq_iff.1 h
    exact he.trans (Category.id_comp _)
  have hmem : ∀ c, (Scheme.SpecToEquivOfField Ω X t.1).2.hom c ∈ j.toRingHom.range := fun c => by
    obtain ⟨d, hd⟩ := hτ ((Scheme.SpecToEquivOfField Ω X t.1).2.hom c)
      (congrArg (fun φ => φ.hom c) hfix)
    exact ⟨d, hd⟩
  let eK : K ≃+* j.toRingHom.range := RingEquiv.ofBijective j.toRingHom.rangeRestrict
    ⟨fun a b hab => j.injective (congrArg Subtype.val hab),
      j.toRingHom.rangeRestrict_surjective⟩
  let ι₀ : X.residueField (Scheme.SpecToEquivOfField Ω X t.1).1 ⟶ CommRingCat.of K :=
    CommRingCat.ofHom (eK.symm.toRingHom.comp
      ((Scheme.SpecToEquivOfField Ω X t.1).2.hom.codRestrict _ hmem))
  have hι₀ : ι₀ ≫ CommRingCat.ofHom j.toRingHom = (Scheme.SpecToEquivOfField Ω X t.1).2 := by
    ext c
    change j (eK.symm ⟨_, hmem c⟩) = _
    exact congrArg Subtype.val (eK.apply_symm_apply ⟨_, hmem c⟩)
  have ht1 : Spec.map (Scheme.SpecToEquivOfField Ω X t.1).2 ≫
      X.fromSpecResidueField (Scheme.SpecToEquivOfField Ω X t.1).1 = t.1 := by
    rw [← Scheme.SpecToEquivOfField_symm_apply, Equiv.symm_apply_apply]
  have hover : (Spec.map ι₀ ≫ X.fromSpecResidueField (Scheme.SpecToEquivOfField Ω X t.1).1) ≫
      f = Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [fromSpecResidueField_comp_eq_iff]
    have ht2 := t.2
    rw [← ht1, fromSpecResidueField_comp_eq_iff, ← hι₀] at ht2
    refine eq_of_comp_ofHom_eq (j := j.toRingHom) ?_
    rw [Category.assoc, ht2]
    ext c
    exact (j.commutes c).symm
  refine ⟨⟨Spec.map ι₀ ≫ X.fromSpecResidueField (Scheme.SpecToEquivOfField Ω X t.1).1,
    hover⟩, ?_⟩
  apply Subtype.ext
  change Spec.map (CommRingCat.ofHom j.toRingHom) ≫ Spec.map ι₀ ≫
      X.fromSpecResidueField (Scheme.SpecToEquivOfField Ω X t.1).1 = t.1
  rw [← Category.assoc, ← Spec.map_comp, hι₀, ht1]

/-- **Field-valued points fixed by an automorphism.** Let `j : K → Ω` be a `k`-embedding and
`τ` a `k`-endomorphism of `Ω` whose fixed elements are exactly the image of `j`. Then the
`Ω`-valued points `t` of `X` with `Spec τ ≫ t = t` are exactly those coming from `X(K)`. -/
def fixedFieldValuedPointsEquiv {K Ω : Type u} [Field K] [Field Ω] [Algebra k K] [Algebra k Ω]
    (j : K →ₐ[k] Ω) (τ : Ω →ₐ[k] Ω) (hj : ∀ c : K, τ (j c) = j c)
    (hτ : ∀ a : Ω, τ a = a → a ∈ Set.range j) :
    fieldValuedPoints f K ≃ {t : fieldValuedPoints f Ω // fieldValuedPointsPrecomp f τ t = t} :=
  Equiv.ofBijective
    (fun t => ⟨fieldValuedPointsMap f j t, by
      apply Subtype.ext
      simp only [fieldValuedPointsPrecomp, fieldValuedPointsMap, ← Category.assoc,
        ← Spec.map_comp]
      congr 3
      ext c
      exact hj c⟩)
    (by
      refine ⟨fun a b hab => fieldValuedPointsMap_injective f j (congrArg Subtype.val hab), ?_⟩
      rintro ⟨t, ht⟩
      obtain ⟨s, hs⟩ := exists_fieldValuedPointsMap_eq_of_precomp_eq f j τ hτ t ht
      exact ⟨s, Subtype.ext hs⟩)

end AlgebraicGeometry

end
