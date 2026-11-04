module

public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Coherent comparisons along a cofiltered category

Let `𝒦` be a cofiltered category and `Φ` a family of objects of a category `𝒟` indexed by the
objects of `𝒦`, together with isomorphisms `e g : Φ k ≅ Φ j` for the morphisms `g : j ⟶ k`
which turn composition into composition. Then there is exactly one way to compare any two
members of the family compatibly with `e`: `Φ j ≅ Φ k` is `e a ≪≫ (e b)⁻¹` for any
`a : m ⟶ j`, `b : m ⟶ k`, and the choice of `(m, a, b)` does not matter. This is the footnote in
the proof of [Stacks, Tag 0F7I]: the comparisons compose, and along a morphism they are the
given isomorphisms.

## Main definitions

* `CategoryTheory.IsCofiltered.isoSystemComparison`: the comparison `Φ j ≅ Φ k`.

## Main results

* `CategoryTheory.IsCofiltered.isoSystemComparison_eq`: it is computed by any cone over `j, k`.
* `CategoryTheory.IsCofiltered.isoSystemComparison_trans`: the comparisons compose.
* `CategoryTheory.IsCofiltered.isoSystemComparison_of_hom`: along `g : j ⟶ k` the comparison
  `Φ k ≅ Φ j` is `e g`.
-/

@[expose] public section

namespace CategoryTheory.IsCofiltered

variable {𝒦 : Type*} [Category* 𝒦] [IsCofiltered 𝒦] {𝒟 : Type*} [Category* 𝒟] {Φ : 𝒦 → 𝒟}
  (e : ∀ {j k : 𝒦}, (j ⟶ k) → (Φ k ≅ Φ j))
  (he : ∀ {j k l : 𝒦} (g : j ⟶ k) (h : k ⟶ l), e (g ≫ h) = e h ≪≫ e g)

/-- The comparison `Φ j ≅ Φ k` through the chosen cone `min j k`. -/
noncomputable def isoSystemComparison (j k : 𝒦) : Φ j ≅ Φ k :=
  e (minToLeft j k) ≪≫ (e (minToRight j k)).symm

omit [IsCofiltered 𝒦] in
include he in
/-- The isomorphism attached to an identity is the identity. -/
lemma isoSystem_id (j : 𝒦) : e (𝟙 j) = Iso.refl _ := by
  have h := he (𝟙 j) (𝟙 j)
  rw [Category.id_comp] at h
  ext
  have h' := congrArg Iso.hom h
  simp only [Iso.trans_hom] at h'
  simpa using (cancel_epi (e (𝟙 j)).hom).1 (h'.symm.trans (Category.comp_id _).symm)

omit [IsCofiltered 𝒦] in
include he in
/-- Restricting a cone along a morphism into its vertex does not change the comparison. -/
lemma isoSystem_restrict {m j k m' : 𝒦} (a : m ⟶ j) (b : m ⟶ k) (w : m' ⟶ m) :
    e a ≪≫ (e b).symm = e (w ≫ a) ≪≫ (e (w ≫ b)).symm := by
  rw [he, he]
  ext
  simp

include he in
/-- **The comparison does not depend on the cone.** -/
lemma isoSystem_cone_eq {m m' j k : 𝒦} (a : m ⟶ j) (b : m ⟶ k) (a' : m' ⟶ j) (b' : m' ⟶ k) :
    e a ≪≫ (e b).symm = e a' ≪≫ (e b').symm := by
  let n := min m m'
  let c := minToLeft m m'
  let c' := minToRight m m'
  let p := eqHom (c ≫ a) (c' ≫ a')
  have hp : p ≫ c ≫ a = p ≫ c' ≫ a' := by
    simpa only [Category.assoc] using eq_condition (c ≫ a) (c' ≫ a')
  let r := eqHom (p ≫ c ≫ b) (p ≫ c' ≫ b')
  have hr : r ≫ p ≫ c ≫ b = r ≫ p ≫ c' ≫ b' := by
    simpa only [Category.assoc] using eq_condition (p ≫ c ≫ b) (p ≫ c' ≫ b')
  rw [isoSystem_restrict e he a b (r ≫ p ≫ c), isoSystem_restrict e he a' b' (r ≫ p ≫ c')]
  simp only [Category.assoc]
  rw [hp, hr]

include he in
/-- **The comparison is computed by any cone over `j` and `k`.** -/
lemma isoSystemComparison_eq {m j k : 𝒦} (a : m ⟶ j) (b : m ⟶ k) :
    isoSystemComparison e j k = e a ≪≫ (e b).symm :=
  isoSystem_cone_eq e he _ _ a b

include he in
/-- **The comparisons compose.** -/
lemma isoSystemComparison_trans (j k l : 𝒦) :
    isoSystemComparison e j k ≪≫ isoSystemComparison e k l = isoSystemComparison e j l := by
  let m := min (min j k) l
  let t : m ⟶ j := minToLeft _ _ ≫ minToLeft j k
  let s : m ⟶ k := minToLeft _ _ ≫ minToRight j k
  let v : m ⟶ l := minToRight _ _
  rw [isoSystemComparison_eq e he t s, isoSystemComparison_eq e he s v,
    isoSystemComparison_eq e he t v]
  ext
  simp

include he in
/-- **Along a morphism `g : j ⟶ k` the comparison `Φ k ≅ Φ j` is `e g`.** -/
lemma isoSystemComparison_of_hom {j k : 𝒦} (g : j ⟶ k) :
    isoSystemComparison e k j = e g := by
  rw [isoSystemComparison_eq e he g (𝟙 j), isoSystem_id e he]
  ext
  simp

end CategoryTheory.IsCofiltered
