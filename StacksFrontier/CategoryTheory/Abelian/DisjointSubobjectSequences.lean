module

public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Exact sequences attached to two disjoint subobjects

Let `C` be an abelian category, `L` an object and `a : A ⟶ L`, `b : B ⟶ L` two monomorphisms
with trivial intersection, and let `k : K ⟶ L` be their sum: a monomorphism through which `a`
and `b` factor, with `A ⊞ B ⟶ K` an epimorphism. Writing `L/A`, `L/B`, `L/K` for the cokernels,
this file proves that the following sequences are short exact:

* `0 ⟶ A ⊞ B ⟶ L ⟶ L/K ⟶ 0`,
* `0 ⟶ L ⟶ L/A ⊞ L/B ⟶ L/K ⟶ 0`,
* `0 ⟶ B ⟶ L/A ⟶ L/K ⟶ 0`.

These are the module-theoretic identities `A ∩ B = 0`, `A + B = K`, `L = L ×_{L/K} …` read in an
abelian category, and they are proved with the refinement calculus of
`Mathlib.CategoryTheory.Abelian.Refinements`.

## Main results

* `CategoryTheory.DisjointSubobjects.shortExact_desc`: the first sequence.
* `CategoryTheory.DisjointSubobjects.shortExact_lift`: the second sequence.
* `CategoryTheory.DisjointSubobjects.shortExact_quotient`: the third sequence.
* `CategoryTheory.ShortComplex.ShortExact.exists_of_iso`: a short exact sequence transported along
  isomorphisms of its three terms.
-/

@[expose] public section

namespace CategoryTheory.DisjointSubobjects

open Category Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  {L A B K : C} (a : A ⟶ L) (b : B ⟶ L) (k : K ⟶ L) [Mono a] [Mono b] [Mono k]
  (eA : A ⟶ K) (eB : B ⟶ K) (hA : eA ≫ k = a) (hB : eB ≫ k = b)
  (hepi : Epi (biprod.desc eA eB))
  (hdisj : ∀ ⦃T : C⦄ (x : T ⟶ A) (y : T ⟶ B), x ≫ a = y ≫ b → x = 0)

omit [Mono a] in
include hdisj in
/-- With trivial intersection, a map into `A` and a map into `B` with the same composite in `L`
both vanish. -/
lemma eq_zero_right {T : C} (x : T ⟶ A) (y : T ⟶ B) (h : x ≫ a = y ≫ b) : y = 0 := by
  rw [← cancel_mono b, ← h, hdisj x y h, zero_comp, zero_comp]

/-- The restriction `L/A ⟶ L/K`. -/
noncomputable abbrev quotientMapLeft : cokernel a ⟶ cokernel k :=
  cokernel.desc a (cokernel.π k) (by rw [← hA, assoc, cokernel.condition, comp_zero])

/-- The restriction `L/B ⟶ L/K`. -/
noncomputable abbrev quotientMapRight : cokernel b ⟶ cokernel k :=
  cokernel.desc b (cokernel.π k) (by rw [← hB, assoc, cokernel.condition, comp_zero])

omit [Mono a] [Mono b] in
include hA hB hepi in
/-- A map into `L` killed by `L ⟶ L/K` comes, up to refinement, from `A ⊞ B`. -/
lemma exists_desc_of_comp_π_eq_zero {T : C} (x : T ⟶ L) (hx : x ≫ cokernel.π k = 0) :
    ∃ (T' : C) (π : T' ⟶ T) (_ : Epi π) (y : T' ⟶ A ⊞ B), π ≫ x = y ≫ biprod.desc a b := by
  obtain ⟨T', π, hπ, y, hy⟩ := surjective_up_to_refinements_of_epi (biprod.desc eA eB)
    (Abelian.monoLift k x hx)
  refine ⟨T', π, hπ, y, ?_⟩
  rw [← Abelian.monoLift_comp k x hx, ← assoc, hy, assoc]
  congr 1
  apply biprod.hom_ext' <;> simp [hA, hB]

omit [Mono a] in
include hdisj in
/-- With trivial intersection, `A ⊞ B ⟶ L` is a monomorphism. -/
lemma mono_desc : Mono (biprod.desc a b) := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro T z hz
  have h : (z ≫ biprod.fst) ≫ a = (-(z ≫ biprod.snd)) ≫ b := by
    rw [Preadditive.neg_comp, eq_neg_iff_add_eq_zero, assoc, assoc, ← hz, ← Preadditive.comp_add]
    congr 1
    apply biprod.hom_ext' <;> simp
  have h1 := hdisj _ _ h
  have h2 := eq_zero_right a b hdisj _ _ h
  rw [neg_eq_zero] at h2
  apply biprod.hom_ext <;> simpa

omit [Mono a] in
include hA hB hepi hdisj in
/-- **`0 ⟶ A ⊞ B ⟶ L ⟶ L/K ⟶ 0` is short exact.** -/
lemma shortExact_desc :
    (ShortComplex.mk (biprod.desc a b) (cokernel.π k) (by
      apply biprod.hom_ext' <;> simp [← hA, ← hB])).ShortExact where
  mono_f := mono_desc a b hdisj
  exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro T x hx
    exact exists_desc_of_comp_π_eq_zero a b k eA eB hA hB hepi x hx

include hA hB hepi hdisj in
/-- **`0 ⟶ L ⟶ L/A ⊞ L/B ⟶ L/K ⟶ 0` is short exact**, the second map being the difference of the
two restrictions. -/
lemma shortExact_lift :
    (ShortComplex.mk (biprod.lift (cokernel.π a) (cokernel.π b))
      (biprod.desc (quotientMapLeft a k eA hA) (-quotientMapRight b k eB hB)) (by
        rw [biprod.lift_desc, Preadditive.comp_neg, cokernel.π_desc, cokernel.π_desc,
          add_neg_cancel])).ShortExact where
  mono_f := by
    rw [Preadditive.mono_iff_cancel_zero]
    intro T x hx
    have hxa : x ≫ cokernel.π a = 0 := by simpa using hx =≫ biprod.fst
    have hxb : x ≫ cokernel.π b = 0 := by simpa using hx =≫ biprod.snd
    have h := (Abelian.monoLift_comp a x hxa).trans (Abelian.monoLift_comp b x hxb).symm
    show x = 0
    rw [← Abelian.monoLift_comp a x hxa, hdisj _ _ h, zero_comp]
  exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro T w hw
    obtain ⟨T₁, π₁, hπ₁, s, hs⟩ := surjective_up_to_refinements_of_epi (cokernel.π a)
      (w ≫ biprod.fst)
    obtain ⟨T₂, π₂, hπ₂, t, ht⟩ := surjective_up_to_refinements_of_epi (cokernel.π b)
      (π₁ ≫ w ≫ biprod.snd)
    have hst : (π₂ ≫ s - t) ≫ cokernel.π k = 0 := by
      have h1 : s ≫ cokernel.π k = π₁ ≫ w ≫ biprod.fst ≫ quotientMapLeft a k eA hA := by
        rw [← cokernel.π_desc a (cokernel.π k), ← assoc s, ← hs, assoc, assoc]
      have h2 : t ≫ cokernel.π k = π₂ ≫ π₁ ≫ w ≫ biprod.snd ≫ quotientMapRight b k eB hB := by
        rw [← cokernel.π_desc b (cokernel.π k), ← assoc t, ← ht, assoc, assoc, assoc]
      have h3 : w ≫ biprod.fst ≫ quotientMapLeft a k eA hA =
          w ≫ biprod.snd ≫ quotientMapRight b k eB hB := by
        rw [← sub_eq_zero, ← Preadditive.comp_sub, ← hw]
        congr 1
        apply biprod.hom_ext' <;> simp [sub_eq_add_neg]
      rw [Preadditive.sub_comp, assoc, h1, h2, h3, sub_self]
    obtain ⟨T₃, π₃, hπ₃, y, hy⟩ :=
      exists_desc_of_comp_π_eq_zero a b k eA eB hA hB hepi _ hst
    have hdesc : biprod.desc a b = biprod.fst ≫ a + biprod.snd ≫ b := by
      apply biprod.hom_ext' <;> simp
    have hy' : π₃ ≫ π₂ ≫ s = π₃ ≫ t + (y ≫ biprod.fst ≫ a + y ≫ biprod.snd ≫ b) := by
      rw [← Preadditive.comp_add, ← hdesc, ← hy, Preadditive.comp_sub, add_sub_cancel]
    refine ⟨T₃, π₃ ≫ π₂ ≫ π₁, inferInstance,
      π₃ ≫ π₂ ≫ s - y ≫ biprod.fst ≫ a, ?_⟩
    show (π₃ ≫ π₂ ≫ π₁) ≫ w = (π₃ ≫ π₂ ≫ s - y ≫ biprod.fst ≫ a) ≫
      biprod.lift (cokernel.π a) (cokernel.π b)
    have e : π₃ ≫ π₂ ≫ s - y ≫ biprod.fst ≫ a = π₃ ≫ t + y ≫ biprod.snd ≫ b := by
      rw [hy']
      abel
    apply biprod.hom_ext
    · simp only [assoc, biprod.lift_fst, Preadditive.sub_comp, cokernel.condition, comp_zero,
        sub_zero]
      rw [← hs]
    · rw [e]
      simp only [assoc, biprod.lift_snd, Preadditive.add_comp, cokernel.condition, comp_zero,
        add_zero]
      rw [← ht]
  epi_g := by
    have : Epi (quotientMapLeft a k eA hA) := epi_of_epi_fac (cokernel.π_desc _ _ _)
    exact epi_of_epi_fac (biprod.inl_desc _ _)


include hA hB hepi hdisj in
/-- **`0 ⟶ B ⟶ L/A ⟶ L/K ⟶ 0` is short exact.** -/
lemma shortExact_quotient :
    (ShortComplex.mk (b ≫ cokernel.π a) (quotientMapLeft a k eA hA) (by
      rw [assoc, cokernel.π_desc, ← hB, assoc, cokernel.condition, comp_zero])).ShortExact where
  mono_f := by
    rw [Preadditive.mono_iff_cancel_zero]
    intro T z hz
    have hz' : (z ≫ b) ≫ cokernel.π a = 0 := by rw [assoc]; exact hz
    exact eq_zero_right a b hdisj _ _ (Abelian.monoLift_comp a (z ≫ b) hz')
  exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro T w hw
    obtain ⟨T₁, π₁, hπ₁, s, hs⟩ := surjective_up_to_refinements_of_epi (cokernel.π a) w
    have hs0 : s ≫ cokernel.π k = 0 := by
      rw [← cokernel.π_desc a (cokernel.π k), ← assoc s, ← hs, assoc]
      show π₁ ≫ w ≫ quotientMapLeft a k eA hA = 0
      rw [hw, comp_zero]
    obtain ⟨T₂, π₂, hπ₂, y, hy⟩ :=
      exists_desc_of_comp_π_eq_zero a b k eA eB hA hB hepi s hs0
    refine ⟨T₂, π₂ ≫ π₁, inferInstance, y ≫ biprod.snd, ?_⟩
    have hdesc : biprod.desc a b = biprod.fst ≫ a + biprod.snd ≫ b := by
      apply biprod.hom_ext' <;> simp
    show (π₂ ≫ π₁) ≫ w = (y ≫ biprod.snd) ≫ b ≫ cokernel.π a
    rw [assoc, hs, ← assoc, hy, hdesc, Preadditive.comp_add, Preadditive.add_comp, assoc, assoc,
      assoc, cokernel.condition, comp_zero, comp_zero, zero_add, assoc, assoc]
  epi_g := epi_of_epi_fac (cokernel.π_desc _ _ _)


/-- **Short exactness transported along isomorphisms of the three terms**: if `S` is short
exact and `X₁ ≅ S.X₁`, `X₂ ≅ S.X₂`, `X₃ ≅ S.X₃`, there is a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
lemma _root_.CategoryTheory.ShortComplex.ShortExact.exists_of_iso {S : ShortComplex C}
    (hS : S.ShortExact) {X₁ X₂ X₃ : C} (e₁ : X₁ ≅ S.X₁) (e₂ : X₂ ≅ S.X₂) (e₃ : X₃ ≅ S.X₃) :
    ∃ (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (w : f ≫ g = 0), (ShortComplex.mk f g w).ShortExact := by
  refine ⟨e₁.hom ≫ S.f ≫ e₂.inv, e₂.hom ≫ S.g ≫ e₃.inv, by simp, ?_⟩
  refine ShortComplex.shortExact_of_iso ?_ hS
  exact ShortComplex.isoMk e₁.symm e₂.symm e₃.symm (by simp) (by simp)

end CategoryTheory.DisjointSubobjects
