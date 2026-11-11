module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import StacksCore.CategoryTheory.Preadditive.Biproducts
public import StacksCore.Tactic.StacksAttribute

/-!
# Kernels, cokernels and splittings of idempotents in a preadditive category

Let `f : x ⟶ x` be an idempotent endomorphism in a preadditive category and `g = 𝟙 x - f`.
This file proves the elementary facts of Stacks, Homology, Section 12.3 (end): `g` is again
idempotent and `f ≫ g = g ≫ f = 0`; a kernel of `f` is a retract of `x` whose retraction is a
cokernel of `f` (and dually); if `f` and `g` each have a kernel or a cokernel then
`x ≅ Ker f ⊞ Ker g`; and for a split monomorphism `j` with retraction `q`, `j` is a kernel and
`q` a cokernel of `𝟙 x - q ≫ j`, and `x ≅ Ker (q ≫ j) ⊞ y`.

Stacks writes composition as `∘`; here `a ≫ b` is `b ∘ a`, so the Stacks equation `g = i ∘ p`
reads `p ≫ i = g`, and `q ∘ j = id` reads `j ≫ q = 𝟙`.

## Main results

* `comp_id_sub_eq_zero_and_id_sub_comp_eq_zero_and_id_sub_idem` (Stacks 0H9N).
* `comp_retraction_eq_id_and_isColimit_of_isLimit_kernelFork_idempotent` and its three
  companions (Stacks 0H9P (1)–(4)).
* `nonempty_biprod_iso_of_idempotent_kernel_or_cokernel` (Stacks 0H9Q).
* `nonempty_isLimit_kernelFork_id_sub_of_retraction`,
  `nonempty_isColimit_cokernelCofork_id_sub_of_retraction` (Stacks 0H9R (1), (2)).
* `kernel_cokernel_biprod_of_retraction` (Stacks 0H9S).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Idempotents

variable {C : Type*} [Category* C] [Preadditive C]

/-- **Stacks 0H9N.** For an idempotent `f : x ⟶ x` of a preadditive category, with
`g = 𝟙 x - f`, one has `f ∘ g = 0`, `g ∘ f = 0` and `g ∘ g = g`. -/
@[stacks 0H9N]
theorem comp_id_sub_eq_zero_and_id_sub_comp_eq_zero_and_id_sub_idem {x : C} (f : x ⟶ x)
    (hf : f ≫ f = f) :
    (𝟙 x - f) ≫ f = 0 ∧ f ≫ (𝟙 x - f) = 0 ∧ (𝟙 x - f) ≫ (𝟙 x - f) = 𝟙 x - f := by
  refine ⟨?_, ?_, idem_of_id_sub_idem f hf⟩
  · simp [Preadditive.sub_comp, hf]
  · simp [Preadditive.comp_sub, hf]

section KernelCokernel

variable {x K : C} {f : x ⟶ x}

/-- Part (1) of Stacks 0H9P as a construction: if `i` is a kernel of the idempotent `f` and
`p ≫ i = 𝟙 x - f`, then `p` is a cokernel of `f`. -/
def isColimitCokernelCoforkOfIsLimitKernelForkIdempotent (hf : f ≫ f = f) {i : K ⟶ x}
    (hi : i ≫ f = 0) (hlim : IsLimit (KernelFork.ofι i hi)) {p : x ⟶ K}
    (hp : p ≫ i = 𝟙 x - f) (hfp : f ≫ p = 0) :
    IsColimit (CokernelCofork.ofπ p hfp) :=
  have hmono : Mono i := Fork.IsLimit.mono hlim
  have hip : i ≫ p = 𝟙 K := by
    rw [← cancel_mono i, Category.assoc, hp, Preadditive.comp_sub, hi, sub_zero,
      Category.comp_id, Category.id_comp]
  CokernelCofork.IsColimit.ofπ _ _ (fun a _ ↦ i ≫ a)
    (fun a ha ↦ by
      rw [← Category.assoc, hp, Preadditive.sub_comp, ha, sub_zero, Category.id_comp])
    (fun a _ m hm ↦ by rw [← hm, ← Category.assoc, hip, Category.id_comp])

/-- **Stacks 0H9P (1).** Let `f : x ⟶ x` be idempotent in a preadditive category, with
kernel `i : K ⟶ x`, and let `p : x ⟶ K` be the (unique) morphism with `g = i ∘ p`, where
`g = 𝟙 x - f`. Then `p ∘ i = 𝟙 K` and `p` is a cokernel of `f`. -/
@[stacks 0H9P "(1)"]
theorem comp_retraction_eq_id_and_isColimit_of_isLimit_kernelFork_idempotent
    (hf : f ≫ f = f) {i : K ⟶ x} (hi : i ≫ f = 0) (hlim : IsLimit (KernelFork.ofι i hi))
    {p : x ⟶ K} (hp : p ≫ i = 𝟙 x - f) :
    i ≫ p = 𝟙 K ∧ ∃ hfp : f ≫ p = 0, Nonempty (IsColimit (CokernelCofork.ofπ p hfp)) := by
  have hmono : Mono i := Fork.IsLimit.mono hlim
  have hfp : f ≫ p = 0 := by
    rw [← cancel_mono i, Category.assoc, hp, Preadditive.comp_sub, Category.comp_id, hf,
      sub_self, zero_comp]
  refine ⟨?_, hfp, ⟨isColimitCokernelCoforkOfIsLimitKernelForkIdempotent hf hi hlim hp hfp⟩⟩
  rw [← cancel_mono i, Category.assoc, hp, Preadditive.comp_sub, hi, sub_zero,
    Category.comp_id, Category.id_comp]

/-- Part (2) of Stacks 0H9P as a construction: if `p` is a cokernel of the idempotent `f` and
`p ≫ i = 𝟙 x - f`, then `i` is a kernel of `f`. -/
def isLimitKernelForkOfIsColimitCokernelCoforkIdempotent (hf : f ≫ f = f) {p : x ⟶ K}
    (hp : f ≫ p = 0) (hcolim : IsColimit (CokernelCofork.ofπ p hp)) {i : K ⟶ x}
    (hpi : p ≫ i = 𝟙 x - f) (hif : i ≫ f = 0) :
    IsLimit (KernelFork.ofι i hif) :=
  have hepi : Epi p := Cofork.IsColimit.epi hcolim
  have hip : i ≫ p = 𝟙 K := by
    rw [← cancel_epi p, ← Category.assoc, hpi, Preadditive.sub_comp, hp, sub_zero,
      Category.comp_id, Category.id_comp]
  KernelFork.IsLimit.ofι _ _ (fun a _ ↦ a ≫ p)
    (fun a ha ↦ by
      rw [Category.assoc, hpi, Preadditive.comp_sub, ha, sub_zero, Category.comp_id])
    (fun a _ m hm ↦ by rw [← hm, Category.assoc, hip, Category.comp_id])

/-- **Stacks 0H9P (2).** Let `f : x ⟶ x` be idempotent in a preadditive category, with
cokernel `p : x ⟶ K`, and let `i : K ⟶ x` be the (unique) morphism with `g = i ∘ p`, where
`g = 𝟙 x - f`. Then `p ∘ i = 𝟙 K` and `i` is a kernel of `f`. -/
@[stacks 0H9P "(2)"]
theorem comp_retraction_eq_id_and_isLimit_of_isColimit_cokernelCofork_idempotent
    (hf : f ≫ f = f) {p : x ⟶ K} (hp : f ≫ p = 0) (hcolim : IsColimit (CokernelCofork.ofπ p hp))
    {i : K ⟶ x} (hpi : p ≫ i = 𝟙 x - f) :
    i ≫ p = 𝟙 K ∧ ∃ hif : i ≫ f = 0, Nonempty (IsLimit (KernelFork.ofι i hif)) := by
  have hepi : Epi p := Cofork.IsColimit.epi hcolim
  have hif : i ≫ f = 0 := by
    rw [← cancel_epi p, ← Category.assoc, hpi, Preadditive.sub_comp, Category.id_comp, hf,
      sub_self, comp_zero]
  refine ⟨?_, hif, ⟨isLimitKernelForkOfIsColimitCokernelCoforkIdempotent hf hp hcolim hpi hif⟩⟩
  rw [← cancel_epi p, ← Category.assoc, hpi, Preadditive.sub_comp, hp, sub_zero,
    Category.comp_id, Category.id_comp]

/-- **Stacks 0H9P (3).** Let `f : x ⟶ x` be idempotent in a preadditive category and
`g = 𝟙 x - f`. If `g` has kernel `j : L ⟶ x` and `q : x ⟶ L` is the (unique) morphism with
`f = j ∘ q`, then `q ∘ j = 𝟙 L` and `q` is a cokernel of `g`. -/
@[stacks 0H9P "(3)"]
theorem comp_retraction_eq_id_and_isColimit_of_isLimit_kernelFork_id_sub_idempotent
    (hf : f ≫ f = f) {j : K ⟶ x} (hj : j ≫ (𝟙 x - f) = 0)
    (hlim : IsLimit (KernelFork.ofι j hj)) {q : x ⟶ K} (hq : q ≫ j = f) :
    j ≫ q = 𝟙 K ∧
      ∃ hgq : (𝟙 x - f) ≫ q = 0, Nonempty (IsColimit (CokernelCofork.ofπ q hgq)) :=
  comp_retraction_eq_id_and_isColimit_of_isLimit_kernelFork_idempotent
    (idem_of_id_sub_idem f hf) hj hlim (by rw [hq, sub_sub_cancel])

/-- **Stacks 0H9P (4).** Let `f : x ⟶ x` be idempotent in a preadditive category and
`g = 𝟙 x - f`. If `g` has cokernel `q : x ⟶ L` and `j : L ⟶ x` is the (unique) morphism with
`f = j ∘ q`, then `q ∘ j = 𝟙 L` and `j` is a kernel of `g`. -/
@[stacks 0H9P "(4)"]
theorem comp_retraction_eq_id_and_isLimit_of_isColimit_cokernelCofork_id_sub_idempotent
    (hf : f ≫ f = f) {q : x ⟶ K} (hq : (𝟙 x - f) ≫ q = 0)
    (hcolim : IsColimit (CokernelCofork.ofπ q hq)) {j : K ⟶ x} (hqj : q ≫ j = f) :
    j ≫ q = 𝟙 K ∧
      ∃ hjg : j ≫ (𝟙 x - f) = 0, Nonempty (IsLimit (KernelFork.ofι j hjg)) :=
  comp_retraction_eq_id_and_isLimit_of_isColimit_cokernelCofork_idempotent
    (idem_of_id_sub_idem f hf) hq hcolim (by rw [hqj, sub_sub_cancel])

/-- **Stacks 0H9Q.** Let `f : x ⟶ x` be idempotent in a preadditive category and
`g = 𝟙 x - f`. Suppose `f` has a kernel `i : K ⟶ x` or a cokernel `p : x ⟶ K`, and `g` has a
kernel `j : L ⟶ x` or a cokernel `q : x ⟶ L`, where the remaining morphisms are those of
Stacks 0H9P, i.e. `g = i ∘ p` and `f = j ∘ q`. Then all four (co)kernels exist: `i` is a kernel
and `p` a cokernel of `f`, and `j` is a kernel and `q` a cokernel of `g` (so `K` is both
`Ker f` and `Coker f`, `L` both `Ker g` and `Coker g`), and `x ≅ K ⊞ L`, the direct sum
structure being given by `i, j, p, q`: the isomorphism is `(p, q) : x ⟶ K ⊞ L` with inverse
`[i, j] : K ⊞ L ⟶ x`. -/
@[stacks 0H9Q]
theorem nonempty_biprod_iso_of_idempotent_kernel_or_cokernel (hf : f ≫ f = f) {L : C}
    {i : K ⟶ x} {p : x ⟶ K} {j : L ⟶ x} {q : x ⟶ L}
    (hpi : p ≫ i = 𝟙 x - f) (hqj : q ≫ j = f)
    (hfK : (∃ w : i ≫ f = 0, Nonempty (IsLimit (KernelFork.ofι i w))) ∨
      (∃ w : f ≫ p = 0, Nonempty (IsColimit (CokernelCofork.ofπ p w))))
    (hgL : (∃ w : j ≫ (𝟙 x - f) = 0, Nonempty (IsLimit (KernelFork.ofι j w))) ∨
      (∃ w : (𝟙 x - f) ≫ q = 0, Nonempty (IsColimit (CokernelCofork.ofπ q w)))) :
    (∃ w : i ≫ f = 0, Nonempty (IsLimit (KernelFork.ofι i w))) ∧
      (∃ w : f ≫ p = 0, Nonempty (IsColimit (CokernelCofork.ofπ p w))) ∧
      (∃ w : j ≫ (𝟙 x - f) = 0, Nonempty (IsLimit (KernelFork.ofι j w))) ∧
      (∃ w : (𝟙 x - f) ≫ q = 0, Nonempty (IsColimit (CokernelCofork.ofπ q w))) ∧
      ∃ (_ : HasBinaryBiproduct K L) (e : x ≅ K ⊞ L),
        e.hom = biprod.lift p q ∧ e.inv = biprod.desc i j := by
  obtain ⟨hip, hK₁, hK₂⟩ : i ≫ p = 𝟙 K ∧
      (∃ w : i ≫ f = 0, Nonempty (IsLimit (KernelFork.ofι i w))) ∧
      (∃ w : f ≫ p = 0, Nonempty (IsColimit (CokernelCofork.ofπ p w))) := by
    rcases hfK with ⟨w, ⟨hl⟩⟩ | ⟨w, ⟨hc⟩⟩
    · obtain ⟨h1, h2⟩ :=
        comp_retraction_eq_id_and_isColimit_of_isLimit_kernelFork_idempotent hf w hl hpi
      exact ⟨h1, ⟨w, ⟨hl⟩⟩, h2⟩
    · obtain ⟨h1, h2⟩ :=
        comp_retraction_eq_id_and_isLimit_of_isColimit_cokernelCofork_idempotent hf w hc hpi
      exact ⟨h1, h2, ⟨w, ⟨hc⟩⟩⟩
  obtain ⟨hjq, hL₁, hL₂⟩ : j ≫ q = 𝟙 L ∧
      (∃ w : j ≫ (𝟙 x - f) = 0, Nonempty (IsLimit (KernelFork.ofι j w))) ∧
      (∃ w : (𝟙 x - f) ≫ q = 0, Nonempty (IsColimit (CokernelCofork.ofπ q w))) := by
    rcases hgL with ⟨w, ⟨hl⟩⟩ | ⟨w, ⟨hc⟩⟩
    · obtain ⟨h1, h2⟩ :=
        comp_retraction_eq_id_and_isColimit_of_isLimit_kernelFork_id_sub_idempotent hf w hl hqj
      exact ⟨h1, ⟨w, ⟨hl⟩⟩, h2⟩
    · obtain ⟨h1, h2⟩ :=
        comp_retraction_eq_id_and_isLimit_of_isColimit_cokernelCofork_id_sub_idempotent hf w hc
          hqj
      exact ⟨h1, h2, ⟨w, ⟨hc⟩⟩⟩
  have htot : p ≫ i + q ≫ j = 𝟙 x := by rw [hpi, hqj, sub_add_cancel]
  have hb := isBinaryBilimitOfTotal (BinaryBicone.mk' hip hjq htot) htot
  have : HasBinaryBiproduct K L := HasBinaryBiproduct.mk ⟨_, hb⟩
  obtain ⟨wi, hli⟩ := hK₁
  obtain ⟨wj, hlj⟩ := hL₁
  have hiq : i ≫ q = 0 := by
    calc i ≫ q = i ≫ q ≫ j ≫ q := by rw [hjq, Category.comp_id]
      _ = (i ≫ f) ≫ q := by rw [← hqj]; simp only [Category.assoc]
      _ = 0 := by rw [wi, zero_comp]
  have hjp : j ≫ p = 0 := by
    calc j ≫ p = j ≫ p ≫ i ≫ p := by rw [hip, Category.comp_id]
      _ = (j ≫ (𝟙 x - f)) ≫ p := by rw [← hpi]; simp only [Category.assoc]
      _ = 0 := by rw [wj, zero_comp]
  refine ⟨⟨wi, hli⟩, hK₂, ⟨wj, hlj⟩, hL₂, this,
    { hom := biprod.lift p q
      inv := biprod.desc i j
      hom_inv_id := by simp [htot]
      inv_hom_id := by ext <;> simp [hip, hjq, hiq, hjp] }, rfl, rfl⟩

end KernelCokernel

section Retraction

variable {x y : C} {j : y ⟶ x} {q : x ⟶ y}

/-- Part (1) of Stacks 0H9R as a construction: if `j ≫ q = 𝟙 y`, then `j` is a kernel of
`𝟙 x - q ≫ j`. -/
def isLimitKernelForkIdSubOfRetraction (hjq : j ≫ q = 𝟙 y) :
    IsLimit (KernelFork.ofι j (show j ≫ (𝟙 x - q ≫ j) = 0 by
      rw [Preadditive.comp_sub, ← Category.assoc, hjq, Category.comp_id, Category.id_comp,
        sub_self])) :=
  KernelFork.IsLimit.ofι _ _ (fun a _ ↦ a ≫ q)
    (fun a ha ↦ by
      rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at ha
      rw [Category.assoc, ← ha])
    (fun a _ m hm ↦ by rw [← hm, Category.assoc, hjq, Category.comp_id])

/-- Part (2) of Stacks 0H9R as a construction: if `j ≫ q = 𝟙 y`, then `q` is a cokernel of
`𝟙 x - q ≫ j`. -/
def isColimitCokernelCoforkIdSubOfRetraction (hjq : j ≫ q = 𝟙 y) :
    IsColimit (CokernelCofork.ofπ q (show (𝟙 x - q ≫ j) ≫ q = 0 by
      rw [Preadditive.sub_comp, Category.assoc, hjq, Category.comp_id, Category.id_comp,
        sub_self])) :=
  CokernelCofork.IsColimit.ofπ _ _ (fun a _ ↦ j ≫ a)
    (fun a ha ↦ by
      rw [Preadditive.sub_comp, Category.id_comp, sub_eq_zero] at ha
      rw [← Category.assoc, ← ha])
    (fun a _ m hm ↦ by rw [← hm, ← Category.assoc, hjq, Category.id_comp])

/-- **Stacks 0H9R (1).** Let `j : y ⟶ x` and `q : x ⟶ y` be morphisms of a preadditive
category with `q ∘ j = 𝟙 y`. Then `𝟙 x - j ∘ q` has kernel `j`. -/
@[stacks 0H9R "(1)"]
theorem nonempty_isLimit_kernelFork_id_sub_of_retraction (hjq : j ≫ q = 𝟙 y) :
    ∃ w : j ≫ (𝟙 x - q ≫ j) = 0, Nonempty (IsLimit (KernelFork.ofι j w)) :=
  ⟨_, ⟨isLimitKernelForkIdSubOfRetraction hjq⟩⟩

/-- **Stacks 0H9R (2).** Let `j : y ⟶ x` and `q : x ⟶ y` be morphisms of a preadditive
category with `q ∘ j = 𝟙 y`. Then `𝟙 x - j ∘ q` has cokernel `q`. -/
@[stacks 0H9R "(2)"]
theorem nonempty_isColimit_cokernelCofork_id_sub_of_retraction (hjq : j ≫ q = 𝟙 y) :
    ∃ w : (𝟙 x - q ≫ j) ≫ q = 0, Nonempty (IsColimit (CokernelCofork.ofπ q w)) :=
  ⟨_, ⟨isColimitCokernelCoforkIdSubOfRetraction hjq⟩⟩

/-- **Stacks 0H9S.** Let `j : y ⟶ x` and `q : x ⟶ y` be morphisms of a preadditive category
with `q ∘ j = 𝟙 y`. If `j ∘ q` has a kernel or a cokernel, then it has both, and
`x ≅ Ker (j ∘ q) ⊞ y` and `x ≅ Coker (j ∘ q) ⊞ y`, where the direct sum structures consist of
`j`, `q`, the canonical (co)kernel morphism, and a remaining morphism which is uniquely
determined: there is a unique `r : x ⟶ Ker (j ∘ q)` such that `(r, q) : x ⟶ Ker (j ∘ q) ⊞ y`
is an isomorphism with inverse `[ι, j]`, and a unique `s : Coker (j ∘ q) ⟶ x` such that
`(π, q) : x ⟶ Coker (j ∘ q) ⊞ y` is an isomorphism with inverse `[s, j]`. -/
@[stacks 0H9S]
theorem kernel_cokernel_biprod_of_retraction (hjq : j ≫ q = 𝟙 y)
    (h : HasKernel (q ≫ j) ∨ HasCokernel (q ≫ j)) :
    ∃ (_ : HasKernel (q ≫ j)) (_ : HasCokernel (q ≫ j))
      (_ : HasBinaryBiproduct (kernel (q ≫ j)) y)
      (_ : HasBinaryBiproduct (cokernel (q ≫ j)) y),
      (∃! r : x ⟶ kernel (q ≫ j), ∃ e : x ≅ kernel (q ≫ j) ⊞ y,
        e.hom = biprod.lift r q ∧ e.inv = biprod.desc (kernel.ι (q ≫ j)) j) ∧
      (∃! s : cokernel (q ≫ j) ⟶ x, ∃ e : x ≅ cokernel (q ≫ j) ⊞ y,
        e.hom = biprod.lift (cokernel.π (q ≫ j)) q ∧ e.inv = biprod.desc s j) := by
  have hf : (q ≫ j) ≫ (q ≫ j) = q ≫ j := by
    rw [Category.assoc, ← Category.assoc j, hjq, Category.id_comp]
  obtain ⟨hgf, hfg, -⟩ := comp_id_sub_eq_zero_and_id_sub_comp_eq_zero_and_id_sub_idem _ hf
  have hgL : (∃ w : j ≫ (𝟙 x - q ≫ j) = 0, Nonempty (IsLimit (KernelFork.ofι j w))) ∨
      (∃ w : (𝟙 x - q ≫ j) ≫ q = 0, Nonempty (IsColimit (CokernelCofork.ofπ q w))) :=
    Or.inl (nonempty_isLimit_kernelFork_id_sub_of_retraction hjq)
  have kerSide : ∀ [HasKernel (q ≫ j)],
      (∃ w : (q ≫ j) ≫ kernel.lift _ _ hgf = 0,
        Nonempty (IsColimit (CokernelCofork.ofπ _ w))) ∧
      ∃ (_ : HasBinaryBiproduct (kernel (q ≫ j)) y) (e : x ≅ kernel (q ≫ j) ⊞ y),
        e.hom = biprod.lift (kernel.lift _ _ hgf) q ∧
          e.inv = biprod.desc (kernel.ι (q ≫ j)) j := fun {_} ↦ by
    obtain ⟨-, h2, -, -, h5⟩ := nonempty_biprod_iso_of_idempotent_kernel_or_cokernel hf
      (i := kernel.ι _) (p := kernel.lift _ _ hgf) (kernel.lift_ι _ _ _) rfl
      (Or.inl ⟨kernel.condition _, ⟨kernelIsKernel _⟩⟩) hgL
    exact ⟨h2, h5⟩
  have cokSide : ∀ [HasCokernel (q ≫ j)],
      (∃ w : cokernel.desc _ _ hfg ≫ (q ≫ j) = 0,
        Nonempty (IsLimit (KernelFork.ofι _ w))) ∧
      ∃ (_ : HasBinaryBiproduct (cokernel (q ≫ j)) y) (e : x ≅ cokernel (q ≫ j) ⊞ y),
        e.hom = biprod.lift (cokernel.π (q ≫ j)) q ∧
          e.inv = biprod.desc (cokernel.desc _ _ hfg) j := fun {_} ↦ by
    obtain ⟨h1, -, -, -, h5⟩ := nonempty_biprod_iso_of_idempotent_kernel_or_cokernel hf
      (i := cokernel.desc _ _ hfg) (p := cokernel.π _) (cokernel.π_desc _ _ _) rfl
      (Or.inr ⟨cokernel.condition _, ⟨cokernelIsCokernel _⟩⟩) hgL
    exact ⟨h1, h5⟩
  have hK : HasKernel (q ≫ j) := by
    rcases h with h | h
    · exact h
    · obtain ⟨w, ⟨hl⟩⟩ := cokSide.1
      exact HasLimit.mk ⟨_, hl⟩
  have hC : HasCokernel (q ≫ j) := by
    obtain ⟨w, ⟨hc⟩⟩ := kerSide.1
    exact HasColimit.mk ⟨_, hc⟩
  obtain ⟨hbK, eK, hK₁, hK₂⟩ := kerSide.2
  obtain ⟨hbC, eC, hC₁, hC₂⟩ := cokSide.2
  refine ⟨hK, hC, hbK, hbC, ⟨_, ⟨eK, hK₁, hK₂⟩, fun r ⟨e, h₁, h₂⟩ ↦ ?_⟩,
    ⟨_, ⟨eC, hC₁, hC₂⟩, fun s ⟨e, h₁, h₂⟩ ↦ ?_⟩⟩
  · have htot := e.hom_inv_id
    rw [h₁, h₂, biprod.lift_desc] at htot
    rw [← cancel_mono (kernel.ι _), kernel.lift_ι, ← htot, add_sub_cancel_right]
  · have htot := e.hom_inv_id
    rw [h₁, h₂, biprod.lift_desc] at htot
    rw [← cancel_epi (cokernel.π _), cokernel.π_desc, ← htot, add_sub_cancel_right]

end Retraction

end CategoryTheory.Idempotents
