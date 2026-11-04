module

public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Objects on which `p^(m - a)` and `p^a` form exact sequences

Let `C` be an abelian category and `p m : ℕ`.  An object `X` is *pow-exact* if for every
`a ≤ m` every generalized element of `X` killed by `p^a` is, up to refinement, a multiple of
`p^(m - a)`.  For a sheaf of `ℤ/pᵐℤ`-modules this is flatness over `ℤ/pᵐℤ`.

The class is closed under cokernels of monomorphisms between pow-exact objects killed by
`p^m`, and such monomorphisms are pure: `A ∩ p^a B = p^a A`.  This is what keeps an injective
resolution of a flat sheaf of `ℤ/pᵐℤ`-modules exact modulo `p^{m'}`, in the change of
coefficients behind [Tag 03V2].

## Main definitions

* `CategoryTheory.Abelian.PowExact p m X`.

## Main results

* `CategoryTheory.Abelian.PowExact.of_shortExact`: the cokernel of a monomorphism of pow-exact
  objects killed by `p^m` is pow-exact.
* `CategoryTheory.Abelian.PowExact.pure`: such a monomorphism is pure.

## References

* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
-/

@[expose] public section

namespace CategoryTheory.Abelian

open CategoryTheory Limits Preadditive

variable {C : Type*} [Category* C] [Abelian C] (p m : ℕ)

/-- `X` is pow-exact if, for every `a ≤ m`, every generalized element of `X` killed by `p^a` is
a multiple of `p^(m - a)` up to refinement. -/
def PowExact (X : C) : Prop :=
  ∀ a ≤ m, ∀ ⦃T : C⦄ (x : T ⟶ X), x ≫ ((p ^ a) • 𝟙 X) = 0 →
    ∃ (T' : C) (π : T' ⟶ T) (_ : Epi π) (y : T' ⟶ X), π ≫ x = y ≫ ((p ^ (m - a)) • 𝟙 X)

variable {p m}

/-- Multiplication by `n` commutes with every morphism. -/
theorem nsmul_id_comp {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    (n • 𝟙 X) ≫ f = f ≫ (n • 𝟙 Y) := by
  rw [nsmul_comp, comp_nsmul, Category.id_comp, Category.comp_id]

/-- **Purity**: for a monomorphism `f : A ⟶ B` with `A` pow-exact and `B` killed by `p^m`, a
generalized element of `A` which is `p^a` times one of `B` is `p^a` times one of `A`, up to
refinement. -/
theorem PowExact.pure {A B : C} (f : A ⟶ B) [Mono f] (hA : PowExact p m A)
    (hB : (p ^ m) • 𝟙 B = 0) {a : ℕ} (ha : a ≤ m) {T : C} (x : T ⟶ A) (z : T ⟶ B)
    (hxz : x ≫ f = z ≫ ((p ^ a) • 𝟙 B)) :
    ∃ (T' : C) (π : T' ⟶ T) (_ : Epi π) (w : T' ⟶ A), π ≫ x = w ≫ ((p ^ a) • 𝟙 A) := by
  have hx : x ≫ ((p ^ (m - a)) • 𝟙 A) = 0 := by
    rw [← cancel_mono f, zero_comp, Category.assoc, nsmul_id_comp, ← Category.assoc, hxz,
      Category.assoc, nsmul_comp, Category.id_comp, smul_smul, ← pow_add, Nat.add_sub_cancel' ha,
      hB, comp_zero]
  obtain ⟨T', π, hπ, w, hw⟩ := hA (m - a) (Nat.sub_le m a) x hx
  rw [Nat.sub_sub_self ha] at hw
  exact ⟨T', π, hπ, w, hw⟩

/-- Given `z` into the middle term with `z ≫ p^a` mapping to zero, up to refinement `z` differs
from an element of the first term by something killed by `p^a`. -/
private theorem exists_sub_comp_nsmul_eq_zero {S : ShortComplex C} (hS : S.ShortExact)
    (h₁ : PowExact p m S.X₁) (hB : (p ^ m) • 𝟙 S.X₂ = 0) {a : ℕ} (ha : a ≤ m) {T : C}
    (z : T ⟶ S.X₂) (hz : (z ≫ ((p ^ a) • 𝟙 S.X₂)) ≫ S.g = 0) :
    ∃ (T' : C) (π : T' ⟶ T) (_ : Epi π) (w' : T' ⟶ S.X₁),
      (π ≫ z - w' ≫ S.f) ≫ ((p ^ a) • 𝟙 S.X₂) = 0 := by
  have := hS.mono_f
  obtain ⟨T₂, π₂, hπ₂, w, hw⟩ := hS.exact.exact_up_to_refinements _ hz
  obtain ⟨T₃, π₃, hπ₃, w', hw'⟩ := PowExact.pure S.f h₁ hB ha w (π₂ ≫ z)
    (by rw [← hw, Category.assoc])
  refine ⟨T₃, π₃ ≫ π₂, inferInstance, w', ?_⟩
  rw [sub_comp, sub_eq_zero]
  simp only [Category.assoc]
  rw [hw, ← Category.assoc, hw', Category.assoc, nsmul_id_comp]

/-- **The cokernel of a monomorphism of pow-exact objects killed by `p^m` is pow-exact.** -/
theorem PowExact.of_shortExact {S : ShortComplex C} (hS : S.ShortExact)
    (h₁ : PowExact p m S.X₁) (h₂ : PowExact p m S.X₂) (hB : (p ^ m) • 𝟙 S.X₂ = 0) :
    PowExact p m S.X₃ := by
  have := hS.mono_f
  have := hS.epi_g
  intro a ha T x hx
  obtain ⟨T₁, π₁, hπ₁, z, hz⟩ := surjective_up_to_refinements_of_epi S.g x
  have hz' : (z ≫ ((p ^ a) • 𝟙 S.X₂)) ≫ S.g = 0 := by
    rw [Category.assoc, nsmul_id_comp, ← Category.assoc, ← hz, Category.assoc, hx, comp_zero]
  obtain ⟨T₂, π₂, hπ₂, w, hd⟩ := exists_sub_comp_nsmul_eq_zero hS h₁ hB ha z hz'
  obtain ⟨T₃, π₃, hπ₃, v, hv⟩ := h₂ a ha _ hd
  refine ⟨T₃, π₃ ≫ π₂ ≫ π₁, inferInstance, v ≫ S.g, ?_⟩
  have e : π₃ ≫ π₂ ≫ z = v ≫ ((p ^ (m - a)) • 𝟙 S.X₂) + π₃ ≫ w ≫ S.f := by
    rw [← hv, comp_sub, sub_add_cancel]
  calc (π₃ ≫ π₂ ≫ π₁) ≫ x = (π₃ ≫ π₂ ≫ z) ≫ S.g := by
        simp only [Category.assoc, hz]
    _ = (v ≫ S.g) ≫ ((p ^ (m - a)) • 𝟙 S.X₃) := by
        rw [e]
        simp only [add_comp, Category.assoc, S.zero, comp_zero, add_zero, nsmul_id_comp]

/-- The reduction `X / p^a X` of an object, as the cokernel of `p^a`. -/
noncomputable abbrev powReduction (a : ℕ) (X : C) : C := cokernel ((p ^ a) • 𝟙 X)

/-- The map induced on reductions. -/
noncomputable abbrev powReductionMap (a : ℕ) {X Y : C} (f : X ⟶ Y) :
    powReduction (p := p) a X ⟶ powReduction (p := p) a Y :=
  cokernel.map _ _ f f (nsmul_id_comp f _)

/-- The exactness of `X --p^a--> X ⟶ X / p^a X`, up to refinement. -/
private lemma exists_of_comp_cokernel_π_eq_zero {X T : C} (a : ℕ) (x : T ⟶ X)
    (hx : x ≫ cokernel.π ((p ^ a) • 𝟙 X) = 0) :
    ∃ (T' : C) (π : T' ⟶ T) (_ : Epi π) (y : T' ⟶ X), π ≫ x = y ≫ ((p ^ a) • 𝟙 X) :=
  (ShortComplex.exact_cokernel ((p ^ a) • 𝟙 X)).exact_up_to_refinements x hx

/-- **Reduction modulo `p^a` is exact on a short exact sequence whose first term is pow-exact**
and whose middle term is killed by `p^m`. -/
theorem PowExact.reduction_shortExact {S : ShortComplex C} (hS : S.ShortExact)
    (h₁ : PowExact p m S.X₁) (hB : (p ^ m) • 𝟙 S.X₂ = 0) {a : ℕ} (ha : a ≤ m) :
    (ShortComplex.mk (powReductionMap (p := p) a S.f) (powReductionMap (p := p) a S.g)
      (by ext; simp)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro T y hy
    obtain ⟨T₁, π₁, hπ₁, y', hy'⟩ :=
      surjective_up_to_refinements_of_epi (cokernel.π ((p ^ a) • 𝟙 S.X₂)) y
    have h0 : (y' ≫ S.g) ≫ cokernel.π ((p ^ a) • 𝟙 S.X₃) = 0 := by
      have := congrArg (π₁ ≫ ·) hy
      simp only [comp_zero] at this
      rw [← this, ← Category.assoc, hy', Category.assoc, Category.assoc]
      simp
    obtain ⟨T₂, π₂, hπ₂, c, hc⟩ := exists_of_comp_cokernel_π_eq_zero _ _ h0
    obtain ⟨T₃, π₃, hπ₃, b, hb⟩ := surjective_up_to_refinements_of_epi S.g c
    have h1 : (π₃ ≫ π₂ ≫ y' - b ≫ ((p ^ a) • 𝟙 S.X₂)) ≫ S.g = 0 := by
      rw [sub_comp, sub_eq_zero]
      simp only [Category.assoc]
      rw [hc, ← Category.assoc, hb, Category.assoc, nsmul_id_comp]
    obtain ⟨T₄, π₄, hπ₄, a', ha'⟩ := hS.exact.exact_up_to_refinements _ h1
    refine ⟨T₄, π₄ ≫ π₃ ≫ π₂ ≫ π₁, inferInstance, a' ≫ cokernel.π _, ?_⟩
    have e : π₄ ≫ π₃ ≫ π₂ ≫ y' = a' ≫ S.f + π₄ ≫ b ≫ ((p ^ a) • 𝟙 S.X₂) := by
      rw [← ha', comp_sub, sub_add_cancel]
    calc (π₄ ≫ π₃ ≫ π₂ ≫ π₁) ≫ y = (π₄ ≫ π₃ ≫ π₂ ≫ y') ≫ cokernel.π ((p ^ a) • 𝟙 S.X₂) := by
          simp only [Category.assoc, hy']
      _ = (a' ≫ S.f + π₄ ≫ b ≫ ((p ^ a) • 𝟙 S.X₂)) ≫ cokernel.π ((p ^ a) • 𝟙 S.X₂) := by
          rw [e]
      _ = (a' ≫ cokernel.π _) ≫ powReductionMap (p := p) a S.f := by
          simp [add_comp]
  · rw [mono_iff_cancel_zero]
    intro T y hy
    obtain ⟨T₁, π₁, hπ₁, x, hx⟩ :=
      surjective_up_to_refinements_of_epi (cokernel.π ((p ^ a) • 𝟙 S.X₁)) y
    have h0 : (x ≫ S.f) ≫ cokernel.π ((p ^ a) • 𝟙 S.X₂) = 0 := by
      have := congrArg (π₁ ≫ ·) hy
      simp only [comp_zero] at this
      rw [← this, ← Category.assoc, hx]
      simp
    obtain ⟨T₂, π₂, hπ₂, z, hz⟩ := exists_of_comp_cokernel_π_eq_zero _ _ h0
    obtain ⟨T₃, π₃, hπ₃, w, hw⟩ := PowExact.pure S.f h₁ hB ha (π₂ ≫ x) z
      (by rw [Category.assoc, hz])
    rw [← cancel_epi (π₃ ≫ π₂ ≫ π₁), comp_zero]
    simp only [Category.assoc]
    rw [hx, ← Category.assoc π₂, ← Category.assoc π₃, hw]
    simp
  · exact epi_of_epi_fac (f := cokernel.π ((p ^ a) • 𝟙 S.X₂))
      (g := powReductionMap (p := p) a S.g) (h := S.g ≫ cokernel.π ((p ^ a) • 𝟙 S.X₃)) (by simp)

/-- `p^(m - a)` followed by `p^a` is `p^m`, which vanishes on an object killed by `p^m`. -/
theorem pow_sub_nsmul_comp_pow_nsmul {X : C} (hX : (p ^ m) • 𝟙 X = 0) {a : ℕ} (ha : a ≤ m) :
    ((p ^ (m - a)) • 𝟙 X) ≫ ((p ^ a) • 𝟙 X) = 0 := by
  rw [nsmul_comp, Category.id_comp, smul_smul, ← pow_add, Nat.sub_add_cancel ha, hX]

/-- **Pow-exactness from the exactness of `X --p^(m-a)--> X --p^a--> X`** for every `a ≤ m`. -/
theorem powExact_of_exact {X : C} (hX : (p ^ m) • 𝟙 X = 0)
    (h : ∀ a (ha : a ≤ m), (ShortComplex.mk _ _ (pow_sub_nsmul_comp_pow_nsmul hX ha)).Exact) :
    PowExact p m X :=
  fun a ha _ x hx => (h a ha).exact_up_to_refinements x hx

/-- A pow-exact object gives exact sequences `X --p^(m-a)--> X --p^a--> X`. -/
theorem PowExact.exact {X : C} (hX : (p ^ m) • 𝟙 X = 0) (h : PowExact p m X) {a : ℕ}
    (ha : a ≤ m) : (ShortComplex.mk _ _ (pow_sub_nsmul_comp_pow_nsmul hX ha)).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  exact fun _ x hx => h a ha x hx

/-- A zero object is pow-exact. -/
theorem PowExact.of_isZero {X : C} (hX : IsZero X) : PowExact p m X :=
  fun _ _ T _ _ => ⟨T, 𝟙 T, inferInstance, 0, hX.eq_of_tgt _ _⟩

/-- **A biproduct of pow-exact objects is pow-exact.** -/
theorem PowExact.biprod {X Y : C} (hX : PowExact p m X) (hY : PowExact p m Y) :
    PowExact p m (X ⊞ Y) := by
  intro a ha T x hx
  have hx₁ : (x ≫ biprod.fst) ≫ ((p ^ a) • 𝟙 X) = 0 := by
    rw [Category.assoc, ← nsmul_id_comp, ← Category.assoc, hx, zero_comp]
  obtain ⟨T₁, π₁, hπ₁, y₁, hy₁⟩ := hX a ha _ hx₁
  have hx₂ : (π₁ ≫ x ≫ biprod.snd) ≫ ((p ^ a) • 𝟙 Y) = 0 := by
    rw [Category.assoc, Category.assoc, ← nsmul_id_comp, ← Category.assoc x, hx, zero_comp,
      comp_zero]
  obtain ⟨T₂, π₂, hπ₂, y₂, hy₂⟩ := hY a ha _ hx₂
  refine ⟨T₂, π₂ ≫ π₁, inferInstance, (π₂ ≫ y₁) ≫ biprod.inl + y₂ ≫ biprod.inr, ?_⟩
  simp only [Preadditive.comp_nsmul, Category.comp_id] at hy₁ hy₂
  apply biprod.hom_ext
  · simp only [Category.assoc, Preadditive.comp_nsmul, Preadditive.nsmul_comp, add_comp,
      biprod.inl_fst, biprod.inr_fst, comp_zero, add_zero, Category.comp_id, hy₁]
  · simp only [Category.assoc, Preadditive.comp_nsmul, Preadditive.nsmul_comp, add_comp,
      biprod.inl_snd, biprod.inr_snd, comp_zero, zero_add, Category.comp_id, hy₂]

/-! ### The `p`-torsion of a short exact sequence -/

/-- `e : X' ⟶ X` exhibits `X'` as the `n`-torsion `X[n]` of `X`: it is a monomorphism killed
by `n`, through which every morphism killed by `n` factors. -/
structure IsTorsionKernel (n : ℕ) {X' X : C} (e : X' ⟶ X) : Prop where
  /-- The morphism `e` is a monomorphism. -/
  mono : Mono e
  /-- The composite of `e` with multiplication by `n` on `X` is zero. -/
  comp_eq_zero : e ≫ (n • 𝟙 X) = 0
  /-- Every morphism to `X` killed by multiplication by `n` factors through `e`. -/
  exists_lift : ∀ ⦃T : C⦄ (t : T ⟶ X), t ≫ (n • 𝟙 X) = 0 → ∃ s : T ⟶ X', s ≫ e = t

/-- A `n`-torsion kernel is a kernel of multiplication by `n`. -/
noncomputable def IsTorsionKernel.isLimit {n : ℕ} {X' X : C} {e : X' ⟶ X}
    (h : IsTorsionKernel n e) : IsLimit (KernelFork.ofι e h.comp_eq_zero) :=
  have := h.mono
  KernelFork.IsLimit.ofι _ _ (fun t ht => (h.exists_lift t ht).choose)
    (fun t ht => (h.exists_lift t ht).choose_spec)
    (fun t ht s hs => by rw [← cancel_mono e, hs, (h.exists_lift t ht).choose_spec])

/-- **A left exact additive functor preserves `n`-torsion kernels.** -/
theorem IsTorsionKernel.map {D : Type*} [Category* D] [Abelian D] (G : C ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] {n : ℕ} {X' X : C} {e : X' ⟶ X} (h : IsTorsionKernel n e) :
    IsTorsionKernel n (G.map e) := by
  have hz : G.map e ≫ (n • 𝟙 (G.obj X)) = 0 := by
    rw [← G.map_id, ← G.map_nsmul, ← G.map_comp, h.comp_eq_zero, G.map_zero]
  have hl := (KernelFork.ofι e h.comp_eq_zero).isLimitMapConeEquiv G
    (isLimitOfPreserves G h.isLimit)
  have hG : G.map (n • 𝟙 X) = n • 𝟙 (G.obj X) := by rw [G.map_nsmul, G.map_id]
  refine ⟨mono_of_isLimit_fork hl, hz, fun T t ht =>
    ⟨hl.lift (KernelFork.ofι (f := G.map (n • 𝟙 X)) t (by rwa [hG])), ?_⟩⟩
  exact Fork.IsLimit.lift_ι hl

/-- **Two `n`-torsion kernels of the same object are isomorphic**: a morphism between them over
the object is an isomorphism. -/
theorem IsTorsionKernel.isIso_of_comp {n : ℕ} {A A' X : C} {e : A ⟶ X} {e' : A' ⟶ X}
    (h : IsTorsionKernel n e) (h' : IsTorsionKernel n e') (g : A ⟶ A') (hg : g ≫ e' = e) :
    IsIso g := by
  have := h.mono
  have := h'.mono
  obtain ⟨s, hs⟩ := h.exists_lift e' h'.comp_eq_zero
  refine ⟨s, ?_, ?_⟩
  · rw [← cancel_mono e, Category.assoc, hs, hg, Category.id_comp]
  · rw [← cancel_mono e', Category.assoc, hg, hs, Category.id_comp]

/-- A pow-exact object stays pow-exact under an exact additive functor. -/
theorem PowExact.map {D : Type*} [Category* D] [Abelian D] (G : C ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] {X : C} (hX : (p ^ m) • 𝟙 X = 0)
    (h : PowExact p m X) : PowExact p m (G.obj X) := by
  have hGX : (p ^ m) • 𝟙 (G.obj X) = 0 := by
    rw [← G.map_id, ← G.map_nsmul, hX, G.map_zero]
  refine powExact_of_exact hGX (fun a ha => ?_)
  refine (ShortComplex.exact_iff_of_iso ?_).1 ((h.exact hX ha).map G)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [G.map_nsmul]) (by simp [G.map_nsmul])

/-- **Taking `p^a`-torsion is exact on a short exact sequence whose first term is pow-exact**
and whose middle term is killed by `p^m`, `a ≤ m`: if `S'` maps to `S` by `p^a`-torsion
kernels, then `S'` is short exact. -/
theorem PowExact.torsion_shortExact {S S' : ShortComplex C} (hS : S.ShortExact)
    (h₁ : PowExact p m S.X₁) (hB : (p ^ m) • 𝟙 S.X₂ = 0) {a : ℕ} (ha : a ≤ m) (ε : S' ⟶ S)
    (h₁' : IsTorsionKernel (p ^ a) ε.τ₁) (h₂' : IsTorsionKernel (p ^ a) ε.τ₂)
    (h₃' : IsTorsionKernel (p ^ a) ε.τ₃) : S'.ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have := h₁'.mono
  have := h₂'.mono
  have := h₃'.mono
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro T x hx
    have hx' : (x ≫ ε.τ₂) ≫ S.g = 0 := by
      rw [Category.assoc, ε.comm₂₃, ← Category.assoc, hx, zero_comp]
    obtain ⟨T₁, π, hπ, c, hc⟩ := hS.exact.exact_up_to_refinements _ hx'
    have hap : c ≫ ((p ^ a) • 𝟙 S.X₁) = 0 := by
      rw [← cancel_mono S.f, zero_comp, Category.assoc, nsmul_id_comp, ← Category.assoc, ← hc,
        Category.assoc, Category.assoc, h₂'.comp_eq_zero, comp_zero, comp_zero]
    obtain ⟨c', hc'⟩ := h₁'.exists_lift c hap
    refine ⟨T₁, π, hπ, c', ?_⟩
    rw [← cancel_mono ε.τ₂, Category.assoc, Category.assoc, ← ε.comm₁₂, ← Category.assoc c',
      hc', hc]
  · rw [mono_iff_cancel_zero]
    intro T u hu
    rw [← cancel_mono ε.τ₁, zero_comp, ← cancel_mono S.f, zero_comp, Category.assoc, ε.comm₁₂,
      ← Category.assoc, hu, zero_comp]
  · rw [epi_iff_surjective_up_to_refinements]
    intro T y
    obtain ⟨T₁, π₁, hπ₁, b, hb⟩ := surjective_up_to_refinements_of_epi S.g (y ≫ ε.τ₃)
    have hbp : (b ≫ ((p ^ a) • 𝟙 S.X₂)) ≫ S.g = 0 := by
      rw [Category.assoc, nsmul_id_comp, ← Category.assoc, ← hb, Category.assoc,
        Category.assoc, h₃'.comp_eq_zero, comp_zero, comp_zero]
    obtain ⟨T₂, π₂, hπ₂, w, hb'p⟩ := exists_sub_comp_nsmul_eq_zero hS h₁ hB ha b hbp
    obtain ⟨b'', hb''⟩ := h₂'.exists_lift _ hb'p
    refine ⟨T₂, π₂ ≫ π₁, inferInstance, b'', ?_⟩
    rw [← cancel_mono ε.τ₃]
    calc ((π₂ ≫ π₁) ≫ y) ≫ ε.τ₃ = (π₂ ≫ b - w ≫ S.f) ≫ S.g := by
          simp only [sub_comp, Category.assoc, S.zero, comp_zero, sub_zero, ← hb]
      _ = (b'' ≫ S'.g) ≫ ε.τ₃ := by
          rw [Category.assoc, ← ε.comm₂₃, ← Category.assoc, hb'']

end CategoryTheory.Abelian
