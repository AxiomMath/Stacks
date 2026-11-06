module

public import Mathlib
public import StacksFrontier.Homology.DerivedComplete.CompleteAdic

/-!
# A derived Nakayama lemma for modules

Let `A` be a commutative ring and `I ⊆ A` a finitely generated ideal. A derived complete
`A`-module whose reduction `M / I M` vanishes is itself zero.

## Main definitions

There are no new definitions.

## Main results

* `isIso_oneSubSmulShift_moduleCat_iff`: on a module, `oneSubSmulShift M f` is invertible exactly
  when the recurrence operator `(aₙ) ↦ (aₙ - f aₙ₊₁)` is bijective.
* `isIso_oneSubSmulShift_congr`: invertibility of `oneSubSmulShift` depends only on the
  isomorphism class of its argument.
* `bijective_recurrence_iff_isDerivedCompleteModule`: derived completeness of a module is the
  bijectivity of the recurrence operator `(aₙ) ↦ (aₙ - f aₙ₊₁)` on sequences, for every `f ∈ I`.
* `exists_recurrence_solution_mem_range`, `bijective_recurrence_quotient_range`: the recurrence
  stays solvable inside the image of a linear map and in the quotient by that image.
* `subsingleton_of_isDerivedCompleteModule_of_quotient_smul`: the derived Nakayama lemma
  (Stacks 09B9).

## Implementation notes

The vanishing of `M / I M` and of `M` are expressed by `Subsingleton` on the underlying types,
and the submodule `I M` is written `I • ⊤`. Derived completeness of a module is unwound into the
solvability of the recurrence `aₙ - f aₙ₊₁ = bₙ`, which is possible because countable products in
`D(A)` are computed degreewise; from that point the argument is a computation with sequences of
elements. The key step is that the quotient of a derived complete module by the image of an
endomorphism is again derived complete, proved here directly from the recurrence description
rather than through the weak Serre subcategory of derived complete modules.

## References

* [The Stacks Project, Tag 09B9](https://stacks.math.columbia.edu/tag/09B9)
* [Bhatt--Scholze, *Projectivity of the Witt vector affine Grassmannian*][BS]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

noncomputable section

universe u v

/-! ### The recurrence operator

Derived completeness of a module at `f` says that the recurrence `aₙ - f aₙ₊₁ = bₙ` is uniquely
solvable. We record this translation and then work with sequences of elements. -/

section Recurrence

variable {A : Type u} [CommRing A]

/-- The `A`-linear recurrence operator `(aₙ) ↦ (aₙ - f aₙ₊₁)` on sequences in a module. -/
private abbrev nakayamaRecurrence (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M]
    [Module A M] (f : A) : (ℕ → M) →ₗ[A] (ℕ → M) :=
  LinearMap.id - f • LinearMap.funLeft A M Nat.succ

private lemma nakayamaRecurrence_apply (M : Type v) [AddCommGroup M] [Module A M] (f : A)
    (a : ℕ → M) (n : ℕ) : nakayamaRecurrence A M f a n = a n - f • a (n + 1) := rfl

/-- On a module, `oneSubSmulShift M f` is an isomorphism exactly when the recurrence operator is
bijective. -/
theorem isIso_oneSubSmulShift_moduleCat_iff (M : ModuleCat.{v} A) (f : A) :
    IsIso (oneSubSmulShift M f) ↔
      Function.Bijective (fun a : ℕ → M => fun n => a n - f • a (n + 1)) := by
  let e := ModuleCat.piIsoPi (fun _ : ℕ => M)
  let d := ModuleCat.ofHom (nakayamaRecurrence A M f)
  have h : e.inv ≫ oneSubSmulShift M f = d ≫ e.inv := by
    apply Pi.hom_ext
    intro n
    simp only [oneSubSmulShift, milnorMap, e, Category.assoc, Pi.lift_comp_π,
      Preadditive.comp_sub, Linear.comp_smul, Category.comp_id,
      ModuleCat.piIsoPi_inv_kernel_ι]
    ext a
    rfl
  rw [← isIso_comp_left_iff e.inv, h, isIso_comp_right_iff,
    ConcreteCategory.isIso_iff_bijective]
  rfl

/-- `oneSubSmulShift` only depends on the isomorphism class of its argument. -/
theorem isIso_oneSubSmulShift_congr {C : Type*} [Category C] [Preadditive C]
    [Linear A C] [HasProductsOfShape ℕ C] {K K' : C} (e : K ≅ K') (f : A) :
    IsIso (oneSubSmulShift K f) ↔ IsIso (oneSubSmulShift K' f) := by
  have : IsIso (Limits.Pi.map (fun _ : ℕ => e.hom)) := by
    refine ⟨⟨Limits.Pi.map (fun _ : ℕ => e.inv), ?_, ?_⟩⟩
    all_goals
      apply Pi.hom_ext
      intro n
      simp [Category.assoc]
  rw [← isIso_comp_right_iff _ (Limits.Pi.map (fun _ : ℕ => e.hom)),
    oneSubSmulShift_naturality, isIso_comp_left_iff]

/-- Derived completeness of a module at `f` is the unique solvability of the recurrence
`aₙ - f aₙ₊₁ = bₙ`. -/
theorem bijective_recurrence_iff_isDerivedCompleteAt_single (M : ModuleCat.{v} A) (f : A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))] :
    IsDerivedCompleteAt ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M) f ↔
      Function.Bijective (fun a : ℕ → M => fun n => a n - f • a (n + 1)) := by
  let K := (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M
  let e := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} A) 0).app M
  have hzero : IsIso (oneSubSmulShift
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).obj K) f) ↔
      Function.Bijective (fun a : ℕ → M => fun n => a n - f • a (n + 1)) :=
    (isIso_oneSubSmulShift_congr e f).trans (isIso_oneSubSmulShift_moduleCat_iff M f)
  rw [isDerivedCompleteAt_iff_isIso, DerivedCategory.isIso_iff]
  refine ⟨fun h => hzero.mp ((isIso_homology_map_oneSubSmulShift_iff A K f 0).mp (h 0)),
    fun h n => (isIso_homology_map_oneSubSmulShift_iff A K f n).mpr ?_⟩
  rcases eq_or_ne n 0 with rfl | hn
  · exact hzero.mpr h
  · have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) n).obj K) := by
      rcases lt_or_gt_of_ne hn with hn | hn
      · exact DerivedCategory.isZero_of_isGE K 0 n hn
      · exact DerivedCategory.isZero_of_isLE K 0 n hn
    have := ModuleCat.isZero_iff_subsingleton.mp hz
    exact (isIso_oneSubSmulShift_moduleCat_iff _ f).mpr
      ⟨fun _ _ _ => Subsingleton.elim _ _, fun a => ⟨a, Subsingleton.elim _ _⟩⟩

/-- Derived completeness of a module with respect to `I` is the unique solvability of the
recurrence `aₙ - f aₙ₊₁ = bₙ` for every `f ∈ I`. -/
theorem bijective_recurrence_iff_isDerivedCompleteModule (I : Ideal A) (M : ModuleCat.{v} A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))] :
    IsDerivedCompleteModule I M ↔
      ∀ f ∈ I, Function.Bijective (fun a : ℕ → M => fun n => a n - f • a (n + 1)) :=
  forall₂_congr fun f _ => bijective_recurrence_iff_isDerivedCompleteAt_single M f

end Recurrence

/-! ### Sequences in a derived complete module -/

section Sequences

variable {A : Type u} [CommRing A] {M M₀ : Type v} [AddCommGroup M] [Module A M]
  [AddCommGroup M₀] [Module A M₀]

/-- If the recurrence is solvable in `M₀`, then it is solvable inside the image of a linear map
out of `M₀`. -/
theorem exists_recurrence_solution_mem_range (f : A) (φ : M₀ →ₗ[A] M)
    (hsurj : Function.Surjective (fun a : ℕ → M₀ => fun n => a n - f • a (n + 1)))
    (b : ℕ → M) (hb : ∀ n, b n ∈ LinearMap.range φ) :
    ∃ u : ℕ → M, (∀ n, u n ∈ LinearMap.range φ) ∧ ∀ n, u n - f • u (n + 1) = b n := by
  classical
  choose y hy using hb
  obtain ⟨x, hx⟩ := hsurj y
  refine ⟨fun n => φ (x n), fun n => ⟨x n, rfl⟩, fun n => ?_⟩
  have hxn : x n - f • x (n + 1) = y n := congrFun hx n
  calc φ (x n) - f • φ (x (n + 1)) = φ (x n - f • x (n + 1)) := by
        rw [map_sub, map_smul]
    _ = φ (y n) := by rw [hxn]
    _ = b n := hy n

/-- The quotient of a module in which the recurrence is uniquely solvable by the image of a
linear map whose source has solvable recurrence again has that property: this is the closure of
derived complete modules under cokernels, at the level of sequences. -/
theorem bijective_recurrence_quotient_range (f : A) (φ : M₀ →ₗ[A] M)
    (hM₀ : Function.Surjective (fun a : ℕ → M₀ => fun n => a n - f • a (n + 1)))
    (hM : Function.Bijective (fun a : ℕ → M => fun n => a n - f • a (n + 1))) :
    Function.Bijective
      (fun c : ℕ → (M ⧸ LinearMap.range φ) => fun n => c n - f • c (n + 1)) := by
  classical
  set N := LinearMap.range φ
  have hlift := N.mkQ_surjective.comp_left (α := ℕ)
  constructor
  · -- injectivity: a solution of the homogeneous recurrence lifts into `N`, hence vanishes
    have hinj : Function.Injective (nakayamaRecurrence A (M ⧸ N) f) := by
      rw [injective_iff_map_eq_zero]
      intro c hc
      obtain ⟨a, rfl⟩ := hlift c
      have hmem : ∀ n, a n - f • a (n + 1) ∈ N := fun n =>
        (Submodule.Quotient.mk_eq_zero N).mp (by simpa using congrFun hc n)
      obtain ⟨u, humem, hu⟩ := exists_recurrence_solution_mem_range f φ hM₀ _ hmem
      have hau : a = u := hM.1 (funext fun n => (hu n).symm)
      funext n
      exact (Submodule.Quotient.mk_eq_zero N).mpr (hau ▸ humem n)
    exact hinj
  · -- surjectivity: lift, solve in `M`, push down
    intro c
    obtain ⟨a, rfl⟩ := hlift c
    obtain ⟨x, hx⟩ := hM.2 a
    refine ⟨fun n => N.mkQ (x n), funext fun n => ?_⟩
    change N.mkQ (x n) - f • N.mkQ (x (n + 1)) = N.mkQ (a n)
    rw [← map_smul, ← map_sub, show x n - f • x (n + 1) = a n from congrFun hx n]

/-- If the recurrence is uniquely solvable in `M` at some `f` for which multiplication by `f`
is surjective, then `M` is zero. -/
private lemma subsingleton_of_bijective_recurrence_of_surjective_smul (f : A)
    (hM : Function.Bijective (fun a : ℕ → M => fun n => a n - f • a (n + 1)))
    (hsurj : Function.Surjective (fun m : M => f • m)) : Subsingleton M := by
  classical
  choose g hg using hsurj
  have hg' : ∀ m : M, f • g m = m := hg
  have hzero : ∀ x : M, x = 0 := by
    intro x
    have hfix : ∀ n, g^[n] x = f • g^[n + 1] x := by
      intro n
      rw [Function.iterate_succ_apply', hg']
    have h0 : (fun n => g^[n] x) = (0 : ℕ → M) := by
      apply hM.1
      funext n
      show g^[n] x - f • g^[n + 1] x = (0 : ℕ → M) n - f • (0 : ℕ → M) (n + 1)
      rw [← hfix n]
      simp
    simpa using congrFun h0 0
  exact subsingleton_of_forall_eq 0 hzero

end Sequences

/-! ### The derived Nakayama lemma -/

section Nakayama

variable {A : Type u} [CommRing A]

private lemma subsingleton_of_bijective_recurrence_of_span_smul_eq_top (I : Ideal A)
    (s : Finset A) (hs : (s : Set A) ⊆ I) {M : Type v} [AddCommGroup M] [Module A M]
    (hM : ∀ f ∈ I, Function.Bijective (fun a : ℕ → M => fun n => a n - f • a (n + 1)))
    (htop : Ideal.span (s : Set A) • (⊤ : Submodule A M) = ⊤) : Subsingleton M := by
  classical
  induction s using Finset.induction_on generalizing M with
  | empty =>
      have hbot : (⊥ : Submodule A M) = ⊤ := by simpa using htop
      exact (Submodule.subsingleton_iff A).mp (subsingleton_iff_bot_eq_top.mp hbot)
  | @insert f₀ s hf₀ ih =>
      have hf₀I : f₀ ∈ I := hs (Finset.mem_insert_self f₀ s)
      set φ : M →ₗ[A] M := f₀ • (LinearMap.id : M →ₗ[A] M)
      have hrange : LinearMap.range φ = Ideal.span {f₀} • (⊤ : Submodule A M) := by
        rw [Submodule.ideal_span_singleton_smul, Submodule.pointwise_smul_def,
          Submodule.map_top]
        rfl
      have hQ : ∀ f ∈ I, Function.Bijective
          (fun c : ℕ → (M ⧸ LinearMap.range φ) => fun n => c n - f • c (n + 1)) :=
        fun f hf => bijective_recurrence_quotient_range f φ (hM f hf).2 (hM f hf)
      have hsup : LinearMap.range φ ⊔ Ideal.span (s : Set A) • (⊤ : Submodule A M) = ⊤ := by
        simpa only [Finset.coe_insert, Ideal.span_insert, Submodule.sup_smul, hrange] using htop
      have hQtop : Ideal.span (s : Set A) • (⊤ : Submodule A (M ⧸ LinearMap.range φ)) = ⊤ := by
        have hmap := ((LinearMap.range φ).map_mkQ_eq_top
          (Ideal.span (s : Set A) • (⊤ : Submodule A M))).mpr hsup
        simpa only [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] using hmap
      exact subsingleton_of_bijective_recurrence_of_surjective_smul f₀ (hM f₀ hf₀I)
        (LinearMap.range_eq_top.mp (Submodule.Quotient.subsingleton_iff.mp
          (ih (fun a ha => hs (Finset.mem_insert_of_mem ha)) hQ hQtop)))

/-- **Stacks 09B9.** A derived complete module with zero reduction modulo a finitely generated
ideal is zero. -/
@[stacks 09B9]
theorem subsingleton_of_isDerivedCompleteModule_of_quotient_smul
    (A : Type u) [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    (I : Ideal A) (M : ModuleCat.{v} A) (hI : I.FG)
    (hM : IsDerivedCompleteModule I M)
    (hMI : Subsingleton (M ⧸ (I • ⊤ : Submodule A M))) : Subsingleton M := by
  obtain ⟨s, hs⟩ := hI
  refine subsingleton_of_bijective_recurrence_of_span_smul_eq_top I s
    (fun a ha => hs ▸ Submodule.subset_span ha)
    ((bijective_recurrence_iff_isDerivedCompleteModule I M).mp hM) ?_
  rw [show Ideal.span (s : Set A) = I from hs]
  exact Submodule.Quotient.subsingleton_iff.mp hMI

end Nakayama

end

end
