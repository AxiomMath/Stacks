module

public import StacksFrontier.Algebra.Module.TwoTermComplex.Basic
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# A finite projective model of a two-term complex of flat modules

Let `R` be a Noetherian ring and `d : C₀ ⟶ C₁` a map of flat `R`-modules whose kernel and cokernel
are finite. Choose finitely many elements of `C₁` generating the cokernel, i.e. a map
`φ₁ : K₁ = R^{⊕ n} ⟶ C₁` with `φ₁ - d : K₁ × C₀ ⟶ C₁` surjective, and let `K₀` be the kernel of
that surjection. Then the square from `K₀ ⟶ K₁` to `C₀ ⟶ C₁` is a comparison square in the sense
of `Stacks.TwoTermComplex.IsComparisonSquare`, `K₁` is finite free and `K₀` is finite projective:

* `K₀` is finite because it is an extension of a submodule of `K₁` by `ker d`;
* `K₀` is flat because it is the kernel of a surjection between flat modules;
* a finite flat module over a Noetherian ring is projective.

This is the step of Mumford's argument (*Abelian varieties*, §5, Lemma 1) for two-term complexes.

## Main definitions

* `Stacks.TwoTermComplex.FinsuppModel.K₀`, `δ`, `φ₀`, `φ₁`: the model attached to a finite family
  in `C₁`.

## Main results

* `Stacks.TwoTermComplex.FinsuppModel.isComparisonSquare`: the model is a comparison square as
  soon as the family generates the cokernel.
* `Stacks.TwoTermComplex.FinsuppModel.finite_K₀`, `flat_K₀`, `projective_K₀`.
* `Stacks.TwoTermComplex.flat_ker_of_surjective`: the kernel of a surjection between flat modules
  is flat.
-/

@[expose] public section

open TensorProduct

universe u

namespace Stacks.TwoTermComplex

variable {R : Type u} [CommRing R]

/-- **A product of two flat modules is flat.** -/
theorem flat_prod {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Flat R M] [Module.Flat R N] : Module.Flat R (M × N) := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro P P' _ _ _ _ f hf
  have hM := Module.Flat.lTensor_preserves_injective_linearMap (M := M) f hf
  have hN := Module.Flat.lTensor_preserves_injective_linearMap (M := N) f hf
  have hcomm : ⇑(TensorProduct.prodLeft R R M N P') ∘ ⇑(f.lTensor (M × N)) =
      ⇑((f.lTensor M).prodMap (f.lTensor N)) ∘ ⇑(TensorProduct.prodLeft R R M N P) := by
    funext x
    induction x using TensorProduct.inductionOn with
    | tmul m p =>
      obtain ⟨a, b⟩ := m
      simp [TensorProduct.prodLeft_tmul]
    | add x y hx hy =>
      simp only [Function.comp_apply, map_add] at hx hy ⊢
      rw [hx, hy]
  have : Function.Injective
      (⇑(TensorProduct.prodLeft R R M N P') ∘ ⇑(f.lTensor (M × N))) := by
    rw [hcomm]
    exact (Prod.map_injective.mpr ⟨hM, hN⟩).comp (TensorProduct.prodLeft R R M N P).injective
  exact Function.Injective.of_comp this

/-- **The kernel of a surjection of flat modules is flat.** For an injective `f : N ⟶ N'` the map
`f ⊗ K ⟶ ...` is read inside `N' ⊗ E`: `N ⊗ K ⟶ N ⊗ E` is injective because `P` is flat, and
`N ⊗ E ⟶ N' ⊗ E` because `E` is. -/
theorem flat_ker_of_surjective {E P : Type u} [AddCommGroup E] [AddCommGroup P] [Module R E]
    [Module R P] [Module.Flat R E] [Module.Flat R P] (π : E →ₗ[R] P)
    (hπ : Function.Surjective π) : Module.Flat R (LinearMap.ker π) := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ f hf
  have h1 : Function.Injective ((LinearMap.ker π).subtype.lTensor N) :=
    LinearMap.lTensor_injective_of_exact_of_flat π hπ _ (LinearMap.ker π).subtype_injective
      (LinearMap.exact_subtype_ker_map π) N
  have h2 : Function.Injective (f.rTensor E) :=
    Module.Flat.rTensor_preserves_injective_linearMap f hf
  have hcomm : ((LinearMap.ker π).subtype.lTensor N') ∘ₗ (f.rTensor (LinearMap.ker π)) =
      (f.rTensor E) ∘ₗ ((LinearMap.ker π).subtype.lTensor N) := by
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  have h3 : Function.Injective
      (((LinearMap.ker π).subtype.lTensor N') ∘ₗ (f.rTensor (LinearMap.ker π))) := by
    rw [hcomm]; exact h2.comp h1
  exact Function.Injective.of_comp h3

namespace FinsuppModel

variable {C₀ C₁ : Type u} [AddCommGroup C₀] [AddCommGroup C₁] [Module R C₀] [Module R C₁]
  (d : C₀ →ₗ[R] C₁) {n : ℕ} (c : Fin n → C₁)

/-- The map `R^{⊕ n} ⟶ C₁` sending the basis to the chosen family. -/
noncomputable abbrev φ₁ : (Fin n →₀ R) →ₗ[R] C₁ := Finsupp.linearCombination R c

/-- The map `R^{⊕ n} × C₀ ⟶ C₁`, `(k, x) ↦ φ₁ k - d x`. -/
noncomputable abbrev π : ((Fin n →₀ R) × C₀) →ₗ[R] C₁ := (φ₁ c).coprod (-d)

/-- The module `K₀`: the kernel of `π`, i.e. the fibre product of `φ₁` and `d`. -/
noncomputable abbrev K₀ : Submodule R ((Fin n →₀ R) × C₀) := LinearMap.ker (π d c)

/-- The map `K₀ ⟶ K₁` of the model. -/
noncomputable abbrev δ : K₀ d c →ₗ[R] (Fin n →₀ R) :=
  LinearMap.fst R _ _ ∘ₗ (K₀ d c).subtype

/-- The map `K₀ ⟶ C₀` of the model. -/
noncomputable abbrev φ₀ : K₀ d c →ₗ[R] C₀ := LinearMap.snd R _ _ ∘ₗ (K₀ d c).subtype

/-- The pair `(δ, φ₀) : K₀ ⟶ R^{⊕ n} × C₀` is the inclusion of `K₀`. -/
theorem prod_δ_φ₀ : (δ d c).prod (φ₀ d c) = (K₀ d c).subtype := by
  ext x <;> rfl

/-- An element `(k, x)` of `K₀` satisfies `φ₁ k = d x`. -/
private theorem φ₁_eq_of_mem_K₀ {x : (Fin n →₀ R) × C₀} (hx : x ∈ K₀ d c) :
    φ₁ c x.1 = d x.2 :=
  sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hx)

/-- **The model is a comparison square** as soon as `φ₁ - d` is surjective, i.e. as soon as the
family `c` generates the cokernel of `d`. -/
theorem isComparisonSquare (hsurj : Function.Surjective (π d c)) :
    IsComparisonSquare (δ d c) d (φ₀ d c) (φ₁ c) where
  comm := by
    ext ⟨⟨k, x⟩, hx⟩
    exact φ₁_eq_of_mem_K₀ d c hx
  injective := by rw [prod_δ_φ₀]; exact Subtype.val_injective
  exact := by rw [prod_δ_φ₀]; exact LinearMap.exact_subtype_ker_map _
  surjective := hsurj

/-- `π` is surjective when the family generates `C₁` modulo the image of `d`. -/
theorem surjective_π (hc : Submodule.span R (Set.range c) ⊔ LinearMap.range d = ⊤) :
    Function.Surjective (π d c) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hc]
  refine sup_le ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨(Finsupp.single i 1, 0), by simp⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨(0, -x), by simp⟩

/-- **`K₀` is finite** over a Noetherian ring when `ker d` is: it is an extension of a submodule
of the finite free module `R^{⊕ n}` by `ker d`. -/
theorem finite_K₀ [IsNoetherianRing R] (hker : Module.Finite R (LinearMap.ker d)) :
    Module.Finite R (K₀ d c) := by
  have hmap : ((⊤ : Submodule R (K₀ d c)).map (δ d c)).FG := IsNoetherian.noetherian _
  have hinf : ((⊤ : Submodule R (K₀ d c)) ⊓ LinearMap.ker (δ d c)).FG := by
    rw [top_inf_eq]
    -- the kernel of `δ` is identified with `ker d` by `φ₀`
    have e : LinearMap.ker (δ d c) ≃ₗ[R] LinearMap.ker d :=
      LinearEquiv.ofBijective ((φ₀ d c).restrict fun x hx => by
          obtain ⟨⟨⟨k, y⟩, hky⟩, rfl⟩ : ∃ z : K₀ d c, z = x := ⟨x, rfl⟩
          simp only [LinearMap.mem_ker] at hx ⊢
          have hk : k = 0 := hx
          simpa [hk] using (φ₁_eq_of_mem_K₀ d c hky).symm)
        ⟨fun x y hxy => by
          apply Subtype.ext; apply Subtype.ext
          have h1 : (x : K₀ d c).1.1 = 0 := LinearMap.mem_ker.mp x.2
          have h2 : (y : K₀ d c).1.1 = 0 := LinearMap.mem_ker.mp y.2
          have h3 : (x : K₀ d c).1.2 = (y : K₀ d c).1.2 := congrArg Subtype.val hxy
          exact Prod.ext (h1.trans h2.symm) h3,
        fun y => ⟨⟨⟨(0, y), by simp [LinearMap.mem_ker.mp y.2]⟩, rfl⟩, rfl⟩⟩
    have : Module.Finite R (LinearMap.ker (δ d c)) := Module.Finite.equiv e.symm
    exact (Submodule.fg_top _).mp (Module.finite_def.mp this)
  exact Module.finite_def.mpr (Submodule.fg_of_fg_map_of_fg_inf_ker (δ d c) hmap hinf)

/-- **`K₀` is flat** when `C₀` and `C₁` are and `π` is onto. -/
theorem flat_K₀ [Module.Flat R C₀] [Module.Flat R C₁] (hsurj : Function.Surjective (π d c)) :
    Module.Flat R (K₀ d c) :=
  have : Module.Flat R ((Fin n →₀ R) × C₀) := flat_prod
  flat_ker_of_surjective (π d c) hsurj

/-- **`K₀` is finite projective** over a Noetherian ring. -/
theorem projective_K₀ [IsNoetherianRing R] [Module.Flat R C₀] [Module.Flat R C₁]
    (hsurj : Function.Surjective (π d c)) (hker : Module.Finite R (LinearMap.ker d)) :
    Module.Projective R (K₀ d c) :=
  have := finite_K₀ d c hker
  have := flat_K₀ d c hsurj
  have := Module.finitePresentation_of_finite R (K₀ d c)
  Module.Flat.projective_of_finitePresentation

end FinsuppModel

/-- **Every two-term complex of flat modules over a Noetherian ring with finite kernel and
cokernel admits a comparison square from a complex `K₀ ⟶ K₁` with `K₁` finite free and `K₀`
finite projective.** -/
theorem exists_finsuppModel [IsNoetherianRing R] {C₀ C₁ : Type u} [AddCommGroup C₀]
    [AddCommGroup C₁] [Module R C₀] [Module R C₁] [Module.Flat R C₀] [Module.Flat R C₁]
    (d : C₀ →ₗ[R] C₁)
    (hcoker : Module.Finite R (C₁ ⧸ LinearMap.range d)) :
    ∃ (n : ℕ) (c : Fin n → C₁), Function.Surjective (FinsuppModel.π d c) := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := C₁ ⧸ LinearMap.range d)
  choose c hc using fun i => Submodule.Quotient.mk_surjective (LinearMap.range d) (s i)
  refine ⟨n, c, FinsuppModel.surjective_π d c ?_⟩
  rw [eq_top_iff]
  intro y _
  have hy : Submodule.Quotient.mk (p := LinearMap.range d) y ∈ Submodule.span R (Set.range s) := by
    rw [hs]; trivial
  have : Submodule.span R (Set.range s) =
      (Submodule.span R (Set.range c)).map (LinearMap.range d).mkQ := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext i
    exact (hc i).symm
  rw [this] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  have hmem : y - z ∈ LinearMap.range d := by
    rw [← Submodule.Quotient.eq]; exact hzy.symm
  have : y = z + (y - z) := by abel
  rw [this]
  exact Submodule.add_mem_sup hz hmem

end Stacks.TwoTermComplex
