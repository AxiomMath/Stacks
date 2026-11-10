module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u v w

/-!
# Criteria for universal exactness of a short exact sequence of modules

Let `R` be a commutative ring and let `0 → M₁ →[f₁] M₂ →[f₂] M₃ → 0` be a short exact sequence
of `R`-modules. This file proves the equivalence of the six characterizations of universal
exactness of Stacks 058K: universal injectivity of `f₁`, exactness of the sequence tensored with
a finitely presented module, the solvability criterion for systems of linear equations in element
and in diagram form, surjectivity of `Hom_R(P, M₂) → Hom_R(P, M₃)` for finitely presented `P`,
and the presentation of the sequence as a directed colimit of split exact sequences with
finitely presented cokernels.

The cycle of implications is the source's: (1) ⇒ (2) is right exactness of the tensor product,
(2) ⇒ (3) tests item (2) on the cokernel `Q` of the map `Rᵐ → Rⁿ` given by the matrix of
coefficients and chases the diagram obtained by tensoring `Rᵐ → Rⁿ → Q → 0` with `f₁`,
(3) ⇒ (4) reads a commutative square off its values on the standard bases, (4) ⇒ (5) lifts a map
from a finitely presented module through a presentation of it, and (5) ⇒ (6) writes `M₃`
as a directed colimit of finitely presented modules and takes fibre products. The cycle is
closed by (6) ⇒ (3), which solves a linear system at a stage of the directed system, where the
retraction of the splitting solves it, together with (3) ⇒ (1).

## Main results

* `Stacks.RingTheory.UniversalExactTFAE.solution`: items (1)–(6) of Stacks 058K, in the source's
  order, as a `List.TFAE`.

## Implementation notes

The source closes the cycle with (6) ⇒ (1), by the stability of a colimit of split exact
sequences under tensoring (Stacks 058J (2)). Here the two implications that leave item (6) and
return to item (1) are split differently: (3) ⇒ (1) is proved directly, and (6) is left through
item (3). Both proofs are elementary. For (3) ⇒ (1): an element of `M₁ ⊗ Q` involves finitely
many elements of `Q`, and the vanishing of its image in `M₂ ⊗ Q` involves finitely many
relations between them, so the test module `Q` may be replaced by the cokernel of a matrix, and
for such a `Q` item (3) is exactly the injectivity of `f₁ ⊗ Q` read through
`mem_range_mulVecModule_iff` — the reverse reading of the diagram of the source's (2) ⇒ (3).
The resulting cycle is (1) ⇒ (2) ⇒ (3) ⇒ (1) together with (3) ⇒ (4) ⇒ (5) ⇒ (6) ⇒ (3).

The multiplication of a vector of module elements by a matrix over `R`, which is the map
`M₁^{⊕m} → M₁^{⊕n}` of the source's proof of (2) ⇒ (3), is `mulVecModule`; it is
`Matrix.mulVecLin` with entries in a module. Its two properties used here are that it is
compatible with the isomorphism `N ⊗ Rⁿ ≃ Nⁿ` (`piScalarRight_comp_lTensor`) and that its image
is described by the vanishing of a class in `N ⊗ Q` with `Q` the cokernel
(`mem_range_mulVecModule_iff`); together these are the two rows of the source's diagram.

## References

* [StacksProject 058K](https://stacks.math.columbia.edu/tag/058K)
-/

namespace Stacks.RingTheory.UniversalExactTFAE



open LinearMap TensorProduct CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R]

/-! ### Matrices acting on vectors of module elements -/

/-- Multiplication of a vector of elements of an `R`-module `N` by a matrix `a` over `R`:
the map `Nᵏ → Nⁱ` sending `z` to `fun i ↦ ∑ j, a i j • z j`. For `N = R` this is
`Matrix.mulVecLin`. -/
private def mulVecModule {ι κ : Type*} [Fintype κ] (a : ι → κ → R) (N : Type w)
    [AddCommGroup N] [Module R N] : (κ → N) →ₗ[R] (ι → N) :=
  LinearMap.pi fun i => ∑ j, a i j • LinearMap.proj j

private lemma mulVecModule_apply {ι κ : Type*} [Fintype κ] (a : ι → κ → R) (N : Type w)
    [AddCommGroup N] [Module R N] (z : κ → N) (i : ι) :
    mulVecModule a N z i = ∑ j, a i j • z j := by
  simp [mulVecModule]

attribute [local simp] mulVecModule_apply

/-- Multiplication by a matrix commutes with the isomorphism `N ⊗ Rᵏ ≃ Nᵏ`. -/
private lemma piScalarRight_comp_lTensor {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (a : ι → κ → R) (N : Type w) [AddCommGroup N] [Module R N] :
    (TensorProduct.piScalarRight R R N ι).toLinearMap ∘ₗ lTensor N (mulVecModule a R)
      = mulVecModule a N ∘ₗ (TensorProduct.piScalarRight R R N κ).toLinearMap := by
  refine TensorProduct.ext' fun x v => funext fun i => ?_
  simp [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
    Finset.sum_smul, mul_smul]

/-- The isomorphism `N ⊗ Rⁱ ≃ Nⁱ` is natural in `N`. -/
private lemma piScalarRight_comp_rTensor {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    (TensorProduct.piScalarRight R R N ι).toLinearMap ∘ₗ f.rTensor (ι → R)
      = (LinearMap.pi fun i => f ∘ₗ LinearMap.proj i) ∘ₗ
        (TensorProduct.piScalarRight R R M ι).toLinearMap := by
  refine TensorProduct.ext' fun x v => funext fun i => ?_
  simp [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]

/-- The image of multiplication by `a` on `Nⁱ` is cut out by the vanishing of the corresponding
class in `N ⊗ Q`, where `Q` is the cokernel of multiplication by `a` on `Rᵏ`. This is the
exactness of the rows of the source's diagram in the proof of (2) ⇒ (3). -/
private lemma mem_range_mulVecModule_iff {n m : ℕ} (a : Fin n → Fin m → R) (N : Type w)
    [AddCommGroup N] [Module R N] (x : Fin n → N) :
    x ∈ LinearMap.range (mulVecModule a N) ↔
      lTensor N (LinearMap.range (mulVecModule a R)).mkQ
        ((TensorProduct.piScalarRight R R N (Fin n)).symm x) = 0 := by
  have hsq := piScalarRight_comp_lTensor a N
  have hex : Function.Exact (lTensor N (mulVecModule a R))
      (lTensor N (LinearMap.range (mulVecModule a R)).mkQ) :=
    lTensor_exact N (LinearMap.exact_map_mkQ_range _) (Submodule.mkQ_surjective _)
  rw [hex ((TensorProduct.piScalarRight R R N (Fin n)).symm x)]
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨(TensorProduct.piScalarRight R R N (Fin m)).symm z, ?_⟩
    apply (TensorProduct.piScalarRight R R N (Fin n)).injective
    simpa using LinearMap.congr_fun hsq ((TensorProduct.piScalarRight R R N (Fin m)).symm z)
  · rintro ⟨w, hw⟩
    refine ⟨(TensorProduct.piScalarRight R R N (Fin m)) w, ?_⟩
    have := LinearMap.congr_fun hsq w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at this
    rw [← this, hw]
    simp

/-- Injectivity of `f ⊗ id_Q` only depends on the isomorphism class of `Q`. -/
private lemma rTensor_injective_congr {M N Q Q' : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R Q] [AddCommGroup Q'] [Module R Q']
    (f : M →ₗ[R] N) (e : Q ≃ₗ[R] Q') (hf : Function.Injective (f.rTensor Q)) :
    Function.Injective (f.rTensor Q') := by
  set eM := TensorProduct.congr (LinearEquiv.refl R M) e with hEM
  set eN := TensorProduct.congr (LinearEquiv.refl R N) e with hEN
  have key : ∀ t, f.rTensor Q' (eM t) = eN (f.rTensor Q t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul x q => simp [hEM, hEN]
    | add x y hx hy => simp [hx, hy]
  intro s₁ s₂ hs
  obtain ⟨t₁, rfl⟩ := eM.surjective s₁
  obtain ⟨t₂, rfl⟩ := eM.surjective s₂
  rw [key, key] at hs
  exact congrArg eM (hf (eN.injective hs))

/-! ### Presentations by finite free modules -/

/-- Every element of a finitely supported family over a finite type is the sum of its
coordinates against the standard basis. -/
private lemma finsupp_eq_sum_smul_single {k : ℕ} (w : Fin k →₀ R) :
    w = ∑ j, w j • Finsupp.single j (1 : R) := by
  conv_lhs => rw [← Finsupp.univ_sum_single w]
  exact Finset.sum_congr rfl fun j _ => by rw [Finsupp.smul_single, smul_eq_mul, mul_one]

/-- Two maps out of a finite free module agree as soon as they agree on the standard basis. -/
private lemma linearMap_ext_single {k : ℕ} {N : Type*} [AddCommGroup N] [Module R N]
    {F G : (Fin k →₀ R) →ₗ[R] N}
    (hFG : ∀ i, F (Finsupp.single i (1 : R)) = G (Finsupp.single i (1 : R))) : F = G := by
  refine LinearMap.ext fun w => ?_
  conv_lhs => rw [finsupp_eq_sum_smul_single w]
  conv_rhs => rw [finsupp_eq_sum_smul_single w]
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, map_smul, hFG i]

/-- The value of `Finsupp.linearCombination` on a finite index type, as a sum over the whole
index type. -/
theorem linearCombination_apply_fin {R : Type*} [CommSemiring R] {k : ℕ} {N : Type*}
    [AddCommMonoid N] [Module R N] (z : Fin k → N) (w : Fin k →₀ R) :
    Finsupp.linearCombination R z w = ∑ j, w j • z j := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
  intro j
  simp

/-- A finitely presented module is the cokernel of a map of finite free modules
`Rⁿ → Rᵐ`, written with `Fin n →₀ R`. -/
private lemma exists_fin_presentation (R : Type u) [CommRing R] (P : Type w) [AddCommGroup P]
    [Module R P] [Module.FinitePresentation R P] :
    ∃ (n m : ℕ) (α : (Fin n →₀ R) →ₗ[R] (Fin m →₀ R)) (g : (Fin m →₀ R) →ₗ[R] P),
      Function.Surjective g ∧ Function.Exact α g := by
  classical
  obtain ⟨mm, K, e, hK⟩ := Module.FinitePresentation.exists_fin (R := R) (M := P)
  set fe := Finsupp.linearEquivFunOnFinite R R (Fin mm) with hfe
  set g : (Fin mm →₀ R) →ₗ[R] P := e.symm.toLinearMap ∘ₗ K.mkQ ∘ₗ fe.toLinearMap with hg
  have hgsurj : Function.Surjective g :=
    e.symm.surjective.comp ((Submodule.mkQ_surjective K).comp fe.surjective)
  have hker : LinearMap.ker g = K.comap fe.toLinearMap := by
    ext w
    simp [hg, Submodule.mem_comap, Submodule.Quotient.mk_eq_zero]
  have hkerFG : (LinearMap.ker g).FG := by
    rw [hker, Submodule.comap_equiv_eq_map_symm]
    exact hK.map _
  obtain ⟨k, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hkerFG
  refine ⟨k, mm, Finsupp.linearCombination R s, g, hgsurj, ?_⟩
  rw [LinearMap.exact_iff, Finsupp.range_linearCombination, hs]

/-! ### From solvability of linear systems to universal injectivity -/

/-- Tensoring with a map on the left and tensoring with a map on the right commute. -/
private lemma lTensor_rTensor_comm {M N P Q : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (f : M →ₗ[R] N) (g : P →ₗ[R] Q) (t : M ⊗[R] P) :
    lTensor N g (f.rTensor P t) = f.rTensor Q (lTensor M g t) := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
    LinearMap.lTensor_comp_rTensor]

/-- Enlarging a submodule enlarges the image of the map it induces on tensor products. -/
private lemma range_lTensor_subtype_mono (N : Type w) [AddCommGroup N] [Module R N]
    {Q : Type*} [AddCommGroup Q] [Module R Q] {K₁ K₂ : Submodule R Q} (hK : K₁ ≤ K₂) :
    LinearMap.range (lTensor N K₁.subtype) ≤ LinearMap.range (lTensor N K₂.subtype) := by
  rw [← Submodule.subtype_comp_inclusion _ _ hK, LinearMap.lTensor_comp]
  exact LinearMap.range_comp_le_range _ _

/-- An element of `N ⊗ Q` in the image of `N ⊗ K` already comes from `N ⊗ K'` for some finitely
generated submodule `K' ≤ K`, because a tensor is a finite sum of pure tensors. -/
private lemma exists_fg_le_of_mem_range_lTensor (N : Type w) [AddCommGroup N] [Module R N]
    {Q : Type*} [AddCommGroup Q] [Module R Q] (K : Submodule R Q) {ω : N ⊗[R] Q}
    (hω : ω ∈ LinearMap.range (lTensor N K.subtype)) :
    ∃ K' : Submodule R Q, K' ≤ K ∧ K'.FG ∧ ω ∈ LinearMap.range (lTensor N K'.subtype) := by
  obtain ⟨ω, rfl⟩ := hω
  induction ω using TensorProduct.inductionOn with
  | tmul u k =>
      refine ⟨Submodule.span R {(k : Q)}, ?_, Submodule.fg_span_singleton _,
        ⟨u ⊗ₜ ⟨(k : Q), Submodule.mem_span_singleton_self _⟩, by simp⟩⟩
      rw [Submodule.span_le, Set.singleton_subset_iff]
      exact k.2
  | add ω₁ ω₂ h₁ h₂ =>
      obtain ⟨K₁, hK₁, hfg₁, hmem₁⟩ := h₁
      obtain ⟨K₂, hK₂, hfg₂, hmem₂⟩ := h₂
      refine ⟨K₁ ⊔ K₂, sup_le hK₁ hK₂, hfg₁.sup hfg₂, ?_⟩
      rw [map_add]
      exact add_mem (range_lTensor_subtype_mono N le_sup_left hmem₁)
        (range_lTensor_subtype_mono N le_sup_right hmem₂)

/-- Naturality of the commutativity isomorphism of the tensor product. -/
private lemma comm_lTensor {N P Q : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P]
    [Module R P] [AddCommGroup Q] [Module R Q] (g : P →ₗ[R] Q) (t : N ⊗[R] P) :
    TensorProduct.comm R N Q (lTensor N g t) = g.rTensor N (TensorProduct.comm R N P t) := by
  induction t using TensorProduct.inductionOn with
  | tmul u p => simp
  | add t₁ t₂ h₁ h₂ => simp [h₁, h₂]

/-- The form of `Submodule.FG.exists_rTensor_fg_inclusion_eq` with the submodule in the right
factor: two elements of `N ⊗ Q₀` with the same image in `N ⊗ Q` already agree in `N ⊗ Q₁` for
some finitely generated `Q₁ ≥ Q₀`. -/
private lemma exists_fg_lTensor_inclusion_eq {N Q : Type*} [AddCommGroup N] [Module R N]
    [AddCommGroup Q] [Module R Q] {Q₀ : Submodule R Q} (h₀ : Q₀.FG) {x y : N ⊗[R] Q₀}
    (hxy : lTensor N Q₀.subtype x = lTensor N Q₀.subtype y) :
    ∃ Q₁ : Submodule R Q, Q₁.FG ∧ ∃ h : Q₀ ≤ Q₁,
      lTensor N (Submodule.inclusion h) x = lTensor N (Submodule.inclusion h) y := by
  obtain ⟨Q₁, hfg, hle, heq⟩ := h₀.exists_rTensor_fg_inclusion_eq (M := N)
    (x := TensorProduct.comm R N Q₀ x) (y := TensorProduct.comm R N Q₀ y)
    (by rw [← comm_lTensor, ← comm_lTensor, hxy])
  refine ⟨Q₁, hfg, hle, (TensorProduct.comm R N Q₁).injective ?_⟩
  rw [comm_lTensor, comm_lTensor, heq]

/-- `f ⊗ id` read in the coordinates of the isomorphism `N ⊗ Rᶥ ≃ Nᶥ`. -/
private lemma rTensor_piScalarRight_symm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (x : ι → M) :
    f.rTensor (ι → R) ((TensorProduct.piScalarRight R R M ι).symm x)
      = (TensorProduct.piScalarRight R R N ι).symm fun i => f (x i) := by
  rw [LinearEquiv.eq_symm_apply]
  simpa [funext_iff] using LinearMap.congr_fun (piScalarRight_comp_rTensor (ι := ι) f)
    ((TensorProduct.piScalarRight R R M ι).symm x)

/-- The image of multiplication by the matrix whose columns are a finite family of vectors is the
span of that family. -/
private lemma range_mulVecModule_eq_span {n m : ℕ} (s : Fin m → (Fin n → R)) :
    LinearMap.range (mulVecModule (fun i j => s j i) R) = Submodule.span R (Set.range s) := by
  have h : mulVecModule (fun i j => s j i) R = Fintype.linearCombination R s := by
    refine LinearMap.ext fun z => funext fun i => ?_
    rw [Fintype.linearCombination_apply, mulVecModule_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => by simp [mul_comm]
  rw [h, Fintype.range_linearCombination]

/-- Item (3) makes `f₁ ⊗ Q` injective when `Q` is the quotient of a finite free module by a
finitely generated submodule. This is the reverse reading of the diagram of the source's proof
of (2) ⇒ (3). -/
private lemma injective_rTensor_quotient_of_fg {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] {f₁ : M₁ →ₗ[R] M₂}
    (H3 : ∀ (n m : ℕ) (x : Fin n → M₁) (y : Fin m → M₂) (a : Fin n → Fin m → R),
      (∀ i, f₁ (x i) = ∑ j, a i j • y j) → ∃ z : Fin m → M₁, ∀ i, x i = ∑ j, a i j • z j)
    {n : ℕ} {K : Submodule R (Fin n → R)} (hK : K.FG) :
    Function.Injective (f₁.rTensor ((Fin n → R) ⧸ K)) := by
  classical
  obtain ⟨k, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hK
  have hKa : LinearMap.range (mulVecModule (fun (i : Fin n) (j : Fin k) => s j i) R) = K := by
    rw [range_mulVecModule_eq_span, hs]
  rw [← hKa]
  set a : Fin n → Fin k → R := fun i j => s j i with ha
  set K' := LinearMap.range (mulVecModule a R) with hK'
  refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr ?_)
  intro ζ hζ
  obtain ⟨η, rfl⟩ := LinearMap.lTensor_surjective M₁ (Submodule.mkQ_surjective K') ζ
  set x := (TensorProduct.piScalarRight R R M₁ (Fin n)) η with hxdef
  have hη : η = (TensorProduct.piScalarRight R R M₁ (Fin n)).symm x := by
    rw [hxdef, LinearEquiv.symm_apply_apply]
  have hy : (fun i => f₁ (x i)) ∈ LinearMap.range (mulVecModule a M₂) := by
    rw [mem_range_mulVecModule_iff, ← rTensor_piScalarRight_symm, ← hη, lTensor_rTensor_comm]
    exact hζ
  obtain ⟨y, hy⟩ := hy
  obtain ⟨z, hz⟩ := H3 n k x y a fun i => by
    have hi := congrFun hy i
    rw [mulVecModule_apply] at hi
    exact hi.symm
  have hx : x ∈ LinearMap.range (mulVecModule a M₁) :=
    ⟨z, funext fun i => by rw [mulVecModule_apply, ← hz i]⟩
  rw [mem_range_mulVecModule_iff, ← hη] at hx
  exact hx

/-- Item (3) makes `f₁ ⊗ Q` injective for every finitely generated `Q`: a single element of
`M₂ ⊗ Rⁿ` involves only finitely many of the relations of `Q`, so `Q` may be replaced by a
finitely presented module. -/
private lemma injective_rTensor_of_finite {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] {f₁ : M₁ →ₗ[R] M₂}
    (H3 : ∀ (n m : ℕ) (x : Fin n → M₁) (y : Fin m → M₂) (a : Fin n → Fin m → R),
      (∀ i, f₁ (x i) = ∑ j, a i j • y j) → ∃ z : Fin m → M₁, ∀ i, x i = ∑ j, a i j • z j)
    (Q : Type*) [AddCommGroup Q] [Module R Q] [Module.Finite R Q] :
    Function.Injective (f₁.rTensor Q) := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := Q)
  set p : (Fin n → R) →ₗ[R] Q := Fintype.linearCombination R s with hp
  have hpsurj : Function.Surjective p := by
    rw [← LinearMap.range_eq_top, hp, Fintype.range_linearCombination, hs]
  refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr ?_)
  intro ζ hζ
  obtain ⟨η, rfl⟩ := LinearMap.lTensor_surjective M₁ hpsurj ζ
  have hex : Function.Exact (lTensor M₂ (LinearMap.ker p).subtype) (lTensor M₂ p) :=
    lTensor_exact M₂ (LinearMap.exact_subtype_ker_map p) hpsurj
  have hmem : f₁.rTensor (Fin n → R) η ∈
      LinearMap.range (lTensor M₂ (LinearMap.ker p).subtype) := by
    rw [LinearMap.mem_range]
    exact (hex _).mp (by rwa [lTensor_rTensor_comm])
  obtain ⟨K', hK'le, hK'fg, ω, hω⟩ :=
    exists_fg_le_of_mem_range_lTensor M₂ (LinearMap.ker p) hmem
  have hζ' : f₁.rTensor ((Fin n → R) ⧸ K') (lTensor M₁ K'.mkQ η) = 0 := by
    rw [← lTensor_rTensor_comm, ← hω, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      show K'.mkQ ∘ₗ K'.subtype = 0 from
        LinearMap.ext fun w => (Submodule.Quotient.mk_eq_zero _).mpr w.2]
    simp
  have hzero : lTensor M₁ K'.mkQ η = 0 :=
    injective_rTensor_quotient_of_fg H3 hK'fg (by rw [hζ', map_zero])
  rw [← Submodule.liftQ_mkQ K' p hK'le, LinearMap.lTensor_comp, LinearMap.comp_apply, hzero,
    map_zero]

/-- **(3) ⇒ (1)** of Stacks 058K: solvability of the linear systems of item (3) makes `f₁ ⊗ Q`
injective for every module `Q`. A given element of `M₁ ⊗ Q` involves only finitely many
elements of `Q`, and only finitely many relations between them, so `Q` may be replaced by a
finitely generated, then by a finitely presented, module. -/
private theorem injective_rTensor_of_solvable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] {f₁ : M₁ →ₗ[R] M₂}
    (H3 : ∀ (n m : ℕ) (x : Fin n → M₁) (y : Fin m → M₂) (a : Fin n → Fin m → R),
      (∀ i, f₁ (x i) = ∑ j, a i j • y j) → ∃ z : Fin m → M₁, ∀ i, x i = ∑ j, a i j • z j)
    (Q : Type*) [AddCommGroup Q] [Module R Q] : Function.Injective (f₁.rTensor Q) := by
  refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr ?_)
  intro ζ hζ
  have htop : Function.Surjective ((⊤ : Submodule R Q).subtype) := fun q => ⟨⟨q, trivial⟩, rfl⟩
  obtain ⟨Q₀, -, hQ₀fg, ζ₀, hζ₀⟩ := exists_fg_le_of_mem_range_lTensor M₁ (⊤ : Submodule R Q)
    (LinearMap.mem_range.mpr (LinearMap.lTensor_surjective M₁ htop ζ))
  obtain ⟨Q₁, hQ₁fg, hle, heq⟩ := exists_fg_lTensor_inclusion_eq (N := M₂) hQ₀fg
    (x := f₁.rTensor Q₀ ζ₀) (y := 0) (by rw [map_zero, lTensor_rTensor_comm, hζ₀]; exact hζ)
  have : Module.Finite R Q₁ := Module.Finite.iff_fg.mpr hQ₁fg
  have hζ₁ : lTensor M₁ (Submodule.inclusion hle) ζ₀ = 0 := by
    refine injective_rTensor_of_finite H3 Q₁ ?_
    rw [← lTensor_rTensor_comm, heq, map_zero, map_zero]
  rw [← hζ₀, ← Submodule.subtype_comp_inclusion _ _ hle, LinearMap.lTensor_comp,
    LinearMap.comp_apply, hζ₁, map_zero]

/-! ### Colimits of directed systems of modules -/

/-- A finite set of indices in a directed preorder has an upper bound above any given index. -/
private lemma exists_upperBound {J : Type*} [Preorder J] [IsDirected J (· ≤ ·)]
    (s : Finset J) (j₀ : J) : ∃ k, j₀ ≤ k ∧ ∀ j ∈ s, j ≤ k := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨j₀, le_rfl, by simp⟩
  | insert a s _ ih =>
      obtain ⟨k, hk, hs⟩ := ih
      obtain ⟨k', hk1, hk2⟩ := exists_ge_ge (α := J) a k
      exact ⟨k', hk.trans hk2, fun j hj =>
        (Finset.mem_insert.mp hj).elim (fun hja => hja ▸ hk1) fun hj => (hs j hj).trans hk2⟩

section DirectedColimit

variable {A : Type u} [CommRing A] {J : Type v} [Preorder J] {D : J ⥤ ModuleCat.{v} A}

/-- The legs of a cocone are compatible with the maps of the system. -/
private lemma cocone_ι_map_apply (c : Cocone D) {i j : J} (hij : i ≤ j) (u : D.obj i) :
    (c.ι.app j).hom ((D.map (homOfLE hij)).hom u) = (c.ι.app i).hom u := by
  rw [← ModuleCat.comp_apply, c.w]

/-- Two consecutive maps of the system compose to the map of the composite. -/
private lemma map_homOfLE_map_homOfLE (D : J ⥤ ModuleCat.{v} A) {i j k : J} (hij : i ≤ j)
    (hjk : j ≤ k) (u : D.obj i) :
    (D.map (homOfLE hjk)).hom ((D.map (homOfLE hij)).hom u)
      = (D.map (homOfLE (hij.trans hjk))).hom u := by
  rw [← ModuleCat.comp_apply, ← D.map_comp]
  rfl

/-- The values of a functor on a preordered type form a directed system of modules. -/
private lemma directedSystem_functor (D : J ⥤ ModuleCat.{v} A) :
    DirectedSystem (fun j => (D.obj j : Type v))
      (fun _ _ h => ((D.map (homOfLE h)).hom : _ → _)) where
  map_self u := by simp
  map_map {i j k} hij hjk u := map_homOfLE_map_homOfLE D hij hjk u

attribute [local instance] directedSystem_functor

variable [IsDirected J (· ≤ ·)] [Nonempty J]

omit [IsDirected J (· ≤ ·)] [Nonempty J] in
/-- A colimit cocone on a directed system of modules is the direct limit of the system: some
isomorphism from `Module.DirectLimit` onto its point carries the canonical maps to the legs. -/
private lemma exists_linearEquiv_directLimit [DecidableEq J] {c : Cocone D} (hc : IsColimit c) :
    ∃ e : Module.DirectLimit (fun j => (D.obj j : Type v))
        (fun _ _ h => (D.map (homOfLE h)).hom) ≃ₗ[A] c.pt,
      ∀ (j : J) (u : D.obj j),
        e (Module.DirectLimit.of A J _ (fun _ _ h => (D.map (homOfLE h)).hom) j u)
          = (c.ι.app j).hom u := by
  refine ⟨((ModuleCat.directLimitIsColimit (R := A) (fun j => (D.obj j : Type v))
    (fun _ _ h => (D.map (homOfLE h)).hom)).coconePointUniqueUpToIso hc).toLinearEquiv,
    fun j u => ?_⟩
  exact congrFun (congrArg (fun g => (ModuleCat.Hom.hom g : _ → _))
    (IsColimit.comp_coconePointUniqueUpToIso_hom
      (ModuleCat.directLimitIsColimit (R := A) (fun j => (D.obj j : Type v))
        (fun _ _ h => (D.map (homOfLE h)).hom)) hc j)) u

/-- The legs of a colimit cocone on a directed system of modules are jointly surjective. -/
private lemma exists_leg_apply_eq {c : Cocone D} (hc : IsColimit c) (w : c.pt) :
    ∃ (j : J) (u : D.obj j), (c.ι.app j).hom u = w := by
  classical
  obtain ⟨e, he⟩ := exists_linearEquiv_directLimit hc
  obtain ⟨j, u, hu⟩ := Module.DirectLimit.exists_of (e.symm w)
  exact ⟨j, u, by rw [← he, hu, e.apply_symm_apply]⟩

omit [Nonempty J] in
/-- The legs of a colimit cocone on a directed system of modules detect vanishing one stage
later. -/
private lemma exists_map_eq_zero {c : Cocone D} (hc : IsColimit c) {j : J} {u : D.obj j}
    (hu : (c.ι.app j).hom u = 0) :
    ∃ (k : J) (hjk : j ≤ k), (D.map (homOfLE hjk)).hom u = 0 := by
  classical
  obtain ⟨e, he⟩ := exists_linearEquiv_directLimit hc
  exact Module.DirectLimit.of.zero_exact (e.injective (by rw [he, hu, map_zero]))

/-- A finite family of elements of the point of a colimit cocone comes from a single stage. -/
private lemma exists_leg_apply_eq_pi {ι : Type*} [Finite ι] {c : Cocone D} (hc : IsColimit c)
    (y : ι → c.pt) : ∃ (j : J) (u : ι → D.obj j), ∀ l, (c.ι.app j).hom (u l) = y l := by
  classical
  choose js us hus using fun l => exists_leg_apply_eq hc (y l)
  obtain ⟨j, -, hj⟩ := exists_upperBound (Set.finite_range js).toFinset (Classical.arbitrary J)
  have hle : ∀ l, js l ≤ j := fun l =>
    hj _ ((Set.finite_range js).mem_toFinset.mpr ⟨l, rfl⟩)
  exact ⟨j, fun l => (D.map (homOfLE (hle l))).hom (us l),
    fun l => by rw [cocone_ι_map_apply, hus l]⟩

omit [Nonempty J] in
/-- A finite family of elements of one stage that vanish in the colimit already vanish together
at a later stage. -/
private lemma exists_map_eq_zero_pi {ι : Type*} [Finite ι] {c : Cocone D} (hc : IsColimit c)
    {j : J} (u : ι → D.obj j) (hu : ∀ l, (c.ι.app j).hom (u l) = 0) :
    ∃ (k : J) (hjk : j ≤ k), ∀ l, (D.map (homOfLE hjk)).hom (u l) = 0 := by
  classical
  choose ks hks hks0 using fun l => exists_map_eq_zero hc (hu l)
  obtain ⟨k, hk, hkall⟩ := exists_upperBound (Set.finite_range ks).toFinset j
  refine ⟨k, hk, fun l => ?_⟩
  have hlk : ks l ≤ k := hkall _ ((Set.finite_range ks).mem_toFinset.mpr ⟨l, rfl⟩)
  rw [← map_homOfLE_map_homOfLE D (hks l) hlk, hks0 l, map_zero]

omit [Nonempty J] in
/-- A linear relation over a finite family that holds between the images of elements of a stage
in the colimit already holds, between their images, at some later stage. -/
private lemma exists_map_eq_sum_smul {n m : ℕ} {c : Cocone D} (hc : IsColimit c) {j : J}
    (x : Fin n → D.obj j) (y : Fin m → D.obj j) (a : Fin n → Fin m → A)
    (hxy : ∀ i, (c.ι.app j).hom (x i) = ∑ l, a i l • (c.ι.app j).hom (y l)) :
    ∃ (k : J) (hjk : j ≤ k), ∀ i,
      (D.map (homOfLE hjk)).hom (x i) = ∑ l, a i l • (D.map (homOfLE hjk)).hom (y l) := by
  obtain ⟨k, hjk, hk⟩ := exists_map_eq_zero_pi hc (fun i => x i - ∑ l, a i l • y l) fun i => by
    rw [map_sub, map_sum, sub_eq_zero, hxy i]
    simp
  refine ⟨k, hjk, fun i => ?_⟩
  have hki := hk i
  rw [map_sub, map_sum, sub_eq_zero] at hki
  simpa using hki

/-- A cocone on a directed system of modules whose legs are jointly surjective and which detects
vanishing one stage later is a colimit cocone: the converse of `exists_leg_apply_eq` and
`exists_map_eq_zero`. -/
private noncomputable def isColimitOfJointlySurjective (c : Cocone D)
    (hsurj : ∀ w : c.pt, ∃ (j : J) (u : D.obj j), (c.ι.app j).hom u = w)
    (hzero : ∀ (j : J) (u : D.obj j), (c.ι.app j).hom u = 0 →
      ∃ (k : J) (hjk : j ≤ k), (D.map (homOfLE hjk)).hom u = 0) :
    IsColimit c := by
  classical
  set hL := ModuleCat.directLimitIsColimit (R := A) (fun j => (D.obj j : Type v))
    (fun _ _ h => (D.map (homOfLE h)).hom) with hLdef
  have hfac : ∀ (j : J) (u : D.obj j),
      (hL.desc c).hom (Module.DirectLimit.of A J _ (fun _ _ h => (D.map (homOfLE h)).hom) j u)
        = (c.ι.app j).hom u := fun j u =>
    congrFun (congrArg (fun g => (ModuleCat.Hom.hom g : _ → _)) (hL.fac c j)) u
  have : IsIso (hL.desc c) := by
    refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨?_, fun w => ?_⟩
    · refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
      obtain ⟨j, u, rfl⟩ := Module.DirectLimit.exists_of z
      rw [hfac] at hz
      obtain ⟨k, hjk, hk⟩ := hzero j u hz
      have hof : (Module.DirectLimit.of A J (fun j => (D.obj j : Type v))
            (fun _ _ h => (D.map (homOfLE h)).hom) k) ((D.map (homOfLE hjk)).hom u)
          = Module.DirectLimit.of A J _ (fun _ _ h => (D.map (homOfLE h)).hom) j u :=
        Module.DirectLimit.of_f
      rw [← hof, hk]
      exact map_zero _
    · obtain ⟨j, u, rfl⟩ := hsurj w
      exact ⟨Module.DirectLimit.of A J _ _ j u, hfac j u⟩
  exact IsColimit.ofPointIso hL

end DirectedColimit

/-! ### A module as a directed colimit of finitely presented modules -/

section Stages

variable (A : Type u) [CommRing A] [Small.{v} A] (N : Type v) [AddCommGroup N] [Module A N]

/-- The free `A`-module on the elements of `N`, with coefficients transported into `Type v`. -/
private abbrev freeOn : Type v := N →₀ Shrink.{v} A

/-- The canonical surjection of the free module on `N` onto `N`. -/
private noncomputable def freeOnProj : freeOn A N →ₗ[A] N :=
  Finsupp.linearCombination A id ∘ₗ
    (Finsupp.mapRange.linearEquiv (Shrink.linearEquiv A A)).toLinearMap

private lemma freeOnProj_single (m : N) (c : Shrink.{v} A) :
    freeOnProj A N (Finsupp.single m c) = Shrink.linearEquiv A A c • m := by
  simp [freeOnProj]

/-- The basis element of `freeOn A N` at an element `m : N`. -/
private noncomputable def freeOnGen (m : N) : freeOn A N :=
  Finsupp.single m ((Shrink.linearEquiv A A).symm 1)

private lemma freeOnProj_freeOnGen (m : N) : freeOnProj A N (freeOnGen A N m) = m := by
  rw [freeOnGen, freeOnProj_single]
  simp

/-- A stage of the system: a finite set of generators together with a finite set of relations. -/
private def Stage : Type v := Finset N × Finset (freeOn A N)

/-- The order on stages: inclusion of generators and of relations. -/
private abbrev stagePreorder : Preorder (Stage A N) :=
  inferInstanceAs (Preorder (Finset N × Finset (freeOn A N)))

attribute [local instance] stagePreorder

/-- The free module on the generators of a stage. -/
private noncomputable abbrev stageFree (p : Stage A N) : Submodule A (freeOn A N) :=
  Finsupp.supported (Shrink.{v} A) A (↑p.1 : Set N)

/-- The submodule of relations imposed at a stage. -/
private noncomputable abbrev stageRel (p : Stage A N) : Submodule A (stageFree A N p) :=
  Submodule.span A
    {w : stageFree A N p | (↑w : freeOn A N) ∈ p.2 ∧ freeOnProj A N (↑w : freeOn A N) = 0}

/-- The finitely presented module at a stage. -/
private abbrev stageModule (p : Stage A N) : Type v := stageFree A N p ⧸ stageRel A N p

omit [AddCommGroup N] [Module A N] in
private lemma stageFree_finitePresentation (p : Stage A N) :
    Module.FinitePresentation A (stageFree A N p) :=
  ((Finsupp.supportedEquivFinsupp (M := Shrink.{v} A) (R := A) (↑p.1 : Set N)).trans
    (Finsupp.mapRange.linearEquiv (Shrink.linearEquiv A A))).finitePresentation_iff.mpr
      inferInstance

private lemma stageRel_fg (p : Stage A N) : (stageRel A N p).FG :=
  Submodule.fg_span (Set.Finite.subset
    (Set.Finite.preimage Subtype.val_injective.injOn p.2.finite_toSet)
    fun _ hw => Finset.mem_coe.mpr hw.1)

private lemma stageModule_finitePresentation (p : Stage A N) :
    Module.FinitePresentation A (stageModule A N p) := by
  have := stageFree_finitePresentation A N p
  exact Module.finitePresentation_of_surjective (stageRel A N p).mkQ
    (Submodule.mkQ_surjective _) (by rw [Submodule.ker_mkQ]; exact stageRel_fg A N p)

/-- The map to `N` from the module at a stage. -/
private noncomputable def stageLeg (p : Stage A N) : stageModule A N p →ₗ[A] N :=
  (stageRel A N p).liftQ (freeOnProj A N ∘ₗ (stageFree A N p).subtype)
    (by
      rw [Submodule.span_le]
      intro w hw
      simpa using hw.2)

private lemma stageLeg_mk (p : Stage A N) (w : stageFree A N p) :
    stageLeg A N p ((stageRel A N p).mkQ w) = freeOnProj A N (↑w : freeOn A N) := rfl

omit [AddCommGroup N] [Module A N] in
private lemma stageFree_mono {p q : Stage A N} (hpq : p ≤ q) :
    stageFree A N p ≤ stageFree A N q :=
  Finsupp.supported_mono (Finset.coe_subset.mpr hpq.1)

private lemma stageRel_le {p q : Stage A N} (hpq : p ≤ q) :
    stageRel A N p ≤ (stageRel A N q).comap (Submodule.inclusion (stageFree_mono A N hpq)) := by
  rw [Submodule.span_le]
  intro w hw
  have h1 : Submodule.inclusion (stageFree_mono A N hpq) w ∈ stageRel A N q :=
    Submodule.subset_span ⟨hpq.2 hw.1, hw.2⟩
  exact h1

/-- The transition map of the system. -/
private noncomputable def stageTrans {p q : Stage A N} (hpq : p ≤ q) :
    stageModule A N p →ₗ[A] stageModule A N q :=
  Submodule.mapQ _ _ (Submodule.inclusion (stageFree_mono A N hpq)) (stageRel_le A N hpq)

private lemma stageLeg_stageTrans {p q : Stage A N} (hpq : p ≤ q) (u : stageModule A N p) :
    stageLeg A N q (stageTrans A N hpq u) = stageLeg A N p u := by
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (stageRel A N p) u
  rfl

private lemma stageTrans_self (p : Stage A N) (u : stageModule A N p) :
    stageTrans A N (le_refl p) u = u := by
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (stageRel A N p) u
  rfl

private lemma stageTrans_stageTrans {p q r : Stage A N} (hpq : p ≤ q) (hqr : q ≤ r)
    (u : stageModule A N p) :
    stageTrans A N hqr (stageTrans A N hpq u) = stageTrans A N (hpq.trans hqr) u := by
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (stageRel A N p) u
  rfl

private lemma exists_stageLeg_eq (x : N) :
    ∃ (p : Stage A N) (u : stageModule A N p), stageLeg A N p u = x := by
  classical
  refine ⟨({x}, ∅), (stageRel A N ({x}, ∅)).mkQ ⟨freeOnGen A N x, ?_⟩, ?_⟩
  · exact Finsupp.single_mem_supported _ _ (by simp)
  · exact freeOnProj_freeOnGen A N x

private lemma exists_stageTrans_eq_zero {p : Stage A N} (u : stageModule A N p)
    (hu : stageLeg A N p u = 0) :
    ∃ (q : Stage A N) (hpq : p ≤ q), stageTrans A N hpq u = 0 := by
  classical
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (stageRel A N p) u
  have hw : freeOnProj A N (↑w : freeOn A N) = 0 := hu
  refine ⟨(p.1, insert (↑w : freeOn A N) p.2), ⟨le_refl _, Finset.subset_insert _ _⟩, ?_⟩
  refine (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨?_, ?_⟩)
  · exact Finset.mem_insert_self _ _
  · exact hw

omit [AddCommGroup N] [Module A N] in
private lemma nonempty_stage : Nonempty (Stage A N) :=
  ⟨((∅, ∅) : Finset N × Finset (freeOn A N))⟩

omit [AddCommGroup N] [Module A N] in
private lemma isDirected_stage : IsDirected (Stage A N) (· ≤ ·) := by
  classical
  exact ⟨fun p q => ⟨(p.1 ∪ q.1, p.2 ∪ q.2),
    ⟨Finset.subset_union_left, Finset.subset_union_left⟩,
    ⟨Finset.subset_union_right, Finset.subset_union_right⟩⟩⟩

end Stages

attribute [local instance] stagePreorder

/-! ### The system of fibre products -/

section System

variable {A : Type u} [CommRing A] [Small.{v} A] {M₁ M₂ M₃ : Type v} [AddCommGroup M₁]
  [Module A M₁] [AddCommGroup M₂] [Module A M₂] [AddCommGroup M₃] [Module A M₃]
  (f₁ : M₁ →ₗ[A] M₂) (f₂ : M₂ →ₗ[A] M₃)

/-- The fibre product of `M₂` and the module at a stage over `M₃`. -/
private noncomputable abbrev fibreProduct (p : Stage A M₃) :
    Submodule A (M₂ × stageModule A M₃ p) :=
  LinearMap.ker (f₂ ∘ₗ LinearMap.fst A M₂ (stageModule A M₃ p)
    - stageLeg A M₃ p ∘ₗ LinearMap.snd A M₂ (stageModule A M₃ p))

private lemma mem_fibreProduct {p : Stage A M₃} {z : M₂ × stageModule A M₃ p} :
    z ∈ fibreProduct f₂ p ↔ f₂ z.1 = stageLeg A M₃ p z.2 := by
  simp [LinearMap.mem_ker, sub_eq_zero]

/-- The injection of the fibre product sequence at a stage. -/
private noncomputable def fibreProductF (h : Function.Exact f₁ f₂) (p : Stage A M₃) :
    M₁ →ₗ[A] fibreProduct f₂ p :=
  LinearMap.codRestrict _ (f₁.prod 0) fun x => by
    simp [h.apply_apply_eq_zero]

/-- The surjection of the fibre product sequence at a stage. -/
private noncomputable def fibreProductG (p : Stage A M₃) :
    fibreProduct f₂ p →ₗ[A] stageModule A M₃ p :=
  LinearMap.snd A M₂ (stageModule A M₃ p) ∘ₗ (fibreProduct f₂ p).subtype

/-- The sequence at a stage: the pullback of the given sequence along the map to `M₃` from the
finitely presented module at that stage. -/
private noncomputable def stageComplex (h : Function.Exact f₁ f₂) (p : Stage A M₃) :
    ShortComplex (ModuleCat.{v} A) :=
  ModuleCat.shortComplexOfCompEqZero (fibreProductF f₁ f₂ h p) (fibreProductG f₂ p)
    (LinearMap.ext fun _ => rfl)

/-- The transition map of the system of fibre products. -/
private noncomputable def fibreProductTrans {p q : Stage A M₃} (hpq : p ≤ q) :
    fibreProduct f₂ p →ₗ[A] fibreProduct f₂ q :=
  LinearMap.codRestrict _
    (((LinearMap.fst A M₂ (stageModule A M₃ p)).prod
        (stageTrans A M₃ hpq ∘ₗ LinearMap.snd A M₂ (stageModule A M₃ p))) ∘ₗ
      (fibreProduct f₂ p).subtype)
    fun z => by
      rw [mem_fibreProduct]
      simpa [stageLeg_stageTrans] using (mem_fibreProduct f₂).mp z.2

/-- The directed system of fibre product sequences. -/
private noncomputable def stageFunctor (h : Function.Exact f₁ f₂) :
    Stage A M₃ ⥤ ShortComplex (ModuleCat.{v} A) where
  obj p := stageComplex f₁ f₂ h p
  map {p q} φ :=
    { τ₁ := 𝟙 _
      τ₂ := ModuleCat.ofHom (fibreProductTrans f₂ (leOfHom φ))
      τ₃ := ModuleCat.ofHom (stageTrans A M₃ (leOfHom φ))
      comm₁₂ := by
        ext x
        exact Subtype.ext (Prod.ext rfl (map_zero (stageTrans A M₃ (leOfHom φ))).symm)
      comm₂₃ := by
        ext z
        rfl }
  map_id p := by
    refine ShortComplex.Hom.ext rfl ?_ ?_
    · ext z
      exact Subtype.ext (Prod.ext rfl (stageTrans_self A M₃ p _))
    · ext u
      exact stageTrans_self A M₃ p u
  map_comp {p q r} φ ψ := by
    refine ShortComplex.Hom.ext rfl ?_ ?_
    · ext z
      exact Subtype.ext (Prod.ext rfl
        (stageTrans_stageTrans A M₃ (leOfHom φ) (leOfHom ψ) _).symm)
    · ext u
      exact (stageTrans_stageTrans A M₃ (leOfHom φ) (leOfHom ψ) u).symm

/-- The cocone on the system of fibre products whose point is the given sequence. -/
private noncomputable def stageCocone (h : Function.Exact f₁ f₂) :
    Cocone (stageFunctor f₁ f₂ h) where
  pt := ModuleCat.shortComplexOfCompEqZero f₁ f₂ h.linearMap_comp_eq_zero
  ι :=
    { app := fun p =>
        { τ₁ := 𝟙 _
          τ₂ := ModuleCat.ofHom
            (LinearMap.fst A M₂ (stageModule A M₃ p) ∘ₗ (fibreProduct f₂ p).subtype)
          τ₃ := ModuleCat.ofHom (stageLeg A M₃ p)
          comm₁₂ := by
            ext x
            rfl
          comm₂₃ := by
            ext z
            exact (mem_fibreProduct f₂).mp z.2 }
      naturality := fun p q φ => by
        refine ShortComplex.Hom.ext ?_ ?_ ?_
        · exact (Category.comp_id _).trans rfl
        · ext z
          rfl
        · ext u
          exact stageLeg_stageTrans A M₃ (leOfHom φ) u }

end System

/-! ### The two steps involving the colimit description -/

/-- **(5) ⇒ (6)** of Stacks 058K: if every map from a finitely presented module to `M₃` lifts to
`M₂`, then the sequence is the colimit of a directed system of split exact sequences with
finitely presented cokernels. -/
private theorem exists_directed_split_colimit_of_surjective_compRight
    {R : Type u} [CommRing R] [Small.{v} R] {M₁ M₂ M₃ : Type v} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃] {f₁ : M₁ →ₗ[R] M₂}
    {f₂ : M₂ →ₗ[R] M₃} (h : Function.Exact f₁ f₂) (h₁ : Function.Injective f₁)
    (_h₂ : Function.Surjective f₂)
    (H : ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P],
      Function.Surjective (LinearMap.compRight (M := P) R f₂)) :
    ∃ (J : Type v) (_ : Preorder J) (_ : IsDirected J (· ≤ ·)) (_ : Nonempty J)
        (F : J ⥤ ShortComplex (ModuleCat.{v} R)) (c : Cocone F)
        (_ : IsColimit c)
        (_ : c.pt ≅ ModuleCat.shortComplexOfCompEqZero f₁ f₂ h.linearMap_comp_eq_zero),
      ∀ j, Nonempty (F.obj j).Splitting ∧ Module.FinitePresentation R (F.obj j).X₃ ∧
        IsIso ((c.ι.app j).τ₁) := by
  classical
  have hdir := isDirected_stage R M₃
  have hne := nonempty_stage R M₃
  refine ⟨Stage R M₃, inferInstance, hdir, hne, stageFunctor f₁ f₂ h, stageCocone f₁ f₂ h,
    ?_, Iso.refl _, fun p => ⟨?_, stageModule_finitePresentation R M₃ p, ?_⟩⟩
  · refine ShortComplex.isColimitOfIsColimitπ _ ?_ ?_ ?_
    · exact isColimitOfJointlySurjective _ (fun w => ⟨Classical.arbitrary _, w, rfl⟩)
        (fun p u hu => ⟨p, le_refl p, hu⟩)
    · refine isColimitOfJointlySurjective _ (fun w => ?_) ?_
      · obtain ⟨q, u, hu⟩ := exists_stageLeg_eq R M₃ (f₂ w)
        exact ⟨q, ⟨(w, u), (mem_fibreProduct f₂).mpr hu.symm⟩, rfl⟩
      · rintro p ⟨⟨w, u⟩, hwu⟩ hz
        have hw : w = 0 := hz
        obtain ⟨q, hpq, hq⟩ := exists_stageTrans_eq_zero R M₃ u
          (by rw [← (mem_fibreProduct f₂).mp hwu, hw, map_zero])
        exact ⟨q, hpq, Subtype.ext (Prod.ext hw hq)⟩
    · exact isColimitOfJointlySurjective _ (fun x => exists_stageLeg_eq R M₃ x)
        (fun _ u hu => exists_stageTrans_eq_zero R M₃ u hu)
  · have := stageModule_finitePresentation R M₃ p
    obtain ⟨g, hg⟩ := H (stageModule R M₃ p) (stageLeg R M₃ p)
    have hgu : ∀ u, f₂ (g u) = stageLeg R M₃ p u := fun u => LinearMap.congr_fun hg u
    refine ⟨ShortComplex.Splitting.ofExactOfSection _ ?_
      (ModuleCat.ofHom (LinearMap.codRestrict _ (g.prod LinearMap.id)
        (fun u => (mem_fibreProduct f₂).mpr (hgu u)))) ?_ ?_⟩
    · rw [ShortComplex.moduleCat_exact_iff]
      rintro ⟨⟨w, u⟩, hwu⟩ hz
      have hu : u = 0 := hz
      obtain ⟨x, hx⟩ := (h w).mp (by rw [(mem_fibreProduct f₂).mp hwu, hu, map_zero])
      exact ⟨x, Subtype.ext (Prod.ext hx hu.symm)⟩
    · ext u
      rfl
    · rw [ModuleCat.mono_iff_injective]
      intro x x' hxx
      exact h₁ (congrArg Prod.fst (Subtype.ext_iff.mp hxx))
  · change IsIso (𝟙 (ModuleCat.of R M₁))
    infer_instance

/-- A morphism of short complexes of modules commutes with their injections, on elements. -/
private lemma τ₁_comm_apply {R : Type u} [CommRing R] {S₁ S₂ : ShortComplex (ModuleCat.{v} R)}
    (φ : S₁ ⟶ S₂) (w : S₁.X₁) : S₂.f.hom (φ.τ₁.hom w) = φ.τ₂.hom (S₁.f.hom w) := by
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.comm₁₂]

/-- The retraction of a splitting solves in `X₁` a linear system that the injection solves in
`X₂`: this is what makes item (6) imply item (3). -/
private lemma eq_sum_smul_splitting_r {R : Type u} [CommRing R]
    {S : ShortComplex (ModuleCat.{v} R)} (sp : S.Splitting) {n m : ℕ} (x : Fin n → S.X₁)
    (y : Fin m → S.X₂) (a : Fin n → Fin m → R)
    (hxy : ∀ i, S.f.hom (x i) = ∑ l, a i l • y l) (i : Fin n) :
    x i = ∑ l, a i l • sp.r.hom (y l) := by
  have hr : sp.r.hom (S.f.hom (x i)) = x i := by
    rw [← ModuleCat.comp_apply, sp.f_r]
    rfl
  rw [← hr, hxy i, map_sum]
  simp

/-- **(6) ⇒ (3)** of Stacks 058K: in a colimit of a directed system of split exact sequences
whose left-hand maps to `M₁` are isomorphisms, a linear system as in item (3) can be solved at a
stage of the system, where the retraction of the splitting solves it. -/
private theorem solvable_of_directed_split_colimit
    {R : Type u} [CommRing R] [Small.{v} R] {M₁ M₂ M₃ : Type v} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃] {f₁ : M₁ →ₗ[R] M₂}
    {f₂ : M₂ →ₗ[R] M₃} (h : Function.Exact f₁ f₂)
    (H : ∃ (J : Type v) (_ : Preorder J) (_ : IsDirected J (· ≤ ·)) (_ : Nonempty J)
        (F : J ⥤ ShortComplex (ModuleCat.{v} R)) (c : Cocone F)
        (_ : IsColimit c)
        (_ : c.pt ≅ ModuleCat.shortComplexOfCompEqZero f₁ f₂ h.linearMap_comp_eq_zero),
      ∀ j, Nonempty (F.obj j).Splitting ∧ Module.FinitePresentation R (F.obj j).X₃ ∧
        IsIso ((c.ι.app j).τ₁))
    (n m : ℕ) (x : Fin n → M₁) (y : Fin m → M₂) (a : Fin n → Fin m → R)
    (hxy : ∀ i, f₁ (x i) = ∑ j, a i j • y j) :
    ∃ z : Fin m → M₁, ∀ i, x i = ∑ j, a i j • z j := by
  classical
  obtain ⟨J, _, _, _, F, c, hc, e, hst⟩ := H
  -- move the point of the colimit cocone to the given sequence, and pass to the middle terms
  let c' : Cocone F :=
    { pt := ModuleCat.shortComplexOfCompEqZero f₁ f₂ h.linearMap_comp_eq_zero
      ι := { app := fun j => c.ι.app j ≫ e.hom
             naturality := fun _ _ φ => by
               rw [← Category.assoc, c.w φ]
               simp } }
  have hc₂ : IsColimit (ShortComplex.π₂.mapCocone c') :=
    isColimitOfPreserves (ShortComplex.π₂ (C := ModuleCat.{v} R))
      (hc.ofIsoColimit (Cocone.ext e fun _ => rfl))
  -- the legs at `M₁` are isomorphisms, so every element of `M₁` comes from every stage
  have hxpull : ∀ (j : J) (w : M₁), ∃ v : (F.obj j).X₁, ((c'.ι.app j).τ₁).hom v = w := by
    intro j w
    have h₁ : IsIso ((c.ι.app j).τ₁) := (hst j).2.2
    have h₂ : IsIso e.hom.τ₁ :=
      ⟨e.inv.τ₁, by rw [← ShortComplex.comp_τ₁, e.hom_inv_id, ShortComplex.id_τ₁],
        by rw [← ShortComplex.comp_τ₁, e.inv_hom_id, ShortComplex.id_τ₁]⟩
    have : IsIso ((c'.ι.app j).τ₁) := (inferInstance : IsIso ((c.ι.app j).τ₁ ≫ e.hom.τ₁))
    exact ⟨(inv ((c'.ι.app j).τ₁)).hom w, by simp⟩
  -- lift the `y`'s to a stage `j₀`, and lift `x` there too
  obtain ⟨j₀, y', hy'⟩ : ∃ (j : J) (u : Fin m → (F.obj j).X₂),
      ∀ l, ((c'.ι.app j).τ₂).hom (u l) = y l := exists_leg_apply_eq_pi hc₂ y
  choose x' hx' using fun i => hxpull j₀ (x i)
  -- the relation holds in `M₂`, hence already at some later stage `k`
  obtain ⟨k, hk, hk0⟩ := exists_map_eq_sum_smul hc₂ (fun i => (F.obj j₀).f.hom (x' i)) y' a
    fun i => by
      have h1 : ((c'.ι.app j₀).τ₂).hom ((F.obj j₀).f.hom (x' i)) = f₁ (x i) := by
        rw [← τ₁_comm_apply (c'.ι.app j₀), hx' i]
        rfl
      change ((c'.ι.app j₀).τ₂).hom ((F.obj j₀).f.hom (x' i))
        = ∑ l, a i l • ((c'.ι.app j₀).τ₂).hom (y' l)
      rw [h1, hxy i]
      simp [hy']
  have hkey : ∀ i, (F.obj k).f.hom ((F.map (homOfLE hk)).τ₁.hom (x' i))
      = ∑ l, a i l • (F.map (homOfLE hk)).τ₂.hom (y' l) := fun i => by
    rw [τ₁_comm_apply (F.map (homOfLE hk))]
    exact hk0 i
  -- at the stage `k` the sequence splits, and the retraction of the splitting solves the system
  obtain ⟨sp⟩ := (hst k).1
  refine ⟨fun l => ((c'.ι.app k).τ₁).hom (sp.r.hom ((F.map (homOfLE hk)).τ₂.hom (y' l))),
    fun i => ?_⟩
  have hlegcomp : ∀ (j j' : J) (hjj' : j ≤ j') (w : (F.obj j).X₁),
      ((c'.ι.app j').τ₁).hom ((F.map (homOfLE hjj')).τ₁.hom w) = ((c'.ι.app j).τ₁).hom w :=
    fun _ _ hjj' w => cocone_ι_map_apply (ShortComplex.π₁.mapCocone c') hjj' w
  have hleg : ((c'.ι.app k).τ₁).hom ((F.map (homOfLE hk)).τ₁.hom (x' i)) = x i := by
    rw [hlegcomp j₀ k hk (x' i), hx' i]
  rw [← hleg, eq_sum_smul_splitting_r sp _ _ a hkey i, map_sum]
  simp

/-! ### The theorem -/

/-- **Stacks 058K**, items (1)–(6) in the source's order, for a short exact sequence
`0 → M₁ → M₂ → M₃ → 0` of `R`-modules in `Type v`: `f₁ ⊗ id_Q` is injective for every `Q`; the
tensored sequence is short exact for every finitely presented `Q`; every finite linear system over
`M₂` with right-hand side in `M₁` is solvable in `M₁`; every square from `Rⁿ → Rᵐ` lifts through
`M₁`; `Hom_R(P, M₂) → Hom_R(P, M₃)` is surjective for every finitely presented `P`; and the
sequence is a directed colimit of split sequences with finitely presented third terms whose
coprojections are isomorphisms on the first terms. -/
public theorem solution {R : Type u} [CommRing R] [Small.{v} R]
    {M₁ M₂ M₃ : Type v} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃] {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃}
    (h : Function.Exact f₁ f₂) (h₁ : Function.Injective f₁) (h₂ : Function.Surjective f₂) :
    List.TFAE
      [ ∀ (Q : Type v) [AddCommGroup Q] [Module R Q], Function.Injective (f₁.rTensor Q),
        ∀ (Q : Type v) [AddCommGroup Q] [Module R Q] [Module.FinitePresentation R Q],
          Function.Injective (f₁.rTensor Q) ∧ Function.Exact (f₁.rTensor Q) (f₂.rTensor Q) ∧
            Function.Surjective (f₂.rTensor Q),
        ∀ (n m : ℕ) (x : Fin n → M₁) (y : Fin m → M₂) (a : Fin n → Fin m → R),
          (∀ i, f₁ (x i) = ∑ j, a i j • y j) → ∃ z : Fin m → M₁, ∀ i, x i = ∑ j, a i j • z j,
        ∀ (n m : ℕ) (α : (Fin n →₀ R) →ₗ[R] (Fin m →₀ R)) (β : (Fin n →₀ R) →ₗ[R] M₁)
          (γ : (Fin m →₀ R) →ₗ[R] M₂), f₁ ∘ₗ β = γ ∘ₗ α →
            ∃ δ : (Fin m →₀ R) →ₗ[R] M₁, δ ∘ₗ α = β,
        ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P],
          Function.Surjective (LinearMap.compRight (M := P) R f₂),
        ∃ (J : Type v) (_ : Preorder J) (_ : IsDirected J (· ≤ ·)) (_ : Nonempty J)
            (F : J ⥤ ShortComplex (ModuleCat.{v} R)) (c : Cocone F) (_ : IsColimit c)
            (_ : c.pt ≅ ModuleCat.shortComplexOfCompEqZero f₁ f₂ h.linearMap_comp_eq_zero),
          ∀ j, Nonempty (F.obj j).Splitting ∧ Module.FinitePresentation R (F.obj j).X₃ ∧
            IsIso ((c.ι.app j).τ₁) ] := by
  classical
  tfae_have 1 → 2 := fun H1 Q _ _ _ =>
    ⟨H1 Q, rTensor_exact Q h h₂, LinearMap.rTensor_surjective Q h₂⟩
  tfae_have 2 → 3 := by
    intro H2 n m x y a hxy
    set K := LinearMap.range (mulVecModule a R) with hK
    have : Small.{v} ((Fin n → R) ⧸ K) := small_of_surjective (Submodule.mkQ_surjective K)
    have : Module.FinitePresentation R ((Fin n → R) ⧸ K) :=
      Module.finitePresentation_of_surjective K.mkQ (Submodule.mkQ_surjective K)
        (by rw [Submodule.ker_mkQ, hK]; exact Submodule.fg_range _)
    have : Module.FinitePresentation R (Shrink.{v} ((Fin n → R) ⧸ K)) :=
      (Shrink.linearEquiv R ((Fin n → R) ⧸ K)).finitePresentation_iff.mpr inferInstance
    have hinjQ : Function.Injective (f₁.rTensor ((Fin n → R) ⧸ K)) :=
      rTensor_injective_congr f₁ (Shrink.linearEquiv R ((Fin n → R) ⧸ K))
        (H2 (Shrink.{v} ((Fin n → R) ⧸ K))).1
    -- the image of `x` in `M₂ⁿ` is in the image of `M₂ᵐ`
    have hy : (fun i => f₁ (x i)) ∈ LinearMap.range (mulVecModule a M₂) :=
      ⟨y, funext fun i => by rw [mulVecModule_apply]; exact (hxy i).symm⟩
    rw [mem_range_mulVecModule_iff] at hy
    -- so its class in `M₂ ⊗ Q` vanishes; by injectivity so does the class of `x` in `M₁ ⊗ Q`
    have hx0 : lTensor M₁ K.mkQ ((TensorProduct.piScalarRight R R M₁ (Fin n)).symm x) = 0 := by
      apply hinjQ
      rwa [map_zero, ← lTensor_rTensor_comm, rTensor_piScalarRight_symm]
    obtain ⟨z, hz⟩ := (mem_range_mulVecModule_iff a M₁ x).2 hx0
    exact ⟨z, fun i => by rw [← hz, mulVecModule_apply]⟩
  tfae_have 3 → 4 := by
    intro H3 n m α β γ hsq
    have hγ : ∀ (w : Fin m →₀ R), γ w = ∑ j, w j • γ (Finsupp.single j (1 : R)) := by
      intro w
      conv_lhs => rw [finsupp_eq_sum_smul_single w]
      rw [map_sum]
      simp only [map_smul]
    obtain ⟨z, hz⟩ := H3 n m (fun i => β (Finsupp.single i 1)) (fun j => γ (Finsupp.single j 1))
      (fun i j => α (Finsupp.single i 1) j) (by
        intro i
        have := LinearMap.congr_fun hsq (Finsupp.single i (1 : R))
        simp only [LinearMap.comp_apply] at this
        rw [this, hγ])
    refine ⟨Finsupp.linearCombination R z, linearMap_ext_single fun i => ?_⟩
    rw [LinearMap.comp_apply, linearCombination_apply_fin, hz i]
  tfae_have 4 → 5 := by
    intro H4 P _ _ _ φ
    obtain ⟨n, m, α, g, hgsurj, hgex⟩ := exists_fin_presentation R P
    -- lift `φ ∘ g` to `M₂` using freeness of `Rᵐ`
    obtain ⟨h₂', hh₂'⟩ := Module.projective_lifting_property f₂ (φ ∘ₗ g) h₂
    -- and lift `h₂' ∘ α` to `M₁`, using freeness of `Rⁿ` and exactness at `M₂`
    have hmem : ∀ i : Fin n, ∃ u : M₁, f₁ u = h₂' (α (Finsupp.single i (1 : R))) := by
      intro i
      refine (h _).mp ?_
      have hval := LinearMap.congr_fun hh₂' (α (Finsupp.single i (1 : R)))
      simp only [LinearMap.comp_apply] at hval
      rw [hval, hgex.apply_apply_eq_zero, map_zero]
    choose u hu using hmem
    set hh₁ := Finsupp.linearCombination R u with hdefh₁
    have hf₁h₁ : f₁ ∘ₗ hh₁ = h₂' ∘ₗ α := by
      refine linearMap_ext_single fun i => ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hdefh₁,
        Finsupp.linearCombination_single, one_smul, hu i]
    obtain ⟨k₁, hk₁⟩ := H4 n m α hh₁ h₂' hf₁h₁
    -- correct the lift so that it kills the relations
    set h₂'' := h₂' - f₁ ∘ₗ k₁ with hdefh₂''
    have hh₂''α : h₂'' ∘ₗ α = 0 := by
      rw [hdefh₂'', LinearMap.sub_comp, LinearMap.comp_assoc, hk₁, hf₁h₁, sub_self]
    -- descend it to `P`
    have hle : LinearMap.ker g ≤ LinearMap.ker h₂'' := by
      intro w hw
      rw [LinearMap.mem_ker] at hw ⊢
      obtain ⟨t, rfl⟩ := (hgex w).mp hw
      exact LinearMap.congr_fun hh₂''α t
    set ψ := (LinearMap.ker g).liftQ h₂'' hle ∘ₗ
      (LinearMap.quotKerEquivOfSurjective g hgsurj).symm.toLinearMap with hdefψ
    have hψ : ψ ∘ₗ g = h₂'' := by
      refine LinearMap.ext fun w => ?_
      have hq : (LinearMap.quotKerEquivOfSurjective g hgsurj).symm (g w)
          = Submodule.Quotient.mk w := by
        rw [LinearEquiv.symm_apply_eq]
        simp [LinearMap.quotKerEquivOfSurjective]
      simp [hdefψ, hq]
    refine ⟨ψ, ?_⟩
    change f₂ ∘ₗ ψ = φ
    refine LinearMap.ext fun p => ?_
    obtain ⟨w, rfl⟩ := hgsurj p
    have hw := LinearMap.congr_fun hψ w
    have h2 := LinearMap.congr_fun hh₂' w
    simp only [LinearMap.comp_apply] at hw h2 ⊢
    rw [hw, hdefh₂'']
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub, h.apply_apply_eq_zero,
      sub_zero]
    exact h2
  tfae_have 5 → 6 := fun H5 =>
    exists_directed_split_colimit_of_surjective_compRight h h₁ h₂ H5
  tfae_have 3 → 1 := fun H3 Q _ _ => injective_rTensor_of_solvable H3 Q
  tfae_have 6 → 3 := fun H6 n m x y a hxy =>
    solvable_of_directed_split_colimit h H6 n m x y a hxy
  tfae_finish

end Stacks.RingTheory.UniversalExactTFAE

/-!
# Criteria for universal exactness of a short exact sequence of modules

Let `R` be a commutative ring and let `0 → M₁ →[f₁] M₂ →[f₂] M₃ → 0` be a short exact sequence
of `R`-modules. Following Lazard, `f₁` is *universally injective* when `f₁ ⊗ id_Q` is injective
for every `R`-module `Q`, and the sequence is *universally exact* when it is exact and `f₁` is
universally injective (Stacks 058I). This file states the six equivalent characterizations of
universal exactness of Stacks 058K: universal injectivity of `f₁`; exactness of the sequence
tensored with an arbitrary finitely presented module; a solvability criterion for linear
equations, in element form and in diagram form; surjectivity of `Hom_R(P, M₂) → Hom_R(P, M₃)`
for `P` finitely presented; and the presentation of the sequence as a directed colimit of split
exact sequences with finitely presented cokernels. Items (3), (4), (5) and (6) are the analogues
for universal exactness of the criteria for flatness of Stacks 00HK, 058D, 058F and 058G.

## Main results

* `Function.Exact.universallyExact_tfae`: items (1)–(6) of Stacks 058K, in the source's order,
  as a `List.TFAE`.

## Implementation notes

Exactness of the sequence is a hypothesis rather than a member of the list, so item (1) is what
remains of "the sequence is universally exact", namely universal injectivity of `f₁`. Likewise
in item (2) the two conjuncts `Function.Exact (f₁.rTensor Q) (f₂.rTensor Q)` and
`Function.Surjective (f₂.rTensor Q)` hold for every `Q` by right exactness of the tensor
product, so the content of item (2) is its first conjunct; they are stated because the source's
item (2) is the exactness of the whole tensored sequence, and a user of item (2) wants it.

The three modules live in a single universe `v` and `R` is assumed `Small.{v}`, as in
`Module.Flat.iff_rTensor_exact'`. This is what lets every item be tested on modules in
`Type v`: a finitely generated `R`-module is a quotient of some `Rⁿ`, hence `Small.{v}`, hence
isomorphic to a module in `Type v`, so items (1), (2) and (5) as stated are the source's
conditions for test modules in every universe. The hypothesis is not decoration: item (6) asks
for a diagram of short complexes of modules in `Type v`, and without it there may be no nonzero
finitely presented module in `Type v` at all. For `R = ℚ[X_i ; i ∈ I]` in `Type 1` with `I`
uncountable and `M₁ = 0`, `M₂ = M₃ = ℚ` in `Type 0` (with `X_i` acting as `0`), every nonzero
finitely presented `R`-module has cardinality `|I|`, so item (6) fails for the split sequence
`0 → 0 → ℚ → ℚ → 0`, while items (1)–(5) hold. When `v = max u v`, and in particular whenever
`R` and the modules share a universe, `Small.{v} R` is found by instance search.

Item (4) writes `Rⁿ` as `Fin n →₀ R`, as in
`Module.Flat.exists_factorization_of_finitePresentation` and in Stacks 058E; the
map `Rᵐ → M₁` produced is pinned by the commutation `δ ∘ₗ α = β`, which is the source's top
triangle. Item (5) pins the map
`Hom_R(P, M₂) → Hom_R(P, M₃)` as `LinearMap.compRight R f₂`, postcomposition with `f₂`.

Item (6) is stated with a functor from a directed nonempty preorder `J` to
`ShortComplex (ModuleCat.{v} R)` and an explicit colimit cocone, rather than with
`Module.DirectLimit` plumbing: a directed system of short exact sequences is a diagram of short
complexes, and
`Nonempty (F.obj j).Splitting` is exactly splitness of the `j`-th sequence. `J` is a directed
preorder, not merely filtered, so that item (6) is the source's condition and not a weakening of
it (a directed nonempty preorder is filtered, so nothing is lost the other way). The source
writes the left-hand term of every sequence in the system as `M₁` itself; here that is recorded
by `IsIso ((c.ι.app j).τ₁)`, the statement that the cocone leg `M_{1,j} → M₁` is an isomorphism,
which is what the source's proof produces. `Mathlib` has no definition of universal injectivity,
so no such notion is referred to; item (1) spells it out.

Faithfulness. (1) No hypothesis is dead. `h` is used to form item (6) and is mathematically live:
for `f₁ = f₂ = id : ℤ → ℤ` item (1) holds and item (2) fails. `h₁` is live: for `M₁ = ℤ`,
`M₂ = M₃ = 0` item (5) holds and item (1) fails. `h₂` is live: for `M₁ = M₂ = 0`, `M₃ = ℤ`
item (1) holds while item (5) fails at `P = ℤ`. `Small.{v} R` is live by the example above.
(2) The scalars and the base are the source's: every tensor product is `⊗[R]`, every `Hom` is
`→ₗ[R]`, the diagram of item (6) is in `ModuleCat.{v} R`, and nothing is localized or base
changed. (3) Every canonical map the source names is pinned, not merely asserted to exist:
`f₁ ⊗ id_Q` and `f₂ ⊗ id_Q` are `f₁.rTensor Q` and `f₂.rTensor Q`, the map of item (5) is
`LinearMap.compRight R f₂`, the colimit of item (6) is a cocone on the short complex
`ModuleCat.shortComplexOfCompEqZero f₁ f₂` built from `f₁` and `f₂` themselves, and the
identification of the left-hand terms is the cocone leg `(c.ι.app j).τ₁`. (4) The instantiation
is not degenerate, and no item is vacuous: for `R = ℤ`, `M₁ = ℤ`, `M₂ = ℤ × ℤ`, `M₃ = ℤ` with
`f₁ = inl` and `f₂ = snd` all six items hold, whereas for `R = ℤ`, `M₁ = ℤ`, `M₂ = ℤ`,
`M₃ = ℤ ⧸ 2ℤ` with `f₁` multiplication by `2` all six fail — item (1) at `Q = ℤ ⧸ 2ℤ`, item (3)
at `n = m = 1`, `x₁ = 1`, `y₁ = 1`, `a₁₁ = 2`, and item (5) at `P = ℤ ⧸ 2ℤ`.

## References

* [StacksProject 058K](https://stacks.math.columbia.edu/tag/058K)
-/



@[expose] public section

open CategoryTheory CategoryTheory.Limits

/-- **Stacks 058K.** Let `0 → M₁ →[f₁] M₂ →[f₂] M₃ → 0` be a short exact sequence of `R`-modules.
The following are equivalent:
1. the sequence is universally exact, that is, `f₁ ⊗ id_Q` is injective for every `R`-module `Q`;
2. for every finitely presented `R`-module `Q` the sequence
   `0 → M₁ ⊗ Q → M₂ ⊗ Q → M₃ ⊗ Q → 0` is exact;
3. whenever `x i ∈ M₁`, `y j ∈ M₂` and `a i j ∈ R` satisfy `f₁ (x i) = ∑ j, a i j • y j` for all
   `i`, there are `z j ∈ M₁` with `x i = ∑ j, a i j • z j` for all `i`;
4. every commutative square `f₁ ∘ β = γ ∘ α` with `α : Rⁿ → Rᵐ`, `β : Rⁿ → M₁` and `γ : Rᵐ → M₂`
   admits `δ : Rᵐ → M₁` with `δ ∘ α = β`;
5. for every finitely presented `R`-module `P` the map `Hom_R(P, M₂) → Hom_R(P, M₃)` given by
   postcomposition with `f₂` is surjective;
6. the sequence is the colimit of a directed system of split exact sequences
   `0 → M₁ → M_{2,j} → M_{3,j} → 0` with `M_{3,j}` finitely presented. -/
@[stacks 058K "Items (1)-(6), in the source's order, as a `List.TFAE`."]
public theorem Function.Exact.universallyExact_tfae {R : Type u} [CommRing R] [Small.{v} R]
    {M₁ M₂ M₃ : Type v} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃] {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃}
    (h : Function.Exact f₁ f₂) (h₁ : Function.Injective f₁) (h₂ : Function.Surjective f₂) :
    List.TFAE
      [ ∀ (Q : Type v) [AddCommGroup Q] [Module R Q], Function.Injective (f₁.rTensor Q),
        ∀ (Q : Type v) [AddCommGroup Q] [Module R Q] [Module.FinitePresentation R Q],
          Function.Injective (f₁.rTensor Q) ∧ Function.Exact (f₁.rTensor Q) (f₂.rTensor Q) ∧
            Function.Surjective (f₂.rTensor Q),
        ∀ (n m : ℕ) (x : Fin n → M₁) (y : Fin m → M₂) (a : Fin n → Fin m → R),
          (∀ i, f₁ (x i) = ∑ j, a i j • y j) → ∃ z : Fin m → M₁, ∀ i, x i = ∑ j, a i j • z j,
        ∀ (n m : ℕ) (α : (Fin n →₀ R) →ₗ[R] (Fin m →₀ R)) (β : (Fin n →₀ R) →ₗ[R] M₁)
          (γ : (Fin m →₀ R) →ₗ[R] M₂), f₁ ∘ₗ β = γ ∘ₗ α →
            ∃ δ : (Fin m →₀ R) →ₗ[R] M₁, δ ∘ₗ α = β,
        ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P],
          Function.Surjective (LinearMap.compRight (M := P) R f₂),
        ∃ (J : Type v) (_ : Preorder J) (_ : IsDirected J (· ≤ ·)) (_ : Nonempty J)
            (F : J ⥤ ShortComplex (ModuleCat.{v} R)) (c : Cocone F) (_ : IsColimit c)
            (_ : c.pt ≅ ModuleCat.shortComplexOfCompEqZero f₁ f₂ h.linearMap_comp_eq_zero),
          ∀ j, Nonempty (F.obj j).Splitting ∧ Module.FinitePresentation R (F.obj j).X₃ ∧
            IsIso ((c.ι.app j).τ₁) ] :=
  Stacks.RingTheory.UniversalExactTFAE.solution (M₃ := M₃) h h₁ h₂

end

/-!
# A universally exact sequence with finitely presented cokernel is split

Let `R` be a commutative ring and let `0 → M₁ →[f₁] M₂ →[f₂] M₃ → 0` be a short exact sequence of
`R`-modules with `M₃` of finite presentation. This file proves Stacks 058L: the sequence is split
if and only if it is universally exact, that is, if and only if `f₁ ⊗ id_Q` is injective for every
`R`-module `Q`.

Both directions are one step. A split sequence is universally exact (Stacks 058J): if `f₂` has a
section then, the sequence being exact with `f₁` injective, `f₁` has a retraction `r`, and
`r ⊗ id_Q` is then a left inverse of `f₁ ⊗ id_Q`; so the latter is injective for every `Q`, with
no hypothesis on `M₃`. Conversely, universal exactness gives, by item (5) of Stacks 058K applied
to the finitely presented module `P = M₃`, that postcomposition with `f₂` is a surjection
`Hom_R(M₃, M₂) → Hom_R(M₃, M₃)`; a preimage of `id_{M₃}` is a section of `f₂`.

## Main results

* `Stacks.RingTheory.UniversalExactSplit.solution`: the statement of Stacks 058L,
  `Function.Exact.split_iff_forall_rTensor_injective`.

## Implementation notes

The forward direction goes through `Function.Exact.split_tfae'`, whose item (1) is the pair
`Function.Injective f₁` and the existence of a section of `f₂` and whose item (2) is the pair
`Function.Surjective f₂` and the existence of a retraction of `f₁`; only the retraction is used.
That a linear map with a retraction stays injective after tensoring is the private lemma
`Stacks.RingTheory.UniversalExactSplit.rTensor_injective_of_comp_eq_id`, stated for an arbitrary
commutative semiring and arbitrary modules since neither the exact sequence nor the finite
presentation plays any role in it. It is the substance of Stacks 058J, `Mathlib` having no
lemma for it.

## References

* [StacksProject 058L](https://stacks.math.columbia.edu/tag/058L)
-/



namespace Stacks.RingTheory.UniversalExactSplit

/-- A linear map admitting a retraction is injective after tensoring with any module: the tensored
retraction is a left inverse of the tensored map. -/
@[sga "3 I 4.6.6" "special case"]
private lemma rTensor_injective_of_comp_eq_id {R : Type*} [CommSemiring R] {M N : Type*}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] {f : M →ₗ[R] N} {r : N →ₗ[R] M}
    (hr : r ∘ₗ f = LinearMap.id) (Q : Type*) [AddCommMonoid Q] [Module R Q] :
    Function.Injective (f.rTensor Q) := by
  intro a b hab
  simpa [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hr] using congrArg (r.rTensor Q) hab

/-- **Stacks 058L**: for a short exact sequence `0 → M₁ → M₂ → M₃ → 0` of `R`-modules with `M₃`
finitely presented, `f₂` has an `R`-linear section if and only if `f₁ ⊗ id_Q` is injective for
every `R`-module `Q`. -/
public theorem solution {R : Type u} [CommRing R]
    [Small.{v} R] {M₁ M₂ M₃ : Type v} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
    [Module R M₂] [AddCommGroup M₃] [Module R M₃] [Module.FinitePresentation R M₃]
    {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃} (h : Function.Exact f₁ f₂)
    (h₁ : Function.Injective f₁) (h₂ : Function.Surjective f₂) :
    (∃ l : M₃ →ₗ[R] M₂, f₂ ∘ₗ l = LinearMap.id) ↔
      ∀ (Q : Type v) [AddCommGroup Q] [Module R Q],
        Function.Injective (f₁.rTensor Q) := by
  constructor
  · rintro hsec Q _ _
    have key := h.split_tfae'.out 1 2
    obtain ⟨-, r, hr⟩ := key.mp ⟨h₁, hsec⟩
    exact rTensor_injective_of_comp_eq_id hr Q
  · intro huniv
    have key := (h.universallyExact_tfae h₁ h₂).out 1 5
    obtain ⟨l, hl⟩ := key.mp huniv M₃ LinearMap.id
    exact ⟨l, by simpa using hl⟩

end Stacks.RingTheory.UniversalExactSplit

/-!
# A universally exact sequence with finitely presented cokernel is split

Let `R` be a commutative ring and let `0 → M₁ →[f₁] M₂ →[f₂] M₃ → 0` be a short exact sequence of
`R`-modules. Following Lazard, `f₁` is *universally injective* when `f₁ ⊗ id_Q` is injective for
every `R`-module `Q`, and the sequence is *universally exact* when it is exact and `f₁` is
universally injective (Stacks 058I). A split sequence is universally exact, since tensoring
preserves direct sums (Stacks 058J); the converse fails in general, the standard example being
`0 → ⨁ ℤ → ∏ ℤ → M₃ → 0` over `ℤ` (Stacks 058N). This file states Stacks 058L: the converse does
hold as soon as the cokernel `M₃` is of finite presentation, so that for such a sequence
universal exactness, splitness, and the existence of a section of `f₂` are one condition.

This is the module-theoretic counterpart of Stacks 058M, which says that flatness of `M₃` is
equivalent to universal exactness of *every* short exact sequence ending in `M₃`: here finite
presentation of `M₃` is imposed instead, and the conclusion is the much stronger one that the
given sequence splits.

## Main results

* `Function.Exact.split_iff_forall_rTensor_injective`: for a short exact sequence
  `0 → M₁ →[f₁] M₂ →[f₂] M₃ → 0` of `R`-modules with `M₃` of finite presentation, `f₂` admits an
  `R`-linear section if and only if `f₁ ⊗ id_Q : M₁ ⊗ Q → M₂ ⊗ Q` is injective for every
  `R`-module `Q`.

## Implementation notes

Exactness of the sequence is carried by the three hypotheses `Function.Exact f₁ f₂`,
`Function.Injective f₁` and `Function.Surjective f₂`, as in Stacks 058K and Stacks 058M, rather
than by a `ShortComplex.ShortExact` object; this is what lets this statement be chained with
item (5) of Stacks 058K, whose hypotheses are literally these, and with
`Function.Exact.split_tfae'`. Consequently "is universally exact" contributes only its second
half, universal injectivity of `f₁`, the first half being hypothesised. `Mathlib` has no
predicate for universal injectivity, so none is referred to; the condition is spelled out with
`LinearMap.rTensor`, exactly as item (1) of Stacks 058K does.

"Split" is spelled `∃ l, f₂ ∘ₗ l = LinearMap.id`, the existence of a section of `f₂`, which is
the second conjunct of the first item of Mathlib's `Function.Exact.split_tfae'`. Together with
the hypothesis `Function.Injective f₁` that is item (1) of that list, so the two remaining
descriptions of a split sequence — a retraction `l` of `f₁`, and an isomorphism
`e : M₂ ≃ₗ[R] M₁ × M₃` carrying `f₁` to `inl` and `f₂` to `snd` — follow from this statement by
`h.split_tfae'` with no further work, and are therefore not restated here. The section itself is
not canonical, and the source claims no more than its existence.

The three modules and the test module live in a single universe `Type v` and `R : Type u` is
assumed `Small.{v}`, the convention of `Module.Flat.iff_rTensor_exact'` and of Stacks 058E,
058F, 058K and 058M. This is not a weakening: `Small.{v} R` holds automatically when
`v = max u v`, in particular whenever `R` and the modules share a universe, so the single-universe
form is the instance `v := max u v` of this statement. It is also what makes the `Type v` test
modules exhaust all `R`-modules up to isomorphism, which is what the forward direction consumes:
the module witnessing universal injectivity in the source's argument is the cokernel `Q` of the
matrix of a presentation of `M₃`, a quotient of a finite free module and hence `Small.{u}` but not
in general `Small.{v}`.

Faithfulness. (1) No hypothesis is dead. `Function.Exact f₁ f₂` is live in both directions: for
`R = ℤ`, `M₁ = M₂ = ℤ`, `M₃ = ℤ ⧸ 2ℤ`, `f₁ = id` and `f₂` the reduction map the right-hand side
holds and `f₂` has no section, while for `M₁ = M₂ = M₃ = ℤ`, `f₁` multiplication by `2` and
`f₂ = id` the left-hand side holds and `f₁ ⊗ id_{ℤ ⧸ 2ℤ}` is not injective. `Function.Injective
f₁` is live: for `M₁ = M₂ = M₃ = ℤ`, `f₁ = 0` and `f₂ = id` the sequence is exact, `f₂` splits,
and `f₁ ⊗ id_ℤ = 0` is not injective. `Function.Surjective f₂` is live: for `M₁ = M₂ = 0`,
`M₃ = ℤ` and `f₁ = f₂ = 0` the sequence is exact, `f₁ ⊗ id_Q` is injective for every `Q`, and `f₂`
has no section. `Module.FinitePresentation R M₃` is live by Stacks 058N (1): over `R = ℤ` the
sequence `0 → ⨁_{n} ℤ → ∏_{n} ℤ → M₃ → 0` is universally exact and does not split. `Small.{v} R`
is used as described above and is automatic when `R` and the modules share a universe; no claim is
made that it cannot be removed. (2) The scalars and the base are the source's: `M₁`, `M₂`, `M₃`
and `Q` are `R`-modules, `f₁`, `f₂` and `l` are `R`-linear, finite presentation is over `R`, and
every tensor product is `⊗[R]`; nothing is localized or base changed. (3) Both maps the source
names are pinned: `f₁ ⊗ id_Q` is `f₁.rTensor Q`, built from `f₁` itself, and the section is pinned
by the equation `f₂ ∘ₗ l = LinearMap.id`, so the left-hand side is a statement about the given
`f₂` and not the existence of some split sequence. (4) The instantiation is not degenerate and
both directions have content: for `R = ℤ`, `M₁ = ℤ`, `M₂ = ℤ × ℤ`, `M₃ = ℤ`, `f₁ = inl` and
`f₂ = snd` both sides hold with `M₃` finitely presented, while for `R = ℤ`, `M₁ = M₂ = ℤ`,
`f₁` multiplication by `2` and `M₃ = ℤ ⧸ 2ℤ` finitely presented both sides fail, the right-hand
side at `Q = ℤ ⧸ 2ℤ`.

## References

* [StacksProject 058L](https://stacks.math.columbia.edu/tag/058L)
-/



@[expose] public section

/-- **Stacks 058L.** Let `0 → M₁ →[f₁] M₂ →[f₂] M₃ → 0` be a short exact sequence of `R`-modules
with `M₃` of finite presentation. Then `f₂` admits an `R`-linear section — equivalently, the
sequence is split — if and only if the sequence is universally exact, that is, if and only if
`f₁ ⊗ id_Q : M₁ ⊗ Q → M₂ ⊗ Q` is injective for every `R`-module `Q`. -/
@[stacks 058L "Exactness is hypothesised; splitness is the existence of a section of `f₂`."]
public theorem Function.Exact.split_iff_forall_rTensor_injective {R : Type u} [CommRing R]
    [Small.{v} R] {M₁ M₂ M₃ : Type v} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
    [Module R M₂] [AddCommGroup M₃] [Module R M₃] [Module.FinitePresentation R M₃]
    {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃} (h : Function.Exact f₁ f₂)
    (h₁ : Function.Injective f₁) (h₂ : Function.Surjective f₂) :
    (∃ l : M₃ →ₗ[R] M₂, f₂ ∘ₗ l = LinearMap.id) ↔
      ∀ (Q : Type v) [AddCommGroup Q] [Module R Q],
        Function.Injective (f₁.rTensor Q) :=
  Stacks.RingTheory.UniversalExactSplit.solution (M₁ := M₁) h h₁ h₂

end
