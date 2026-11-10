module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.HodgeProjectiveBundleFormula
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.KunnethAxiom
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.ProjectiveSpaceHodgeModule
public import StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceDeRhamClassPow
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.ProjectiveBundleAxiomDegreewise
public import StacksFrontier.AlgebraicGeometry.ProjAmple.Basic

/-!
# The projective bundle formula for Hodge cohomology of a trivial projective bundle

Let `k` be a field, `r ≥ 0`, `ℙʳ_k = Proj k[T₀, …, T_r]` with structure morphism
`π₀ : ℙʳ_k ⟶ Spec k`, and let `t : V ⟶ Spec k` be a quasi-compact `k`-scheme with affine diagonal,
for instance an affine `k`-scheme. Let `W = ℙʳ_k ×_k V`, with projections `pr₁ : W ⟶ ℙʳ_k` and
`pr₂ : W ⟶ V`, a `k`-scheme through `π = pr₁ ≫ π₀`. Let `ξ₀ = c₁^{Hodge}(𝒪(1)) ∈ H^1(ℙʳ_k, Ω^1)`,
placed in total degree `2` of `H^*_{Hodge}(ℙʳ_k/k)`, and `ξ = pr₁^* ξ₀ ∈ H^2_{Hodge}(W/k)`.
This file proves the projective bundle formula for the trivial bundle `W ⟶ V`: for every `n ∈ ℤ`
the map

`∏_{i ≤ r} H^{n - 2i}_{Hodge}(V/k) ⟶ H^n_{Hodge}(W/k)`, `(a_i) ↦ ∑ ξ^i ∪ pr₂^* a_i`,

is bijective.

The proof combines the Künneth formula for Hodge cohomology
(`Stacks.HodgeWeil.bijective_hodgeSchemeKunnethMap_pullback`) with the Hodge cohomology of `ℙʳ_k`
([Stacks, Tag 0FMI]): `H^b(ℙʳ_k, Ω^a) = 0` unless `a = b ≤ r`, and `H^a(ℙʳ_k, Ω^a)` is a line
spanned by `ξ₀^a` for `a ≤ r`. In bidegree `(m, s)` the Künneth formula identifies
`H^s(W, Ω^m)` with `⨁_{a + c = m, b + d = s} H^b(ℙʳ_k, Ω^a) ⊗_k H^d(V, Ω^c)`; only the summands
with `a = b ≤ r` survive, and tensoring with the basis vector `ξ₀^a` identifies
`H^a(ℙʳ_k, Ω^a) ⊗_k H^d(V, Ω^c)` with `H^d(V, Ω^c)`. Summing over `m + s = n`, the summand
`H^d(V, Ω^c)` of `H^{n - 2i}_{Hodge}(V/k)` is carried to the summand of bidegree
`(i + c, i + d)` of `H^n_{Hodge}(W/k)` by `a ↦ pr₁^* ξ₀^i ∪ pr₂^* a`, which is `ξ^i ∪ pr₂^* a`
because the pullback is multiplicative.

## Main definitions

* `Stacks.HodgeWeil.projectiveSpaceHodgeClass`: `ξ₀ = c₁^{Hodge}(𝒪(1))` in
  `H^2_{Hodge}(ℙʳ_k/k)`.
* `Stacks.HodgeWeil.trivialBundleHodgeClass`: `ξ = pr₁^* ξ₀` in `H^2_{Hodge}(W/k)`.
* `Stacks.HodgeWeil.trivialBundleKunnethMap`: the map
  `⨁_{i ≤ r} ⨁_{c + d = n - 2i} H^d(V, Ω^c) ⟶ H^n_{Hodge}(W/k)`, `a ↦ pr₁^* ξ₀^i ∪ pr₂^* a`,
  through the Künneth formula.

## Main results

* `Stacks.HodgeWeil.hodge_projectiveBundleAxiom`: **axiom (A3) for Hodge cohomology**,
  `(hodgeFirstChernClassData k).ProjectiveBundleAxiom`.
* `Stacks.HodgeWeil.bijective_degreewiseMap_trivialProjectiveBundle`: **the projective bundle
  formula for the trivial bundle `ℙʳ_k ×_k V ⟶ V`**, in every degree.
* `Stacks.HodgeWeil.bijective_trivialBundleKunnethMap`: the map through the Künneth formula is
  bijective.
* `Stacks.HodgeWeil.hodgeFirstChernClassModule_pow`: the `p`-th power of `c₁^{Hodge}(L)` in
  `H^*_{Hodge}(X/S)` is the cup power `Stacks.HodgeWeil.hodgeFirstChernClassPow` in bidegree
  `(p, p)`.
* `Stacks.HodgeWeil.bijective_of_lof_eq_lof_of_injective`: a map of direct sums carrying each
  summand bijectively onto a summand, along an injective map of index sets missing only zero
  summands, is bijective.

## Implementation notes

The class `ξ₀` is formed from the class of `𝒪(1)` in `Pic(ℙʳ_k)` given by
`Stacks.WeilCohomology.picardClassOf`, the spelling of `c₁^H(𝒪_P(1))` in
`Stacks.WeilCohomology.FirstChernClassData.bundleClass`; it is by definition the class
`Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.projectiveTwistingSheafOnePicardClass` for which
the Hodge cohomology of `ℙʳ_k` is computed (`Stacks.HodgeWeil.picardClassOf_projectiveTwistOne`).

The source `∏_{i ≤ r} H^{n - 2i}_{Hodge}(V/k)` is written as the direct sum over the pairs
`(i, (c, d))` with `c + d = n - 2i` (`Stacks.HodgeWeil.trivialBundleDegreewiseSource`), so that
the bijectivity is checked on the summands. The base `V` is only required to be quasi-compact
with affine diagonal, the hypotheses of the Künneth formula; an affine `V` satisfies them.

## References

* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Section 0FID](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 0FMI](https://stacks.math.columbia.edu/tag/0FMI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff)
open Stacks.ProjectiveBundleDeRham (projectiveTwistOne isInvertible_projectiveTwistOne)
open Stacks.AlgebraicGeometry.ProjectiveSpaceHodge (projectiveTwistingSheafOnePicardClass)
open AlgebraicGeometry.SheafOfModules (hodgeCohomologyComponent reindexHodgeDeg hodgeCohomologyCup)
open scoped TensorProduct

universe u

namespace Stacks.HodgeWeil

/-! ### Maps of direct sums -/

section DirectSum

variable {R : Type*} [Semiring R] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
  {M : ι → Type*} {N : κ → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ c, AddCommMonoid (N c)] [∀ c, Module R (N c)]

/-- **A map of direct sums carrying each summand bijectively onto a summand is bijective**, once
the map of index sets `e : ι ⟶ κ` is injective and the summands `N c`, `c ∉ e(ι)`, vanish. -/
theorem bijective_of_lof_eq_lof_of_injective (F : DirectSum ι M →ₗ[R] DirectSum κ N)
    {e : ι → κ} (he : Function.Injective e) (g : ∀ i, M i →ₗ[R] N (e i))
    (hg : ∀ i, Function.Bijective (g i)) (hN : ∀ c, (∀ i, e i ≠ c) → Subsingleton (N c))
    (hF : ∀ i x, F (DirectSum.lof R ι M i x) = DirectSum.lof R κ N (e i) (g i x)) :
    Function.Bijective F := by
  have hc : ∀ (i : ι) (z : DirectSum ι M), F z (e i) = g i (z i) := by
    intro i z
    induction z using DirectSum.induction_on with
    | zero => rw [map_zero, DirectSum.zero_apply, DirectSum.zero_apply, map_zero]
    | add z z' hz hz' => rw [map_add, DirectSum.add_apply, DirectSum.add_apply, hz, hz', map_add]
    | of j x =>
      rw [← DirectSum.lof_eq_of R, hF]
      by_cases hij : j = i
      · subst hij
        rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_eq_same, DirectSum.of_eq_same]
      · rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of,
          DirectSum.of_eq_of_ne _ _ _ (he.ne (Ne.symm hij)),
          DirectSum.of_eq_of_ne _ _ _ (Ne.symm hij), map_zero]
  refine ⟨fun z z' hzz => DFinsupp.ext fun i => (hg i).1 ?_, fun w => ?_⟩
  · rw [← hc, ← hc, hzz]
  · induction w using DirectSum.induction_on with
    | zero => exact ⟨0, map_zero F⟩
    | add w w' hw hw' =>
      obtain ⟨z, rfl⟩ := hw
      obtain ⟨z', rfl⟩ := hw'
      exact ⟨z + z', map_add F z z'⟩
    | of c y =>
      by_cases hci : ∃ i, e i = c
      · obtain ⟨i, rfl⟩ := hci
        obtain ⟨x, rfl⟩ := (hg i).2 y
        exact ⟨DirectSum.lof R ι M i x, hF i x⟩
      · have := hN c fun i h => hci ⟨i, h⟩
        exact ⟨0, by rw [map_zero, Subsingleton.elim y 0, map_zero]⟩

/-- **The same for a target which is a direct sum of direct sums**: a map
`⨁_i M i ⟶ ⨁_c ⨁_{d ∈ D c} N c d` carrying each summand `M i` bijectively onto the summand
`N (e i)`, for an injective `e : ι ⟶ Σ c, D c` missing only zero summands, is bijective. -/
theorem bijective_of_lof_eq_lof_lof_of_injective {κ : Type*} [DecidableEq κ] {D : κ → Type*}
    [∀ c, DecidableEq (D c)] {N : ∀ c, D c → Type*} [∀ c d, AddCommMonoid (N c d)]
    [∀ c d, Module R (N c d)]
    (F : DirectSum ι M →ₗ[R] DirectSum κ fun c => DirectSum (D c) (N c))
    {e : ι → Σ c, D c} (he : Function.Injective e) (g : ∀ i, M i →ₗ[R] N (e i).1 (e i).2)
    (hg : ∀ i, Function.Bijective (g i))
    (hN : ∀ c d, (∀ i, e i ≠ ⟨c, d⟩) → Subsingleton (N c d))
    (hF : ∀ i x, F (DirectSum.lof R ι M i x) =
      DirectSum.lof R κ _ (e i).1 (DirectSum.lof R (D (e i).1) (N (e i).1) (e i).2 (g i x))) :
    Function.Bijective F := by
  have h := bijective_of_lof_eq_lof_of_injective
    ((DirectSum.sigmaLcurryEquiv R (δ := N)).symm.toLinearMap ∘ₗ F) he g hg
    (fun c hc => hN c.1 c.2 hc) fun i x => by
      rw [LinearMap.comp_apply, hF, LinearEquiv.coe_coe, LinearEquiv.symm_apply_eq]
      exact (DirectSum.sigmaCurry_of (δ := N) (e i) (g i x)).symm
  rw [LinearMap.coe_comp, LinearEquiv.coe_coe] at h
  exact (Function.Bijective.of_comp_iff' (DirectSum.sigmaLcurryEquiv R (δ := N)).symm.bijective
    F).1 h

end DirectSum

/-- **Tensoring with the basis vector of a free module of rank one is bijective**:
`q ↦ b₀ ⊗ q`, `Q ⟶ P ⊗_K Q`, for a basis `(b₀)` of `P`. -/
theorem bijective_tensorProductMk_of_basis {K : Type*} [CommSemiring K] {P Q : Type*}
    [AddCommMonoid P] [Module K P] [AddCommMonoid Q] [Module K Q]
    (b : Module.Basis (Fin 1) K P) :
    Function.Bijective (TensorProduct.mk K P Q (b 0)) := by
  let e : P ⊗[K] Q ≃ₗ[K] Q :=
    (TensorProduct.congr (b.equivFun.trans (LinearEquiv.funUnique (Fin 1) K K))
      (LinearEquiv.refl K Q)).trans (TensorProduct.lid K Q)
  have h : (TensorProduct.mk K P Q (b 0) : Q → P ⊗[K] Q) = e.symm := funext fun q => by
    rw [LinearEquiv.eq_symm_apply]
    simp [e, TensorProduct.congr_tmul]
  rw [h]
  exact e.symm.bijective

/-! ### The degreewise projective bundle map -/

section Graded

variable {F : Type*} [Field F] {A B : Type*} [Ring A] [Algebra F A] [Ring B] [Algebra F B]
  {𝒜 : ℤ → Submodule F A} [_root_.GradedAlgebra 𝒜] {ℬ : ℤ → Submodule F B}
  [_root_.GradedAlgebra ℬ]

omit [_root_.GradedAlgebra 𝒜] in
/-- The degreewise projective bundle map is additive. -/
theorem degreewiseMap_add {φ : A →ₐ[F] B} (hφ : ∀ n, ∀ a ∈ 𝒜 n, φ a ∈ ℬ n) {ξ : B}
    (hξ : ξ ∈ ℬ 2) (r : ℕ) (n : ℤ) (a a' : ∀ i : Fin r, 𝒜 (n - 2 * ((i : ℕ) : ℤ))) :
    Stacks.WeilDeRham.degreewiseMap 𝒜 ℬ hφ hξ r n (a + a') =
      Stacks.WeilDeRham.degreewiseMap 𝒜 ℬ hφ hξ r n a +
        Stacks.WeilDeRham.degreewiseMap 𝒜 ℬ hφ hξ r n a' := by
  refine Subtype.ext ?_
  simp only [Stacks.WeilDeRham.coe_degreewiseMap, Submodule.coe_add, Pi.add_apply, map_add,
    mul_add, Finset.sum_add_distrib]

omit [_root_.GradedAlgebra 𝒜] in
/-- On a family `(a_j)` concentrated in the index `i`, the degreewise projective bundle map is
`ξ^i φ(a_i)`. -/
theorem coe_degreewiseMap_of_forall_ne {φ : A →ₐ[F] B} (hφ : ∀ n, ∀ a ∈ 𝒜 n, φ a ∈ ℬ n)
    {ξ : B} (hξ : ξ ∈ ℬ 2) (r : ℕ) (n : ℤ) (a : ∀ i : Fin r, 𝒜 (n - 2 * ((i : ℕ) : ℤ)))
    (i : Fin r) (ha : ∀ j, j ≠ i → a j = 0) :
    (Stacks.WeilDeRham.degreewiseMap 𝒜 ℬ hφ hξ r n a : B) = ξ ^ (i : ℕ) * φ (a i) := by
  rw [Stacks.WeilDeRham.coe_degreewiseMap, Finset.sum_eq_single i (fun j _ hj => by
      rw [ha j hj, ZeroMemClass.coe_zero, map_zero, mul_zero])
    (by simp)]

omit [_root_.GradedAlgebra 𝒜] in
/-- Additivity of the degreewise projective bundle map, in the form of an induction step. -/
theorem coe_degreewiseMap_eq_add {φ : A →ₐ[F] B} (hφ : ∀ n, ∀ a ∈ 𝒜 n, φ a ∈ ℬ n) {ξ : B}
    (hξ : ξ ∈ ℬ 2) (r : ℕ) (n : ℤ) {a a' a'' : ∀ i : Fin r, 𝒜 (n - 2 * ((i : ℕ) : ℤ))}
    (h : a'' = a + a') {x x' x'' : B} (hx : x'' = x + x')
    (ha : (Stacks.WeilDeRham.degreewiseMap 𝒜 ℬ hφ hξ r n a : B) = x)
    (ha' : (Stacks.WeilDeRham.degreewiseMap 𝒜 ℬ hφ hξ r n a' : B) = x') :
    (Stacks.WeilDeRham.degreewiseMap 𝒜 ℬ hφ hξ r n a'' : B) = x'' := by
  rw [h, hx, degreewiseMap_add, Submodule.coe_add, ha, ha']

omit [_root_.GradedAlgebra 𝒜] in
/-- The degreewise projective bundle map vanishes on `0`. -/
theorem coe_degreewiseMap_eq_zero {φ : A →ₐ[F] B} (hφ : ∀ n, ∀ a ∈ 𝒜 n, φ a ∈ ℬ n) {ξ : B}
    (hξ : ξ ∈ ℬ 2) (r : ℕ) (n : ℤ) {a : ∀ i : Fin r, 𝒜 (n - 2 * ((i : ℕ) : ℤ))} (h : a = 0)
    {x : B} (hx : x = 0) : (Stacks.WeilDeRham.degreewiseMap 𝒜 ℬ hφ hξ r n a : B) = x := by
  subst h hx
  simp [Stacks.WeilDeRham.coe_degreewiseMap]

end Graded

/-! ### Powers of the first Chern class -/

section Powers

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The product of two classes of pure bidegree is the cup product of pure bidegrees, read in the
degree `n'` for `n + m = n'`. -/
private theorem of_of_mul_of_of {n m n' : ℤ} (h : n + m = n') (i : HodgeBidegreeInt n)
    (j : HodgeBidegreeInt m) (ξ : hodgeCohomologyComponent (formsAlgebras f) i.1.1 (i.1.2 : ℤ))
    (ζ : hodgeCohomologyComponent (formsAlgebras f) j.1.1 (j.1.2 : ℤ)) :
    DirectSum.of (hodgePiece (formsAlgebras f)) n (DirectSum.of _ i ξ) *
        DirectSum.of (hodgePiece (formsAlgebras f)) m (DirectSum.of _ j ζ) =
      DirectSum.of (hodgePiece (formsAlgebras f)) n'
        (DirectSum.of (fun k : HodgeBidegreeInt n' =>
            (hodgeCohomologyComponent (formsAlgebras f) k.1.1 (k.1.2 : ℤ) : Type u))
          ⟨(i.1.1 + j.1.1, i.1.2 + j.1.2), (hodgeBidegreeInt_add i j).trans h⟩
          (reindexHodgeDeg (formsAlgebras f) (Nat.cast_add i.1.2 j.1.2).symm
            (hodgeCohomologyCup (formsAlgebras f) i.1.1 j.1.1 (i.1.2 : ℤ) (j.1.2 : ℤ) ξ ζ))) := by
  subst h
  rw [hodgeAlgebra_of_mul_of, hodgePieceMul_of]

/-- **The powers of `c₁^{Hodge}(L)` in `H^*_{Hodge}(X/S)`**: the `p`-th power of the class
`c₁^{Hodge}(L) ∈ H^1(X, Ω^1)` of total degree `2` is the cup power
`Stacks.HodgeWeil.hodgeFirstChernClassPow f L p ∈ H^p(X, Ω^p)`, in total degree `2p`. -/
theorem hodgeFirstChernClassModule_pow (L : Stacks.Picard.ofScheme X) (p : ℕ) :
    (DirectSum.of (hodgePiece (formsAlgebras f)) 2
      (DirectSum.of (fun i : HodgeBidegreeInt 2 =>
          (hodgeCohomologyComponent (formsAlgebras f) i.1.1 (i.1.2 : ℤ) : Type u))
        bidegreeOneOne (hodgeFirstChernClassModule f L))) ^ p =
      DirectSum.of (hodgePiece (formsAlgebras f)) (2 * (p : ℤ))
        (DirectSum.of (fun i : HodgeBidegreeInt (2 * (p : ℤ)) =>
            (hodgeCohomologyComponent (formsAlgebras f) i.1.1 (i.1.2 : ℤ) : Type u))
          ⟨(p, p), by push_cast; ring⟩ (hodgeFirstChernClassPow f L p)) := by
  induction p with
  | zero =>
    rw [pow_zero, hodgeAlgebra_one, hodgePieceOne]
    exact (of_castHodgePiece (formsAlgebras f) (show (0 : ℤ) = 2 * ((0 : ℕ) : ℤ) by norm_num)
      _).symm.trans (congrArg _ (castHodgePiece_of _ _ _ _))
  | succ p ih =>
    rw [pow_succ, ih]
    exact of_of_mul_of_of f (by push_cast; ring) _ _ _ _

end Powers

variable {k : Type u} [Field k]

/-! ### The class of `𝒪(1)` on `ℙʳ_k` -/

variable (k) in
/-- **The class `ξ₀ = c₁^{Hodge}(𝒪(1))` of `ℙʳ_k`**, in `H^1(ℙʳ_k, Ω^1)` placed in total degree
`2` of `H^*_{Hodge}(ℙʳ_k/k)`. -/
def projectiveSpaceHodgeClass (r : ℕ) : hodgeAlgebra (formsAlgebras (projToSpecCoeff k r)) :=
  DirectSum.of (hodgePiece (formsAlgebras (projToSpecCoeff k r))) 2
    (DirectSum.of (fun i : HodgeBidegreeInt 2 =>
        (hodgeCohomologyComponent (formsAlgebras (projToSpecCoeff k r)) i.1.1 (i.1.2 : ℤ) :
          Type u))
      bidegreeOneOne
      (hodgeFirstChernClassModule (projToSpecCoeff k r)
        (Stacks.WeilCohomology.picardClassOf _ (projectiveTwistOne k r)
          (isInvertible_projectiveTwistOne k r))))

variable (k) in
/-- The class of `𝒪(1)` in `Pic(ℙʳ_k)` formed through `Stacks.WeilCohomology.picardClassOf` is
`Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.projectiveTwistingSheafOnePicardClass`. -/
theorem picardClassOf_projectiveTwistOne (r : ℕ) :
    Stacks.WeilCohomology.picardClassOf _ (projectiveTwistOne k r)
      (isInvertible_projectiveTwistOne k r) = projectiveTwistingSheafOnePicardClass k r :=
  rfl

variable (k) in
/-- A basis of the line `H^i(ℙʳ_k, Ω^i)`, `i ≤ r`, whose vector is the cup power
`c₁^{Hodge}(𝒪(1))^i` ([Stacks, Tag 0FMI]). -/
def projectiveSpaceHodgeBasis (r : ℕ) (i : Fin (r + 1)) :
    Module.Basis (Fin 1) k
      (hodgeCohomologyComponent (formsAlgebras (projToSpecCoeff k r)) (i : ℕ) ((i : ℕ) : ℤ)) :=
  (exists_basis_hodgeFirstChernClassPow k r i (Nat.lt_succ_iff.mp i.2)).choose

variable (k) in
/-- The vector of `Stacks.HodgeWeil.projectiveSpaceHodgeBasis` is `c₁^{Hodge}(𝒪(1))^i`. -/
theorem projectiveSpaceHodgeBasis_zero (r : ℕ) (i : Fin (r + 1)) :
    projectiveSpaceHodgeBasis k r i 0 = hodgeFirstChernClassPow (projToSpecCoeff k r)
      (projectiveTwistingSheafOnePicardClass k r) i :=
  (exists_basis_hodgeFirstChernClassPow k r i (Nat.lt_succ_iff.mp i.2)).choose_spec

variable (k) in
/-- **`ξ₀^i` is the basis vector of `H^i(ℙʳ_k, Ω^i)`**, in total degree `2i`, for `i ≤ r`. -/
theorem projectiveSpaceHodgeClass_pow (r : ℕ) (i : Fin (r + 1)) :
    projectiveSpaceHodgeClass k r ^ (i : ℕ) =
      DirectSum.of (hodgePiece (formsAlgebras (projToSpecCoeff k r))) (2 * ((i : ℕ) : ℤ))
        (DirectSum.of (fun j : HodgeBidegreeInt (2 * ((i : ℕ) : ℤ)) =>
            (hodgeCohomologyComponent (formsAlgebras (projToSpecCoeff k r)) j.1.1 (j.1.2 : ℤ) :
              Type u))
          ⟨((i : ℕ), (i : ℕ)), by push_cast; ring⟩ (projectiveSpaceHodgeBasis k r i 0)) := by
  rw [projectiveSpaceHodgeBasis_zero, projectiveSpaceHodgeClass, picardClassOf_projectiveTwistOne]
  exact hodgeFirstChernClassModule_pow (projToSpecCoeff k r) _ (i : ℕ)

/-! ### The Künneth decomposition of `ℙʳ_k ×_k V` -/

/-- The summand met by `ξ₀^i ⊗ a`, `a ∈ H^d(V, Ω^c)` with `c + d = n - 2i`, in the Künneth
decomposition of `H^n_{Hodge}(ℙʳ_k ×_k V)`: the summand of bidegrees `(i, i)` and `(c, d)` of the
bidegree `(i + c, i + d)`. -/
def trivialBundleKunnethIndex (r : ℕ) (n : ℤ)
    (x : Σ i : Fin (r + 1), HodgeBidegreeInt (n - 2 * ((i : ℕ) : ℤ))) :
    Σ j : HodgeBidegreeInt n, {y : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd y = j.1} :=
  ⟨⟨((x.1 : ℕ) + x.2.1.1, (x.1 : ℕ) + x.2.1.2), by
      have h := x.2.2
      dsimp only at h ⊢
      push_cast at h ⊢
      omega⟩,
    ⟨(((x.1 : ℕ), (x.1 : ℕ)), x.2.1), rfl⟩⟩

/-- The map `trivialBundleKunnethIndex r n` is injective. -/
theorem injective_trivialBundleKunnethIndex (r : ℕ) (n : ℤ) :
    Function.Injective (trivialBundleKunnethIndex r n) := by
  rintro ⟨i, ⟨cd, h⟩⟩ ⟨i', ⟨cd', h'⟩⟩ he
  have h2 := congrArg (fun z => z.2.1) he
  simp only [trivialBundleKunnethIndex, Prod.mk.injEq] at h2
  obtain ⟨⟨hi, -⟩, rfl⟩ := h2
  obtain rfl : i = i' := Fin.ext hi
  rfl

section Kunneth

variable {V : Scheme.{u}} (t : V ⟶ Spec (.of k)) (r : ℕ)
  (b : ∀ i : Fin (r + 1), Module.Basis (Fin 1) k
    (hodgeCohomologyComponent (formsAlgebras (projToSpecCoeff k r)) (i : ℕ) ((i : ℕ) : ℤ)))

/-- The inclusion `⨁_{i ≤ r} ⨁_{c + d = n - 2i} H^d(V, Ω^c) ⟶
⨁_{m + s = n} ⨁_{a + c = m, b + d = s} H^b(ℙʳ_k, Ω^a) ⊗_k H^d(V, Ω^c)`,
`a ↦ b_i ⊗ a` into the summand of bidegrees `(i, i)` and `(c, d)`, for a basis `b_i` of
`H^i(ℙʳ_k, Ω^i)`. -/
def trivialBundleKunnethInclusion (n : ℤ) :
    (DirectSum (Σ i : Fin (r + 1), HodgeBidegreeInt (n - 2 * ((i : ℕ) : ℤ))) fun x =>
        hodgeCohomologyComponent (formsAlgebras t) x.2.1.1 (x.2.1.2 : ℤ)) →ₗ[k]
      DirectSum (HodgeBidegreeInt n) (fun j =>
        DirectSum {y : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd y = j.1} fun y =>
          hodgeCohomologyComponent (formsAlgebras (projToSpecCoeff k r)) y.1.1.1 (y.1.1.2 : ℤ) ⊗[k]
            hodgeCohomologyComponent (formsAlgebras t) y.1.2.1 (y.1.2.2 : ℤ)) :=
  DirectSum.toModule k _ _ fun x =>
    DirectSum.lof k (HodgeBidegreeInt n) (fun j =>
        DirectSum {y : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd y = j.1} fun y =>
          hodgeCohomologyComponent (formsAlgebras (projToSpecCoeff k r)) y.1.1.1 (y.1.1.2 : ℤ) ⊗[k]
            hodgeCohomologyComponent (formsAlgebras t) y.1.2.1 (y.1.2.2 : ℤ))
        (trivialBundleKunnethIndex r n x).1 ∘ₗ
      DirectSum.lof k _ (fun y : {y : (ℕ × ℕ) × (ℕ × ℕ) //
            hodgeBidegreeAdd y = (trivialBundleKunnethIndex r n x).1.1} =>
          hodgeCohomologyComponent (formsAlgebras (projToSpecCoeff k r)) y.1.1.1 (y.1.1.2 : ℤ) ⊗[k]
            hodgeCohomologyComponent (formsAlgebras t) y.1.2.1 (y.1.2.2 : ℤ))
        (trivialBundleKunnethIndex r n x).2 ∘ₗ
      TensorProduct.mk k
        (hodgeCohomologyComponent (formsAlgebras (projToSpecCoeff k r)) (x.1 : ℕ) ((x.1 : ℕ) : ℤ))
        (hodgeCohomologyComponent (formsAlgebras t) x.2.1.1 (x.2.1.2 : ℤ)) (b x.1 0)

/-- The inclusion into the Künneth decomposition sends `v` in the summand of index `x` to
`b x.1 0 ⊗ₜ v` in the summand `trivialBundleKunnethIndex r n x`. -/
theorem trivialBundleKunnethInclusion_lof (n : ℤ)
    (x : Σ i : Fin (r + 1), HodgeBidegreeInt (n - 2 * ((i : ℕ) : ℤ)))
    (v : hodgeCohomologyComponent (formsAlgebras t) x.2.1.1 (x.2.1.2 : ℤ)) :
    trivialBundleKunnethInclusion t r b n (DirectSum.lof k _ _ x v) =
      DirectSum.lof k (HodgeBidegreeInt n) (fun j =>
          DirectSum {y : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd y = j.1} fun y =>
            hodgeCohomologyComponent (formsAlgebras (projToSpecCoeff k r)) y.1.1.1
                (y.1.1.2 : ℤ) ⊗[k]
              hodgeCohomologyComponent (formsAlgebras t) y.1.2.1 (y.1.2.2 : ℤ))
        (trivialBundleKunnethIndex r n x).1
        (DirectSum.lof k _ (fun y : {y : (ℕ × ℕ) × (ℕ × ℕ) //
              hodgeBidegreeAdd y = (trivialBundleKunnethIndex r n x).1.1} =>
            hodgeCohomologyComponent (formsAlgebras (projToSpecCoeff k r)) y.1.1.1
                (y.1.1.2 : ℤ) ⊗[k]
              hodgeCohomologyComponent (formsAlgebras t) y.1.2.1 (y.1.2.2 : ℤ))
          (trivialBundleKunnethIndex r n x).2 (b x.1 0 ⊗ₜ v)) :=
  DirectSum.toModule_lof k _ _

/-- **The inclusion into the Künneth decomposition is bijective**: by [Stacks, Tag 0FMI]
`H^b(ℙʳ_k, Ω^a) = 0` unless `a = b ≤ r`, and tensoring with the basis vector of the line
`H^a(ℙʳ_k, Ω^a)` is bijective. -/
theorem bijective_trivialBundleKunnethInclusion (n : ℤ) :
    Function.Bijective (trivialBundleKunnethInclusion t r b n) := by
  refine bijective_of_lof_eq_lof_lof_of_injective _ (injective_trivialBundleKunnethIndex r n)
    (fun x => TensorProduct.mk k
      (hodgeCohomologyComponent (formsAlgebras (projToSpecCoeff k r)) (x.1 : ℕ) ((x.1 : ℕ) : ℤ))
      (hodgeCohomologyComponent (formsAlgebras t) x.2.1.1 (x.2.1.2 : ℤ)) (b x.1 0))
    (fun x => bijective_tensorProductMk_of_basis (b x.1))
    ?_ (trivialBundleKunnethInclusion_lof t r b n)
  rintro ⟨⟨m, s⟩, hj⟩ ⟨⟨⟨a, a'⟩, ⟨c, d⟩⟩, hy⟩ hne
  by_cases ha : a = a' ∧ a ≤ r
  · obtain ⟨rfl, ha⟩ := ha
    have hy' := hy
    simp only [hodgeBidegreeAdd, Prod.mk.injEq] at hy'
    obtain ⟨rfl, rfl⟩ := hy'
    refine (hne ⟨⟨a, Nat.lt_succ_of_le ha⟩, ⟨(c, d), ?_⟩⟩ rfl).elim
    dsimp only at hj ⊢
    push_cast at hj ⊢
    omega
  · have := ModuleCat.subsingleton_of_isZero
      (isZero_hodgeCohomologyComponent_projectiveSpace k r a (a' : ℤ) (by omega))
    dsimp only
    infer_instance

/-- **The map `⨁_{i ≤ r} ⨁_{c + d = n - 2i} H^d(V, Ω^c) ⟶ H^n_{Hodge}(ℙʳ_k ×_k V)`**,
`a ↦ pr₁^* b_i ∪ pr₂^* a` on the summand `H^d(V, Ω^c)` of index `i`, through the Künneth
decomposition, for a basis `b_i` of `H^i(ℙʳ_k, Ω^i)`. -/
def trivialBundleKunnethMap (n : ℤ) :
    (DirectSum (Σ i : Fin (r + 1), HodgeBidegreeInt (n - 2 * ((i : ℕ) : ℤ))) fun x =>
        hodgeCohomologyComponent (formsAlgebras t) x.2.1.1 (x.2.1.2 : ℤ)) →ₗ[k]
      DirectSum (HodgeBidegreeInt n) fun j =>
        hodgeCohomologyComponent
          (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
          j.1.1 (j.1.2 : ℤ) :=
  (DirectSum.lmap (fun j : HodgeBidegreeInt n => hodgeSchemeKunnethMap (projToSpecCoeff k r) t
      (pullback.fst _ _) (pullback.snd _ _) pullback.condition j.1)) ∘ₗ
    trivialBundleKunnethInclusion t r b n

/-- `trivialBundleKunnethMap` is the Künneth map in each bidegree applied after
`trivialBundleKunnethInclusion`. -/
theorem trivialBundleKunnethMap_apply (n : ℤ)
    (z : DirectSum (Σ i : Fin (r + 1), HodgeBidegreeInt (n - 2 * ((i : ℕ) : ℤ))) fun x =>
      hodgeCohomologyComponent (formsAlgebras t) x.2.1.1 (x.2.1.2 : ℤ)) :
    trivialBundleKunnethMap t r b n z =
      (DirectSum.lmap (fun j : HodgeBidegreeInt n => hodgeSchemeKunnethMap (projToSpecCoeff k r) t
        (pullback.fst _ _) (pullback.snd _ _) pullback.condition j.1))
        (trivialBundleKunnethInclusion t r b n z) :=
  rfl

/-- On the summand `H^d(V, Ω^c)` of index `i` the map is `a ↦ pr₁^* b_i ∪ pr₂^* a`, in the
bidegree `(i + c, i + d)`. -/
theorem trivialBundleKunnethMap_of (n : ℤ)
    (x : Σ i : Fin (r + 1), HodgeBidegreeInt (n - 2 * ((i : ℕ) : ℤ)))
    (v : hodgeCohomologyComponent (formsAlgebras t) x.2.1.1 (x.2.1.2 : ℤ)) :
    trivialBundleKunnethMap t r b n (DirectSum.of _ x v) =
      DirectSum.lof k (HodgeBidegreeInt n) (fun j : HodgeBidegreeInt n =>
          (hodgeCohomologyComponent
            (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
            j.1.1 (j.1.2 : ℤ) : Type u))
        ⟨((x.1 : ℕ) + x.2.1.1, (x.1 : ℕ) + x.2.1.2), by
          have hx := x.2.2
          dsimp only at hx ⊢
          push_cast at hx ⊢
          omega⟩
        (reindexHodgeDeg
          (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
          (Nat.cast_add (x.1 : ℕ) x.2.1.2).symm
          (hodgeCohomologyCup
            (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
            (x.1 : ℕ) x.2.1.1 ((x.1 : ℕ) : ℤ) (x.2.1.2 : ℤ)
            (hodgePullback (pullback.fst (projToSpecCoeff k r) t)
              (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r) (projToSpecCoeff k r)
              (𝟙 _) (Category.comp_id _).symm (x.1 : ℕ) ((x.1 : ℕ) : ℤ) (b x.1 0))
            (hodgePullback (pullback.snd (projToSpecCoeff k r) t)
              (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r) t (𝟙 _)
              (hodgeSchemeSquare_snd pullback.condition) x.2.1.1 (x.2.1.2 : ℤ) v))) := by
  have h1 := trivialBundleKunnethInclusion_lof t r b n x v
  have h3 := hodgeSchemeKunnethMap_lof_tmul (projToSpecCoeff k r) t (pullback.fst _ _)
    (pullback.snd _ _) pullback.condition ((x.1 : ℕ), (x.1 : ℕ)) x.2.1 (b x.1 0) v
  refine (congrArg (DFunLike.coe (trivialBundleKunnethMap t r b n))
    (DirectSum.lof_eq_of k (Σ i : Fin (r + 1), HodgeBidegreeInt (n - 2 * ((i : ℕ) : ℤ)))
      (fun x : Σ i : Fin (r + 1), HodgeBidegreeInt (n - 2 * ((i : ℕ) : ℤ)) =>
        (hodgeCohomologyComponent (formsAlgebras t) x.2.1.1 (x.2.1.2 : ℤ) : Type u))
      x v).symm).trans ?_
  refine (trivialBundleKunnethMap_apply t r b n _).trans ?_
  refine (congrArg (DFunLike.coe (DirectSum.lmap (fun j : HodgeBidegreeInt n =>
    hodgeSchemeKunnethMap (projToSpecCoeff k r) t (pullback.fst _ _) (pullback.snd _ _)
      pullback.condition j.1))) h1).trans ?_
  refine (DirectSum.lmap_lof _ _ _).trans ?_
  exact congrArg (DirectSum.lof k (HodgeBidegreeInt n) (fun j : HodgeBidegreeInt n =>
    (hodgeCohomologyComponent
      (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
      j.1.1 (j.1.2 : ℤ) : Type u)) _) h3

/-- **The map through the Künneth decomposition is bijective**, for `V` quasi-compact with affine
diagonal: the inclusion into the Künneth decomposition is bijective, and so is the Künneth map
in every bidegree (`Stacks.HodgeWeil.bijective_hodgeSchemeKunnethMap_pullback`). -/
theorem bijective_trivialBundleKunnethMap [CompactSpace V]
    [IsAffineHom (pullback.diagonal (terminal.from V))] (n : ℤ) :
    Function.Bijective (trivialBundleKunnethMap t r b n) := by
  have := Stacks.ProjAmple.compactSpace_proj_polyGrading k r
  have hK : ∀ j : HodgeBidegreeInt n, Function.Bijective (hodgeSchemeKunnethMap
      (projToSpecCoeff k r) t (pullback.fst _ _) (pullback.snd _ _) pullback.condition j.1) :=
    fun j => bijective_hodgeSchemeKunnethMap_pullback _ _ j.1
  have hL : Function.Bijective (DirectSum.lmap (fun j : HodgeBidegreeInt n =>
      hodgeSchemeKunnethMap (projToSpecCoeff k r) t (pullback.fst _ _) (pullback.snd _ _)
        pullback.condition j.1)) :=
    ⟨(DirectSum.lmap_injective _).2 fun j => (hK j).1,
      (DirectSum.lmap_surjective _).2 fun j => (hK j).2⟩
  rw [trivialBundleKunnethMap, LinearMap.coe_comp]
  exact hL.comp (bijective_trivialBundleKunnethInclusion t r b n)

end Kunneth

/-! ### The projective bundle formula for `ℙʳ_k ×_k V ⟶ V` -/

section Bundle

variable {V : Scheme.{u}} (t : V ⟶ Spec (.of k)) (r : ℕ)

/-- **The class `ξ = pr₁^* c₁^{Hodge}(𝒪(1))`** of the trivial projective bundle
`ℙʳ_k ×_k V ⟶ V`, in `H^2_{Hodge}(ℙʳ_k ×_k V/k)`, the fibre product being a `k`-scheme through
`pr₁ ≫ π₀`. -/
def trivialBundleHodgeClass :
    hodgeAlgebra (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r)) :=
  hodgeAlgebraPullbackOverBase (pullback.fst (projToSpecCoeff k r) t) (specScalars k)
    (projToSpecCoeff k r) (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r)
    (Category.comp_id _).symm (projectiveSpaceHodgeClass k r)

/-- `ξ = pr₁^* c₁^{Hodge}(𝒪(1))` lies in `H^2_{Hodge}(ℙʳ_k ×_k V/k)`. -/
theorem trivialBundleHodgeClass_mem :
    letI := hodgeAlgebraAlgebra
      (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
      (hodgeScalarsOverField (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
    trivialBundleHodgeClass t r ∈
      hodgeGrade (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
        (hodgeScalarsOverField (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r)) 2 :=
  hodgeAlgebraPullbackOverBase_mem_hodgeGrade _ _ _ _ _ 2 _ (of_mem_hodgeGrade _ _ 2 _)

/-- The pullback on `H^*_{Hodge}` of a class of pure bidegree is the pullback of pure bidegrees. -/
private theorem hodgeAlgebraPullback_of_of {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (f : X ⟶ S) (g : S' ⟶ S) (w : g' ≫ f = f' ≫ g) (n : ℤ) (i : HodgeBidegreeInt n)
    (x : hodgeCohomologyComponent (formsAlgebras f) i.1.1 (i.1.2 : ℤ)) :
    hodgeAlgebraPullback g' f' f g w
        (DirectSum.of (hodgePiece (formsAlgebras f)) n (DirectSum.of _ i x)) =
      DirectSum.of (hodgePiece (formsAlgebras f')) n
        (DirectSum.of (fun j : HodgeBidegreeInt n =>
          (hodgeCohomologyComponent (formsAlgebras f') j.1.1 (j.1.2 : ℤ) : Type u)) i
          (hodgePullback g' f' f g w i.1.1 (i.1.2 : ℤ) x)) :=
  (hodgeAlgebraPullback_of _ _ _ _ _ _ _).trans
    (congrArg _ (hodgePiecePullback_of _ _ _ _ _ _ _ _))

/-- `ξ^i` is the pullback of the basis vector of `H^i(ℙʳ_k, Ω^i)`, in total degree `2i`. -/
theorem trivialBundleHodgeClass_pow (i : Fin (r + 1)) :
    trivialBundleHodgeClass t r ^ (i : ℕ) =
      DirectSum.of (hodgePiece
          (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r)))
        (2 * ((i : ℕ) : ℤ))
        (DirectSum.of (fun j : HodgeBidegreeInt (2 * ((i : ℕ) : ℤ)) =>
            (hodgeCohomologyComponent
              (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
              j.1.1 (j.1.2 : ℤ) : Type u))
          ⟨((i : ℕ), (i : ℕ)), by push_cast; ring⟩
          (hodgePullback (pullback.fst (projToSpecCoeff k r) t)
            (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r) (projToSpecCoeff k r)
            (𝟙 _) (Category.comp_id _).symm (i : ℕ) ((i : ℕ) : ℤ)
            (projectiveSpaceHodgeBasis k r i 0))) := by
  refine (map_pow (hodgeAlgebraPullback (pullback.fst (projToSpecCoeff k r) t)
    (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r) (projToSpecCoeff k r) (𝟙 _)
    (Category.comp_id _).symm) (projectiveSpaceHodgeClass k r) (i : ℕ)).symm.trans ?_
  rw [projectiveSpaceHodgeClass_pow]
  exact hodgeAlgebraPullback_of_of _ _ _ _ _ _ _ _

/-- The family `(a_i)_{i ≤ r}`, `a_i ∈ H^{n - 2i}_{Hodge}(V/k)`, with the components
`a_i = ∑_{c + d = n - 2i} z_{i, (c, d)}` of `z ∈ ⨁_{i ≤ r} ⨁_{c + d = n - 2i} H^d(V, Ω^c)`. -/
def trivialBundleDegreewiseSource (n : ℤ)
    (z : DirectSum (Σ i : Fin (r + 1), HodgeBidegreeInt (n - 2 * ((i : ℕ) : ℤ))) fun x =>
      hodgeCohomologyComponent (formsAlgebras t) x.2.1.1 (x.2.1.2 : ℤ)) (i : Fin (r + 1)) :
    hodgeGrade (formsAlgebras t) (hodgeScalarsOverField t) (n - 2 * ((i : ℕ) : ℤ)) :=
  ⟨DirectSum.of (hodgePiece (formsAlgebras t)) (n - 2 * ((i : ℕ) : ℤ))
      (DirectSum.sigmaCurry (δ := fun (i : Fin (r + 1))
          (cd : HodgeBidegreeInt (n - 2 * ((i : ℕ) : ℤ))) =>
        (hodgeCohomologyComponent (formsAlgebras t) cd.1.1 (cd.1.2 : ℤ) : Type u)) z i),
    of_mem_hodgeGrade _ _ _ _⟩

/-- The component of index `i` of `trivialBundleDegreewiseSource t r n z`, as an element of the
Hodge algebra of `V`. -/
theorem coe_trivialBundleDegreewiseSource (n : ℤ)
    (z : DirectSum (Σ i : Fin (r + 1), HodgeBidegreeInt (n - 2 * ((i : ℕ) : ℤ))) fun x =>
      hodgeCohomologyComponent (formsAlgebras t) x.2.1.1 (x.2.1.2 : ℤ)) (i : Fin (r + 1)) :
    (trivialBundleDegreewiseSource t r n z i : hodgeAlgebra (formsAlgebras t)) =
      DirectSum.of (hodgePiece (formsAlgebras t)) (n - 2 * ((i : ℕ) : ℤ))
        (DirectSum.sigmaCurry (δ := fun (i : Fin (r + 1))
            (cd : HodgeBidegreeInt (n - 2 * ((i : ℕ) : ℤ))) =>
          (hodgeCohomologyComponent (formsAlgebras t) cd.1.1 (cd.1.2 : ℤ) : Type u)) z i) :=
  rfl

/-- `trivialBundleDegreewiseSource` is additive. -/
theorem trivialBundleDegreewiseSource_add (n : ℤ)
    (z z' : DirectSum (Σ i : Fin (r + 1), HodgeBidegreeInt (n - 2 * ((i : ℕ) : ℤ))) fun x =>
      hodgeCohomologyComponent (formsAlgebras t) x.2.1.1 (x.2.1.2 : ℤ)) :
    trivialBundleDegreewiseSource t r n (z + z') =
      trivialBundleDegreewiseSource t r n z + trivialBundleDegreewiseSource t r n z' :=
  funext fun i => Subtype.ext (by
    simp only [coe_trivialBundleDegreewiseSource, Pi.add_apply, Submodule.coe_add, map_add,
      DirectSum.add_apply])

/-- `trivialBundleDegreewiseSource` sends `0` to `0`. -/
theorem trivialBundleDegreewiseSource_zero (n : ℤ) :
    trivialBundleDegreewiseSource t r n 0 = 0 :=
  funext fun i => Subtype.ext (by
    simp only [coe_trivialBundleDegreewiseSource, map_zero, DirectSum.zero_apply, Pi.zero_apply,
      ZeroMemClass.coe_zero])

/-- **`∏_{i ≤ r} H^{n - 2i}_{Hodge}(V/k) = ⨁_{i ≤ r} ⨁_{c + d = n - 2i} H^d(V, Ω^c)`**. -/
theorem bijective_trivialBundleDegreewiseSource (n : ℤ) :
    Function.Bijective (trivialBundleDegreewiseSource t r n) := by
  refine ⟨fun z z' hzz => ?_, fun a => ?_⟩
  · apply (DirectSum.sigmaCurryEquiv (δ := fun (i : Fin (r + 1))
        (cd : HodgeBidegreeInt (n - 2 * ((i : ℕ) : ℤ))) =>
      (hodgeCohomologyComponent (formsAlgebras t) cd.1.1 (cd.1.2 : ℤ) : Type u))).injective
    refine DFinsupp.ext fun i => DirectSum.of_injective (β := hodgePiece (formsAlgebras t)) _ ?_
    exact congrArg Subtype.val (congrFun hzz i)
  · choose y hy using fun i : Fin (r + 1) =>
      (mem_hodgeGrade (formsAlgebras t) (hodgeScalarsOverField t) _ (a i : _)).1 (a i).2
    refine ⟨(DirectSum.sigmaCurryEquiv (δ := fun (i : Fin (r + 1))
        (cd : HodgeBidegreeInt (n - 2 * ((i : ℕ) : ℤ))) =>
      (hodgeCohomologyComponent (formsAlgebras t) cd.1.1 (cd.1.2 : ℤ) : Type u))).symm
        (DFinsupp.equivFunOnFintype.symm y), funext fun i => Subtype.ext ?_⟩
    refine Eq.trans ?_ (hy i).symm
    exact congrArg (DirectSum.of (hodgePiece (formsAlgebras t)) (n - 2 * ((i : ℕ) : ℤ)))
      (congrFun (congrArg DFunLike.coe ((DirectSum.sigmaCurryEquiv (δ := fun (i : Fin (r + 1))
          (cd : HodgeBidegreeInt (n - 2 * ((i : ℕ) : ℤ))) =>
        (hodgeCohomologyComponent (formsAlgebras t) cd.1.1 (cd.1.2 : ℤ) : Type u))).apply_symm_apply
          (DFinsupp.equivFunOnFintype.symm y))) i)

/-- For `v` in the summand of index `x`, the component of index `j ≠ x.1` of
`trivialBundleDegreewiseSource t r n v` vanishes. -/
theorem trivialBundleDegreewiseSource_of_ne (n : ℤ)
    (x : Σ i : Fin (r + 1), HodgeBidegreeInt (n - 2 * ((i : ℕ) : ℤ)))
    (v : hodgeCohomologyComponent (formsAlgebras t) x.2.1.1 (x.2.1.2 : ℤ)) (j : Fin (r + 1))
    (hj : j ≠ x.1) :
    trivialBundleDegreewiseSource t r n (DirectSum.of _ x v) j = 0 :=
  Subtype.ext ((congrArg (DirectSum.of (hodgePiece (formsAlgebras t)) (n - 2 * ((j : ℕ) : ℤ)))
    ((DFunLike.congr_fun (DirectSum.sigmaCurry_of (δ := fun (i : Fin (r + 1))
        (cd : HodgeBidegreeInt (n - 2 * ((i : ℕ) : ℤ))) =>
      (hodgeCohomologyComponent (formsAlgebras t) cd.1.1 (cd.1.2 : ℤ) : Type u)) x v) j).trans
      (DirectSum.of_eq_of_ne _ _ _ hj))).trans (map_zero _))

/-- For `v` in the summand of index `x`, the component of index `x.1` of
`trivialBundleDegreewiseSource t r n v` is `v` in the bidegree `x.2`. -/
theorem coe_trivialBundleDegreewiseSource_of_self (n : ℤ)
    (x : Σ i : Fin (r + 1), HodgeBidegreeInt (n - 2 * ((i : ℕ) : ℤ)))
    (v : hodgeCohomologyComponent (formsAlgebras t) x.2.1.1 (x.2.1.2 : ℤ)) :
    (trivialBundleDegreewiseSource t r n (DirectSum.of _ x v) x.1 :
        hodgeAlgebra (formsAlgebras t)) =
      DirectSum.of (hodgePiece (formsAlgebras t)) (n - 2 * ((x.1 : ℕ) : ℤ))
        (DirectSum.of (fun e : HodgeBidegreeInt (n - 2 * ((x.1 : ℕ) : ℤ)) =>
          (hodgeCohomologyComponent (formsAlgebras t) e.1.1 (e.1.2 : ℤ) : Type u)) x.2 v) :=
  congrArg (DirectSum.of (hodgePiece (formsAlgebras t)) (n - 2 * ((x.1 : ℕ) : ℤ)))
    ((DFunLike.congr_fun (DirectSum.sigmaCurry_of (δ := fun (i : Fin (r + 1))
        (cd : HodgeBidegreeInt (n - 2 * ((i : ℕ) : ℤ))) =>
      (hodgeCohomologyComponent (formsAlgebras t) cd.1.1 (cd.1.2 : ℤ) : Type u)) x v) x.1).trans
      (DirectSum.of_eq_same _ _))

/-- **`ξ^i ∪ pr₂^* a = pr₁^* ξ₀^i ∪ pr₂^* a`** for `a ∈ H^d(V, Ω^c)`, `c + d = n - 2i`: the cup
product of pure bidegrees, in the bidegree `(i + c, i + d)`. -/
theorem trivialBundleHodgeClass_pow_mul (n : ℤ)
    (x : Σ i : Fin (r + 1), HodgeBidegreeInt (n - 2 * ((i : ℕ) : ℤ)))
    (v : hodgeCohomologyComponent (formsAlgebras t) x.2.1.1 (x.2.1.2 : ℤ)) :
    trivialBundleHodgeClass t r ^ (x.1 : ℕ) *
        hodgeAlgebraPullback (pullback.snd (projToSpecCoeff k r) t)
          (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r) t (𝟙 _)
          (hodgeSchemeSquare_snd pullback.condition)
          (DirectSum.of (hodgePiece (formsAlgebras t)) (n - 2 * ((x.1 : ℕ) : ℤ))
            (DirectSum.of (fun e : HodgeBidegreeInt (n - 2 * ((x.1 : ℕ) : ℤ)) =>
              (hodgeCohomologyComponent (formsAlgebras t) e.1.1 (e.1.2 : ℤ) : Type u)) x.2 v)) =
      DirectSum.of (hodgePiece
          (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))) n
        (DirectSum.of (fun j : HodgeBidegreeInt n => (hodgeCohomologyComponent
            (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
            j.1.1 (j.1.2 : ℤ) : Type u))
          ⟨((x.1 : ℕ) + x.2.1.1, (x.1 : ℕ) + x.2.1.2), by
            have hx := x.2.2
            dsimp only at hx ⊢
            push_cast at hx ⊢
            omega⟩
          (reindexHodgeDeg
            (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
            (Nat.cast_add (x.1 : ℕ) x.2.1.2).symm
            (hodgeCohomologyCup
              (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
              (x.1 : ℕ) x.2.1.1 ((x.1 : ℕ) : ℤ) (x.2.1.2 : ℤ)
              (hodgePullback (pullback.fst (projToSpecCoeff k r) t)
                (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r)
                (projToSpecCoeff k r) (𝟙 _) (Category.comp_id _).symm (x.1 : ℕ)
                ((x.1 : ℕ) : ℤ) (projectiveSpaceHodgeBasis k r x.1 0))
              (hodgePullback (pullback.snd (projToSpecCoeff k r) t)
                (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r) t (𝟙 _)
                (hodgeSchemeSquare_snd pullback.condition) x.2.1.1 (x.2.1.2 : ℤ) v)))) := by
  refine (congrArg₂ (fun a b => a * b) (trivialBundleHodgeClass_pow t r x.1)
    (hodgeAlgebraPullback_of_of _ _ _ _ _ _ _ _)).trans ?_
  exact of_of_mul_of_of _ (by ring) _ _ _ _

/-- The degreewise projective bundle map on the class `a ∈ H^d(V, Ω^c)` in the slot `i` is the
map through the Künneth decomposition. -/
theorem coe_degreewiseMap_trivialBundleDegreewiseSource_of (n : ℤ)
    (x : Σ i : Fin (r + 1), HodgeBidegreeInt (n - 2 * ((i : ℕ) : ℤ)))
    (v : hodgeCohomologyComponent (formsAlgebras t) x.2.1.1 (x.2.1.2 : ℤ)) :
    letI := hodgeAlgebraAlgebra (formsAlgebras t) (hodgeScalarsOverField t)
    letI := hodgeAlgebraAlgebra
      (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
      (hodgeScalarsOverField (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
    letI := hodgeGradedAlgebra (formsAlgebras t) (hodgeScalarsOverField t)
    letI := hodgeGradedAlgebra
      (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
      (hodgeScalarsOverField (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
    (Stacks.WeilDeRham.degreewiseMap
      (hodgeGrade (formsAlgebras t) (hodgeScalarsOverField t))
      (hodgeGrade (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
        (hodgeScalarsOverField (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r)))
      (hodgeAlgebraPullbackOverBase_mem_hodgeGrade (pullback.snd (projToSpecCoeff k r) t)
        (specScalars k) t (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r)
        (hodgeSchemeSquare_snd pullback.condition))
      (trivialBundleHodgeClass_mem t r) (r + 1) n
      (trivialBundleDegreewiseSource t r n (DirectSum.of _ x v)) :
        hodgeAlgebra (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))) =
      DirectSum.of (hodgePiece
          (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))) n
        (trivialBundleKunnethMap t r (projectiveSpaceHodgeBasis k r) n (DirectSum.of _ x v)) := by
  let := hodgeAlgebraAlgebra (formsAlgebras t) (hodgeScalarsOverField t)
  let := hodgeAlgebraAlgebra
    (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
    (hodgeScalarsOverField (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
  let := hodgeGradedAlgebra (formsAlgebras t) (hodgeScalarsOverField t)
  let := hodgeGradedAlgebra
    (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
    (hodgeScalarsOverField (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
  refine (coe_degreewiseMap_of_forall_ne _ _ _ _ _ x.1
    (trivialBundleDegreewiseSource_of_ne t r n x v)).trans ?_
  refine (congrArg (fun y => trivialBundleHodgeClass t r ^ (x.1 : ℕ) *
    hodgeAlgebraPullback (pullback.snd (projToSpecCoeff k r) t)
      (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r) t (𝟙 _)
      (hodgeSchemeSquare_snd pullback.condition) y)
    (coe_trivialBundleDegreewiseSource_of_self t r n x v)).trans ?_
  refine (trivialBundleHodgeClass_pow_mul t r n x v).trans ?_
  refine Eq.trans ?_ (congrArg (DirectSum.of (hodgePiece
      (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))) n)
    (trivialBundleKunnethMap_of t r (projectiveSpaceHodgeBasis k r) n x v).symm)
  exact congrArg _ (DirectSum.lof_eq_of k (HodgeBidegreeInt n) (fun j : HodgeBidegreeInt n =>
    (hodgeCohomologyComponent
      (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
      j.1.1 (j.1.2 : ℤ) : Type u)) _ _).symm

/-- **The degreewise projective bundle map is the map through the Künneth decomposition**, read in
`H^n_{Hodge}(ℙʳ_k ×_k V/k)`. -/
theorem coe_degreewiseMap_trivialBundleDegreewiseSource (n : ℤ)
    (z : DirectSum (Σ i : Fin (r + 1), HodgeBidegreeInt (n - 2 * ((i : ℕ) : ℤ))) fun x =>
      hodgeCohomologyComponent (formsAlgebras t) x.2.1.1 (x.2.1.2 : ℤ)) :
    letI := hodgeAlgebraAlgebra (formsAlgebras t) (hodgeScalarsOverField t)
    letI := hodgeAlgebraAlgebra
      (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
      (hodgeScalarsOverField (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
    letI := hodgeGradedAlgebra (formsAlgebras t) (hodgeScalarsOverField t)
    letI := hodgeGradedAlgebra
      (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
      (hodgeScalarsOverField (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
    (Stacks.WeilDeRham.degreewiseMap
      (hodgeGrade (formsAlgebras t) (hodgeScalarsOverField t))
      (hodgeGrade (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
        (hodgeScalarsOverField (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r)))
      (hodgeAlgebraPullbackOverBase_mem_hodgeGrade (pullback.snd (projToSpecCoeff k r) t)
        (specScalars k) t (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r)
        (hodgeSchemeSquare_snd pullback.condition))
      (trivialBundleHodgeClass_mem t r) (r + 1) n (trivialBundleDegreewiseSource t r n z) :
        hodgeAlgebra (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))) =
      DirectSum.of (hodgePiece
          (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))) n
        (trivialBundleKunnethMap t r (projectiveSpaceHodgeBasis k r) n z) := by
  let := hodgeAlgebraAlgebra (formsAlgebras t) (hodgeScalarsOverField t)
  let := hodgeAlgebraAlgebra
    (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
    (hodgeScalarsOverField (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
  let := hodgeGradedAlgebra (formsAlgebras t) (hodgeScalarsOverField t)
  let := hodgeGradedAlgebra
    (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
    (hodgeScalarsOverField (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
  induction z using DirectSum.induction_on with
  | zero =>
    exact coe_degreewiseMap_eq_zero _ _ _ _ (trivialBundleDegreewiseSource_zero t r n)
      ((congrArg _ (map_zero _)).trans (map_zero _))
  | add z z' hz hz' =>
    exact coe_degreewiseMap_eq_add _ _ _ _ (trivialBundleDegreewiseSource_add t r n z z')
      ((congrArg _ (map_add _ _ _)).trans (map_add _ _ _)) hz hz'
  | of x v => exact coe_degreewiseMap_trivialBundleDegreewiseSource_of t r n x v

/-- **The projective bundle formula for the trivial bundle `ℙʳ_k ×_k V ⟶ V` in Hodge
cohomology.** Let `k` be a field, `t : V ⟶ Spec k` a quasi-compact `k`-scheme with affine
diagonal (for instance an affine `k`-scheme), `W = ℙʳ_k ×_k V` a `k`-scheme through
`pr₁ ≫ π₀`, and `ξ = pr₁^* c₁^{Hodge}(𝒪(1)) ∈ H^2_{Hodge}(W/k)`. For every `n ∈ ℤ` the map
`∏_{i ≤ r} H^{n - 2i}_{Hodge}(V/k) ⟶ H^n_{Hodge}(W/k)`, `(a_i) ↦ ∑ ξ^i ∪ pr₂^* a_i`, is
bijective. -/
theorem bijective_degreewiseMap_trivialProjectiveBundle [CompactSpace V]
    [IsAffineHom (pullback.diagonal (terminal.from V))] (n : ℤ) :
    letI := hodgeAlgebraAlgebra (formsAlgebras t) (hodgeScalarsOverField t)
    letI := hodgeAlgebraAlgebra
      (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
      (hodgeScalarsOverField (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
    letI := hodgeGradedAlgebra (formsAlgebras t) (hodgeScalarsOverField t)
    letI := hodgeGradedAlgebra
      (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
      (hodgeScalarsOverField (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
    Function.Bijective (Stacks.WeilDeRham.degreewiseMap
      (hodgeGrade (formsAlgebras t) (hodgeScalarsOverField t))
      (hodgeGrade (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
        (hodgeScalarsOverField (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r)))
      (hodgeAlgebraPullbackOverBase_mem_hodgeGrade (pullback.snd (projToSpecCoeff k r) t)
        (specScalars k) t (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r)
        (hodgeSchemeSquare_snd pullback.condition))
      (trivialBundleHodgeClass_mem t r) (r + 1) n) := by
  let := hodgeAlgebraAlgebra (formsAlgebras t) (hodgeScalarsOverField t)
  let := hodgeAlgebraAlgebra
    (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
    (hodgeScalarsOverField (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
  let := hodgeGradedAlgebra (formsAlgebras t) (hodgeScalarsOverField t)
  let := hodgeGradedAlgebra
    (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
    (hodgeScalarsOverField (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
  refine (Function.Bijective.of_comp_iff _ (bijective_trivialBundleDegreewiseSource t r n)).1 ?_
  convert (bijective_toHodgeGrade
      (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
      (hodgeScalarsOverField (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
      (rfl : n = n)).comp
    (bijective_trivialBundleKunnethMap t r (projectiveSpaceHodgeBasis k r) n) using 1
  exact funext fun z => Subtype.ext (coe_degreewiseMap_trivialBundleDegreewiseSource t r n z)

end Bundle

/-! ### Axiom (A3) for Hodge cohomology -/

/-- **Axiom (A3), the projective bundle formula, for Hodge cohomology** ([Stacks, Remark 0FWE]):
for a field `k`, the Hodge cohomology `H^*_{Hodge}(X/k) = ⨁_{p + q = *} H^q(X, Ω^p_{X/k})` of
smooth projective `k`-schemes with `c₁^{Hodge}` satisfies the projective bundle formula: for `ℰ`
locally free of rank `r + 1` on `X` and `p : P = 𝐏(ℰ) ⟶ X`, the map
`⨁_{i = 0, …, r} H^*(X)(-i) ⟶ H^*(P)`, `(a_i) ↦ ∑ c₁^{Hodge}(𝒪_P(1))^i ∪ p^*(a_i)` is bijective.

The proof is the Leray--Hirsch argument for the Hodge differential graded algebra
`⨁_p Ω^p[-p]`: the map is an isomorphism in the derived category once it is so over a basis of
affine opens over which `ℰ` is free (`bijective_degreewiseMap_bundle_of_trivial`), and there `P`
is `ℙʳ_k ×_k V`, where the Künneth formula and the Hodge cohomology of `ℙʳ_k` apply
(`bijective_degreewiseMap_trivialProjectiveBundle`). -/
theorem hodge_projectiveBundleAxiom (k : Type u) [Field k] :
    (hodgeFirstChernClassData k).ProjectiveBundleAxiom :=
  hodge_projectiveBundleAxiom_of_bijective_degreewiseMap k fun X s E r _ n =>
    bijective_degreewiseMap_bundle_of_trivial (k := k)
      (fun _ _ t r n => bijective_degreewiseMap_trivialProjectiveBundle t r n) X s E r n

end Stacks.HodgeWeil

end
