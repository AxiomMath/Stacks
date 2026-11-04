module

public import StacksFrontier.RingTheory.Cech.WeightedVariablesGradedVanishing
public import StacksFrontier.RingTheory.Cech.ShrinkFunctor
public import StacksFrontier.AlgebraicGeometry.DeRham.DeRhamCohomology.FormsDirectSum
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.Kaehler.Polynomial
public import StacksFrontier.RingTheory.DeRham.LaurentResidueTransport

/-!
# The graded Čech complex of the differential forms of `R[x₁, …, x_m, y₁, …, y_n]`

Let `A = R[x₁, …, x_m, y₁, …, y_n]`, graded by `deg xᵢ = 0` and `deg yⱼ = 1`, and let
`M = Ω^a_{A/R}` be its module of relative `a`-forms, graded by the weights of
[Stacks, Tag 0FU9]: `dxᵢ` has weight `0` and `dyⱼ` has weight `1`. This file proves that in the
extended Čech complex `C^•(y₁, …, y_n; M)`, **every homogeneous cocycle of positive weight is the
coboundary of a homogeneous cochain of the same weight**, in every degree.

The forms `dx_I ∧ dy_J` form a homogeneous basis of `M` over `A`, of weights `|J| ≤ n`, so the
Čech complex of `M` is the direct sum of the Čech complexes of `A` shifted by `|J|`, and the
statement is `Cech.WeightedVariables.exists_eq_cechD_of_neg_lt` for the weights
`e - |J| ≥ 1 - n > -n`. Geometrically: `H^q(𝐏^{n-1}, Ω^a(k))` of the relevant pieces vanishes for
`q > 0` and `k > 0`.

## Main definitions

* `Cech.WeightedVariables.Forms`: the module `Ω^a_{A/R}`.
* `Cech.WeightedVariables.formsGrading`: its grading by weight.
* `Cech.WeightedVariables.formsBasis`: its basis `dx_I ∧ dy_J`.
* `Cech.WeightedVariables.posPart`: the sums of homogeneous elements of positive weight in a
  localization of the forms.

## Main results

* `Cech.WeightedVariables.coord_mem_intGrading`: the coordinates in that basis of a form of
  weight `e` are homogeneous of weight `e - |J|`.
* `Cech.WeightedVariables.forms_exists_eq_cechD`: **the vanishing**, in one weight.
* `Cech.WeightedVariables.forms_exists_eq_cechD_of_posPart`: the same for a cocycle all of
  whose components are sums of homogeneous elements of positive weight.

## References

* [Stacks Project, Tag 0FU9](https://stacks.math.columbia.edu/tag/0FU9)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open MvPolynomial KaehlerDifferential

attribute [local instance] instVAddNatIntGradedLocalizedModule

universe u

namespace Cech.WeightedVariables

variable (R : Type u) [CommRing R] (m n a : ℕ)

/-- The module `Ω^a_{A/R}` of relative `a`-forms of `A = R[x, y]`. -/
abbrev Forms : Type u := ⋀[Ring R m n]^a (Ω[Ring R m n⁄R])

/-- The additive group structure on `Ω^a_{A/R}`. -/
instance : AddCommGroup (Forms R m n a) := inferInstance

/-- The `A`-module structure on `Ω^a_{A/R}`. -/
instance : Module (Ring R m n) (Forms R m n a) := inferInstance

/-- The `R`-module structure on `Ω^a_{A/R}`. -/
instance : Module R (Forms R m n a) := inferInstance

/-- The grading of `Ω^a_{A/R}` by weight, `dyⱼ` having weight one ([Stacks, Tag 0FU9]). -/
abbrev formsGrading (e : ℤ) : Submodule R (Forms R m n a) :=
  gradedDifferentialFormComponent (intGrading R m n) a e

/-- `Ω^a_{A/R}` is the internal direct sum of its weight components. -/
theorem isInternal_formsGrading : DirectSum.IsInternal (formsGrading R m n a) :=
  isInternal_gradedDifferentialFormComponent (intGrading R m n)
    (DirectSum.Decomposition.isInternal _) a

/-- The decomposition of `Ω^a_{A/R}` into its weight components. -/
instance : DirectSum.Decomposition (formsGrading R m n a) :=
  (isInternal_formsGrading R m n a).chooseDecomposition

variable {R m n a}

/-- Multiplying a form of weight `j` by a function of weight `i` gives a form of weight
`i + j`. -/
theorem smul_mem_formsGrading {i j : ℤ} {c : Ring R m n} (hc : c ∈ intGrading R m n i)
    {x : Forms R m n a} (hx : x ∈ formsGrading R m n a j) :
    c • x ∈ formsGrading R m n a (i + j) := by
  have hle : formsGrading R m n a j ≤
      (formsGrading R m n a (i + j)).comap
        ((LinearMap.lsmul (Ring R m n) (Forms R m n a) c).restrictScalars R) := by
    rw [formsGrading, gradedDifferentialFormComponent_le_iff]
    intro degree b hsum
    rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, smul_smul]
    have h := smul_ιMulti_D_mem_gradedDifferentialFormComponent (intGrading R m n)
      (Fin.cons (i + degree 0) fun k => degree k.succ)
      (Fin.cons (c * (b 0 : Ring R m n)) fun k => (b k.succ : Ring R m n))
      (fun k => by
        refine Fin.cases ?_ (fun k => ?_) k
        · simpa using SetLike.mul_mem_graded hc (b 0).2
        · simp)
      (g := i + j) (by rw [Fin.sum_univ_succ, hsum, Fin.sum_univ_succ]; simp; ring)
    simpa using h
  exact hle hx

/-- `Ω^a_{A/R}`, graded by weight, is a graded module over `A` with its `ℕ`-grading. -/
instance : SetLike.GradedSMul (natGrading R m n) (formsGrading R m n a) where
  smul_mem {i j c x} hc hx := by
    have h := smul_mem_formsGrading (natGrading_le_intGrading R m n i hc) hx
    exact h

/-! ### The homogeneous basis -/

variable (m n) in
/-- A linear order on the variables, used to enumerate the wedge products of their
differentials. -/
abbrev varOrder : LinearOrder (Fin m ⊕ Fin n) :=
  LinearOrder.lift' finSumFinEquiv finSumFinEquiv.injective

variable (R m n a) in
/-- **The basis `dx_I ∧ dy_J` of `Ω^a_{A/R}`.** -/
def formsBasis : Module.Basis (Set.powersetCard (Fin m ⊕ Fin n) a) (Ring R m n) (Forms R m n a) :=
  letI := varOrder m n
  (mvPolynomialBasis R (Fin m ⊕ Fin n)).exteriorPower a

variable (m n) in
/-- The weight of the basis element indexed by a set of variables: the number of `yⱼ` in it. -/
def basisWeight (s : Set.powersetCard (Fin m ⊕ Fin n) a) : ℕ :=
  ∑ v ∈ (s : Finset (Fin m ⊕ Fin n)), Sum.elim (0 : Fin m → ℕ) 1 v

/-- The weight of a basis element is at most `n`. -/
theorem basisWeight_le (s : Set.powersetCard (Fin m ⊕ Fin n) a) : basisWeight m n s ≤ n := by
  calc basisWeight m n s ≤ ∑ v : Fin m ⊕ Fin n, Sum.elim (0 : Fin m → ℕ) 1 v :=
        Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    _ = n := by simp [Fintype.sum_sum_type]

/-- The basis element indexed by `s` is the wedge product of the differentials of the variables
in `s`, taken in increasing order. -/
theorem formsBasis_apply (s : Set.powersetCard (Fin m ⊕ Fin n) a) :
    formsBasis R m n a s = letI := varOrder m n
      exteriorPower.ιMulti (Ring R m n) a fun k =>
        D R (Ring R m n) (X (Finset.orderEmbOfFin (s : Finset (Fin m ⊕ Fin n)) s.2 k)) := by
  let := varOrder m n
  rw [formsBasis, exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  congr 1
  funext k
  exact mvPolynomialBasis_apply R _ _

/-- The basis element `dx_I ∧ dy_J` has weight `|J|`. -/
theorem formsBasis_mem (s : Set.powersetCard (Fin m ⊕ Fin n) a) :
    formsBasis R m n a s ∈ formsGrading R m n a (basisWeight m n s : ℤ) := by
  let := varOrder m n
  rw [formsBasis_apply, ← one_smul (Ring R m n) (exteriorPower.ιMulti _ _ _)]
  let v := Finset.orderEmbOfFin (s : Finset (Fin m ⊕ Fin n)) s.2
  have h := smul_ιMulti_D_mem_gradedDifferentialFormComponent (intGrading R m n)
    (Fin.cons 0 fun k => (Sum.elim (0 : Fin m → ℤ) 1 (v k) : ℤ))
    (Fin.cons 1 fun k => (X (v k) : Ring R m n))
    (fun k => by
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa using SetLike.one_mem_graded (intGrading R m n)
      · simpa using isWeightedHomogeneous_X R (Sum.elim 0 1 : Fin m ⊕ Fin n → ℤ) (v k))
    (g := (basisWeight m n s : ℤ)) (by
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, zero_add, basisWeight]
      push_cast
      have hs : Finset.univ.map v.toEmbedding = (s : Finset (Fin m ⊕ Fin n)) :=
        Finset.map_orderEmbOfFin_univ _ _
      have hmap := Finset.sum_map Finset.univ v.toEmbedding
        (fun x => ((Sum.elim (0 : Fin m → ℕ) 1 x : ℕ) : ℤ))
      rw [hs] at hmap
      rw [hmap]
      refine Finset.sum_congr rfl fun k _ => ?_
      show (((Sum.elim (0 : Fin m → ℕ) 1 (v k) : ℕ)) : ℤ) = Sum.elim (0 : Fin m → ℤ) 1 (v k)
      rcases v k with x | x <;> simp)
  simpa [v] using h

/-- The weight-`j` component of a finite sum is the sum of the weight-`j` components. -/
private theorem coe_decompose_sum_apply {ι κ M σ : Type*} [AddCommMonoid M] [SetLike σ M]
    [AddSubmonoidClass σ M] (ℳ : ι → σ) [DecidableEq ι] [DirectSum.Decomposition ℳ]
    (s : Finset κ) (f : κ → M) (j : ι) :
    (DirectSum.decompose ℳ (∑ i ∈ s, f i) j : M) =
      ∑ i ∈ s, (DirectSum.decompose ℳ (f i) j : M) := by
  rw [DirectSum.decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]

/-- The weight-`j` component of a homogeneous element of weight `i` is itself if `i = j` and
`0` otherwise. -/
private theorem coe_decompose_of_mem {ι M σ : Type*} [AddCommMonoid M] [SetLike σ M]
    [AddSubmonoidClass σ M] (ℳ : ι → σ) [DecidableEq ι] [DirectSum.Decomposition ℳ] {x : M}
    {i : ι} (hx : x ∈ ℳ i) (j : ι) : (DirectSum.decompose ℳ x j : M) = if i = j then x else 0 := by
  split_ifs with h
  · subst h; exact DirectSum.decompose_of_mem_same _ hx
  · exact DirectSum.decompose_of_mem_ne _ hx h

/-- The weight-`w` component of `c • (dx_I ∧ dy_J)` is `c_{w - |J|} • (dx_I ∧ dy_J)`. -/
theorem decompose_smul_formsBasis (c : Ring R m n) (s : Set.powersetCard (Fin m ⊕ Fin n) a)
    (w : ℤ) :
    (DirectSum.decompose (formsGrading R m n a) (c • formsBasis R m n a s) w :
        Forms R m n a) =
      (DirectSum.decompose (intGrading R m n) c (w - basisWeight m n s) : Ring R m n) •
        formsBasis R m n a s := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose (intGrading R m n) c]
  rw [Finset.sum_smul, coe_decompose_sum_apply]
  have hterm : ∀ k : ℤ, (DirectSum.decompose (formsGrading R m n a)
      ((DirectSum.decompose (intGrading R m n) c k : Ring R m n) • formsBasis R m n a s) w :
        Forms R m n a) =
      if k = w - basisWeight m n s then
        (DirectSum.decompose (intGrading R m n) c k : Ring R m n) • formsBasis R m n a s
      else 0 := by
    intro k
    have hmem := smul_mem_formsGrading (DirectSum.decompose (intGrading R m n) c k).2
      (formsBasis_mem (R := R) s)
    rw [coe_decompose_of_mem _ hmem]
    simp only [eq_sub_iff_add_eq]
  simp_rw [hterm]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [DFinsupp.notMem_support_iff.1 h, ZeroMemClass.coe_zero, zero_smul]

/-- **The coordinates of a form of weight `w` in the basis `dx_I ∧ dy_J` are homogeneous of weight
`w - |J|`.** -/
theorem coord_mem_intGrading {w : ℤ} {x : Forms R m n a} (hx : x ∈ formsGrading R m n a w)
    (s : Set.powersetCard (Fin m ⊕ Fin n) a) :
    (formsBasis R m n a).repr x s ∈ intGrading R m n (w - basisWeight m n s) := by
  classical
  have hx' : x = ∑ t, (DirectSum.decompose (intGrading R m n) ((formsBasis R m n a).repr x t)
      (w - basisWeight m n t) : Ring R m n) • formsBasis R m n a t := by
    have h1 : (DirectSum.decompose (formsGrading R m n a) x w : Forms R m n a) = x :=
      DirectSum.decompose_of_mem_same _ hx
    conv_lhs => rw [← h1, ← (formsBasis R m n a).sum_repr x]
    rw [coe_decompose_sum_apply]
    exact Finset.sum_congr rfl fun t _ => decompose_smul_formsBasis _ t w
  have h := congrArg (fun y => (formsBasis R m n a).repr y s) hx'
  simp only [Module.Basis.repr_sum_self] at h
  rw [h]
  exact (DirectSum.decompose (intGrading R m n) ((formsBasis R m n a).repr x s)
    (w - basisWeight m n s)).2

end Cech.WeightedVariables

/-! ### Graded maps on the Čech complex -/

namespace Cech

variable {S : Type u} [CommRing S] {r : ℕ} (f : Fin r → S) {M N : Type u} [AddCommGroup M]
  [Module S M] [AddCommGroup N] [Module S N]

/-- The component of the induced map on a Čech term is the induced map on the component. -/
theorem cechTermMap_apply (g : M →ₗ[S] N) (p : ℕ) (z : cechTerm f M p)
    (s : {s : Finset (Fin r) // s.card = p}) :
    cechTermMap f g p z s = cechModMap f g s.1 (z s) := by
  classical
  induction z using DirectSum.induction_on with
  | zero => rw [map_zero, DFinsupp.zero_apply, DFinsupp.zero_apply, map_zero]
  | of t x =>
      rw [← DirectSum.lof_eq_of S, cechTermMap_lof]
      by_cases h : t = s
      · subst h
        rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_eq_same, DirectSum.of_eq_same]
      · rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_apply, DirectSum.of_apply,
          dite_eq_right h, dite_eq_right h, map_zero]
  | add z z' hz hz' => rw [map_add, DFinsupp.add_apply, DFinsupp.add_apply, hz, hz', map_add]

variable {σ τ υ : Type*} [SetLike σ S] [AddSubgroupClass σ S] {𝒜 : ℕ → σ} [GradedRing 𝒜]
  [SetLike τ M] [AddSubgroupClass τ M] {ℳ : ℤ → τ} [SetLike.GradedSMul 𝒜 ℳ]
  [SetLike υ N] [AddSubgroupClass υ N] {𝒩 : ℤ → υ} [SetLike.GradedSMul 𝒜 𝒩]

omit [AddSubgroupClass υ N] [SetLike.GradedSMul 𝒜 𝒩] in
/-- A linear map raising weights by `δ` raises the weights of localizations by `δ`. -/
theorem cechModMap_mem_gradedPiece (g : M →ₗ[S] N) (δ : ℤ)
    (hg : ∀ j x, x ∈ ℳ j → g x ∈ 𝒩 (j + δ)) (t : Finset (Fin r)) {d : ℕ}
    (hfd : (∏ i ∈ t, f i) ∈ 𝒜 d) {e : ℤ}
    {y : cechMod f M t} (hy : y ∈ Stacks.GradedLocalization.gradedPiece 𝒜 ℳ (∏ i ∈ t, f i) e) :
    cechModMap f g t y ∈ Stacks.GradedLocalization.gradedPiece 𝒜 𝒩 (∏ i ∈ t, f i) (e + δ) := by
  obtain ⟨k, x, hx, rfl⟩ := (Stacks.GradedLocalization.mem_gradedPiece_iff 𝒜 ℳ hfd e y).1 hy
  rw [cechModMap_mk]
  refine Stacks.GradedLocalization.mk_mem_gradedPiece 𝒜 𝒩 hfd ?_
  have := hg _ x hx
  rwa [show e + k • (d : ℤ) + δ = e + δ + k • (d : ℤ) by ring] at this

omit [AddSubgroupClass υ N] [SetLike.GradedSMul 𝒜 𝒩] in
/-- A linear map raising weights by `δ` raises the weights of Čech cochains by `δ`. -/
theorem cechTermMap_mem_gradedCechTerm (g : M →ₗ[S] N) (δ : ℤ)
    (hg : ∀ j x, x ∈ ℳ j → g x ∈ 𝒩 (j + δ)) {c : Fin r → ℕ} (hc : ∀ i, f i ∈ 𝒜 (c i)) {e : ℤ}
    {p : ℕ} {z : cechTerm f M p} (hz : z ∈ gradedCechTerm 𝒜 ℳ f e p) :
    cechTermMap f g p z ∈ gradedCechTerm 𝒜 𝒩 f (e + δ) p := fun s => by
  rw [cechTermMap_apply]
  exact cechModMap_mem_gradedPiece f g δ hg s.1 (SetLike.prod_mem_graded 𝒜 c f fun i _ => hc i)
    (hz s)

/-- The induced map on Čech terms is additive in the linear map. -/
theorem cechTermMap_sum {ι : Type*} (t : Finset ι) (g : ι → M →ₗ[S] N) (p : ℕ) :
    cechTermMap f (∑ i ∈ t, g i) p = ∑ i ∈ t, cechTermMap f (g i) p := by
  classical
  refine DirectSum.linearMap_ext S fun s => LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, cechTermMap_lof, LinearMap.sum_apply, ← map_sum]
  congr 1
  simp only [cechModMap, map_sum, LinearMap.sum_apply]

end Cech

namespace Cech.WeightedVariables

variable {R : Type u} [CommRing R] {m n a : ℕ}

/-- **In the Čech complex of the forms, a cocycle of positive weight is a coboundary of the same
weight.** -/
theorem forms_exists_eq_cechD (w : ℤ) (hw : 1 ≤ w) (p : ℕ)
    {z : cechTerm (yVar R m n) (Forms R m n a) (p + 1)}
    (hz : z ∈ gradedCechTerm (natGrading R m n) (formsGrading R m n a) (yVar R m n) w (p + 1))
    (hdz : cechD (yVar R m n) (Forms R m n a) (p + 1) z = 0) :
    ∃ β ∈ gradedCechTerm (natGrading R m n) (formsGrading R m n a) (yVar R m n) w p,
      cechD (yVar R m n) (Forms R m n a) p β = z := by
  classical
  set b := formsBasis R m n a
  have hcoord : ∀ s, ∃ β ∈ gradedCechTerm (natGrading R m n) (intGrading R m n) (yVar R m n)
      (w - basisWeight m n s) p, cechD (yVar R m n) (Ring R m n) p β =
        cechTermMap (yVar R m n) (b.coord s) (p + 1) z := by
    intro s
    refine exists_eq_cechD_of_neg_lt R m n _ (by have := basisWeight_le (a := a) s; omega) p
      ?_ ?_
    · have h := cechTermMap_mem_gradedCechTerm (yVar R m n) (b.coord s) (-(basisWeight m n s : ℤ))
        (fun j x hx => by
          rw [Module.Basis.coord_apply, ← sub_eq_add_neg]
          exact coord_mem_intGrading hx s) (yVar_mem R m n) hz
      rwa [← sub_eq_add_neg] at h
    · rw [← LinearMap.comp_apply, cechTermMap_comp_cechD, LinearMap.comp_apply, hdz, map_zero]
  choose β hβ hdβ using hcoord
  refine ⟨∑ s, cechTermMap (yVar R m n) (LinearMap.toSpanSingleton (Ring R m n) _ (b s)) p (β s),
    sum_mem fun s _ => ?_, ?_⟩
  · have h := cechTermMap_mem_gradedCechTerm (yVar R m n)
      (LinearMap.toSpanSingleton (Ring R m n) _ (b s)) (basisWeight m n s)
      (fun j x hx => by
        rw [LinearMap.toSpanSingleton_apply]
        exact smul_mem_formsGrading hx (formsBasis_mem s)) (yVar_mem R m n) (hβ s)
    rwa [sub_add_cancel] at h
  · simp only [map_sum]
    have hcomm := fun s => LinearMap.congr_fun
      (cechTermMap_comp_cechD (yVar R m n) (LinearMap.toSpanSingleton (Ring R m n) _ (b s)) p)
      (β s)
    simp only [LinearMap.comp_apply] at hcomm
    simp only [hcomm, hdβ]
    have hid : ∑ s, (LinearMap.toSpanSingleton (Ring R m n) (Forms R m n a) (b s)).comp
        (b.coord s) = LinearMap.id := by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.sum_apply, LinearMap.comp_apply,
        LinearMap.toSpanSingleton_apply, Module.Basis.coord_apply, LinearMap.id_apply]
      exact b.sum_repr x
    have hsum : (∑ s, cechTermMap (yVar R m n)
        (LinearMap.toSpanSingleton (Ring R m n) (Forms R m n a) (b s)) (p + 1)
          (cechTermMap (yVar R m n) (b.coord s) (p + 1) z)) =
        cechTermMap (yVar R m n) (∑ s, (LinearMap.toSpanSingleton (Ring R m n)
          (Forms R m n a) (b s)).comp (b.coord s)) (p + 1) z := by
      rw [cechTermMap_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [cechTermMap_comp, LinearMap.comp_apply]
    rw [hsum, hid, cechTermMap_id, LinearMap.id_apply]

/-! ### The positive part -/

variable (R m n a) in
/-- **The positive part of a localization `M_{∏_{j ∈ t} yⱼ}` of the forms**: the sums of
homogeneous elements of positive weight. -/
def posPart (t : Finset (Fin n)) : AddSubgroup (cechMod (yVar R m n) (Forms R m n a) t) :=
  ⨆ e : ℕ, Stacks.GradedLocalization.gradedPiece (natGrading R m n) (formsGrading R m n a)
    (∏ i ∈ t, yVar R m n i) ((e : ℤ) + 1)

/-- The product `∏_{j ∈ t} yⱼ` is homogeneous of degree `|t|`. -/
theorem prod_yVar_mem_natGrading (t : Finset (Fin n)) :
    (∏ i ∈ t, yVar R m n i) ∈ natGrading R m n (∑ _i ∈ t, 1) :=
  SetLike.prod_mem_graded (natGrading R m n) (fun _ => 1) (yVar R m n) fun i _ => yVar_mem R m n i

/-- The transition maps of the Čech complex preserve the positive part. -/
theorem cechι_mem_posPart {s t : Finset (Fin n)} (h : s ⊆ t)
    {z : cechMod (yVar R m n) (Forms R m n a) s} (hz : z ∈ posPart R m n a s) :
    cechι (yVar R m n) (Forms R m n a) h z ∈ posPart R m n a t := by
  induction hz using AddSubgroup.iSup_induction' with
  | hp e z hz =>
      exact AddSubgroup.mem_iSup_of_mem e (mem_gradedPiece_cechι (natGrading R m n)
        (formsGrading R m n a) (yVar R m n) (c := fun _ => 1) (yVar_mem R m n) h _ hz)
  | h1 => rw [map_zero]; exact (posPart R m n a t).zero_mem
  | hadd z z' _ _ hz hz' => rw [map_add]; exact (posPart R m n a t).add_mem hz hz'

/-- An element of the positive part has no component of weight `≤ 0`. -/
theorem decompose_eq_zero_of_mem_posPart {t : Finset (Fin n)}
    {z : cechMod (yVar R m n) (Forms R m n a) t} (hz : z ∈ posPart R m n a t) {e : ℤ}
    (he : e ≤ 0) :
    letI := Stacks.GradedLocalization.gradedDecomposition (natGrading R m n) (formsGrading R m n a)
      (prod_yVar_mem_natGrading (R := R) (m := m) t)
    (DirectSum.decompose (Stacks.GradedLocalization.gradedPiece (natGrading R m n)
      (formsGrading R m n a) (∏ i ∈ t, yVar R m n i)) z e : cechMod (yVar R m n) (Forms R m n a) t)
        = 0 := by
  let := Stacks.GradedLocalization.gradedDecomposition (natGrading R m n) (formsGrading R m n a)
    (prod_yVar_mem_natGrading (R := R) (m := m) t)
  induction hz using AddSubgroup.iSup_induction' with
  | hp k z hz => exact DirectSum.decompose_of_mem_ne _ hz (by omega)
  | h1 => rw [DirectSum.decompose_zero, DFinsupp.zero_apply, ZeroMemClass.coe_zero]
  | hadd z z' _ _ hz hz' =>
      rw [DirectSum.decompose_add, DFinsupp.add_apply, AddSubgroup.coe_add, hz, hz', add_zero]

/-- **In the Čech complex of the forms, a cocycle whose components lie in the positive part is the
coboundary of a cochain whose components lie in the positive part.** -/
theorem forms_exists_eq_cechD_of_posPart (q : ℕ)
    (z : cechTerm (yVar R m n) (Forms R m n a) (q + 2)) (hz : ∀ s, z s ∈ posPart R m n a s.1)
    (hdz : cechD (yVar R m n) (Forms R m n a) (q + 2) z = 0) :
    ∃ w : cechTerm (yVar R m n) (Forms R m n a) (q + 1),
      (∀ s, w s ∈ posPart R m n a s.1) ∧ cechD (yVar R m n) (Forms R m n a) (q + 1) w = z := by
  classical
  obtain ⟨T, y, hy, hyz, hsum⟩ := exists_sum_mem_gradedCechTerm (natGrading R m n)
    (formsGrading R m n a) (yVar R m n) (c := fun _ => 1) (yVar_mem R m n) (q + 2) z
  have hneg : ∀ e, e ≤ 0 → y e = 0 := by
    intro e he
    refine DFinsupp.ext fun s => ?_
    let := Stacks.GradedLocalization.gradedDecomposition (natGrading R m n)
      (formsGrading R m n a) (prod_yVar_mem_natGrading (R := R) (m := m) s.1)
    have h0 := decompose_eq_zero_of_mem_posPart (hz s) he
    rw [← hsum, DFinsupp.finsetSum_apply, coe_decompose_sum_apply] at h0
    have hterm : ∀ e' ∈ T, (DirectSum.decompose (Stacks.GradedLocalization.gradedPiece
        (natGrading R m n) (formsGrading R m n a) (∏ i ∈ s.1, yVar R m n i)) (y e' s) e :
          cechMod (yVar R m n) (Forms R m n a) s.1) = if e' = e then y e' s else 0 := by
      exact fun e' _ => coe_decompose_of_mem _ (hy e' s) e
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq'] at h0
    split_ifs at h0 with hT
    · exact h0
    · rw [hyz e hT, DFinsupp.zero_apply]
  have hcoc : ∀ e ∈ T, cechD (yVar R m n) (Forms R m n a) (q + 2) (y e) = 0 := by
    intro e he
    rw [← hsum, map_sum] at hdz
    exact eq_zero_of_sum_mem_gradedCechTerm_eq_zero (natGrading R m n) (formsGrading R m n a)
      (yVar R m n) (c := fun _ => 1) (yVar_mem R m n) (q + 2 + 1) T _
      (fun d hd => cechD_mem_gradedCechTerm (natGrading R m n) (formsGrading R m n a)
        (yVar R m n) (c := fun _ => 1) (yVar_mem R m n) d (q + 2) (hy d)) hdz he
  have hex : ∀ e ∈ T.filter (1 ≤ ·), ∃ β : cechTerm (yVar R m n) (Forms R m n a) (q + 1),
      (∀ s, β s ∈ posPart R m n a s.1) ∧ cechD (yVar R m n) (Forms R m n a) (q + 1) β = y e := by
    intro e he
    obtain ⟨he, hpos⟩ := Finset.mem_filter.1 he
    obtain ⟨β, hβ, hdβ⟩ := forms_exists_eq_cechD e hpos (q + 1) (hy e) (hcoc e he)
    refine ⟨β, fun s => AddSubgroup.mem_iSup_of_mem (e - 1).toNat ?_, hdβ⟩
    have : ((e - 1).toNat : ℤ) + 1 = e := by omega
    rw [this]
    exact hβ s
  choose! β hβ hdβ using hex
  have hzsum : (∑ e ∈ T.filter (1 ≤ ·), y e) = z := by
    rw [← hsum, Finset.sum_filter_of_ne]
    intro e _ hne
    by_contra hlt
    exact hne (hneg e (by omega))
  refine ⟨∑ e ∈ T.filter (1 ≤ ·), β e, fun s => ?_, ?_⟩
  · rw [DFinsupp.finsetSum_apply]
    exact (posPart R m n a s.1).sum_mem fun e he => hβ e he s
  · rw [map_sum, ← hzsum]
    exact Finset.sum_congr rfl hdβ

end Cech.WeightedVariables

end
