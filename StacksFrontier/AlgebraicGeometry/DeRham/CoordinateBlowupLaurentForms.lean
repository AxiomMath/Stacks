module

public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupLaurent
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic

/-!
# Laurent frame coordinates for differential forms on the coordinate blowup

Let `Λ = R[x₁^{±}, …, x_m^{±}, y₁^{±}, …, y_n^{±}]` be the Laurent polynomial ring
(`AddMonoidAlgebra R (σ →₀ ℤ)` with `σ = Fin m ⊕ Fin n`). The *frame* of the forms on the torus
`D(x₁ ⋯ y_n)` of the coordinate blowup is `dx₁, …, dx_m, d log y₁, …, d log y_n`; the coordinates
of `d f` in it are `∂f/∂x_i` and `y_j ∂f/∂y_j`, the *frame operators*. This file sets up the
resulting coordinates of exterior powers of Kähler differentials and computes which Laurent
monomials and frame vectors can occur, which is the combinatorial input of the Čech computation
of clause (3) of [Stacks, Tag 0FUR].

## Main definitions

* `Stacks.DeRham.CoordinateCech.frameOp`: the frame operators, derivations of `Λ` over `R`.
* `Stacks.DeRham.CoordinateCech.frameCoord`: the coordinates of an element of `⋀^a_Λ Λ^σ` in the
  standard basis, unfolded as a finitely supported function of a pair (subset, Laurent exponent).

## References

* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
-/

@[expose] public noncomputable section

open AddMonoidAlgebra

universe u

namespace Stacks.DeRham.CoordinateCech

variable (R : Type u) [CommRing R] (m n : ℕ)

/-- The Laurent polynomial ring in the variables `x₁, …, x_m, y₁, …, y_n`. -/
abbrev Lau : Type u := AddMonoidAlgebra R ((Fin m ⊕ Fin n) →₀ ℤ)

/-- The free `Λ`-module on the frame. -/
abbrev FrameVec : Type u := (Fin m ⊕ Fin n) → Lau R m n

variable {m n}

/-- The exponent shift of a frame operator: `∂/∂x_i` lowers the exponent of `x_i` by one, the Euler
operator `y_j ∂/∂y_j` keeps exponents. -/
def frameShift : Fin m ⊕ Fin n → (Fin m ⊕ Fin n) →₀ ℤ
  | .inl i => Finsupp.single (.inl i) 1
  | .inr _ => 0

variable {R}

/-- The frame operator on coefficient functions. -/
def frameOpCoeff (s : Fin m ⊕ Fin n) :
    (((Fin m ⊕ Fin n) →₀ ℤ) →₀ R) →ₗ[R] (((Fin m ⊕ Fin n) →₀ ℤ) →₀ R) :=
  Finsupp.lsum R fun w => (w s) • Finsupp.lsingle (w - frameShift s)

/-- **The frame operator** at `s`: `∂/∂x_i` for `s = x_i` and `y_j ∂/∂y_j` for `s = y_j`. On a
monomial `z^w` it multiplies by the exponent `w_s` and shifts by `frameShift s`. -/
def frameOp (s : Fin m ⊕ Fin n) : Lau R m n →ₗ[R] Lau R m n where
  toFun f := ofCoeff (frameOpCoeff s f.coeff)
  map_add' f g := by
    change ofCoeff (frameOpCoeff s (f.coeff + g.coeff)) = _
    rw [map_add]
    rfl
  map_smul' c f := by
    change ofCoeff (frameOpCoeff s (c • f.coeff)) = _
    rw [map_smul]
    rfl

/-- The frame operator at `s` sends the monomial `r z^w` to `(w s) r z^(w - frameShift s)`. -/
theorem frameOp_single (s : Fin m ⊕ Fin n) (w : (Fin m ⊕ Fin n) →₀ ℤ) (r : R) :
    frameOp s (single w r) = single (w - frameShift s) ((w s) • r) := by
  show ofCoeff (frameOpCoeff s (Finsupp.single w r)) = _
  simp [frameOpCoeff, Finsupp.lsum_single]

/-- **The frame operators are derivations**: the Leibniz rule. -/
theorem frameOp_mul (s : Fin m ⊕ Fin n) (f g : Lau R m n) :
    frameOp s (f * g) = frameOp s f * g + f * frameOp s g := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f f' hf hf' =>
    rw [add_mul, map_add, hf, hf', map_add, add_mul, add_mul]
    abel
  | single v r =>
    induction g using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add g g' hg hg' =>
      rw [mul_add, map_add, hg, hg', map_add, mul_add, mul_add]
      abel
    | single w t =>
      rw [single_mul_single, frameOp_single, frameOp_single, frameOp_single, single_mul_single,
        single_mul_single, show v - frameShift s + w = v + w - frameShift s by abel,
        show v + (w - frameShift s) = v + w - frameShift s by abel, ← single_add]
      congr 1
      simp only [Finsupp.coe_add, Pi.add_apply, add_smul, smul_mul_assoc, mul_smul_comm]

/-- A frame operator kills the constants. -/
theorem frameOp_single_zero (s : Fin m ⊕ Fin n) (r : R) : frameOp s (single 0 r) = 0 := by
  rw [frameOp_single]
  simp

/-- The frame coordinates `(∂f/∂x_i, y_j ∂f/∂y_j)` of `d f`. -/
def frameD (f : Lau R m n) : FrameVec R m n := fun s => frameOp s f

/-- The Leibniz rule for the frame coordinates: `frameD (f g) = f • frameD g + g • frameD f`. -/
theorem frameD_mul (f g : Lau R m n) : frameD (f * g) = f • frameD g + g • frameD f := by
  funext s
  simp only [frameD, frameOp_mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The frame coordinates are additive. -/
theorem frameD_add (f g : Lau R m n) : frameD (f + g) = frameD f + frameD g := by
  funext s
  simp [frameD]

/-! ### The frame map on Kähler differentials and their exterior powers -/

section Frame

variable {R0 A : CommRingCat.{u}} (φ : R0 ⟶ A) (lam : A →+* Lau R m n)
  (hlam : ∀ (r : R0) (s : Fin m ⊕ Fin n), frameOp s (lam (φ r)) = 0)

/-- The frame coordinates as a derivation of `A` over `R0`, the target a `Λ`-module made an
`A`-module through `lam`. -/
def frameDerivation :
    letI := Module.compHom (FrameVec R m n) lam
    (ModuleCat.of A (FrameVec R m n)).Derivation φ :=
  letI := Module.compHom (FrameVec R m n) lam
  ModuleCat.Derivation.mk (fun b => frameD (lam b))
    (fun b b' => by rw [map_add, frameD_add])
    (fun b b' => by rw [map_mul, frameD_mul]; rfl)
    (fun r => funext fun s => hlam r s)

/-- **The frame map on Kähler differentials**: `d f ↦ frameD (lam f)`. -/
def kaehlerFrame : CommRingCat.KaehlerDifferential φ →+ FrameVec R m n :=
  letI := Module.compHom (FrameVec R m n) lam
  (frameDerivation φ lam hlam).desc.hom.toAddMonoidHom

/-- The frame map sends `d f` to `frameD (lam f)`. -/
theorem kaehlerFrame_d (f : A) :
    kaehlerFrame φ lam hlam (CommRingCat.KaehlerDifferential.d f) = frameD (lam f) := by
  let := Module.compHom (FrameVec R m n) lam
  exact (frameDerivation φ lam hlam).desc_d f

/-- The frame map on Kähler differentials is `A`-linear, `A` acting on the target through
`lam`. -/
theorem kaehlerFrame_smul (c : A) (ω : CommRingCat.KaehlerDifferential φ) :
    kaehlerFrame φ lam hlam (c • ω) = lam c • kaehlerFrame φ lam hlam ω := by
  let := Module.compHom (FrameVec R m n) lam
  exact (frameDerivation φ lam hlam).desc.hom.map_smul c ω

/-- The frame map on `a`-tuples of differentials, as an `A`-alternating map, the target made an
`A`-module through `lam`. -/
def formsFrameAlt (a : ℕ) :
    letI := Module.compHom (⋀[Lau R m n]^a (FrameVec R m n)) lam
    CommRingCat.KaehlerDifferential φ [⋀^Fin a]→ₗ[A] ⋀[Lau R m n]^a (FrameVec R m n) :=
  letI := Module.compHom (⋀[Lau R m n]^a (FrameVec R m n)) lam
  { toFun := fun v => exteriorPower.ιMulti (Lau R m n) a (kaehlerFrame φ lam hlam ∘ v)
    map_update_add' := fun v i x y => by
      classical
      simp only [Function.comp_update, map_add]
      convert (exteriorPower.ιMulti (Lau R m n) a).map_update_add _ i _ _
    map_update_smul' := fun v i c x => by
      classical
      simp only [Function.comp_update, kaehlerFrame_smul]
      exact (exteriorPower.ιMulti (Lau R m n) a).map_update_smul _ i (lam c) _
    map_eq_zero_of_eq' := fun v i j h hij =>
      (exteriorPower.ιMulti (Lau R m n) a).map_eq_zero_of_eq _ (by simp [h]) hij }

/-- **The frame map on exterior powers**: `⋀^a_A Ω[A/R0] ⟶ ⋀^a_Λ Λ^σ`,
`c • d g₁ ∧ ⋯ ∧ d g_a ↦ lam c • frameD (lam g₁) ∧ ⋯ ∧ frameD (lam g_a)`. -/
def formsFrame (a : ℕ) :
    ⋀[A]^a (CommRingCat.KaehlerDifferential φ) →+ ⋀[Lau R m n]^a (FrameVec R m n) :=
  letI := Module.compHom (⋀[Lau R m n]^a (FrameVec R m n)) lam
  (exteriorPower.alternatingMapLinearEquiv (formsFrameAlt φ lam hlam a)).toAddMonoidHom

/-- The frame map on exterior powers sends `ω₁ ∧ ⋯ ∧ ω_a` to the wedge of the frame images of
the `ω_i`. -/
theorem formsFrame_ιMulti (a : ℕ) (v : Fin a → CommRingCat.KaehlerDifferential φ) :
    formsFrame φ lam hlam a (exteriorPower.ιMulti A a v) =
      exteriorPower.ιMulti (Lau R m n) a (kaehlerFrame φ lam hlam ∘ v) := by
  let := Module.compHom (⋀[Lau R m n]^a (FrameVec R m n)) lam
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ v

/-- The frame map on exterior powers is `A`-linear, `A` acting on the target through `lam`. -/
theorem formsFrame_smul (a : ℕ) (c : A) (ω : ⋀[A]^a (CommRingCat.KaehlerDifferential φ)) :
    formsFrame φ lam hlam a (c • ω) = lam c • formsFrame φ lam hlam a ω := by
  let := Module.compHom (⋀[Lau R m n]^a (FrameVec R m n)) lam
  exact (exteriorPower.alternatingMapLinearEquiv (formsFrameAlt φ lam hlam a)).map_smul c ω

/-- **The frame map on a generator** `c • d g₁ ∧ ⋯ ∧ d g_a`. -/
theorem formsFrame_smul_ιMulti_d (a : ℕ) (c : A) (g : Fin a → A) :
    formsFrame φ lam hlam a
        (c • exteriorPower.ιMulti A a fun i => CommRingCat.KaehlerDifferential.d (g i)) =
      lam c • exteriorPower.ιMulti (Lau R m n) a fun i => frameD (lam (g i)) := by
  rw [formsFrame_smul, formsFrame_ιMulti]
  congr 2
  funext i
  exact kaehlerFrame_d φ lam hlam (g i)

end Frame

/-! ### Supports of products -/

/-- The exponents of a product of Laurent polynomials are sums of exponents of the factors. -/
private theorem exists_add_of_mem_support_mul {f g : Lau R m n} {v : (Fin m ⊕ Fin n) →₀ ℤ}
    (hv : v ∈ (f * g).coeff.support) :
    ∃ a ∈ f.coeff.support, ∃ b ∈ g.coeff.support, a + b = v := by
  classical
  exact Finset.mem_add.1 (AddMonoidAlgebra.support_coeff_mul_subset _ _ hv)

/-- The exponents of a finite product of Laurent polynomials are sums of exponents of the
factors. -/
theorem exists_of_mem_support_prod {a : ℕ} (f : Fin a → Lau R m n) {v : (Fin m ⊕ Fin n) →₀ ℤ}
    (hv : v ∈ (∏ i, f i).coeff.support) :
    ∃ w : Fin a → (Fin m ⊕ Fin n) →₀ ℤ, (∀ i, w i ∈ (f i).coeff.support) ∧ v = ∑ i, w i := by
  classical
  induction a generalizing v with
  | zero =>
    refine ⟨Fin.elim0, fun i => i.elim0, ?_⟩
    rw [Fin.prod_univ_zero] at hv
    simpa using AddMonoidAlgebra.support_coeff_one_subset hv
  | succ a ih =>
    rw [Fin.prod_univ_succ] at hv
    obtain ⟨w0, hw0, w', hw', rfl⟩ := exists_add_of_mem_support_mul hv
    obtain ⟨w, hw, rfl⟩ := ih (fun i => f i.succ) hw'
    exact ⟨Fin.cons w0 w, Fin.cons hw0 hw, by rw [Fin.sum_univ_succ]; rfl⟩

/-! ### Coordinates -/

/-- The standard basis of `Λ^σ`, indexed by the lexicographically ordered variables. -/
def frameBasis : Module.Basis (Lex (Fin m ⊕ Fin n)) (Lau R m n) (FrameVec R m n) :=
  (Pi.basisFun (Lau R m n) (Fin m ⊕ Fin n)).reindex toLex

/-- The basis vector of `frameBasis` at `s` is the standard unit vector at `s`. -/
theorem frameBasis_apply (s : Lex (Fin m ⊕ Fin n)) :
    (frameBasis : Module.Basis _ (Lau R m n) (FrameVec R m n)) s = Pi.single (ofLex s) 1 := by
  simp [frameBasis]

/-- The coordinate of `x` along the basis vector of `frameBasis` at `s` is `x s`. -/
theorem frameBasis_coord (s : Lex (Fin m ⊕ Fin n)) (x : FrameVec R m n) :
    (frameBasis : Module.Basis _ (Lau R m n) (FrameVec R m n)).coord s x = x (ofLex s) := by
  simp [frameBasis]

variable (m n) in
/-- The index of a frame coordinate: an `a`-element set of variables (the wedge of their frame
vectors) and a Laurent exponent. -/
abbrev FrameIndex (a : ℕ) : Type :=
  (Set.powersetCard (Lex (Fin m ⊕ Fin n)) a) × ((Fin m ⊕ Fin n) →₀ ℤ)

variable (R) in
/-- **The frame coordinates** of an element of `⋀^a_Λ Λ^σ`: the coefficient of `z^v` in its
coordinate along the wedge of the frame vectors of a set `S`. -/
def frameCoord (a : ℕ) : ⋀[Lau R m n]^a (FrameVec R m n) →+ (FrameIndex m n a →₀ R) where
  toFun x := Finsupp.uncurry
    (((frameBasis.exteriorPower a).repr x).mapRange AddMonoidAlgebra.coeff coeff_zero)
  map_zero' := by ext; simp [Finsupp.uncurry_apply]
  map_add' x y := by ext; simp [Finsupp.uncurry_apply]

/-- The frame coordinate of `x` at `(S, v)` is the coefficient of `z^v` in the coordinate of `x`
along the wedge of the frame vectors of `S`. -/
theorem frameCoord_apply (a : ℕ) (x : ⋀[Lau R m n]^a (FrameVec R m n)) (e : FrameIndex m n a) :
    frameCoord R a x e = ((frameBasis.exteriorPower a).repr x e.1).coeff e.2 := by
  simp [frameCoord, Finsupp.uncurry_apply]

/-- An element of `⋀^a_Λ Λ^σ` is determined by its frame coordinates. -/
theorem frameCoord_injective (a : ℕ) : Function.Injective (frameCoord R (m := m) (n := n) a) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  refine (frameBasis.exteriorPower a).repr.injective ?_
  rw [map_zero]
  ext S v
  simpa [frameCoord_apply] using congrArg (fun F => F (S, v)) hx

/-- The coordinate of a wedge of frame vectors along `S` is the minor at the columns `S`. -/
theorem repr_ιMulti (a : ℕ) (vec : Fin a → FrameVec R m n)
    (S : Set.powersetCard (Lex (Fin m ⊕ Fin n)) a) :
    (frameBasis.exteriorPower a).repr (exteriorPower.ιMulti (Lau R m n) a vec) S =
      (Matrix.of fun i j => vec i (ofLex (Set.powersetCard.ofFinEmbEquiv.symm S j))).det := by
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  simp only [frameBasis_coord]

/-- The integer minor of a wedge of frame basis vectors: the coordinate of
`e_{f 0} ∧ ⋯ ∧ e_{f (a-1)}` along the wedge of the frame vectors of `S`. -/
def frameMinor {a : ℕ} (f : Fin a → Fin m ⊕ Fin n) (S : Set.powersetCard (Lex (Fin m ⊕ Fin n)) a) :
    ℤ :=
  (Matrix.of fun i j => if f i = ofLex (Set.powersetCard.ofFinEmbEquiv.symm S j) then 1 else 0).det

/-- The frame coordinate at `(S, v)` of `Q • e_{f 0} ∧ ⋯ ∧ e_{f (a-1)}` is the minor
`frameMinor f S` times the coefficient of `z^v` in `Q`. -/
theorem frameCoord_smul_ιMulti_single (a : ℕ) (Q : Lau R m n) (f : Fin a → Fin m ⊕ Fin n)
    (e : FrameIndex m n a) :
    frameCoord R a (Q • exteriorPower.ιMulti (Lau R m n) a fun i => Pi.single (f i) 1) e =
      frameMinor f e.1 • Q.coeff e.2 := by
  classical
  rw [frameCoord_apply, map_smul, Finsupp.smul_apply, repr_ιMulti]
  have hdet : (Matrix.of fun i j => (Pi.single (f i) (1 : Lau R m n) :
        FrameVec R m n) (ofLex (Set.powersetCard.ofFinEmbEquiv.symm e.1 j))).det =
      ((frameMinor f e.1 : ℤ) : Lau R m n) := by
    rw [frameMinor]
    refine Eq.trans ?_ (RingHom.map_det (Int.castRingHom (Lau R m n)) _).symm
    congr 1
    ext i j
    simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Pi.single_apply]
    split_ifs <;> simp_all [eq_comm]
  rw [hdet, smul_eq_mul, mul_comm, ← zsmul_eq_mul]
  rfl

/-- A minor vanishes unless every column index is one of the vectors. -/
theorem frameMinor_eq_zero {a : ℕ} (f : Fin a → Fin m ⊕ Fin n)
    (S : Set.powersetCard (Lex (Fin m ⊕ Fin n)) a) {t : Lex (Fin m ⊕ Fin n)}
    (ht : t ∈ (S : Finset (Lex (Fin m ⊕ Fin n)))) (hf : ∀ i, f i ≠ ofLex t) :
    frameMinor f S = 0 := by
  obtain ⟨j, hj⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S t).2 ht
  refine Matrix.det_eq_zero_of_column_eq_zero j fun i => ?_
  simp only [Matrix.of_apply, hj, hf i, ite_false]

/-- The frame coordinates of `d g` in the standard basis. -/
theorem frameD_eq_sum (g : Lau R m n) :
    frameD g = ∑ s, frameOp s g • (Pi.single s 1 : FrameVec R m n) := by
  classical
  funext t
  simp [frameD, Finset.sum_apply, Pi.single_apply]

/-- **Expansion of a generator in frame coordinates.** -/
theorem frameCoord_smul_ιMulti_frameD (a : ℕ) (c : Lau R m n) (g : Fin a → Lau R m n)
    (e : FrameIndex m n a) :
    frameCoord R a (c • exteriorPower.ιMulti (Lau R m n) a fun i => frameD (g i)) e =
      ∑ f : Fin a → Fin m ⊕ Fin n,
        frameMinor f e.1 • (c * ∏ i, frameOp (f i) (g i)).coeff e.2 := by
  classical
  have h1 : (exteriorPower.ιMulti (Lau R m n) a fun i => frameD (g i)) =
      ∑ f : Fin a → Fin m ⊕ Fin n, (∏ i, frameOp (f i) (g i)) •
        exteriorPower.ιMulti (Lau R m n) a fun i => (Pi.single (f i) 1 : FrameVec R m n) := by
    simp_rw [frameD_eq_sum]
    refine ((exteriorPower.ιMulti (Lau R m n) a).toMultilinearMap.map_sum
      (fun i s => frameOp s (g i) • (Pi.single s 1 : FrameVec R m n))).trans ?_
    refine Finset.sum_congr rfl fun f _ => ?_
    exact (exteriorPower.ιMulti (Lau R m n) a).toMultilinearMap.map_smul_univ _ _
  rw [h1, Finset.smul_sum, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [smul_smul, frameCoord_smul_ιMulti_single]

/-! ### The exponents that occur over an intersection of charts -/

/-- The exponents of the functions over the intersection of the charts in `T`: nonnegative in
the `x`'s, of nonnegative degree in the `y`'s, and nonnegative in every `y_k` with `k ∉ T`. -/
def ChartExp (T : Set (ULift.{u} (Fin n))) (v : (Fin m ⊕ Fin n) →₀ ℤ) : Prop :=
  (∀ l, 0 ≤ v (Sum.inl l)) ∧ 0 ≤ yDegree m n v ∧ negSet.{u} m n v ⊆ T

/-- A Laurent polynomial all of whose exponents are chart exponents. -/
def IsChartLaurent (T : Set (ULift.{u} (Fin n))) (f : Lau R m n) : Prop :=
  ∀ v ∈ f.coeff.support, ChartExp T v

/-- The charts a frame coordinate needs: those `y_k` in which its exponent is negative, or is
`≤ 0` while `d log y_k` occurs in it. -/
def frameNeed {a : ℕ} (e : FrameIndex m n a) : Set (ULift.{u} (Fin n)) :=
  {k | e.2 (Sum.inr k.down) < 0 ∨
    (toLex (Sum.inr k.down) ∈ (e.1 : Finset (Lex (Fin m ⊕ Fin n))) ∧ e.2 (Sum.inr k.down) ≤ 0)}

/-- The frame coordinates occurring in the forms over the intersection of the charts in `T`. -/
def FrameAllowed (T : Set (ULift.{u} (Fin n))) {a : ℕ} (e : FrameIndex m n a) : Prop :=
  (∀ l, 0 ≤ e.2 (Sum.inl l)) ∧ 0 ≤ yDegree m n e.2 ∧ frameNeed e ⊆ T

/-- An exponent is a chart exponent for `T` if and only if it is nonnegative in the `x`'s, of
nonnegative degree in the `y`'s, and nonnegative in every `y_k` with `k ∉ T`. -/
theorem chartExp_iff (T : Set (ULift.{u} (Fin n))) (v : (Fin m ⊕ Fin n) →₀ ℤ) :
    ChartExp T v ↔ (∀ l, 0 ≤ v (Sum.inl l)) ∧ 0 ≤ yDegree m n v ∧
      ∀ k : Fin n, (⟨k⟩ : ULift.{u} (Fin n)) ∉ T → 0 ≤ v (Sum.inr k) := by
  refine and_congr_right fun _ => and_congr_right fun _ => ⟨fun h k hk => ?_, fun h k hk => ?_⟩
  · by_contra hlt
    exact hk (h (show (⟨k⟩ : ULift.{u} (Fin n)) ∈ negSet.{u} m n v from by
      simp only [negSet, Set.mem_ofPred_eq]; omega))
  · by_contra hkT
    have := h k.down hkT
    simp only [negSet, Set.mem_ofPred_eq] at hk
    omega

/-- A monomial with a chart exponent is a chart Laurent polynomial. -/
theorem isChartLaurent_single {T : Set (ULift.{u} (Fin n))} {w : (Fin m ⊕ Fin n) →₀ ℤ}
    (hw : ChartExp T w) (r : R) : IsChartLaurent T (single w r) := fun v hv => by
  obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hv)
  exact hw

/-- A frame coordinate is allowed for `T` if and only if its exponent is nonnegative in the `x`'s,
of nonnegative degree in the `y`'s, and for every `k ∉ T` nonnegative in `y_k`, and at least one
in `y_k` when `d log y_k` occurs in it. -/
theorem frameAllowed_iff (T : Set (ULift.{u} (Fin n))) {a : ℕ} (e : FrameIndex m n a) :
    FrameAllowed T e ↔ (∀ l, 0 ≤ e.2 (Sum.inl l)) ∧ 0 ≤ yDegree m n e.2 ∧
      ∀ k : Fin n, (⟨k⟩ : ULift.{u} (Fin n)) ∉ T → 0 ≤ e.2 (Sum.inr k) ∧
        (toLex (Sum.inr k) ∈ (e.1 : Finset (Lex (Fin m ⊕ Fin n))) → 1 ≤ e.2 (Sum.inr k)) := by
  refine and_congr_right fun _ => and_congr_right fun _ => ⟨fun h k hk => ?_, fun h k hk => ?_⟩
  · by_contra hc
    refine hk (h ?_)
    simp only [frameNeed, Set.mem_ofPred_eq]
    by_cases hS : toLex (Sum.inr k) ∈ (e.1 : Finset (Lex (Fin m ⊕ Fin n)))
    · have : ¬(0 ≤ e.2 (Sum.inr k) ∧ 1 ≤ e.2 (Sum.inr k)) := fun h' => hc ⟨h'.1, fun _ => h'.2⟩
      by_cases hneg : e.2 (Sum.inr k) < 0
      · exact Or.inl hneg
      · exact Or.inr ⟨hS, by omega⟩
    · have : ¬(0 ≤ e.2 (Sum.inr k)) := fun h' => hc ⟨h', fun h'' => absurd h'' hS⟩
      exact Or.inl (by omega)
  · by_contra hkT
    obtain ⟨h1, h2⟩ := h k.down hkT
    simp only [frameNeed, Set.mem_ofPred_eq] at hk
    rcases hk with hk | ⟨hk1, hk2⟩
    · omega
    · have := h2 hk1; omega

/-- The exponents of `frameOp s g` are exponents `w` of `g` with `w s ≠ 0`, shifted. -/
theorem exists_of_mem_support_frameOp (s : Fin m ⊕ Fin n) (g : Lau R m n)
    {v : (Fin m ⊕ Fin n) →₀ ℤ} (hv : v ∈ (frameOp s g).coeff.support) :
    ∃ w ∈ g.coeff.support, w s ≠ 0 ∧ v = w - frameShift s := by
  classical
  have hg : frameOp s g = ∑ w ∈ g.coeff.support, single (w - frameShift s) ((w s) • g.coeff w) := by
    conv_lhs => rw [← ofCoeff_coeff g, ← Finsupp.sum_single g.coeff]
    rw [Finsupp.sum, ofCoeff_sum, map_sum]
    exact Finset.sum_congr rfl fun w _ => frameOp_single s w _
  rw [hg, coeff_sum, Finsupp.mem_support_iff, Finsupp.finsetSum_apply] at hv
  obtain ⟨w, hw, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  rw [coeff_single, Finsupp.single_apply] at hne
  split_ifs at hne with h
  · exact ⟨w, hw, fun h0 => hne (by rw [h0, zero_smul]), h.symm⟩
  · exact absurd rfl hne

/-- The exponent shift of a frame operator vanishes in every `y_k`. -/
theorem frameShift_inr (s : Fin m ⊕ Fin n) (k : Fin n) : frameShift s (Sum.inr k) = 0 := by
  cases s <;> simp [frameShift]

/-- The exponent shift of the frame operator at `s` is one in `x_l` if `s = x_l` and zero
otherwise. -/
theorem frameShift_inl (s : Fin m ⊕ Fin n) (l : Fin m) :
    frameShift s (Sum.inl l) = if s = Sum.inl l then 1 else 0 := by
  cases s with
  | inl i => by_cases h : i = l <;> simp [frameShift, h]
  | inr j => simp [frameShift]

/-- The exponent shift of a frame operator has degree zero in the `y`'s. -/
theorem yDegree_frameShift (s : Fin m ⊕ Fin n) : yDegree m n (frameShift s) = 0 := by
  simp [yDegree, frameShift_inr]

/-- The total degree in the `y`'s is additive. -/
theorem yDegree_add (v w : (Fin m ⊕ Fin n) →₀ ℤ) :
    yDegree m n (v + w) = yDegree m n v + yDegree m n w :=
  map_add (yDegreeHom m n) v w

/-- The total degree in the `y`'s commutes with subtraction. -/
theorem yDegree_sub (v w : (Fin m ⊕ Fin n) →₀ ℤ) :
    yDegree m n (v - w) = yDegree m n v - yDegree m n w :=
  map_sub (yDegreeHom m n) v w

/-- The total degree in the `y`'s commutes with finite sums. -/
theorem yDegree_sum {ι : Type*} (s : Finset ι) (f : ι → (Fin m ⊕ Fin n) →₀ ℤ) :
    yDegree m n (∑ i ∈ s, f i) = ∑ i ∈ s, yDegree m n (f i) :=
  map_sum (yDegreeHom m n) f s

/-- An exponent of a frame coordinate of `c • ⋀ frameD (g i)` is an exponent of `c` plus
shifted exponents of the `g i`, for a frame choice `f` with nonzero minor. -/
theorem exists_of_mem_support_frameCoord {a : ℕ} (c : Lau R m n) (g : Fin a → Lau R m n)
    (e : FrameIndex m n a)
    (he : e ∈ (frameCoord R a
      (c • exteriorPower.ιMulti (Lau R m n) a fun i => frameD (g i))).support) :
    ∃ f : Fin a → Fin m ⊕ Fin n, frameMinor f e.1 ≠ 0 ∧ ∃ w0 ∈ c.coeff.support,
      ∃ w : Fin a → (Fin m ⊕ Fin n) →₀ ℤ, (∀ i, w i ∈ (g i).coeff.support) ∧
        (∀ i, w i (f i) ≠ 0) ∧ e.2 = w0 + ∑ i, (w i - frameShift (f i)) := by
  classical
  rw [Finsupp.mem_support_iff, frameCoord_smul_ιMulti_frameD] at he
  obtain ⟨f, -, hf⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  have hcoeff : e.2 ∈ (c * ∏ i, frameOp (f i) (g i)).coeff.support :=
    Finsupp.mem_support_iff.2 fun h => hf (by rw [h, smul_zero])
  obtain ⟨w0, hw0, w', hw', hsum⟩ := exists_add_of_mem_support_mul hcoeff
  obtain ⟨w'', hw'', rfl⟩ := exists_of_mem_support_prod _ hw'
  choose w hw hws hww using fun i => exists_of_mem_support_frameOp (f i) (g i) (hw'' i)
  refine ⟨f, fun h => hf (by rw [h, zero_smul]), w0, hw0, w, hw, hws, ?_⟩
  rw [← hsum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => hww i

/-- **The frame coordinates of a generator over the intersection of the charts in `T` are
allowed.** -/
theorem frameAllowed_of_mem_support (T : Set (ULift.{u} (Fin n))) {a : ℕ} (c : Lau R m n)
    (g : Fin a → Lau R m n) (hc : IsChartLaurent T c) (hg : ∀ i, IsChartLaurent T (g i))
    (e : FrameIndex m n a)
    (he : e ∈ (frameCoord R a
      (c • exteriorPower.ιMulti (Lau R m n) a fun i => frameD (g i))).support) :
    FrameAllowed T e := by
  classical
  obtain ⟨f, hminor, w0, hw0, w, hw, hws, hv⟩ := exists_of_mem_support_frameCoord c g e he
  obtain ⟨hc1, hc2, hc3⟩ := (chartExp_iff T w0).1 (hc w0 hw0)
  have hgi := fun i => (chartExp_iff T (w i)).1 (hg i (w i) (hw i))
  rw [frameAllowed_iff]
  refine ⟨fun l => ?_, ?_, fun k hk => ⟨?_, fun hS => ?_⟩⟩
  · rw [hv, Finsupp.add_apply, Finsupp.finsetSum_apply]
    refine add_nonneg (hc1 l) (Finset.sum_nonneg fun i _ => ?_)
    rw [Finsupp.sub_apply, frameShift_inl]
    split_ifs with h
    · have h1 := (hgi i).1 l
      have h2 := hws i
      rw [h] at h2
      omega
    · simpa using (hgi i).1 l
  · rw [hv, yDegree_add, yDegree_sum]
    refine add_nonneg hc2 (Finset.sum_nonneg fun i _ => ?_)
    rw [yDegree_sub, yDegree_frameShift, sub_zero]
    exact (hgi i).2.1
  · rw [hv, Finsupp.add_apply, Finsupp.finsetSum_apply]
    refine add_nonneg (hc3 k hk) (Finset.sum_nonneg fun i _ => ?_)
    rw [Finsupp.sub_apply, frameShift_inr, sub_zero]
    exact (hgi i).2.2 k hk
  · obtain ⟨i0, hi0⟩ : ∃ i, f i = Sum.inr k := by
      by_contra hno
      push Not at hno
      exact hminor (frameMinor_eq_zero f e.1 hS fun i => hno i)
    rw [hv, Finsupp.add_apply, Finsupp.finsetSum_apply,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
    have h0 : 1 ≤ w i0 (Sum.inr k) - frameShift (f i0) (Sum.inr k) := by
      rw [frameShift_inr, sub_zero]
      have h1 := (hgi i0).2.2 k hk
      have h2 := hws i0
      rw [hi0] at h2
      omega
    have h3 : 0 ≤ ∑ i ∈ Finset.univ.erase i0, (w i - frameShift (f i)) (Sum.inr k) :=
      Finset.sum_nonneg fun i _ => by
        rw [Finsupp.sub_apply, frameShift_inr, sub_zero]
        exact (hgi i).2.2 k hk
    have := hc3 k hk
    simp only [Finsupp.sub_apply] at h0 h3 ⊢
    omega

/-- Multiplying by a chart Laurent polynomial keeps the frame coordinates allowed. -/
theorem frameAllowed_smul (T : Set (ULift.{u} (Fin n))) {a : ℕ} (Q : Lau R m n)
    (hQ : IsChartLaurent T Q) (x : ⋀[Lau R m n]^a (FrameVec R m n))
    (hx : ∀ e ∈ (frameCoord R a x).support, FrameAllowed T e) :
    ∀ e ∈ (frameCoord R a (Q • x)).support, FrameAllowed T e := by
  classical
  intro e he
  rw [Finsupp.mem_support_iff, frameCoord_apply, map_smul, Finsupp.smul_apply, smul_eq_mul] at he
  obtain ⟨v0, hv0, v', hv', hsum⟩ := exists_add_of_mem_support_mul (Finsupp.mem_support_iff.2 he)
  have hmem : ((e.1, v') : FrameIndex m n a) ∈ (frameCoord R a x).support := by
    rw [Finsupp.mem_support_iff, frameCoord_apply]
    exact Finsupp.mem_support_iff.1 hv'
  obtain ⟨hq1, hq2, hq3⟩ := (chartExp_iff T v0).1 (hQ v0 hv0)
  obtain ⟨h1, h2, h3⟩ := (frameAllowed_iff T _).1 (hx (e.1, v') hmem)
  rw [frameAllowed_iff, ← hsum]
  refine ⟨fun l => ?_, ?_, fun k hk => ?_⟩
  · simpa using add_nonneg (hq1 l) (h1 l)
  · rw [yDegree_add]
    exact add_nonneg hq2 h2
  · obtain ⟨h31, h32⟩ := h3 k hk
    have := hq3 k hk
    simp only [Finsupp.add_apply]
    have h31' : 0 ≤ v' (Sum.inr k) := h31
    exact ⟨by omega, fun hS => by
      have h4 : 1 ≤ v' (Sum.inr k) := h32 hS
      omega⟩

section Frame

variable {R0 A : CommRingCat.{u}} (φ : R0 ⟶ A)

/-- The wedges of differentials span the exterior powers of the Kähler differentials. -/
theorem span_ιMulti_d (a : ℕ) :
    Submodule.span A (Set.range fun g : Fin a → A =>
      exteriorPower.ιMulti A a fun i => CommRingCat.KaehlerDifferential.d (f := φ) (g i)) = ⊤ := by
  let := φ.hom.toAlgebra
  have hs : Submodule.span A (Set.range fun b : A => CommRingCat.KaehlerDifferential.d (f := φ) b) =
      ⊤ := KaehlerDifferential.span_range_derivation R0 A
  rw [← exteriorPower.ιMulti_span_of_span A a _ hs]
  congr 1
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨_, Set.range_subset_iff.2 fun i => ⟨g i, rfl⟩, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    choose g hg using fun i => hv ⟨i, rfl⟩
    exact ⟨g, congrArg (exteriorPower.ιMulti A a) (funext hg)⟩

/-- An additive property of `⋀^a_A Ω[A/R0]` that holds on the wedges of differentials and is
stable under scalars holds everywhere. -/
theorem formsFrame_induction {a : ℕ}
    {P : ⋀[A]^a (CommRingCat.KaehlerDifferential φ) → Prop} (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y)) (hsmul : ∀ (c : A) x, P x → P (c • x))
    (hgen : ∀ g : Fin a → A, P (exteriorPower.ιMulti A a fun i =>
      CommRingCat.KaehlerDifferential.d (f := φ) (g i)))
    (x : ⋀[A]^a (CommRingCat.KaehlerDifferential φ)) : P x := by
  have hx : x ∈ Submodule.span A (Set.range fun g : Fin a → A =>
      exteriorPower.ιMulti A a fun i => CommRingCat.KaehlerDifferential.d (f := φ) (g i)) := by
    rw [span_ιMulti_d]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, rfl⟩ := hy
    exact hgen g
  | zero => exact h0
  | add y z _ _ hy hz => exact hadd y z hy hz
  | smul c y _ hy => exact hsmul c y hy

variable (lam : A →+* Lau R m n)
  (hlam : ∀ (r : R0) (s : Fin m ⊕ Fin n), frameOp s (lam (φ r)) = 0)

/-- **The frame coordinates of the forms over the intersection of the charts in `T` are
allowed**: for `lam` with values chart Laurent polynomials. -/
theorem frameAllowed_formsFrame (T : Set (ULift.{u} (Fin n))) (hB : ∀ z, IsChartLaurent T (lam z))
    {a : ℕ} (ω : ⋀[A]^a (CommRingCat.KaehlerDifferential φ)) :
    ∀ e ∈ (frameCoord R a (formsFrame φ lam hlam a ω)).support, FrameAllowed T e := by
  classical
  induction ω using formsFrame_induction φ with
  | h0 => simp
  | hadd x y hx hy =>
    intro e he
    rw [map_add, map_add] at he
    exact (Finset.mem_union.1 (Finsupp.support_add he)).elim (hx e) (hy e)
  | hsmul c x hx =>
    rw [formsFrame_smul]
    exact frameAllowed_smul T (lam c) (hB c) _ hx
  | hgen g =>
    have := formsFrame_smul_ιMulti_d φ lam hlam a 1 g
    rw [one_smul, map_one] at this
    rw [this]
    exact frameAllowed_of_mem_support T 1 (fun i => lam (g i)) (by simpa using hB 1)
      (fun i => hB (g i))

/-- A family of Kähler differentials with frame coordinates the standard basis is linearly
independent when `lam` is injective. -/
theorem linearIndependent_of_kaehlerFrame_eq_single (hinj : Function.Injective lam)
    {β : Fin m ⊕ Fin n → CommRingCat.KaehlerDifferential φ}
    (hβf : ∀ s, kaehlerFrame φ lam hlam (β s) = Pi.single s 1) : LinearIndependent A β := by
  classical
  rw [linearIndependent_iff']
  intro t g hg i hi
  have h1 := congrArg (fun x => kaehlerFrame φ lam hlam x i) hg
  simp only [map_sum, kaehlerFrame_smul, hβf, map_zero, Finset.sum_apply, Pi.smul_apply,
    Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Pi.zero_apply] at h1
  rw [Finset.sum_ite_eq t i (fun x => lam (g x)), ite_eq_left hi] at h1
  exact hinj (by rw [h1, map_zero])

/-- **Injectivity criterion for the frame map.** If `lam` is injective and the Kähler
differentials are spanned by a family `β` with frame coordinates the standard basis, then the
frame map on every exterior power is injective. -/
theorem formsFrame_injective (hinj : Function.Injective lam)
    (β : Fin m ⊕ Fin n → CommRingCat.KaehlerDifferential φ)
    (hβ : Submodule.span A (Set.range β) = ⊤)
    (hβf : ∀ s, kaehlerFrame φ lam hlam (β s) = Pi.single s 1) (a : ℕ) :
    Function.Injective (formsFrame φ lam hlam a) := by
  classical
  let bβ : Module.Basis (Lex (Fin m ⊕ Fin n)) A (CommRingCat.KaehlerDifferential φ) :=
    (Module.Basis.mk (linearIndependent_of_kaehlerFrame_eq_single φ lam hlam hinj hβf)
      (by rw [hβ])).reindex toLex
  have hbβ : ∀ t, kaehlerFrame φ lam hlam (bβ t) = frameBasis t := fun t => by
    simp [bβ, hβf, frameBasis_apply]
  let B := bβ.exteriorPower a
  have hB : ∀ S, formsFrame φ lam hlam a (B S) = frameBasis.exteriorPower a S := by
    intro S
    rw [exteriorPower.basis_apply, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
      exteriorPower.ιMulti_family, formsFrame_ιMulti]
    congr 1
    funext j
    exact hbβ _
  refine (injective_iff_map_eq_zero _).2 fun x hx => B.repr.injective ?_
  ext S0
  rw [map_zero, Finsupp.zero_apply]
  have hx' : formsFrame φ lam hlam a x =
      (B.repr x).sum fun S c => lam c • frameBasis.exteriorPower a S := by
    conv_lhs => rw [← B.linearCombination_repr x, Finsupp.linearCombination_apply]
    rw [Finsupp.sum, map_sum, Finsupp.sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [formsFrame_smul, hB]
  have h2 := congrArg (fun y => (frameBasis.exteriorPower a).repr y S0) hx'
  simp only [hx, map_zero, Finsupp.zero_apply, Finsupp.sum, map_sum, map_smul,
    Module.Basis.repr_self, Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finsupp.mem_support_iff] at h2
  by_contra hne
  rw [ite_eq_left hne] at h2
  exact hne (hinj (by rw [← h2, map_zero]))

end Frame

/-! ### The weight-zero part -/

/-- A Laurent polynomial of nonnegative weight: every exponent has nonnegative degree in the
`y`'s. -/
def NonnegW (f : Lau R m n) : Prop := ∀ v ∈ f.coeff.support, 0 ≤ yDegree m n v

variable (R m n) in
/-- **The weight-zero part** of a Laurent polynomial: its monomials of degree zero in the `y`'s. -/
def wt0 : Lau R m n →+ Lau R m n where
  toFun f := ofCoeff (f.coeff.filter fun v => yDegree m n v = 0)
  map_zero' := by ext; simp [Finsupp.filter_apply]
  map_add' f g := by
    ext v
    simp only [coeff_add, Finsupp.filter_add]

/-- The coefficient of `z^v` in the weight-zero part of `f` is that of `f` when `v` has degree
zero in the `y`'s, and zero otherwise. -/
theorem coeff_wt0 (f : Lau R m n) (v : (Fin m ⊕ Fin n) →₀ ℤ) :
    (wt0 R m n f).coeff v = if yDegree m n v = 0 then f.coeff v else 0 := by
  show (f.coeff.filter fun v => yDegree m n v = 0) v = _
  rw [Finsupp.filter_apply]

/-- The weight-zero part of a monomial is the monomial if its exponent has degree zero in the
`y`'s, and zero otherwise. -/
theorem wt0_single (v : (Fin m ⊕ Fin n) →₀ ℤ) (r : R) :
    wt0 R m n (single v r) = if yDegree m n v = 0 then single v r else 0 := by
  ext w
  rw [coeff_wt0]
  by_cases hw : w = v
  · subst hw
    split_ifs <;> simp
  · split_ifs <;> simp [coeff_single, Ne.symm hw]

/-- A Laurent polynomial all of whose exponents have degree zero in the `y`'s is its own
weight-zero part. -/
theorem wt0_eq_self {f : Lau R m n} (hf : ∀ v ∈ f.coeff.support, yDegree m n v = 0) :
    wt0 R m n f = f := by
  ext v
  rw [coeff_wt0]
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (hf v (Finsupp.mem_support_iff.2 (Ne.symm hne)))

/-- A Laurent polynomial none of whose exponents has degree zero in the `y`'s has weight-zero
part zero. -/
theorem wt0_eq_zero {f : Lau R m n} (hf : ∀ v ∈ f.coeff.support, yDegree m n v ≠ 0) :
    wt0 R m n f = 0 := by
  ext v
  rw [coeff_wt0]
  split_ifs with h
  · by_contra hne
    exact hf v (Finsupp.mem_support_iff.2 hne) h
  · rfl

/-- A product of Laurent polynomials of nonnegative weight has nonnegative weight. -/
theorem nonnegW_mul {f g : Lau R m n} (hf : NonnegW f) (hg : NonnegW g) : NonnegW (f * g) := by
  classical
  intro v hv
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_add_of_mem_support_mul hv
  rw [yDegree_add]
  exact add_nonneg (hf a ha) (hg b hb)

/-- An exponent of the weight-zero part of a Laurent polynomial has degree zero in the `y`'s. -/
theorem yDegree_eq_zero_of_mem_support_wt0 {f : Lau R m n} {v : (Fin m ⊕ Fin n) →₀ ℤ}
    (hv : v ∈ (wt0 R m n f).coeff.support) : yDegree m n v = 0 := by
  rw [Finsupp.mem_support_iff, coeff_wt0] at hv
  split_ifs at hv with h
  exacts [h, absurd rfl hv]

/-- The weight-zero part of a Laurent polynomial has nonnegative weight. -/
theorem nonnegW_wt0 (f : Lau R m n) : NonnegW (wt0 R m n f) :=
  fun _ hv => (yDegree_eq_zero_of_mem_support_wt0 hv).ge

/-- For `f` of nonnegative weight, every exponent of `f - wt0 f` has positive degree in the
`y`'s. -/
theorem one_le_yDegree_of_mem_support_sub_wt0 {f : Lau R m n} (hf : NonnegW f) :
    ∀ v ∈ (f - wt0 R m n f).coeff.support, 1 ≤ yDegree m n v := by
  intro v hv
  rw [Finsupp.mem_support_iff, coeff_sub, Finsupp.sub_apply, coeff_wt0] at hv
  split_ifs at hv with h0
  · exact absurd (sub_self _) hv
  · have := hf v (Finsupp.mem_support_iff.2 (by simpa using hv))
    omega

/-- The product of a Laurent polynomial of nonnegative weight with one all of whose exponents
have positive degree in the `y`'s has weight-zero part zero. -/
theorem wt0_mul_eq_zero {p q : Lau R m n} (hp : NonnegW p)
    (hq : ∀ v ∈ q.coeff.support, 1 ≤ yDegree m n v) : wt0 R m n (p * q) = 0 := by
  classical
  refine wt0_eq_zero fun v hv => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_add_of_mem_support_mul hv
  have := hp a ha
  have := hq b hb
  rw [yDegree_add]
  omega

/-- **The weight-zero part is multiplicative on Laurent polynomials of nonnegative weight.** -/
theorem wt0_mul {f g : Lau R m n} (hf : NonnegW f) (hg : NonnegW g) :
    wt0 R m n (f * g) = wt0 R m n f * wt0 R m n g := by
  classical
  have hf₁ := one_le_yDegree_of_mem_support_sub_wt0 hf
  have hg₁ := one_le_yDegree_of_mem_support_sub_wt0 hg
  have hzero : ∀ v ∈ (wt0 R m n f * wt0 R m n g).coeff.support, yDegree m n v = 0 := by
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_add_of_mem_support_mul hv
    rw [yDegree_add, yDegree_eq_zero_of_mem_support_wt0 ha,
      yDegree_eq_zero_of_mem_support_wt0 hb, add_zero]
  have hfg : wt0 R m n ((f - wt0 R m n f) * wt0 R m n g) = 0 := by
    rw [mul_comm]
    exact wt0_mul_eq_zero (nonnegW_wt0 g) hf₁
  have hf' : f = wt0 R m n f + (f - wt0 R m n f) := by abel
  have hg' : g = wt0 R m n g + (g - wt0 R m n g) := by abel
  conv_lhs => rw [hf', hg']
  rw [add_mul, mul_add, mul_add, map_add, map_add, map_add,
    wt0_mul_eq_zero (nonnegW_wt0 f) hg₁, hfg,
    wt0_mul_eq_zero (fun v hv => zero_le_one.trans (hf₁ v hv)) hg₁, wt0_eq_self hzero,
    add_zero, add_zero, add_zero]

/-- The weight-zero part of `1` is `1`. -/
theorem wt0_one : wt0 R m n (1 : Lau R m n) = 1 := by
  refine wt0_eq_self fun v hv => ?_
  have := AddMonoidAlgebra.support_coeff_one_subset hv
  rw [Finset.mem_zero] at this
  subst this
  simp [yDegree]

/-- The Laurent polynomial `1` has nonnegative weight. -/
theorem nonnegW_one : NonnegW (1 : Lau R m n) := by
  rw [← wt0_one]
  exact nonnegW_wt0 1

/-- A finite product of Laurent polynomials of nonnegative weight has nonnegative weight. -/
theorem nonnegW_prod {a : ℕ} (f : Fin a → Lau R m n) (hf : ∀ i, NonnegW (f i)) :
    NonnegW (∏ i, f i) := by
  induction a with
  | zero => rw [Fin.prod_univ_zero]; exact nonnegW_one
  | succ a ih =>
    rw [Fin.prod_univ_succ]
    exact nonnegW_mul (hf 0) (ih _ fun i => hf i.succ)

/-- The weight-zero part of a finite product of Laurent polynomials of nonnegative weight is the
product of their weight-zero parts. -/
theorem wt0_prod {a : ℕ} (f : Fin a → Lau R m n) (hf : ∀ i, NonnegW (f i)) :
    wt0 R m n (∏ i, f i) = ∏ i, wt0 R m n (f i) := by
  induction a with
  | zero => rw [Fin.prod_univ_zero, Fin.prod_univ_zero, wt0_one]
  | succ a ih =>
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, wt0_mul (hf 0) (nonnegW_prod _ fun i => hf i.succ),
      ih _ fun i => hf i.succ]

/-- A frame operator preserves nonnegative weight. -/
theorem nonnegW_frameOp (s : Fin m ⊕ Fin n) {g : Lau R m n} (hg : NonnegW g) :
    NonnegW (frameOp s g) := by
  intro v hv
  obtain ⟨w, hw, -, rfl⟩ := exists_of_mem_support_frameOp s g hv
  rw [yDegree_sub, yDegree_frameShift, sub_zero]
  exact hg w hw

/-- A frame operator commutes with taking the weight-zero part. -/
theorem frameOp_wt0 (s : Fin m ⊕ Fin n) (g : Lau R m n) :
    frameOp s (wt0 R m n g) = wt0 R m n (frameOp s g) := by
  induction g using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add, map_add]
  | single v r =>
    have hdeg : yDegree m n (v - frameShift s) = yDegree m n v := by
      rw [yDegree_sub, yDegree_frameShift, sub_zero]
    rw [wt0_single, frameOp_single, wt0_single, hdeg]
    split_ifs <;> simp [frameOp_single]

/-- **Weight zero commutes with frame coordinates of generators of nonnegative weight.** -/
theorem frameCoord_filter_wt0 {a : ℕ} (c : Lau R m n) (g : Fin a → Lau R m n)
    (hc : NonnegW c) (hg : ∀ i, NonnegW (g i)) :
    (frameCoord R a (c • exteriorPower.ιMulti (Lau R m n) a fun i => frameD (g i))).filter
        (fun e => yDegree m n e.2 = 0) =
      frameCoord R a (wt0 R m n c • exteriorPower.ιMulti (Lau R m n) a fun i =>
        frameD (wt0 R m n (g i))) := by
  classical
  ext e
  rw [Finsupp.filter_apply, frameCoord_smul_ιMulti_frameD, frameCoord_smul_ιMulti_frameD]
  have hP : ∀ f : Fin a → Fin m ⊕ Fin n,
      wt0 R m n c * ∏ i, frameOp (f i) (wt0 R m n (g i)) =
        wt0 R m n (c * ∏ i, frameOp (f i) (g i)) := by
    intro f
    simp_rw [frameOp_wt0]
    rw [wt0_mul hc (nonnegW_prod _ fun i => nonnegW_frameOp _ (hg i)),
      wt0_prod _ fun i => nonnegW_frameOp _ (hg i)]
  simp_rw [hP, coeff_wt0]
  split_ifs with h
  · rfl
  · simp

/-! ### Realising the allowed frame coordinates -/

/-- The frame coordinates of `d x_l` are the unit vector at `x_l`. -/
theorem frameD_single_x (l : Fin m) :
    frameD (single (Finsupp.single (Sum.inl l) 1) (1 : R)) =
      (Pi.single (Sum.inl l) 1 : FrameVec R m n) := by
  classical
  funext s
  rcases s with l' | j
  · rw [frameD, frameOp_single]
    by_cases h : l' = l
    · subst h
      simp [frameShift]
      rfl
    · simp [frameShift, h]
  · simp [frameD, frameOp_single]

/-- For an exponent `w` vanishing in the `x`'s, the frame coordinates of `d z^w` are `z^w` times
the vector with entries `0` at the `x`'s and `w_j` at `y_j`. -/
theorem frameD_single_y (w : (Fin m ⊕ Fin n) →₀ ℤ) (hw : ∀ l, w (Sum.inl l) = 0) :
    frameD (single w (1 : R)) =
      single w (1 : R) • fun s => Sum.elim (fun _ => (0 : Lau R m n))
        (fun j => ((w (Sum.inr j) : ℤ) : Lau R m n)) s := by
  funext s
  rcases s with l | j
  · simp [frameD, frameOp_single, hw l]
  · simp only [frameD, frameOp_single, frameShift, sub_zero, Sum.elim_inr, Pi.smul_apply,
      smul_eq_mul]
    rw [mul_comm, ← zsmul_eq_mul, smul_single]

variable (k : Fin n)

/-- The frame vector of slot `s` in the expansion of `e_s` against the chart-`k` frame: bit
`false` is `e'_s` (`e_{x_l}`, `e_{y_k}`, or `e_{y_j} - e_{y_k}`), bit `true` is the correction
`e_{y_k}` (only for `s = y_j`, `j ≠ k`). -/
def slotVec : Fin m ⊕ Fin n → Bool → FrameVec R m n
  | .inl l, false => Pi.single (.inl l) 1
  | .inl _, true => 0
  | .inr j, false =>
    if j = k then Pi.single (.inr k) 1 else Pi.single (.inr j) 1 - Pi.single (.inr k) 1
  | .inr j, true => if j = k then 0 else Pi.single (.inr k) 1

/-- The exponent of the function whose differential realises a slot. -/
def slotG : Fin m ⊕ Fin n → Bool → (Fin m ⊕ Fin n) →₀ ℤ
  | .inl l, false => Finsupp.single (.inl l) 1
  | .inl _, true => 0
  | .inr j, false => if j = k then yExp m n k else yExp m n j - yExp m n k
  | .inr _, true => yExp m n k

/-- The exponent of the factor relating a slot vector and the differential realising it. -/
def slotH : Fin m ⊕ Fin n → Bool → (Fin m ⊕ Fin n) →₀ ℤ
  | .inl _, _ => 0
  | .inr j, false => if j = k then yExp m n k else yExp m n j - yExp m n k
  | .inr _, true => yExp m n k

/-- Whether a slot vector is nonzero. -/
def slotOk : Fin m ⊕ Fin n → Bool → Prop
  | .inl _, b => b = false
  | .inr j, b => b = false ∨ j ≠ k

/-- The two slot vectors of `s` sum to the unit vector `e_s`. -/
theorem slotVec_add (s : Fin m ⊕ Fin n) :
    slotVec (R := R) k s false + slotVec k s true = Pi.single s 1 := by
  rcases s with l | j
  · simp [slotVec]
  · by_cases h : j = k
    · subst h
      simp [slotVec]
    · simp [slotVec, h]

/-- A slot vector outside `slotOk` is zero. -/
theorem slotVec_eq_zero (s : Fin m ⊕ Fin n) (b : Bool) (h : ¬slotOk k s b) :
    slotVec (R := R) k s b = 0 := by
  rcases s with l | j <;> cases b <;> simp_all [slotOk, slotVec]

/-- The exponent of `y_j` vanishes in every `x_l`. -/
theorem yExp_inl (j : Fin n) (l : Fin m) : yExp m n j (Sum.inl l) = 0 := by simp [yExp]

/-- A nonzero slot vector is `z^(-slotH k s b) • frameD (z^(slotG k s b))`. -/
theorem slotVec_eq (s : Fin m ⊕ Fin n) (b : Bool) (h : slotOk k s b) :
    slotVec (R := R) k s b =
      single (-slotH k s b) (1 : R) • frameD (single (slotG k s b) (1 : R)) := by
  classical
  have hy : ∀ w : (Fin m ⊕ Fin n) →₀ ℤ, (∀ l, w (Sum.inl l) = 0) →
      single (-w) (1 : R) • frameD (single w (1 : R)) = fun s => Sum.elim (fun _ => (0 : Lau R m n))
        (fun j => ((w (Sum.inr j) : ℤ) : Lau R m n)) s := by
    intro w hw
    rw [frameD_single_y w hw, smul_smul, single_mul_single, neg_add_cancel, one_mul,
      show (single 0 (1 : R) : Lau R m n) = 1 from rfl, one_smul]
  rcases s with l | j
  · cases b
    · simp only [slotVec, slotH, slotG, neg_zero, frameD_single_x]
      exact (one_smul (Lau R m n) _).symm
    · simp [slotOk] at h
  · cases b
    · by_cases hj : j = k
      · subst hj
        simp only [slotVec, slotH, slotG, ite_true]
        rw [hy _ (fun l => yExp_inl _ _)]
        funext s
        rcases s with l | j' <;> simp [Pi.single_apply, yExp, Finsupp.single_apply, eq_comm]
      · simp only [slotVec, slotH, slotG, ite_eq_right hj]
        rw [hy _ (fun l => by simp [yExp])]
        funext s
        rcases s with l | j'
        · simp
        · by_cases h1 : j' = j <;> by_cases h2 : j' = k <;>
            simp_all [Pi.single_apply, yExp, Finsupp.single_apply, eq_comm]
    · have hj : j ≠ k := by simpa [slotOk] using h
      simp only [slotVec, slotH, slotG, ite_eq_right hj]
      rw [hy _ (fun l => yExp_inl _ _)]
      funext s
      rcases s with l | j' <;> simp [Pi.single_apply, yExp, Finsupp.single_apply, eq_comm]

/-- The exponent `slotH k s b` vanishes in every `x_l`. -/
theorem slotH_inl (s : Fin m ⊕ Fin n) (b : Bool) (l : Fin m) : slotH k s b (Sum.inl l) = 0 := by
  rcases s with l' | j <;> cases b <;> simp [slotH, yExp]
  split_ifs <;> simp

/-- The exponent of `y_k` is nonzero. -/
theorem yExp_ne_zero : yExp m n k ≠ 0 := by
  intro h
  have := congrArg (fun w => w (Sum.inr k)) h
  simp [yExp] at this

/-- The exponent `slotH k s b` has degree one in the `y`'s if it is the exponent of `y_k`, and
degree zero otherwise. -/
theorem yDegree_slotH (s : Fin m ⊕ Fin n) (b : Bool) :
    yDegree m n (slotH k s b) = if slotH k s b = yExp m n k then 1 else 0 := by
  rcases s with l | j
  · simp [slotH, (yExp_ne_zero k).symm, yDegree]
  · cases b
    · by_cases hj : j = k
      · subst hj
        simp [slotH, yDegree_yExp]
      · have hne : yExp m n j - yExp m n k ≠ yExp m n k := by
          intro h
          have :=congrArg (fun w => w (Sum.inr j)) h
          simp [yExp, hj] at this
        simp only [slotH, ite_eq_right hj, ite_eq_right hne]
        rw [yDegree_sub, yDegree_yExp, yDegree_yExp, sub_self]
    · simp [slotH, yDegree_yExp]

/-- For `j ≠ k`, the exponent `slotH k s b` in `y_j` lies between `0` and `1`, and is `0` unless
`s = y_j`. -/
theorem slotH_inr_le (s : Fin m ⊕ Fin n) (b : Bool) (j : Fin n) (hj : j ≠ k) :
    0 ≤ slotH k s b (Sum.inr j) ∧ slotH k s b (Sum.inr j) ≤ if s = Sum.inr j then 1 else 0 := by
  rcases s with l | j'
  · simp [slotH]
  · cases b
    · by_cases h : j' = k
      · subst h
        simp [slotH, yExp, hj, Ne.symm hj]
      · simp only [slotH, ite_eq_right h, Finsupp.sub_apply, yExp, Finsupp.single_apply,
          Sum.inr.injEq, Ne.symm hj, ite_false, sub_zero]
        by_cases h' : j' = j <;> simp [h']
    · simp only [slotH, yExp, Finsupp.single_apply, Sum.inr.injEq, Ne.symm hj, ite_false,
        le_refl, true_and]
      split_ifs <;> simp

/-- If `slotH k s b` is the exponent of `y_k`, so is `slotG k s b`. -/
theorem slotG_eq_of_slotH (s : Fin m ⊕ Fin n) (b : Bool) (h : slotH k s b = yExp m n k) :
    slotG k s b = yExp m n k := by
  rcases s with l | j
  · simp [slotH] at h
    exact absurd h.symm (yExp_ne_zero k)
  · cases b
    · by_cases hj : j = k
      · subst hj
        simp [slotG]
      · simp only [slotH, ite_eq_right hj] at h
        have := congrArg (fun w => w (Sum.inr j)) h
        simp [yExp, hj] at this
    · simp [slotG]

/-- A nonzero slot vector whose `slotH k s b` is the exponent of `y_k` is the unit vector at
`y_k`. -/
theorem slotVec_eq_of_slotH (s : Fin m ⊕ Fin n) (b : Bool) (hok : slotOk k s b)
    (h : slotH k s b = yExp m n k) : slotVec (R := R) k s b = Pi.single (Sum.inr k) 1 := by
  rcases s with l | j
  · simp [slotH] at h
    exact absurd h.symm (yExp_ne_zero k)
  · cases b
    · by_cases hj : j = k
      · subst hj
        simp [slotVec]
      · simp only [slotH, ite_eq_right hj] at h
        have := congrArg (fun w => w (Sum.inr j)) h
        simp [yExp, hj] at this
    · have hj : j ≠ k := by simpa [slotOk] using hok
      simp [slotVec, hj]

/-- For `k ∈ T`, every exponent `slotG k s b` is a chart exponent for `T`. -/
theorem chartExp_slotG (T : Set (ULift.{u} (Fin n))) (hk : (⟨k⟩ : ULift.{u} (Fin n)) ∈ T)
    (s : Fin m ⊕ Fin n) (b : Bool) : ChartExp T (slotG k s b) := by
  rw [chartExp_iff]
  rcases s with l | j
  · cases b <;> refine ⟨fun l' => ?_, ?_, fun j' _ => ?_⟩ <;>
      simp [slotG, Finsupp.single_apply, yDegree]
    split_ifs <;> simp
  · cases b
    · by_cases hj : j = k
      · subst hj
        refine ⟨fun l' => by simp [slotG, yExp], by simp [slotG, yDegree_yExp], fun j' _ => ?_⟩
        simp [slotG, yExp, Finsupp.single_apply]
        split_ifs <;> simp
      · simp only [slotG, ite_eq_right hj]
        refine ⟨fun l' => by simp [yExp], ?_, fun j' hj' => ?_⟩
        · rw [yDegree_sub, yDegree_yExp, yDegree_yExp]
          simp
        · have hjk : j' ≠ k := fun h => hj' (h ▸ hk)
          simp [yExp, Finsupp.single_apply, Ne.symm hjk]
          split_ifs <;> simp
    · refine ⟨fun l' => by simp [slotG, yExp], by simp [slotG, yDegree_yExp], fun j' _ => ?_⟩
      simp [slotG, yExp, Finsupp.single_apply]
      split_ifs <;> simp

/-- A wedge of slot vectors, written as a generator. -/
theorem ιMulti_slotVec {a : ℕ} (t : Fin a → Fin m ⊕ Fin n) (β : Fin a → Bool)
    (hok : ∀ i, slotOk k (t i) (β i)) :
    (exteriorPower.ιMulti (Lau R m n) a fun i => slotVec k (t i) (β i)) =
      single (-∑ i, slotH k (t i) (β i)) (1 : R) •
        exteriorPower.ιMulti (Lau R m n) a fun i =>
          frameD (single (slotG k (t i) (β i)) (1 : R)) := by
  have h : (fun i => slotVec (R := R) k (t i) (β i)) = fun i =>
      single (-slotH k (t i) (β i)) (1 : R) • frameD (single (slotG k (t i) (β i)) (1 : R)) :=
    funext fun i => slotVec_eq k _ _ (hok i)
  refine (congrArg (exteriorPower.ιMulti (Lau R m n) a) h).trans ?_
  refine ((exteriorPower.ιMulti (Lau R m n) a).toMultilinearMap.map_smul_univ _ _).trans ?_
  congr 1
  rw [AddMonoidAlgebra.prod_single, Finset.prod_const_one, ← Finset.sum_neg_distrib]

/-- The frame coordinate supported at `(S, v)` with value `r` is the frame coordinate vector of
`z^v r` times the wedge of the frame vectors of `S`. -/
theorem single_eq_frameCoord_smul_ιMulti {a : ℕ} (S : Set.powersetCard (Lex (Fin m ⊕ Fin n)) a)
    (v : (Fin m ⊕ Fin n) →₀ ℤ) (r : R) :
    Finsupp.single (S, v) r = frameCoord R a (single v r • exteriorPower.ιMulti (Lau R m n) a
      fun i => (Pi.single (ofLex (Set.powersetCard.ofFinEmbEquiv.symm S i)) 1 :
        FrameVec R m n)) := by
  classical
  have hbasis : (exteriorPower.ιMulti (Lau R m n) a fun i =>
      (Pi.single (ofLex (Set.powersetCard.ofFinEmbEquiv.symm S i)) 1 : FrameVec R m n)) =
      frameBasis.exteriorPower a S := by
    rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
    congr 1
    funext i
    simp [frameBasis_apply]
  ext ⟨S', v'⟩
  rw [hbasis, frameCoord_apply, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply, Finsupp.single_apply]
  by_cases hS : S = S'
  · subst hS
    simp [coeff_single, Finsupp.single_apply]
  · simp [hS]

/-- The wedge of unit frame vectors expands as a sum over choices of slot vectors. -/
theorem ιMulti_single_eq_sum_slotVec {a : ℕ} (t : Fin a → Fin m ⊕ Fin n) :
    (exteriorPower.ιMulti (Lau R m n) a fun i => (Pi.single (t i) 1 : FrameVec R m n)) =
      ∑ β : Fin a → Bool, exteriorPower.ιMulti (Lau R m n) a fun i => slotVec k (t i) (β i) := by
  have h : (fun i => (Pi.single (t i) 1 : FrameVec R m n)) =
      fun i => ∑ b : Bool, slotVec (R := R) k (t i) b := funext fun i => by
    rw [Fintype.sum_bool, add_comm, slotVec_add]
  rw [h]
  exact (exteriorPower.ιMulti (Lau R m n) a).toMultilinearMap.map_sum _

/-- Subtracting the slot exponents lowers the `y`-degree by the number of slots whose exponent is
that of `y_k`. -/
theorem yDegree_sub_sum_slotH {a : ℕ} (t : Fin a → Fin m ⊕ Fin n) (β : Fin a → Bool)
    (v : (Fin m ⊕ Fin n) →₀ ℤ) :
    yDegree m n (v - ∑ i, slotH k (t i) (β i)) =
      yDegree m n v - (Finset.univ.filter fun i => slotH k (t i) (β i) = yExp m n k).card := by
  rw [yDegree_sub, yDegree_sum]
  simp_rw [yDegree_slotH]
  rw [Finset.sum_boole]

/-- For `j ≠ k`, subtracting the slot exponents of an injective family keeps the exponent of
`y_j` nonnegative, provided it is positive whenever some slot is `y_j`. -/
theorem sub_sum_slotH_inr_nonneg {a : ℕ} {t : Fin a → Fin m ⊕ Fin n} (ht : Function.Injective t)
    (β : Fin a → Bool) {v : (Fin m ⊕ Fin n) →₀ ℤ} {j : Fin n} (hjk : j ≠ k)
    (hv₀ : 0 ≤ v (Sum.inr j)) (hv₁ : (∃ i, t i = Sum.inr j) → 1 ≤ v (Sum.inr j)) :
    0 ≤ (v - ∑ i, slotH k (t i) (β i)) (Sum.inr j) := by
  classical
  have hsum : ∑ i, slotH k (t i) (β i) (Sum.inr j) ≤
      ∑ i, (if t i = Sum.inr j then (1 : ℤ) else 0) :=
    Finset.sum_le_sum fun i _ => (slotH_inr_le k (t i) (β i) j hjk).2
  rw [Finset.sum_boole] at hsum
  have hcard : (Finset.univ.filter fun i => t i = Sum.inr j).card ≤ 1 :=
    Finset.card_le_one.2 fun i hi i' hi' => ht (by
      rw [(Finset.mem_filter.1 hi).2, (Finset.mem_filter.1 hi').2])
  rw [Finsupp.sub_apply, Finsupp.finsetSum_apply]
  by_cases hex : ∃ i, t i = Sum.inr j
  · have := hv₁ hex
    omega
  · push Not at hex
    rw [Finset.filter_eq_empty_iff.2 fun i _ => hex i, Finset.card_empty] at hsum
    push_cast at hsum
    omega

variable {k} in
/-- Dividing a chart exponent of positive `y`-degree by `y_k`, with `k ∈ T`, gives a chart
monomial. -/
theorem isChartLaurent_single_sub_yExp {T : Set (ULift.{u} (Fin n))}
    (hk : (⟨k⟩ : ULift.{u} (Fin n)) ∈ T) {w : (Fin m ⊕ Fin n) →₀ ℤ}
    (hwl : ∀ l, 0 ≤ w (Sum.inl l)) (hw : 1 ≤ yDegree m n w)
    (hwj : ∀ j : Fin n, (⟨j⟩ : ULift.{u} (Fin n)) ∉ T → 0 ≤ w (Sum.inr j)) (r : R) :
    IsChartLaurent T (single (w - yExp m n k) r) := by
  refine isChartLaurent_single ((chartExp_iff T _).2
    ⟨fun l => by simpa [yExp] using hwl l, ?_, fun j hj => ?_⟩) r
  · rw [yDegree_sub, yDegree_yExp]
    omega
  · have hjk : j ≠ k := fun h => hj (h ▸ hk)
    simpa [yExp, Finsupp.single_apply, Ne.symm hjk] using hwj j hj

variable {k} in
/-- **Realisation of the allowed frame coordinates of positive weight.** Every frame coordinate
of positive weight allowed over the charts in `T`, with `k ∈ T`, is a sum of frame coordinates of
generators `c • d g₁ ∧ ⋯ ∧ d g_a` with chart Laurent `c, g_i`, each divisible by `y_k` or with a
factor `d y_k`. -/
theorem single_mem_of_generators (T : Set (ULift.{u} (Fin n))) (hk : (⟨k⟩ : ULift.{u} (Fin n)) ∈ T)
    {a : ℕ} (G : AddSubgroup (FrameIndex m n a →₀ R))
    (hG : ∀ (c : Lau R m n) (g : Fin a → Lau R m n), IsChartLaurent T c →
      (∀ i, IsChartLaurent T (g i)) →
      ((∃ c', IsChartLaurent T c' ∧ c = single (yExp m n k) 1 * c') ∨
        ∃ i, g i = single (yExp m n k) 1) →
      frameCoord R a (c • exteriorPower.ιMulti (Lau R m n) a fun i => frameD (g i)) ∈ G)
    (e : FrameIndex m n a) (he1 : ∀ l, 0 ≤ e.2 (Sum.inl l)) (he2 : 1 ≤ yDegree m n e.2)
    (he3 : frameNeed e ⊆ T) (r : R) : Finsupp.single e r ∈ G := by
  classical
  obtain ⟨S, v⟩ := e
  set t : Fin a → Fin m ⊕ Fin n := fun i => ofLex (Set.powersetCard.ofFinEmbEquiv.symm S i)
  have ht_inj : Function.Injective t := fun i i' h =>
    (Set.powersetCard.ofFinEmbEquiv.symm S).injective (by simpa [t] using h)
  have htS : ∀ i, toLex (t i) ∈ (S : Finset (Lex (Fin m ⊕ Fin n))) := fun i =>
    (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S _).1 ⟨i, rfl⟩
  have h0 : Finsupp.single (S, v) r = frameCoord R a (single v r •
      exteriorPower.ιMulti (Lau R m n) a fun i => (Pi.single (t i) 1 : FrameVec R m n)) :=
    single_eq_frameCoord_smul_ιMulti S v r
  rw [h0, ιMulti_single_eq_sum_slotVec k t, Finset.smul_sum, map_sum]
  refine G.sum_mem fun β _ => ?_
  by_cases hA : ∃ i, ¬slotOk k (t i) (β i)
  · obtain ⟨i, hi⟩ := hA
    rw [(exteriorPower.ιMulti (Lau R m n) a).map_coord_zero i (slotVec_eq_zero k _ _ hi), smul_zero,
      map_zero]
    exact G.zero_mem
  push Not at hA
  set P := Finset.univ.filter fun i => slotH k (t i) (β i) = yExp m n k
  by_cases hB : ∃ i i', i ≠ i' ∧ i ∈ P ∧ i' ∈ P
  · obtain ⟨i, i', hii', hi, hi'⟩ := hB
    rw [(exteriorPower.ιMulti (Lau R m n) a).map_eq_zero_of_eq _ (i := i) (j := i') (by
      rw [slotVec_eq_of_slotH k _ _ (hA i) (Finset.mem_filter.1 hi).2,
        slotVec_eq_of_slotH k _ _ (hA i') (Finset.mem_filter.1 hi').2]) hii', smul_zero, map_zero]
    exact G.zero_mem
  push Not at hB
  have hP : P.card ≤ 1 := Finset.card_le_one.2 fun i hi i' hi' => by
    by_contra h
    exact hB i i' h hi hi'
  rw [ιMulti_slotVec k t β hA, smul_smul, single_mul_single, mul_one, ← sub_eq_add_neg]
  set w := v - ∑ i, slotH k (t i) (β i)
  have hdeg : yDegree m n w = yDegree m n v - P.card := yDegree_sub_sum_slotH k t β v
  have hneed : ∀ j : Fin n, (⟨j⟩ : ULift.{u} (Fin n)) ∉ T →
      0 ≤ v (Sum.inr j) ∧ (toLex (Sum.inr j) ∈ (S : Finset (Lex (Fin m ⊕ Fin n))) →
        1 ≤ v (Sum.inr j)) := fun j hj =>
    ((frameAllowed_iff T ((S, v) : FrameIndex m n a)).1 ⟨he1, by omega, he3⟩).2.2 j hj
  have hwj : ∀ j : Fin n, (⟨j⟩ : ULift.{u} (Fin n)) ∉ T → 0 ≤ w (Sum.inr j) := fun j hj =>
    sub_sum_slotH_inr_nonneg k ht_inj β (fun h => hj (h ▸ hk)) (hneed j hj).1
      fun ⟨i, hi⟩ => (hneed j hj).2 (by rw [← hi]; exact htS i)
  have hwl : ∀ l, 0 ≤ w (Sum.inl l) := fun l => by
    simp [w, slotH_inl, he1 l]
  have he2' : 1 ≤ yDegree m n v := he2
  refine hG _ _ (isChartLaurent_single ((chartExp_iff T _).2 ⟨hwl, by rw [hdeg]; omega, hwj⟩) r)
    (fun i => isChartLaurent_single (chartExp_slotG k T hk _ _) 1) ?_
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hP with hP0 | hP1
  · exact .inl ⟨single (w - yExp m n k) r,
      isChartLaurent_single_sub_yExp hk hwl (by rw [hdeg, hP0]; push_cast; omega) hwj r,
      by rw [single_mul_single, one_mul, add_sub_cancel]⟩
  · right
    obtain ⟨i, hi⟩ := Finset.card_eq_one.1 hP1
    have hiP : i ∈ P := hi ▸ Finset.mem_singleton_self i
    exact ⟨i, by rw [slotG_eq_of_slotH k _ _ (Finset.mem_filter.1 hiP).2]⟩

end Stacks.DeRham.CoordinateCech
