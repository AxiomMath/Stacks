module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.CompletedInducedModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.ProcyclicGroupAlgebra

/-!
# The Koszul resolution over the completed group algebra of a procyclic group

Let `G` be a compact group, `σ ∈ G` generating every finite quotient, `Λ` a ring killed by an
integer `n ≠ 0` such that, for every prime `ℓ ∣ n` and every `e`, `G` has a quotient `G → ℤ/ℓ^e`
with open kernel sending `σ` to `1`, and `M` a `Λ`-module with an action of `G` that is trivial on
an open normal subgroup `U₀`. On the completed induced module `M[[G]] = Λ[[G]] ⊗_Λ M` consider the
`Λ[[G]]`-linear twisted shift `T`, sending `δ_g m` to `δ_{g σ} σ⁻¹ m`, and the additive map
`ε : M[[G]] → M`, `δ_g m ↦ g m`. Then `T - 1` is injective, `ε` is surjective and, for `M` finite,
the image of `T - 1` is the kernel of `ε`: the sequence

`0 → M[[G]] --(T - 1)--> M[[G]] --ε--> M → 0`

is exact. For a finite projective `M` this is a projective resolution of `M` over `Λ[[G]]`, which
computes the derived coinvariants `LH₀(G, M)`.

All names are in the namespace `Stacks.GroupHomology.Procyclic`.

## Main definitions

* `completedShift`: the twisted shift `T` on `M[[G]]`.
* `completedEval`: the map `ε : M[[G]] → M`.

## Main results

* `eq_zero_of_completedShift_eq`: `T - 1` is injective.
* `exists_completedShift_sub_eq`: the image of `T - 1` is the kernel of `ε`, for `M` finite.
* `completedEval_surjective`: `ε` is surjective.

## References

* [Stacks Project, Tag 03VQ](https://stacks.math.columbia.edu/tag/03VQ)
-/

@[expose] public noncomputable section

universe u

namespace Stacks.GroupHomology.Procyclic

open CompletedGroupAlgebra CompletedInduced

/-- A sum over `c n` consecutive integers of an `n`-periodic function is `c` times the sum over `n`
of them. -/
public theorem sum_range_mul_of_periodic {N : Type*} [AddCommMonoid N] (f : ℕ → N) (n c : ℕ)
    (hf : ∀ j, f (j + n) = f j) :
    ∑ j ∈ Finset.range (c * n), f j = c • ∑ j ∈ Finset.range n, f j := by
  have hper : ∀ i j, f (j + i * n) = f j := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => intro j; rw [add_mul, one_mul, ← add_assoc, hf, ih]
  induction c with
  | zero => simp
  | succ c ih =>
    rw [add_mul, one_mul, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [add_comm, hper]

/-! ### Finite level -/

section Finite

variable {H : Type u} [Group H] {M : Type u} [AddCommGroup M] [DistribMulAction H M]

/-- The twisted shift on `M[H]`: `δ_x m ↦ δ_{x s} s⁻¹ m`. -/
public def shift (s : H) : (H →₀ M) →+ (H →₀ M) :=
  (Finsupp.mapDomain.addMonoidHom (· * s)).comp
    (Finsupp.mapRange.addMonoidHom (DistribSMul.toAddMonoidHom M s⁻¹))

/-- The twisted shift sends `δ_x m` to `δ_{x s} s⁻¹ m`. -/
public theorem shift_single (s x : H) (m : M) :
    shift s (Finsupp.single x m) = Finsupp.single (x * s) (s⁻¹ • m) := by
  simp [shift, DistribSMul.toAddMonoidHom]
  rfl

/-- The value of the twisted shift of `f` at `y` is `s⁻¹ f(y s⁻¹)`. -/
public theorem shift_apply (s : H) (f : H →₀ M) (y : H) : shift s f y = s⁻¹ • f (y * s⁻¹) := by
  have : y = y * s⁻¹ * s := by rw [inv_mul_cancel_right]
  conv_lhs => rw [this]
  rw [shift, AddMonoidHom.comp_apply, Finsupp.mapDomain.addMonoidHom_apply,
    Finsupp.mapDomain_apply_of_injective (mul_left_injective s)]
  simp [DistribSMul.toAddMonoidHom]
  rfl

/-- The twisted sum `M[H] → M`, `f ↦ Σ_x x f(x)`. -/
public def twistedSum : (H →₀ M) →+ M :=
  Finsupp.liftAddHom fun x => DistribSMul.toAddMonoidHom M x

/-- The twisted sum of `δ_x m` is `x m`. -/
@[simp]
public theorem twistedSum_single (x : H) (m : M) : twistedSum (Finsupp.single x m) = x • m := by
  simp [twistedSum, DistribSMul.toAddMonoidHom]
  rfl

/-- The twisted sum is invariant under the twisted shift. -/
public theorem twistedSum_shift (s : H) (f : H →₀ M) : twistedSum (shift s f) = twistedSum f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add]
  | single x m => rw [shift_single, twistedSum_single, twistedSum_single, mul_smul,
      smul_inv_smul]

/-- Shifting twice is shifting by the product: `T_a T_b = T_{b a}`. -/
public theorem shift_shift (a b : H) (f : H →₀ M) : shift a (shift b f) = shift (b * a) f := by
  refine Finsupp.ext fun y => ?_
  rw [shift_apply, shift_apply, shift_apply, mul_inv_rev, smul_smul, mul_assoc]

/-- `(T_s - 1) Σ_{j < v} T_{s^j} f = T_{s^v} f - f`. -/
public theorem shift_sub_sum_range (s : H) (f : H →₀ M) (v : ℕ) :
    shift s (∑ j ∈ Finset.range v, shift (s ^ j) f) - ∑ j ∈ Finset.range v, shift (s ^ j) f =
      shift (s ^ v) f - f := by
  rw [map_sum]
  simp_rw [shift_shift, ← pow_succ]
  rw [← Finset.sum_sub_distrib, Finset.sum_range_sub (fun j => shift (s ^ j) f) v, pow_zero]
  congr 1
  refine Finsupp.ext fun y => ?_
  rw [shift_apply, inv_one, one_smul, mul_one]

/-- The sum of the values of a shifted function: `Σ T_s f = s⁻¹ Σ f`. -/
public theorem sum_shift (s : H) (f : H →₀ M) :
    (shift s f).sum (fun _ m => m) = s⁻¹ • f.sum (fun _ m => m) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), hf, hg,
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), smul_add]
  | single x m => rw [shift_single, Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]

variable [Fintype H]

/-- The function `y ↦ y⁻¹ m`. -/
public def constTwisted (m : M) : H →₀ M := ∑ y : H, Finsupp.single y (y⁻¹ • m)

/-- The value of `constTwisted m` at `y` is `y⁻¹ m`. -/
public theorem constTwisted_apply (m : M) (y : H) : constTwisted m y = y⁻¹ • m := by
  classical
  rw [constTwisted, Finsupp.finsetSum_apply, Finset.sum_eq_single y]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- The function `y ↦ y⁻¹ m` is fixed by the twisted shift. -/
public theorem shift_constTwisted (s : H) (m : M) : shift s (constTwisted m) = constTwisted m := by
  refine Finsupp.ext fun y => ?_
  rw [shift_apply, constTwisted_apply, constTwisted_apply, ← mul_smul, mul_inv_rev, inv_inv,
    inv_mul_cancel_left]

variable {s : H} (hs : ∀ h : H, ∃ j : ℕ, h = s ^ j)
include hs

/-- **The kernel of `T - 1` at a finite level** consists of the functions `y ↦ y⁻¹ m`. -/
public theorem eq_constTwisted_of_shift_eq {f : H →₀ M} (hf : shift s f = f) :
    f = constTwisted (f 1) := by
  have hstep : ∀ y : H, (y * s⁻¹) • f (y * s⁻¹) = y • f y := by
    intro y
    conv_rhs => rw [← hf, shift_apply, ← mul_smul]
  have hpow : ∀ (j : ℕ) (y : H), (y * s⁻¹ ^ j) • f (y * s⁻¹ ^ j) = y • f y := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro y
      rw [pow_succ, ← mul_assoc, hstep, ih]
  refine Finsupp.ext fun y => ?_
  rw [constTwisted_apply]
  obtain ⟨j, rfl⟩ := hs y
  have := hpow j (s ^ j)
  rw [inv_pow, mul_inv_cancel, one_smul] at this
  rw [this, inv_smul_smul]

/-- The kernel of `T - 1` is `M`, through the value at `1`. -/
public def kerShiftEquiv : ((shift s - AddMonoidHom.id (H →₀ M)).ker) ≃ M where
  toFun f := (f : H →₀ M) 1
  invFun m := ⟨constTwisted m, by
    rw [AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, shift_constTwisted, AddMonoidHom.id_apply,
      sub_self]⟩
  left_inv f := by
    have hf : shift s (f : H →₀ M) = f := by
      have := f.2
      rwa [AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, AddMonoidHom.id_apply, sub_eq_zero]
        at this
    exact Subtype.ext (eq_constTwisted_of_shift_eq hs hf).symm
  right_inv m := by
    change constTwisted m 1 = m
    rw [constTwisted_apply, inv_one, one_smul]

omit [Fintype H] in
/-- **Exactness at a finite level**: the image of `T - 1` is the kernel of the twisted sum, `M`
being finite. -/
public theorem range_shift_sub_eq_ker [Finite H] [Finite M] :
    (shift s - AddMonoidHom.id (H →₀ M)).range = (twistedSum : (H →₀ M) →+ M).ker := by
  let := Fintype.ofFinite H
  have : Finite (H →₀ M) := Finite.of_equiv _ Finsupp.equivFunOnFinite.symm
  set φ := shift s - AddMonoidHom.id (H →₀ M)
  have hle : φ.range ≤ (twistedSum : (H →₀ M) →+ M).ker := by
    rintro _ ⟨f, rfl⟩
    rw [AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, map_sub, twistedSum_shift,
      AddMonoidHom.id_apply, sub_self]
  refine AddSubgroup.eq_of_le_of_card_ge hle ?_
  have hcard : ∀ {N : Type u} [AddCommGroup N] (ψ : (H →₀ M) →+ N),
      Nat.card (H →₀ M) = Nat.card ψ.range * Nat.card ψ.ker := by
    intro N _ ψ
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ψ.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange ψ).toEquiv]
  have hsurj : Function.Surjective (twistedSum : (H →₀ M) →+ M) := fun m =>
    ⟨Finsupp.single 1 m, by rw [twistedSum_single, one_smul]⟩
  have h2 : Nat.card (twistedSum : (H →₀ M) →+ M).range = Nat.card M := by
    rw [AddMonoidHom.range_eq_top_of_surjective _ hsurj]
    exact Nat.card_congr AddSubgroup.topEquiv.toEquiv
  have h1 := hcard φ
  have h3 := hcard twistedSum
  rw [Nat.card_congr (kerShiftEquiv hs)] at h1
  rw [h2] at h3
  have hM : 0 < Nat.card M := Nat.card_pos
  rw [mul_comm] at h1
  exact (Nat.eq_of_mul_eq_mul_left hM (h1.symm.trans h3)).ge

end Finite

/-! ### The twisted shift on `M[[G]]` -/

section Completed

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Λ : Type u} [Ring Λ] {M : Type u} [AddCommGroup M] [Module Λ M] [DistribMulAction G M]
  [SMulCommClass G Λ M] (σ : G)

/-- The twisted shift at the level `U`: `δ_x m ↦ δ_{x σ̄} σ⁻¹ m`. -/
public def levelShift (U : OpenNormalSubgroup G) :
    (G ⧸ (U : Subgroup G) →₀ M) →+ (G ⧸ (U : Subgroup G) →₀ M) :=
  (Finsupp.mapDomain.addMonoidHom (· * (σ : G ⧸ (U : Subgroup G)))).comp
    (Finsupp.mapRange.addMonoidHom (DistribSMul.toAddMonoidHom M σ⁻¹))

omit [IsTopologicalGroup G] in
/-- The twisted shift at the level `U` sends `δ_x m` to `δ_{x σ̄} σ⁻¹ m`. -/
public theorem levelShift_single (U : OpenNormalSubgroup G) (x : G ⧸ (U : Subgroup G)) (m : M) :
    levelShift σ U (Finsupp.single x m) = Finsupp.single (x * σ) (σ⁻¹ • m) := by
  simp [levelShift, DistribSMul.toAddMonoidHom]
  rfl

omit [IsTopologicalGroup G] in
/-- The twisted shifts at levels `U ≤ V` are compatible with the transition map. -/
public theorem mapDomain_levelShift {U V : OpenNormalSubgroup G} (h : U ≤ V)
    (f : G ⧸ (U : Subgroup G) →₀ M) :
    Finsupp.mapDomain (levelMap h) (levelShift σ U f) =
      levelShift σ V (Finsupp.mapDomain (levelMap h) f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, Finsupp.mapDomain_add, hf, hg, Finsupp.mapDomain_add, map_add]
  | single x m =>
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [levelShift_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single, levelShift_single]
      rfl

omit [IsTopologicalGroup G] in
/-- The twisted shift at the level `U` commutes with the convolution action of `Λ[G/U]`. -/
public theorem levelShift_levelAction (U : OpenNormalSubgroup G)
    (x : MonoidAlgebra Λ (G ⧸ (U : Subgroup G))) (f : G ⧸ (U : Subgroup G) →₀ M) :
    levelShift σ U (levelAction Λ M _ x f) = levelAction Λ M _ x (levelShift σ U f) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, addMonoidEnd_add_apply, map_add, hx, hy,
      addMonoidEnd_add_apply]
  | single h a =>
    rw [levelAction_single, levelAction_single]
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [Finsupp.mapDomain_add, smul_add, map_add, hf, hg]
    | single y m =>
      rw [Finsupp.mapDomain_single, Finsupp.smul_single, levelShift_single, levelShift_single,
        Finsupp.mapDomain_single, Finsupp.smul_single, mul_assoc, smul_comm]


/-- **The twisted shift `T` on `M[[G]]`**, a `Λ[[G]]`-linear map. -/
public def completedShift :
    CompletedInduced Λ G M →ₗ[CompletedGroupAlgebra Λ G] CompletedInduced Λ G M where
  toFun f := CompletedInduced.mk (fun U => levelShift σ U (f.level U)) fun U V h => by
    rw [mapDomain_levelShift, CompletedInduced.mapDomain_level]
  map_add' f g := CompletedInduced.ext fun U => by simp
  map_smul' a f := CompletedInduced.ext fun U => by
    simp only [CompletedInduced.level_mk, CompletedInduced.smul_level, RingHom.id_apply]
    exact levelShift_levelAction σ U _ _

omit [IsTopologicalGroup G] in
/-- The component at `U` of `T f` is the twisted shift of the component of `f` at `U`. -/
@[simp]
public theorem completedShift_level (f : CompletedInduced Λ G M) (U : OpenNormalSubgroup G) :
    (completedShift σ f).level U = levelShift σ U (f.level U) :=
  rfl

end Completed


/-! ### Levels and the evaluation `ε` -/

section Levels

variable {G : Type u} [Group G] [TopologicalSpace G] {M : Type u} [AddCommGroup M]

/-- Pushing forward along `G/U → G/V → G/W` is pushing forward along `G/U → G/W`. -/
public theorem mapDomain_levelMap_levelMap {U V W : OpenNormalSubgroup G} (h₁ : U ≤ V)
    (h₂ : V ≤ W) (f : G ⧸ (U : Subgroup G) →₀ M) :
    Finsupp.mapDomain (levelMap h₂) (Finsupp.mapDomain (levelMap h₁) f) =
      Finsupp.mapDomain (levelMap (h₁.trans h₂)) f := by
  rw [← Finsupp.mapDomain_comp]
  congr 1
  funext x
  induction x using QuotientGroup.induction_on with
  | H g => rfl

variable [DistribMulAction G M]

/-- The quotient `G/U` acting on `M`, for `U` acting trivially. -/
@[instance_reducible]
public def levelDistribMulAction (U : OpenNormalSubgroup G) (hU : ∀ g ∈ U, ∀ m : M, g • m = m) :
    DistribMulAction (G ⧸ (U : Subgroup G)) M :=
  DistribMulAction.compHom M (quotientAction M U hU)

/-- The coset `gU` acts on `M` as `g`. -/
public theorem levelDistribMulAction_smul (U : OpenNormalSubgroup G)
    (hU : ∀ g ∈ U, ∀ m : M, g • m = m) (g : G) (m : M) :
    (letI := levelDistribMulAction U hU; (g : G ⧸ (U : Subgroup G)) • m) = g • m :=
  quotientAction_mk M U hU g m

/-- The twisted sum `M[G/U] → M`, `δ_x m ↦ x m`, for `U` acting trivially on `M`. -/
public def levelEval (U : OpenNormalSubgroup G) (hU : ∀ g ∈ U, ∀ m : M, g • m = m) :
    (G ⧸ (U : Subgroup G) →₀ M) →+ M :=
  letI := levelDistribMulAction U hU
  twistedSum

/-- The twisted sum at the level `U` sends `δ_{gU} m` to `g m`. -/
@[simp]
public theorem levelEval_single (U : OpenNormalSubgroup G) (hU : ∀ g ∈ U, ∀ m : M, g • m = m)
    (g : G) (m : M) : levelEval U hU (Finsupp.single (g : G ⧸ (U : Subgroup G)) m) = g • m := by
  let := levelDistribMulAction U hU
  rw [levelEval, twistedSum_single]
  exact levelDistribMulAction_smul U hU g m

/-- The twisted sum is compatible with the transition maps. -/
public theorem levelEval_mapDomain {U V : OpenNormalSubgroup G} (h : U ≤ V)
    (hV : ∀ g ∈ V, ∀ m : M, g • m = m) (f : G ⧸ (U : Subgroup G) →₀ M) :
    levelEval V hV (Finsupp.mapDomain (levelMap h) f) =
      levelEval U (fun g hg => hV g (h hg)) f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [Finsupp.mapDomain_add, map_add, map_add, hf, hg]
  | single x m =>
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [Finsupp.mapDomain_single]
      exact (levelEval_single V hV g m).trans (levelEval_single U _ g m).symm

/-- The twisted sum for the action of `G/U` on `M` is `levelEval U hU`. -/
public theorem twistedSum_eq_levelEval (U : OpenNormalSubgroup G)
    (hU : ∀ g ∈ U, ∀ m : M, g • m = m) :
    (letI := levelDistribMulAction U hU; (twistedSum : (G ⧸ (U : Subgroup G) →₀ M) →+ M)) =
      levelEval U hU := by
  rfl

/-- The twisted sum at the level `U` is invariant under the twisted shift. -/
public theorem levelEval_levelShift (σ : G) (U : OpenNormalSubgroup G)
    (hU : ∀ g ∈ U, ∀ m : M, g • m = m) (f : G ⧸ (U : Subgroup G) →₀ M) :
    levelEval U hU (levelShift σ U f) = levelEval U hU f := by
  let := levelDistribMulAction U hU
  rw [← twistedSum_eq_levelEval]
  exact twistedSum_shift (σ : G ⧸ (U : Subgroup G)) f

end Levels

/-! ### The kernel of `T - 1` dies at deep levels -/

section Deep

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {Λ : Type u} [Ring Λ] {M : Type u} [AddCommGroup M] [Module Λ M] [DistribMulAction G M]
  {σ : G} (hgen : GeneratesQuotients σ)
  {U₀ : OpenNormalSubgroup G} (hU₀ : ∀ g ∈ U₀, ∀ m : M, g • m = m)
include hgen hU₀

/-- A function on `G/W` fixed by the twisted shift is pushed to zero on any level `V ≤ U₀` with `W`
deep below `V`. -/
public theorem mapDomain_eq_zero_of_levelShift_eq {V W : OpenNormalSubgroup G}
    (hV : V ≤ U₀) (hW : IsDeep Λ σ V W) {f : G ⧸ (W : Subgroup G) →₀ M}
    (hf : levelShift σ W f = f) : Finsupp.mapDomain (levelMap hW.1) f = 0 := by
  classical
  let := Fintype.ofFinite (G ⧸ (W : Subgroup G))
  have hWU : ∀ g ∈ W, ∀ m : M, g • m = m := fun g hg => hU₀ g (hV (hW.1 hg))
  let := levelDistribMulAction W hWU
  have hs : ∀ h : G ⧸ (W : Subgroup G), ∃ j : ℕ, h = (σ : G ⧸ (W : Subgroup G)) ^ j :=
    exists_eq_pow hgen W
  have hf' : shift (σ : G ⧸ (W : Subgroup G)) f = f := hf
  have hW' := hW
  obtain ⟨hWV, c, hc, hca⟩ := hW'
  set m := f 1
  set F : ℕ → (G ⧸ (V : Subgroup G) →₀ M) :=
    fun i => Finsupp.single ((σ : G ⧸ (V : Subgroup G)) ^ i) ((σ ^ i)⁻¹ • m) with hF
  have hterm : ∀ i : ℕ, Finsupp.mapDomain (levelMap hW.1)
      (Finsupp.single ((σ : G ⧸ (W : Subgroup G)) ^ i) (((σ : G ⧸ (W : Subgroup G)) ^ i)⁻¹ • m)) =
      F i := by
    intro i
    rw [Finsupp.mapDomain_single, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_inv,
      levelDistribMulAction_smul]
    rfl
  have hper : ∀ j : ℕ, F (j + orderOf (σ : G ⧸ (V : Subgroup G))) = F j := by
    intro j
    have hmem : σ ^ orderOf (σ : G ⧸ (V : Subgroup G)) ∈ (V : Subgroup G) := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, pow_orderOf_eq_one]
    rw [hF]
    beta_reduce
    rw [pow_add, pow_orderOf_eq_one, mul_one, pow_add, mul_inv_rev, mul_smul,
      hU₀ _ (hV ((V : Subgroup G).inv_mem hmem))]
  have hcM : ∀ x : G ⧸ (V : Subgroup G) →₀ M, c • x = 0 := by
    intro x
    refine Finsupp.ext fun y => ?_
    rw [Finsupp.smul_apply, Finsupp.coe_zero, Pi.zero_apply, ← one_smul Λ (x y), ← smul_assoc,
      hca, zero_smul]
  rw [eq_constTwisted_of_shift_eq hs hf', constTwisted, Finsupp.mapDomain_finsetSum,
    sum_univ_eq_sum_range hs]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  have hrange : Finset.range (orderOf (σ : G ⧸ (W : Subgroup G))) =
      Finset.range (c * orderOf (σ : G ⧸ (V : Subgroup G))) := by rw [hc]
  rw [hrange, sum_range_mul_of_periodic F _ c hper, hcM]

/-- Two solutions of `(T - 1) z = x` at a level `W` deep below `V ≤ U₀` have the same image at `V`.
-/
public theorem mapDomain_eq_of_levelShift_sub_eq {V W : OpenNormalSubgroup G}
    (hV : V ≤ U₀) (hW : IsDeep Λ σ V W) {z z' : G ⧸ (W : Subgroup G) →₀ M}
    (h : levelShift σ W z - z = levelShift σ W z' - z') :
    Finsupp.mapDomain (levelMap hW.1) z = Finsupp.mapDomain (levelMap hW.1) z' := by
  have hd : levelShift σ W (z - z') = z - z' :=
    (map_sub _ _ _).trans (sub_eq_sub_iff_sub_eq_sub.1 h)
  rw [← sub_eq_zero, ← Finsupp.mapDomain_sub]
  exact mapDomain_eq_zero_of_levelShift_eq hgen hU₀ hV hW hd

end Deep

/-! ### Exactness on `M[[G]]` -/

section Exactness

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {Λ : Type u} [Ring Λ] {M : Type u} [AddCommGroup M] [Module Λ M] [DistribMulAction G M]
  [SMulCommClass G Λ M] {σ : G} (hgen : GeneratesQuotients σ)
  {U₀ : OpenNormalSubgroup G} (hU₀ : ∀ g ∈ U₀, ∀ m : M, g • m = m)

variable (U₀) in
/-- **The evaluation `ε : M[[G]] → M`**, `δ_g m ↦ g m`, computed at the level `U₀`. -/
public def completedEval : CompletedInduced Λ G M →+ M where
  toFun f := levelEval U₀ hU₀ (f.level U₀)
  map_zero' := by simp
  map_add' f g := by rw [CompletedInduced.level_add, map_add]

omit [IsTopologicalGroup G] [CompactSpace G] [SMulCommClass G Λ M] in
/-- The evaluation may be computed at any level `U ≤ U₀`. -/
public theorem completedEval_eq (f : CompletedInduced Λ G M) {U : OpenNormalSubgroup G}
    (hU : U ≤ U₀) :
    completedEval U₀ hU₀ f = levelEval U (fun g hg => hU₀ g (hU hg)) (f.level U) := by
  change levelEval U₀ hU₀ (f.level U₀) = _
  rw [← CompletedInduced.mapDomain_level hU, levelEval_mapDomain]

omit [IsTopologicalGroup G] [CompactSpace G] [SMulCommClass G Λ M] in
/-- `ε` sends `δ_g m` to `g m`. -/
@[simp]
public theorem completedEval_single (g : G) (m : M) :
    completedEval U₀ hU₀ (CompletedInduced.single (Λ := Λ) g m) = g • m := by
  change levelEval U₀ hU₀ (Finsupp.single _ m) = _
  exact levelEval_single U₀ hU₀ g m

omit [IsTopologicalGroup G] [CompactSpace G] in
/-- `ε` is invariant under the twisted shift `T`. -/
public theorem completedEval_completedShift (f : CompletedInduced Λ G M) :
    completedEval U₀ hU₀ (completedShift σ f) = completedEval U₀ hU₀ f :=
  levelEval_levelShift σ U₀ hU₀ (f.level U₀)

omit [IsTopologicalGroup G] [CompactSpace G] [SMulCommClass G Λ M] in
/-- `ε` is surjective. -/
public theorem completedEval_surjective : Function.Surjective (completedEval (Λ := Λ) U₀ hU₀) :=
  fun m => ⟨CompletedInduced.single 1 m, by rw [completedEval_single, one_smul]⟩

include hgen hU₀

omit [SMulCommClass G Λ M] in
/-- A solution of `(T - 1) z = f_W` at a level `W ≤ U₀`, for `ε(f) = 0`. -/
public theorem exists_levelShift_sub_eq [Finite M] {f : CompletedInduced Λ G M}
    (hf : completedEval U₀ hU₀ f = 0) {W : OpenNormalSubgroup G} (hW : W ≤ U₀) :
    ∃ z, levelShift σ W z - z = f.level W := by
  have hWU : ∀ g ∈ W, ∀ m : M, g • m = m := fun g hg => hU₀ g (hW hg)
  let := levelDistribMulAction W hWU
  let := Fintype.ofFinite (G ⧸ (W : Subgroup G))
  have hs : ∀ h : G ⧸ (W : Subgroup G), ∃ j : ℕ, h = (σ : G ⧸ (W : Subgroup G)) ^ j :=
    exists_eq_pow hgen W
  have hmem : f.level W ∈ (twistedSum : (G ⧸ (W : Subgroup G) →₀ M) →+ M).ker := by
    rw [AddMonoidHom.mem_ker, twistedSum_eq_levelEval, ← completedEval_eq hU₀ f hW, hf]
  rw [← range_shift_sub_eq_ker hs] at hmem
  obtain ⟨z, hz⟩ := hmem
  exact ⟨z, hz⟩

variable {n : ℕ} (hn : n ≠ 0) (hpow : ∀ p : ℕ, p.Prime → p ∣ n → HasPrimePowerQuotients σ p)
  (hΛ : ∀ a : Λ, n • a = 0)
include hn hpow hΛ

/-- **`T - 1` is injective on `M[[G]]`.** -/
public theorem eq_zero_of_completedShift_eq {f : CompletedInduced Λ G M}
    (hf : completedShift σ f = f) : f = 0 := by
  refine CompletedInduced.ext fun U => ?_
  obtain ⟨W, hW⟩ := exists_isDeep hn hpow hΛ (U ⊓ U₀)
  have hfW : levelShift σ W (f.level W) = f.level W := by
    rw [← completedShift_level, hf]
  have h0 := mapDomain_eq_zero_of_levelShift_eq hgen hU₀ inf_le_right hW hfW
  rw [CompletedInduced.mapDomain_level] at h0
  rw [CompletedInduced.level_zero, ← CompletedInduced.mapDomain_level (inf_le_left : U ⊓ U₀ ≤ U),
    h0, Finsupp.mapDomain_zero]

/-- **The image of `T - 1` is the kernel of `ε`**, for `M` finite. -/
public theorem exists_completedShift_sub_eq [Finite M] {f : CompletedInduced Λ G M}
    (hf : completedEval U₀ hU₀ f = 0) :
    ∃ g : CompletedInduced Λ G M, completedShift σ g - g = f := by
  classical
  choose V hV using fun U : OpenNormalSubgroup G => exists_isDeep (σ := σ) hn hpow hΛ (U ⊓ U₀)
  have hV₀ : ∀ U, V U ≤ U₀ := fun U => (hV U).1.trans inf_le_right
  have hVU : ∀ U, V U ≤ U := fun U => (hV U).1.trans inf_le_left
  choose z hz using fun U => exists_levelShift_sub_eq hgen hU₀ hf (hV₀ U)
  let y : ∀ U : OpenNormalSubgroup G, G ⧸ (U : Subgroup G) →₀ M :=
    fun U => Finsupp.mapDomain (levelMap (hVU U)) (z U)
  have hpush : ∀ {X Y : OpenNormalSubgroup G} (h : X ≤ Y) (t : G ⧸ (X : Subgroup G) →₀ M),
      levelShift σ X t - t = f.level X →
      levelShift σ Y (Finsupp.mapDomain (levelMap h) t) - Finsupp.mapDomain (levelMap h) t =
        f.level Y := by
    intro X Y h t ht
    rw [← mapDomain_levelShift, ← Finsupp.mapDomain_sub, ht, CompletedInduced.mapDomain_level]
  have key : ∀ (U W : OpenNormalSubgroup G) (hW : IsDeep Λ σ (U ⊓ U₀) W)
      (t : G ⧸ (W : Subgroup G) →₀ M), levelShift σ W t - t = f.level W →
      Finsupp.mapDomain (levelMap (hW.1.trans inf_le_left)) t = y U := by
    intro U W hW t ht
    let T := W ⊓ V U
    have hTW : T ≤ W := inf_le_left
    have hTV : T ≤ V U := inf_le_right
    obtain ⟨s, hs⟩ := exists_levelShift_sub_eq hgen hU₀ hf (hTV.trans (hV₀ U))
    have h1 : Finsupp.mapDomain (levelMap hW.1) t =
        Finsupp.mapDomain (levelMap hW.1) (Finsupp.mapDomain (levelMap hTW) s) :=
      mapDomain_eq_of_levelShift_sub_eq hgen hU₀ inf_le_right hW
        (by rw [ht, hpush hTW s hs])
    have h2 : Finsupp.mapDomain (levelMap (hV U).1) (z U) =
        Finsupp.mapDomain (levelMap (hV U).1) (Finsupp.mapDomain (levelMap hTV) s) :=
      mapDomain_eq_of_levelShift_sub_eq hgen hU₀ inf_le_right (hV U)
        (by rw [hz, hpush hTV s hs])
    have e1 := congrArg (Finsupp.mapDomain (levelMap (inf_le_left : U ⊓ U₀ ≤ U))) h1
    have e2 := congrArg (Finsupp.mapDomain (levelMap (inf_le_left : U ⊓ U₀ ≤ U))) h2
    simp only [mapDomain_levelMap_levelMap] at e1 e2
    change _ = Finsupp.mapDomain (levelMap (hVU U)) (z U)
    rw [e1, e2]
  refine ⟨CompletedInduced.mk y fun U U' hUU' => ?_, CompletedInduced.ext fun U => ?_⟩
  · let W := V U ⊓ V U'
    have hWU : IsDeep Λ σ (U ⊓ U₀) W := (hV U).mono inf_le_left
    have hWU' : IsDeep Λ σ (U' ⊓ U₀) W := (hV U').mono inf_le_right
    obtain ⟨t, ht⟩ := exists_levelShift_sub_eq hgen hU₀ hf
      ((inf_le_left : W ≤ V U).trans (hV₀ U))
    rw [← key U W hWU t ht, ← key U' W hWU' t ht, mapDomain_levelMap_levelMap]
  · change levelShift σ U (y U) - y U = f.level U
    exact hpush (hVU U) (z U) (hz U)

end Exactness

end Stacks.GroupHomology.Procyclic

end
