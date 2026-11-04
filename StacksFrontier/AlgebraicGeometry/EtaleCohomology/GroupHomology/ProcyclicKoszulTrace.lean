module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.SingleHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.ProcyclicKoszul
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.ProcyclicTrivialTrace

/-!
# The trace on the derived coinvariants of a procyclic group

Let `Γ` be a topological group, `G` a compact normal subgroup and `σ ∈ G` an element generating
every finite quotient of `G`; let `Λ` be a ring killed by an integer `n ≠ 0` such that `G` has the
`ℓ`-power quotients of `Ẑ` for every prime `ℓ ∣ n`. For a finite projective `Λ`-module `V` with an
action of `Γ` that is trivial on an open normal subgroup `U₀` of `G`, the sequence

`0 → V[[G]] --(T - 1)--> V[[G]] --ε--> V → 0`

of `Stacks.GroupHomology.Procyclic.completedShift` is a projective resolution of `V` over
`Λ[[G]]`. Its coinvariants are the complex `V --(σ⁻¹ - 1)--> V`, and `γ ∈ Γ` acts on them by `γ`
in degree `0` and by `Σ_{j < v} σ^{-j} γ` in degree `1`, where `γ σ γ⁻¹ ≡ σ^v` modulo an open
normal subgroup `W ≤ U₀` lying deep below `U₀` for `Λ`. Hence

`Tr(γ | LH₀(G, V)) = Tr(γ | V) - Σ_{j < v} Tr(σ^{-j} γ | V)` in `Λ^♮`.

## Main definitions

* `Stacks.GroupHomology.Procyclic.completedConj`: conjugation by `γ` on `V[[G]]`.
* `Stacks.GroupHomology.Procyclic.shiftKoszulResolution`: the projective resolution.
* `Stacks.GroupHomology.Procyclic.shiftKoszulLift`: the lift of the action of `γ` to it.

## Main results

* `Stacks.GroupHomology.Procyclic.shiftKoszulπ_quasiIso`: the Koszul complex resolves `V`.
* `Stacks.GroupHomology.Procyclic.isPerfect_derivedCoinvariants`: `LH₀(G, V)` is perfect.
* `Stacks.GroupHomology.Procyclic.perfectDerivedTrace_derivedCoinvariantsAction`: the trace.

## References

* [Stacks Project, Tag 03VQ](https://stacks.math.columbia.edu/tag/03VQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.GroupHomology.Procyclic

open CompletedGroupAlgebra CompletedInduced

attribute [local instance] HasDerivedCategory.standard

/-- An additive map of finitely supported functions that multiplies the sum of the values of
each `single` by `c` multiplies the sum of the values of every function by `c`. -/
private theorem sum_eq_smul_of_single {Γ V α β : Type*} [Monoid Γ] [AddCommGroup V]
    [DistribMulAction Γ V] (φ : (α →₀ V) →+ (β →₀ V)) (c : Γ)
    (h : ∀ (a : α) (m : V), (φ (Finsupp.single a m)).sum (fun _ m => m) = c • m)
    (f : α →₀ V) : (φ f).sum (fun _ m => m) = c • f.sum (fun _ m => m) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), hf, hg,
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), smul_add]
  | single x m => rw [h, Finsupp.sum_single_index rfl]

/-! ### Conjugation on `V[[G]]` -/

section Conj

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {G : Subgroup Γ}
  [G.Normal] {Λ : Type u} [Ring Λ] {V : Type u} [AddCommGroup V] [Module Λ V]
  [DistribMulAction Γ V] [SMulCommClass Γ Λ V] (γ : Γ)

/-- Conjugation by `γ` at finite levels: `δ_x m ↦ δ_{γ x γ⁻¹} γ m`, from `G/U'` to `G/U` when
`γ U' γ⁻¹ ≤ U`. -/
public def levelConj {U' U : OpenNormalSubgroup G}
    (h : ∀ g ∈ U', (conjContinuousMulEquiv G γ : G →* G) g ∈ U) :
    (G ⧸ (U' : Subgroup G) →₀ V) →+ (G ⧸ (U : Subgroup G) →₀ V) :=
  (Finsupp.mapDomain.addMonoidHom
      (QuotientGroup.map _ _ (conjContinuousMulEquiv G γ : G →* G) h)).comp
    (Finsupp.mapRange.addMonoidHom (DistribSMul.toAddMonoidHom V γ))

/-- At finite levels, conjugation by `γ` sends `δ_g m` to `δ_{γ g γ⁻¹} (γ m)`. -/
public theorem levelConj_single {U' U : OpenNormalSubgroup G}
    (h : ∀ g ∈ U', (conjContinuousMulEquiv G γ : G →* G) g ∈ U) (g : G) (m : V) :
    levelConj γ h (Finsupp.single (g : G ⧸ (U' : Subgroup G)) m) =
      Finsupp.single (conjContinuousMulEquiv G γ g : G ⧸ (U : Subgroup G)) (γ • m) := by
  simp [levelConj, DistribSMul.toAddMonoidHom]
  rfl

/-- Conjugation from `G/U'` after the transition map `G/U'' → G/U'` is conjugation from `G/U''`. -/
public theorem levelConj_mapDomain {U'' U' U : OpenNormalSubgroup G} (h₁ : U'' ≤ U')
    (h : ∀ g ∈ U', (conjContinuousMulEquiv G γ : G →* G) g ∈ U) (f : G ⧸ (U'' : Subgroup G) →₀ V) :
    levelConj γ h (Finsupp.mapDomain (levelMap h₁) f) =
      levelConj γ (fun g hg => h g (h₁ hg)) f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [Finsupp.mapDomain_add, map_add, map_add, hf, hg]
  | single x m =>
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [Finsupp.mapDomain_single]
      exact (levelConj_single γ h g m).trans (levelConj_single γ _ g m).symm

/-- Conjugation to `G/U` followed by the transition map `G/U → G/W` is conjugation to `G/W`. -/
public theorem mapDomain_levelConj {U' U W : OpenNormalSubgroup G} (h₁ : U ≤ W)
    (h : ∀ g ∈ U', (conjContinuousMulEquiv G γ : G →* G) g ∈ U) (f : G ⧸ (U' : Subgroup G) →₀ V) :
    Finsupp.mapDomain (levelMap h₁) (levelConj γ h f) =
      levelConj γ (fun g hg => h₁ (h g hg)) f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, Finsupp.mapDomain_add, hf, hg, map_add]
  | single x m =>
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [levelConj_single, levelConj_single, Finsupp.mapDomain_single]
      rfl

/-- The level `γ⁻¹ U γ` from which conjugation maps to the level `U`. -/
public abbrev conjLevel (U : OpenNormalSubgroup G) : OpenNormalSubgroup G :=
  comapSubgroup (conjContinuousMulEquiv G γ : G →* G)
    (continuous_coe_monoidHom (conjContinuousMulEquiv G γ)) U

/-- Conjugation by `γ` maps `conjLevel γ U` into `U`. -/
public theorem conj_mem_of_mem_conjLevel (U : OpenNormalSubgroup G) :
    ∀ g ∈ conjLevel γ U, (conjContinuousMulEquiv G γ : G →* G) g ∈ U :=
  map_mem_of_mem_comapSubgroup _ _ U



/-- **Conjugation by `γ` on `V[[G]]`**: `δ_g m ↦ δ_{γ g γ⁻¹} γ m`. -/
public def completedConj : CompletedInduced Λ G V →+ CompletedInduced Λ G V where
  toFun f := CompletedInduced.mk
    (fun U => levelConj γ (conj_mem_of_mem_conjLevel γ U) (f.level (conjLevel γ U)))
    fun U W h => by
      rw [mapDomain_levelConj]
      have hle : conjLevel γ U ⊓ conjLevel γ W ≤ conjLevel γ U := inf_le_left
      have hle' : conjLevel γ U ⊓ conjLevel γ W ≤ conjLevel γ W := inf_le_right
      rw [← CompletedInduced.mapDomain_level hle, ← CompletedInduced.mapDomain_level hle',
        levelConj_mapDomain, levelConj_mapDomain]
  map_zero' := CompletedInduced.ext fun U => by simp
  map_add' f g := CompletedInduced.ext fun U => by simp

omit [SMulCommClass Γ Λ V] in
/-- The conjugate may be computed from any level `U'` with `γ U' γ⁻¹ ≤ U`. -/
public theorem completedConj_level (f : CompletedInduced Λ G V) {U' U : OpenNormalSubgroup G}
    (h : ∀ g ∈ U', (conjContinuousMulEquiv G γ : G →* G) g ∈ U) :
    (completedConj γ f).level U = levelConj γ h (f.level U') := by
  show levelConj γ (conj_mem_of_mem_conjLevel γ U) (f.level (conjLevel γ U)) = _
  have hle : U' ⊓ conjLevel γ U ≤ U' := inf_le_left
  have hle' : U' ⊓ conjLevel γ U ≤ conjLevel γ U := inf_le_right
  rw [← CompletedInduced.mapDomain_level hle, ← CompletedInduced.mapDomain_level hle',
    levelConj_mapDomain, levelConj_mapDomain]

omit [SMulCommClass Γ Λ V] in
/-- Conjugation by `γ` sends `δ_g m` to `δ_{γ g γ⁻¹} (γ m)` in `V[[G]]`. -/
public theorem completedConj_single (g : G) (m : V) :
    completedConj (Λ := Λ) γ (CompletedInduced.single g m) =
      CompletedInduced.single (conjContinuousMulEquiv G γ g) (γ • m) :=
  CompletedInduced.ext fun U => by
    rw [completedConj_level γ _ (conj_mem_of_mem_conjLevel γ U), level_single, level_single,
      levelConj_single]

/-- At finite levels, conjugation by `γ` is semilinear for the conjugation of `Λ[G/U']`. -/
public theorem levelConj_levelAction {U' U : OpenNormalSubgroup G}
    (h : ∀ g ∈ U', (conjContinuousMulEquiv G γ : G →* G) g ∈ U)
    (x : MonoidAlgebra Λ (G ⧸ (U' : Subgroup G))) (f : G ⧸ (U' : Subgroup G) →₀ V) :
    levelConj γ h (levelAction Λ V _ x f) =
      levelAction Λ V _ (quotientMapAlgebra (conjContinuousMulEquiv G γ : G →* G) h x)
        (levelConj γ h f) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, addMonoidEnd_add_apply, map_add, hx, hy, map_add, map_add,
      addMonoidEnd_add_apply]
  | single q a =>
    induction q using QuotientGroup.induction_on with
    | H k =>
      rw [levelAction_single, quotientMapAlgebra_single, levelAction_single]
      induction f using Finsupp.induction_linear with
      | zero => simp
      | add f g hf hg => simp only [Finsupp.mapDomain_add, smul_add, map_add, hf, hg]
      | single x m =>
        induction x using QuotientGroup.induction_on with
        | H g =>
          rw [Finsupp.mapDomain_single, Finsupp.smul_single, ← QuotientGroup.mk_mul,
            levelConj_single, levelConj_single, Finsupp.mapDomain_single, Finsupp.smul_single,
            smul_comm γ a m]
          congr 1
          rw [← QuotientGroup.mk_mul, map_mul]
          rfl

/-- Conjugation by `γ` is semilinear for the automorphism `σ_γ` of `Λ[[G]]`. -/
public theorem completedConj_smul (a : CompletedGroupAlgebra Λ G) (f : CompletedInduced Λ G V) :
    completedConj γ (a • f) = mapRingEquiv (conjContinuousMulEquiv G γ) a • completedConj γ f := by
  refine CompletedInduced.ext fun U => ?_
  rw [completedConj_level γ _ (conj_mem_of_mem_conjLevel γ U), smul_level, smul_level,
    completedConj_level γ _ (conj_mem_of_mem_conjLevel γ U), levelConj_levelAction,
    mapRingEquiv_apply, eval_map _ _ (conj_mem_of_mem_conjLevel γ U)]

/-- Conjugation by `γ` on `V[[G]]`, as a morphism `V[[G]] ⟶ σ_γ^* V[[G]]` of `Λ[[G]]`-modules. -/
public def completedConjHom :
    ModuleCat.of (CompletedGroupAlgebra Λ G) (CompletedInduced Λ G V) ⟶
      (twistFunctor Λ (conjContinuousMulEquiv G γ)).obj
        (ModuleCat.of (CompletedGroupAlgebra Λ G) (CompletedInduced Λ G V)) :=
  ModuleCat.semilinearMapAddEquiv _ _ _
    { toFun := fun f => (completedConj γ f : CompletedInduced Λ G V)
      map_add' := fun f g => map_add (completedConj γ) f g
      map_smul' := completedConj_smul γ }

/-- `completedConjHom γ` is conjugation by `γ`. -/
public theorem completedConjHom_apply (f : CompletedInduced Λ G V) :
    (completedConjHom (Λ := Λ) γ).hom f = (completedConj γ f : CompletedInduced Λ G V) :=
  rfl

omit [SMulCommClass Γ Λ V] in
/-- `Σ (γ f) = γ Σ f`. -/
public theorem sumValues_completedConj (f : CompletedInduced Λ G V) :
    sumValues Λ G V (completedConj γ f) = γ • sumValues Λ G V f := by
  rw [sumValues_eq _ topSubgroup, completedConj_level γ f (conj_mem_of_mem_conjLevel γ topSubgroup),
    sumValues_eq _ (conjLevel γ topSubgroup)]
  refine sum_eq_smul_of_single _ γ (fun x m => ?_) _
  induction x using QuotientGroup.induction_on with
  | H g => rw [levelConj_single, Finsupp.sum_single_index rfl]

/-- Conjugation intertwines the twisted shifts by `σ` and by `γ σ γ⁻¹`. -/
public theorem levelConj_levelShift (σ : G) {U' U : OpenNormalSubgroup G}
    (h : ∀ g ∈ U', (conjContinuousMulEquiv G γ : G →* G) g ∈ U) (f : G ⧸ (U' : Subgroup G) →₀ V) :
    levelConj γ h (levelShift σ U' f) =
      levelShift (conjContinuousMulEquiv G γ σ) U (levelConj γ h f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add, map_add]
  | single x m =>
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [levelShift_single, levelConj_single, levelShift_single, ← QuotientGroup.mk_mul,
        levelConj_single, map_mul, QuotientGroup.mk_mul]
      congr 1
      show γ • ((σ : Γ)⁻¹ • m) = ((γ * σ * γ⁻¹)⁻¹ : Γ) • γ • m
      rw [smul_smul, smul_smul]
      congr 1
      simp [mul_assoc]

end Conj

/-! ### Levels: the evaluation, the shifts and conjugation -/

/-- The level of a difference is the difference of the levels. -/
@[simp]
public theorem completedInduced_level_sub {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {Λ : Type u} [Ring Λ] {M : Type u} [AddCommGroup M] [Module Λ M]
    (f g : CompletedInduced Λ G M) (U : OpenNormalSubgroup G) :
    (f - g).level U = f.level U - g.level U :=
  rfl

section LevelLemmas

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {G : Subgroup Γ}
  [G.Normal] {Λ : Type u} [Ring Λ] {V : Type u} [AddCommGroup V] [Module Λ V]
  [DistribMulAction Γ V] [SMulCommClass Γ Λ V]

omit [IsTopologicalGroup Γ] [G.Normal] in
/-- The twisted sum is `Λ[G/U]`-linear. -/
public theorem levelEval_levelAction (U : OpenNormalSubgroup G)
    (hU : ∀ g ∈ U, ∀ m : V, g • m = m) (x : MonoidAlgebra Λ (G ⧸ (U : Subgroup G)))
    (f : G ⧸ (U : Subgroup G) →₀ V) :
    levelEval U hU (levelAction Λ V _ x f) = quotientAlgebraAction V U hU x (levelEval U hU f) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, addMonoidEnd_add_apply, map_add, hx, hy, map_add,
      addMonoidEnd_add_apply]
  | single q a =>
    induction q using QuotientGroup.induction_on with
    | H h =>
      rw [levelAction_single]
      induction f using Finsupp.induction_linear with
      | zero => simp
      | add f g hf hg => rw [Finsupp.mapDomain_add, smul_add, map_add, hf, hg, map_add, map_add]
      | single y m =>
        induction y using QuotientGroup.induction_on with
        | H g =>
          rw [Finsupp.mapDomain_single, Finsupp.smul_single, ← QuotientGroup.mk_mul,
            levelEval_single, levelEval_single, quotientAlgebraAction_single, mul_smul,
            smul_comm g a m, smul_comm h a]

/-- Conjugation and the twisted sum. -/
public theorem levelEval_levelConj (γ : Γ) {U' U : OpenNormalSubgroup G}
    (h : ∀ g ∈ U', (conjContinuousMulEquiv G γ : G →* G) g ∈ U)
    (hU : ∀ g ∈ U, ∀ m : V, g • m = m) (hU' : ∀ g ∈ U', ∀ m : V, g • m = m)
    (f : G ⧸ (U' : Subgroup G) →₀ V) :
    levelEval U hU (levelConj γ h f) = γ • levelEval U' hU' f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add, smul_add]
  | single x m =>
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [levelConj_single, levelEval_single, levelEval_single]
      show (γ * g * γ⁻¹ : Γ) • γ • m = γ • (g : Γ) • m
      rw [smul_smul, smul_smul, inv_mul_cancel_right]

omit [IsTopologicalGroup Γ] [G.Normal] in
/-- The twisted shift at a level `W` acting trivially is the shift of `G/W`. -/
public theorem levelShift_eq_shift (x : G) (W : OpenNormalSubgroup G)
    (hW : ∀ g ∈ W, ∀ m : V, g • m = m) :
    levelShift (M := V) x W =
      (letI := levelDistribMulAction W hW; shift (x : G ⧸ (W : Subgroup G))) := by
  let := levelDistribMulAction W hW
  refine Finsupp.addHom_ext fun y m => ?_
  rw [levelShift_single, shift_single, ← QuotientGroup.mk_inv, levelDistribMulAction_smul]

omit [IsTopologicalGroup Γ] [G.Normal] in
/-- `(T_σ - 1) Σ_{j < v} T_{σ^j} f = T_{σ^v} f - f` at a level acting trivially. -/
public theorem levelShift_sub_sum_range (σ : G) (W : OpenNormalSubgroup G)
    (hW : ∀ g ∈ W, ∀ m : V, g • m = m) (f : G ⧸ (W : Subgroup G) →₀ V) (v : ℕ) :
    levelShift σ W (∑ j ∈ Finset.range v, levelShift (σ ^ j) W f) -
        ∑ j ∈ Finset.range v, levelShift (σ ^ j) W f = levelShift (σ ^ v) W f - f := by
  let := levelDistribMulAction W hW
  simp only [levelShift_eq_shift _ W hW, QuotientGroup.mk_pow]
  exact shift_sub_sum_range _ f v

omit [IsTopologicalGroup Γ] [G.Normal] in
/-- The twisted shift at a level acting trivially only depends on the class of the element. -/
public theorem levelShift_congr {x y : G} (W : OpenNormalSubgroup G)
    (hW : ∀ g ∈ W, ∀ m : V, g • m = m)
    (hxy : (x : G ⧸ (W : Subgroup G)) = y) : levelShift (M := V) x W = levelShift y W := by
  rw [levelShift_eq_shift x W hW, levelShift_eq_shift y W hW, hxy]

omit [IsTopologicalGroup Γ] [G.Normal] in
/-- `Σ T_x f = x⁻¹ Σ f`. -/
public theorem sum_levelShift (x : G) (W : OpenNormalSubgroup G) (f : G ⧸ (W : Subgroup G) →₀ V) :
    (levelShift x W f).sum (fun _ m => m) = x⁻¹ • f.sum (fun _ m => m) := by
  exact sum_eq_smul_of_single _ _ (fun y m => by
    rw [levelShift_single, Finsupp.sum_single_index rfl]) f

variable [CompactSpace G]

omit [CompactSpace ↥G] in
/-- Conjugation intertwines the twisted shifts on `V[[G]]` by `σ` and by `γ σ γ⁻¹`. -/
public theorem completedConj_completedShift (γ : Γ) (σ : G) (f : CompletedInduced Λ G V) :
    completedConj γ (completedShift σ f) =
      completedShift (conjContinuousMulEquiv G γ σ) (completedConj γ f) :=
  CompletedInduced.ext fun U => by
    rw [completedConj_level γ _ (conj_mem_of_mem_conjLevel γ U), completedShift_level,
      completedShift_level, completedConj_level γ _ (conj_mem_of_mem_conjLevel γ U),
      levelConj_levelShift]

omit [SMulCommClass Γ Λ V] [CompactSpace ↥G] in
/-- `ε (γ f) = γ ε(f)`. -/
public theorem completedEval_completedConj (γ : Γ) {U₀ : OpenNormalSubgroup G}
    (hU₀ : ∀ g ∈ U₀, ∀ m : V, g • m = m) (f : CompletedInduced Λ G V) :
    completedEval U₀ hU₀ (completedConj γ f) = γ • completedEval U₀ hU₀ f := by
  have h : ∀ g ∈ U₀ ⊓ conjLevel γ U₀, (conjContinuousMulEquiv G γ : G →* G) g ∈ U₀ :=
    fun g hg => conj_mem_of_mem_conjLevel γ U₀ g hg.2
  rw [completedEval_eq hU₀ _ le_rfl, completedConj_level γ f h, levelEval_levelConj γ h _
    (fun g hg => hU₀ g hg.1), ← completedEval_eq hU₀ f inf_le_left]

end LevelLemmas

/-! ### The Koszul resolution of `V` -/

/-- The zero terms of the Koszul complex are zero objects. -/
private theorem isZero_punit {Γ : Type u} [Group Γ] [TopologicalSpace Γ] {G : Subgroup Γ}
    (Λ : Type u) [Ring Λ] : IsZero (ModuleCat.of (CompletedGroupAlgebra Λ G) PUnit.{u + 1}) :=
  ModuleCat.isZero_of_subsingleton _

section Resolution

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {G : Subgroup Γ}
  [G.Normal] [CompactSpace G] (Λ : Type u) [Ring Λ] (V : Type u) [AddCommGroup V] [Module Λ V]
  [DistribMulAction Γ V] [SMulCommClass Γ Λ V]

variable (G) in
/-- The terms of the Koszul complex: `V[[G]]` in degrees `0` and `1`, zero elsewhere. -/
public def shiftKoszulX : ℕ → ModuleCat.{u} (CompletedGroupAlgebra Λ G)
  | 0 => ModuleCat.of _ (CompletedInduced Λ G V)
  | 1 => ModuleCat.of _ (CompletedInduced Λ G V)
  | _ + 2 => ModuleCat.of _ PUnit.{u + 1}

variable {V} (σ : G)

/-- The differentials of the Koszul complex: `T - 1`. -/
public def shiftKoszulD : ∀ n : ℕ, shiftKoszulX G Λ V (n + 1) ⟶ shiftKoszulX G Λ V n
  | 0 => ModuleCat.ofHom (completedShift σ - LinearMap.id)
  | _ + 1 => 0

/-- **The Koszul complex** `V[[G]] --(T - 1)--> V[[G]]`. -/
public def shiftKoszulComplex : ChainComplex (ModuleCat.{u} (CompletedGroupAlgebra Λ G)) ℕ :=
  ChainComplex.of (shiftKoszulX G Λ V) (shiftKoszulD Λ σ) fun n => by
    cases n <;> exact zero_comp

omit [IsTopologicalGroup Γ] [G.Normal] [CompactSpace ↥G] in
/-- The differential `V[[G]] ⟶ V[[G]]` of the Koszul complex is `T - 1`. -/
public theorem shiftKoszulComplex_d_one_zero :
    (shiftKoszulComplex Λ σ (V := V)).d 1 0 =
      ModuleCat.ofHom (completedShift σ - LinearMap.id) := by
  show ChainComplex.of.d (shiftKoszulX G Λ V) (shiftKoszulD Λ σ) (0 + 1) 0 = _
  rw [ChainComplex.of_d]
  rfl

variable (hV : IsSmoothFor G V)

/-- The evaluation `ε : V[[G]] → V`, as a `Λ[[G]]`-linear map. -/
public def shiftKoszulAugmentationLinear :
    CompletedInduced Λ G V →ₗ[CompletedGroupAlgebra Λ G] toCompletedGroupAlgebraModuleCat Λ hV
    where
  toFun f := (completedEval hV.choose hV.choose_spec f : V)
  map_add' f g := map_add (completedEval (Λ := Λ) hV.choose hV.choose_spec) f g
  map_smul' a f := by
    change completedEval hV.choose hV.choose_spec (a • f) =
      (letI := completedGroupAlgebraModule Λ hV; a • (show V from
        completedEval hV.choose hV.choose_spec f))
    rw [completedGroupAlgebra_smul_def,
      toAddMonoidEnd_eq V hV hV.choose hV.choose_spec]
    exact levelEval_levelAction _ _ _ _

omit [CompactSpace ↥G] in
omit [IsTopologicalGroup Γ] [G.Normal] in
/-- `shiftKoszulAugmentationLinear Λ hV` is the evaluation `ε`. -/
public theorem shiftKoszulAugmentationLinear_apply (f : CompletedInduced Λ G V) :
    shiftKoszulAugmentationLinear Λ hV f = (completedEval hV.choose hV.choose_spec f : V) :=
  rfl

/-- The evaluation, as a morphism to `V`. -/
public def shiftKoszulAugmentation :
    (shiftKoszulComplex Λ σ (V := V)).X 0 ⟶ toCompletedGroupAlgebraModuleCat Λ hV :=
  ModuleCat.ofHom (X := CompletedInduced Λ G V) (Y := toCompletedGroupAlgebraModuleCat Λ hV)
    (shiftKoszulAugmentationLinear Λ hV)

omit [IsTopologicalGroup Γ] [G.Normal] [CompactSpace ↥G] in
/-- The differential of the Koszul complex followed by the evaluation is zero. -/
public theorem shiftKoszul_d_comp_augmentation :
    (shiftKoszulComplex Λ σ (V := V)).d 1 0 ≫ shiftKoszulAugmentation Λ σ hV = 0 := by
  rw [shiftKoszulComplex_d_one_zero]
  refine ModuleCat.hom_ext (LinearMap.ext fun (f : CompletedInduced Λ G V) => ?_)
  show completedEval hV.choose hV.choose_spec (completedShift σ f - f) = 0
  rw [map_sub, completedEval_completedShift, sub_self]

/-- The evaluation, as a chain map to `V` in degree `0`. -/
public def shiftKoszulπ :
    shiftKoszulComplex Λ σ (V := V) ⟶
      (ChainComplex.single₀ _).obj (toCompletedGroupAlgebraModuleCat Λ hV) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨shiftKoszulAugmentation Λ σ hV, shiftKoszul_d_comp_augmentation Λ σ hV⟩

/-- For a finite projective `Λ`-module `V`, the terms of the Koszul complex are projective. -/
public instance shiftKoszulComplex_projective [Module.Finite Λ V] [Module.Projective Λ V]
    (n : ℕ) : Projective ((shiftKoszulComplex Λ σ (V := V)).X n) := by
  rcases n with _ | _ | n
  · exact (IsProjective.iff_projective (CompletedInduced Λ G V)).1 inferInstance
  · exact (IsProjective.iff_projective (CompletedInduced Λ G V)).1 inferInstance
  · exact (IsProjective.iff_projective PUnit.{u + 1}).1 inferInstance

variable {σ} (hgen : GeneratesQuotients σ) {n : ℕ} (hn : n ≠ 0)
  (hpow : ∀ p : ℕ, p.Prime → p ∣ n → HasPrimePowerQuotients σ p) (hΛ : ∀ a : Λ, n • a = 0)
  [Finite V]

include hgen hn hpow hΛ in
omit [G.Normal] in
/-- **The Koszul complex resolves `V`.** -/
public theorem shiftKoszulπ_quasiIso : QuasiIso (shiftKoszulπ Λ σ hV) where
  quasiIsoAt m := by
    rcases m with _ | m
    · rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ ?_ rfl rfl]
      · constructor
        · rw [ShortComplex.moduleCat_exact_iff]
          intro x hx
          change completedEval hV.choose hV.choose_spec
            (show CompletedInduced Λ G V from x) = 0 at hx
          obtain ⟨y, hy⟩ := exists_completedShift_sub_eq hgen hV.choose_spec hn hpow hΛ hx
          refine ⟨y, ?_⟩
          show ((shiftKoszulComplex Λ σ (V := V)).d 1 0).hom y = x
          rw [shiftKoszulComplex_d_one_zero]
          exact hy
        · rw [ModuleCat.epi_iff_surjective]
          intro x
          exact completedEval_surjective (Λ := Λ) hV.choose_spec (show V from x)
      · show (shiftKoszulComplex Λ σ (V := V)).d 0 0 = 0
        exact (shiftKoszulComplex Λ σ).shape 0 0 (by simp)
    · rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)]
      rcases m with _ | m
      · rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp),
          ShortComplex.moduleCat_exact_iff]
        intro x hx
        refine ⟨0, ?_⟩
        rw [map_zero]
        change ((shiftKoszulComplex Λ σ (V := V)).d 1 0).hom x = 0 at hx
        rw [shiftKoszulComplex_d_one_zero] at hx
        change completedShift σ (show CompletedInduced Λ G V from x) -
          (show CompletedInduced Λ G V from x) = 0 at hx
        exact (eq_zero_of_completedShift_eq hgen hV.choose_spec hn hpow hΛ
          (sub_eq_zero.1 hx)).symm
      · rw [HomologicalComplex.exactAt_iff' _ (m + 3) (m + 2) (m + 1) (by simp) (by simp)]
        refine ShortComplex.exact_of_isZero_X₂ _ ?_
        exact isZero_punit Λ

/-- **The Koszul resolution** `0 → V[[G]] --(T - 1)--> V[[G]] --ε--> V → 0`. -/
public abbrev shiftKoszulResolution [Module.Finite Λ V] [Module.Projective Λ V] :
    ProjectiveResolution (toCompletedGroupAlgebraModuleCat Λ hV) where
  complex := shiftKoszulComplex Λ σ
  π := shiftKoszulπ Λ σ hV
  quasiIso := shiftKoszulπ_quasiIso Λ hV hgen hn hpow hΛ

end Resolution

/-! ### The lift of the action of `γ` -/

section Lift

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {G : Subgroup Γ}
  [G.Normal] [CompactSpace G] {Λ : Type u} [Ring Λ] {V : Type u} [AddCommGroup V] [Module Λ V]
  [DistribMulAction Γ V] [SMulCommClass Γ Λ V] (γ : Γ) {σ : G} (hgen : GeneratesQuotients σ)
  {n : ℕ} (hn : n ≠ 0) (hpow : ∀ p : ℕ, p.Prime → p ∣ n → HasPrimePowerQuotients σ p)
  (hΛ : ∀ a : Λ, n • a = 0) [Finite V] (hV : IsSmoothFor G V)

include hgen hn hpow hΛ hV

omit [G.Normal] [Finite V] in
/-- `T - 1` is injective on `V[[G]]`: `T x - x = T y - y` implies `x = y`. -/
public theorem eq_of_completedShift_sub_eq {x y : CompletedInduced Λ G V}
    (h : completedShift σ x - x = completedShift σ y - y) : x = y := by
  refine sub_eq_zero.1 (eq_zero_of_completedShift_eq hgen hV.choose_spec hn hpow hΛ ?_)
  rw [map_sub]
  exact sub_eq_sub_iff_sub_eq_sub.1 h

/-- For every `f ∈ V[[G]]`, `γ (T f - f)` lies in the image of `T - 1`. -/
public theorem exists_completedConjOne (f : CompletedInduced Λ G V) :
    ∃ g : CompletedInduced Λ G V,
      completedShift σ g - g = completedConj γ (completedShift σ f - f) :=
  exists_completedShift_sub_eq hgen hV.choose_spec hn hpow hΛ (by
    rw [map_sub, completedConj_completedShift, map_sub, completedEval_completedShift, sub_self])

/-- The lift of the action of `γ` in degree `1`: `κ₁ = (T - 1)⁻¹ κ₀ (T - 1)`. -/
public def completedConjOne (f : CompletedInduced Λ G V) : CompletedInduced Λ G V :=
  (exists_completedConjOne γ hgen hn hpow hΛ hV f).choose

/-- `(T - 1) κ₁(f) = γ (T - 1) f`. -/
public theorem completedConjOne_spec (f : CompletedInduced Λ G V) :
    completedShift σ (completedConjOne γ hgen hn hpow hΛ hV f) -
        completedConjOne γ hgen hn hpow hΛ hV f =
      completedConj γ (completedShift σ f - f) :=
  (exists_completedConjOne γ hgen hn hpow hΛ hV f).choose_spec

/-- The lift in degree `1`, as a morphism `V[[G]] ⟶ σ_γ^* V[[G]]`. -/
public def completedConjOneHom :
    ModuleCat.of (CompletedGroupAlgebra Λ G) (CompletedInduced Λ G V) ⟶
      (twistFunctor Λ (conjContinuousMulEquiv G γ)).obj
        (ModuleCat.of (CompletedGroupAlgebra Λ G) (CompletedInduced Λ G V)) :=
  ModuleCat.semilinearMapAddEquiv _ _ _
    { toFun := fun f => (completedConjOne γ hgen hn hpow hΛ hV f : CompletedInduced Λ G V)
      map_add' := fun f g => eq_of_completedShift_sub_eq hgen hn hpow hΛ hV (by
        set κ := completedConjOne γ hgen hn hpow hΛ hV
        have e : completedShift σ (κ f + κ g) - (κ f + κ g) =
            (completedShift σ (κ f) - κ f) + (completedShift σ (κ g) - κ g) := by
          rw [map_add]
          abel
        rw [completedConjOne_spec, e, completedConjOne_spec, completedConjOne_spec, ← map_add,
          map_add (completedShift σ) f g]
        congr 1
        abel)
      map_smul' := fun a f => eq_of_completedShift_sub_eq hgen hn hpow hΛ hV (by
        rw [completedConjOne_spec, map_smul, ← smul_sub, completedConj_smul, map_smul,
          ← smul_sub, completedConjOne_spec]
        rfl) }

/-- `completedConjOneHom` is `completedConjOne`. -/
public theorem completedConjOneHom_apply (f : CompletedInduced Λ G V) :
    (completedConjOneHom γ hgen hn hpow hΛ hV).hom f =
      (completedConjOne γ hgen hn hpow hΛ hV f : CompletedInduced Λ G V) :=
  rfl

omit hgen hn hpow hΛ hV [Finite V] in
variable (Λ) (σ) in
/-- The components of the lift of the action of `γ` to the Koszul resolution. -/
public def shiftKoszulLiftF
    (κ₁ : ModuleCat.of (CompletedGroupAlgebra Λ G) (CompletedInduced Λ G V) ⟶
      (twistFunctor Λ (conjContinuousMulEquiv G γ)).obj
        (ModuleCat.of (CompletedGroupAlgebra Λ G) (CompletedInduced Λ G V))) : ∀ i : ℕ,
    (shiftKoszulComplex Λ σ (V := V)).X i ⟶
      (((twistFunctor Λ (conjContinuousMulEquiv G γ)).mapHomologicalComplex _).obj
        (shiftKoszulComplex Λ σ (V := V))).X i
  | 0 => completedConjHom (Λ := Λ) (V := V) γ
  | 1 => κ₁
  | _ + 2 => 0

/-- **The lift of the action of `γ` to the Koszul resolution.** -/
public def shiftKoszulLift :
    shiftKoszulComplex Λ σ (V := V) ⟶
      ((twistFunctor Λ (conjContinuousMulEquiv G γ)).mapHomologicalComplex _).obj
        (shiftKoszulComplex Λ σ (V := V)) where
  f := shiftKoszulLiftF Λ γ σ (V := V) (completedConjOneHom γ hgen hn hpow hΛ hV)
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    rcases j with _ | j
    · rw [Functor.mapHomologicalComplex_obj_d, shiftKoszulComplex_d_one_zero]
      refine ModuleCat.hom_ext (LinearMap.ext fun (f : CompletedInduced Λ G V) => ?_)
      change completedShift σ (completedConjOne γ hgen hn hpow hΛ hV f) -
          completedConjOne γ hgen hn hpow hΛ hV f =
        completedConj γ (completedShift σ f - f)
      exact completedConjOne_spec γ hgen hn hpow hΛ hV f
    · exact (show IsZero (ModuleCat.of (CompletedGroupAlgebra Λ G) PUnit.{u + 1}) from
        ModuleCat.isZero_of_subsingleton _).eq_of_src _ _

/-- **The lift lifts the action of `γ`.** -/
public theorem shiftKoszulLift_comm [Module.Finite Λ V] [Module.Projective Λ V] :
    shiftKoszulLift γ hgen hn hpow hΛ hV ≫
        (twistResolution (c := conjContinuousMulEquiv G γ)
          (shiftKoszulResolution Λ hV hgen hn hpow hΛ)).π =
      (shiftKoszulResolution Λ hV hgen hn hpow hΛ).π ≫
        (ChainComplex.single₀ _).map (conjActionHom Λ hV γ) := by
  apply HomologicalComplex.to_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  refine ModuleCat.hom_ext (LinearMap.ext fun (f : CompletedInduced Λ G V) => ?_)
  show completedEval hV.choose hV.choose_spec (completedConj γ f) =
    γ • (completedEval hV.choose hV.choose_spec f : V)
  exact completedEval_completedConj γ hV.choose_spec f

/-- **The sum of the values of `κ₁ f`**: `Σ κ₁ f = Σ_{j < v} σ^{-j} γ Σ f`, where `γ σ γ⁻¹ ≡ σ^v`
modulo a level `W` deep below a level `V'` acting trivially. -/
public theorem sumValues_completedConjOne (V' W : OpenNormalSubgroup G)
    (hV' : ∀ g ∈ V', ∀ m : V, g • m = m) (hW : IsDeep Λ σ V' W) {v : ℕ}
    (hv : (conjContinuousMulEquiv G γ σ : G ⧸ (W : Subgroup G)) =
      (σ : G ⧸ (W : Subgroup G)) ^ v) (f : CompletedInduced Λ G V) :
    sumValues Λ G V (completedConjOne γ hgen hn hpow hΛ hV f) =
      ∑ j ∈ Finset.range v, ((σ ^ j : G) : Γ)⁻¹ • γ • sumValues Λ G V f := by
  have hWt : ∀ g ∈ W, ∀ m : V, g • m = m := fun g hg => hV' g (hW.1 hg)
  set F := (completedConj γ f).level W
  set g := ∑ j ∈ Finset.range v, levelShift (σ ^ j) W F
  have hspec := congrArg (fun x : CompletedInduced Λ G V => x.level W)
    (completedConjOne_spec γ hgen hn hpow hΛ hV f)
  simp only [completedInduced_level_sub, completedShift_level] at hspec
  have hg : levelShift σ W g - g = levelShift σ W
      ((completedConjOne γ hgen hn hpow hΛ hV f).level W) -
        (completedConjOne γ hgen hn hpow hΛ hV f).level W := by
    rw [hspec, levelShift_sub_sum_range σ W hWt F v, map_sub, completedConj_completedShift,
      completedInduced_level_sub, completedShift_level,
      levelShift_congr W hWt (by rw [hv, QuotientGroup.mk_pow])]
  have hpush := mapDomain_eq_of_levelShift_sub_eq hgen hV' le_rfl hW hg
  have e : ∀ x : G ⧸ (W : Subgroup G) →₀ V,
      (Finsupp.mapDomain (levelMap hW.1) x).sum (fun _ m => m) = x.sum (fun _ m => m) :=
    fun x => Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)
  have hsum : g.sum (fun _ m => m) =
      ((completedConjOne γ hgen hn hpow hΛ hV f).level W).sum (fun _ m => m) := by
    rw [← e, ← e, hpush]
  rw [sumValues_eq _ W, ← hsum, ← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_levelShift, ← sumValues_eq, sumValues_completedConj]
  rfl

end Lift

/-! ### The trace -/

section Trace

open CategoryTheory.FilteredDerived

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {G : Subgroup Γ}
  [G.Normal] [CompactSpace G] {Λ : Type u} [Ring Λ] {V : Type u} [AddCommGroup V] [Module Λ V]
  [DistribMulAction Γ V] [SMulCommClass Γ Λ V] [Module.Finite Λ V] [Module.Projective Λ V]
  (γ : Γ) {σ : G} (hgen : GeneratesQuotients σ) {n : ℕ} (hn : n ≠ 0)
  (hpow : ∀ p : ℕ, p.Prime → p ∣ n → HasPrimePowerQuotients σ p)
  (hΛ : ∀ a : Λ, n • a = 0) [Finite V] (hV : IsSmoothFor G V)

omit [Module.Finite Λ V] [Module.Projective Λ V] [Finite V] in
variable (σ) in
/-- The coinvariants of the Koszul resolution, a chain complex of `Λ`-modules. -/
public abbrev shiftKoszulCoinvariants : ChainComplex (ModuleCat.{u} Λ) ℕ :=
  ((coinvariantsFunctor Λ G).mapHomologicalComplex _).obj (shiftKoszulComplex Λ σ (V := V))

omit [Module.Finite Λ V] [Module.Projective Λ V] [Finite V] in
variable (σ) in
omit [G.Normal] [CompactSpace ↥G] in
/-- The coinvariants of the Koszul resolution vanish in degrees `k ≥ 2`. -/
public theorem shiftKoszulCoinvariants_isZero (k : ℕ) (hk : 2 ≤ k) :
    IsZero ((shiftKoszulCoinvariants (Λ := Λ) (V := V) σ).X k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by lia⟩
  exact (coinvariantsFunctor Λ G).map_isZero (isZero_punit Λ)

omit [Finite V] in
variable (σ) in
/-- The terms of the coinvariants in degrees `0` and `1` are `V`, through the sum of the values. -/
public def shiftKoszulCoinvariantsXEquiv : ∀ k : ℕ, k ≤ 1 →
    ((shiftKoszulCoinvariants (Λ := Λ) (V := V) σ).X k ≃ₗ[Λ] V)
  | 0, _ => coinvariantsLinearEquiv Λ G V
  | 1, _ => coinvariantsLinearEquiv Λ G V

omit [Finite V] in
variable (σ) in
omit [G.Normal] [CompactSpace ↥G] in
/-- The terms of the coinvariants of the Koszul resolution are finite `Λ`-modules. -/
public theorem shiftKoszulCoinvariants_finite (k : ℕ) :
    Module.Finite Λ ((shiftKoszulCoinvariants (Λ := Λ) (V := V) σ).X k) := by
  rcases le_or_gt k 1 with hk | hk
  · exact Module.Finite.equiv (shiftKoszulCoinvariantsXEquiv σ k hk).symm
  · exact (finite_projective_of_isZero (shiftKoszulCoinvariants_isZero σ k hk)).2

omit [Finite V] in
variable (σ) in
omit [G.Normal] [CompactSpace ↥G] in
/-- The terms of the coinvariants of the Koszul resolution are projective `Λ`-modules. -/
public theorem shiftKoszulCoinvariants_projective (k : ℕ) :
    Module.Projective Λ ((shiftKoszulCoinvariants (Λ := Λ) (V := V) σ).X k) := by
  rcases le_or_gt k 1 with hk | hk
  · exact Module.Projective.of_equiv (shiftKoszulCoinvariantsXEquiv σ k hk).symm
  · exact (finite_projective_of_isZero (shiftKoszulCoinvariants_isZero σ k hk)).1

/-- The endomorphism of the coinvariants of the Koszul resolution induced by the lift. -/
public abbrev shiftKoszulCoinvariantsMap :
    shiftKoszulCoinvariants (Λ := Λ) (V := V) σ ⟶ shiftKoszulCoinvariants (Λ := Λ) (V := V) σ :=
  ((coinvariantsFunctor Λ G).mapHomologicalComplex _).map
      (shiftKoszulLift γ hgen hn hpow hΛ hV) ≫
    ((Functor.mapHomologicalComplexCompIso
      (twistCoinvariantsIso Λ (conjContinuousMulEquiv G γ)) _).app
        (shiftKoszulComplex Λ σ (V := V))).hom

/-- The lift acts on the coinvariants `V` of `V[[G]]` in degree `k` through the sum of the values
of the lift. -/
public theorem shiftKoszulCoinvariantsMap_f_apply (k : ℕ) (hk : k ≤ 1) (m : V) :
    shiftKoszulCoinvariantsXEquiv σ k hk
        (((shiftKoszulCoinvariantsMap γ hgen hn hpow hΛ hV).f k).hom
          ((shiftKoszulCoinvariantsXEquiv σ k hk).symm m)) =
      sumValues Λ G V (if k = 0 then completedConj γ (CompletedInduced.single 1 m)
        else completedConjOne γ hgen hn hpow hΛ hV (CompletedInduced.single 1 m)) := by
  rcases k with _ | _ | k
  · have h1 : (shiftKoszulCoinvariantsXEquiv (Λ := Λ) (V := V) σ 0 hk).symm m =
        Submodule.Quotient.mk (show ((shiftKoszulComplex Λ σ (V := V)).X 0 : Type u) from
          CompletedInduced.single 1 m) :=
      (LinearEquiv.symm_apply_eq _).2 (sumValues_single 1 m).symm
    rw [h1, ite_eq_left rfl]
    rfl
  · have h1 : (shiftKoszulCoinvariantsXEquiv (Λ := Λ) (V := V) σ 1 hk).symm m =
        Submodule.Quotient.mk (show ((shiftKoszulComplex Λ σ (V := V)).X 1 : Type u) from
          CompletedInduced.single 1 m) :=
      (LinearEquiv.symm_apply_eq _).2 (sumValues_single 1 m).symm
    rw [h1, ite_eq_right (by lia : 0 + 1 ≠ 0)]
    rfl
  · lia

include hgen hn hpow hΛ in
omit [G.Normal] in
/-- **The derived coinvariants of a finite projective module are perfect.** -/
public theorem isPerfect_derivedCoinvariants :
    StacksDraft.Perfect.IsPerfect
      (derivedCoinvariants (toCompletedGroupAlgebraModuleCat Λ hV)) := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hfp⟩ := finiteProjectiveComplex_extend
    (shiftKoszulCoinvariants_finite (Λ := Λ) (V := V) σ) (shiftKoszulCoinvariants_projective σ)
    (shiftKoszulCoinvariants_isZero σ)
  exact ⟨_, a, b, ha, hb, fun i => (hfp i).2, fun i => (hfp i).1,
    ⟨derivedCoinvariantsIsoOfResolution (shiftKoszulResolution Λ hV hgen hn hpow hΛ)⟩⟩

omit [Finite V] in
/-- The trace of a finite sum of endomorphisms. -/
public theorem projectiveModuleTrace_finsetSum {ι : Type*} (s : Finset ι)
    (f : ι → Module.End Λ V) :
    Stacks.Trace.projectiveModuleTrace Λ V (∑ i ∈ s, f i) =
      ∑ i ∈ s, Stacks.Trace.projectiveModuleTrace Λ V (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [projectiveModuleTrace_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, projectiveModuleTrace_add, ih]

/-- The trace of the lift on the coinvariants in degree `k ≤ 1`, given the endomorphism `A` of `V`
it induces. -/
public theorem projectiveModuleTrace_shiftKoszulCoinvariantsMap (k : ℕ) (hk : k ≤ 1)
    (A : Module.End Λ V)
    (hA : ∀ m : V, sumValues Λ G V (if k = 0 then completedConj γ (CompletedInduced.single 1 m)
        else completedConjOne γ hgen hn hpow hΛ hV (CompletedInduced.single 1 m)) = A m) :
    haveI := shiftKoszulCoinvariants_finite (Λ := Λ) (V := V) σ k
    haveI := shiftKoszulCoinvariants_projective (Λ := Λ) (V := V) σ k
    Stacks.Trace.projectiveModuleTrace Λ ((shiftKoszulCoinvariants (Λ := Λ) (V := V) σ).X k)
        ((shiftKoszulCoinvariantsMap γ hgen hn hpow hΛ hV).f k).hom =
      Stacks.Trace.projectiveModuleTrace Λ V A := by
  have := shiftKoszulCoinvariants_finite (Λ := Λ) (V := V) σ k
  have := shiftKoszulCoinvariants_projective (Λ := Λ) (V := V) σ k
  set E := shiftKoszulCoinvariantsXEquiv (Λ := Λ) (V := V) σ k hk
  have hconj : E.toLinearMap ∘ₗ ((shiftKoszulCoinvariantsMap γ hgen hn hpow hΛ hV).f k).hom ∘ₗ
      E.symm.toLinearMap = A := by
    refine LinearMap.ext fun m => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      shiftKoszulCoinvariantsMap_f_apply, hA]
  rw [← projectiveModuleTrace_conj Λ E, hconj]

include hgen hn hpow hΛ in
/-- **The trace of `γ` on the derived coinvariants**: if `γ σ γ⁻¹ ≡ σ^v` modulo a level `W` deep
below a level `V'` acting trivially on `V`, then
`Tr(γ | LH₀(G, V)) = Tr(γ | V) - Σ_{j < v} Tr(σ^{-j} γ | V)` in `Λ^♮`. -/
public theorem perfectDerivedTrace_derivedCoinvariantsAction
    (hperf : StacksDraft.Perfect.IsPerfect
      (derivedCoinvariants (toCompletedGroupAlgebraModuleCat Λ hV)))
    (V' W : OpenNormalSubgroup G) (hV' : ∀ g ∈ V', ∀ m : V, g • m = m) (hW : IsDeep Λ σ V' W)
    {v : ℕ} (hv : (conjContinuousMulEquiv G γ σ : G ⧸ (W : Subgroup G)) =
      (σ : G ⧸ (W : Subgroup G)) ^ v) :
    perfectDerivedTrace Λ ⟨_, hperf⟩ (derivedCoinvariantsAction Λ hV γ) =
      Stacks.Trace.projectiveModuleTrace Λ V (DistribMulAction.toModuleEnd Λ V γ) -
        ∑ j ∈ Finset.range v, Stacks.Trace.projectiveModuleTrace Λ V
          (DistribMulAction.toModuleEnd Λ V (((σ ^ j : G) : Γ)⁻¹ * γ)) := by
  set K := shiftKoszulResolution Λ hV hgen hn hpow hΛ
  have hP := finiteProjectiveComplex_extend (shiftKoszulCoinvariants_finite (Λ := Λ) (V := V) σ)
    (shiftKoszulCoinvariants_projective σ) (shiftKoszulCoinvariants_isZero σ)
  have key := derivedCoinvariantsTwistedMap_eq (conjActionHom Λ hV γ) K
    (shiftKoszulLift γ hgen hn hpow hΛ hV) (shiftKoszulLift_comm γ hgen hn hpow hΛ hV)
  have h0 := projectiveModuleTrace_shiftKoszulCoinvariantsMap γ hgen hn hpow hΛ hV 0 (by lia)
    (DistribMulAction.toModuleEnd Λ V γ) fun m => by
      rw [ite_eq_left rfl, sumValues_completedConj, sumValues_single]
      rfl
  have h1 := projectiveModuleTrace_shiftKoszulCoinvariantsMap γ hgen hn hpow hΛ hV 1 le_rfl
    (∑ j ∈ Finset.range v, DistribMulAction.toModuleEnd Λ V (((σ ^ j : G) : Γ)⁻¹ * γ)) fun m => by
      rw [ite_eq_right one_ne_zero, sumValues_completedConjOne γ hgen hn hpow hΛ hV V' W hV' hW hv,
        sumValues_single, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [DistribMulAction.toModuleEnd_apply]
      exact (mul_smul _ _ m).symm
  rw [perfectDerivedTrace_eq_alternatingTrace Λ ⟨_, hperf⟩ _ _ hP
    (derivedCoinvariantsIsoOfResolution K).symm
    (HomologicalComplex.extendMap (shiftKoszulCoinvariantsMap γ hgen hn hpow hΛ hV)
      (ComplexShape.embeddingUpIntLE 0)) ?_]
  · rw [alternatingTrace_extendMap (shiftKoszulCoinvariants_finite (Λ := Λ) (V := V) σ)
      (shiftKoszulCoinvariants_projective σ) (shiftKoszulCoinvariants_isZero σ), h0, h1,
      projectiveModuleTrace_finsetSum]
  · rw [Iso.symm_hom, Iso.symm_inv]
    show _ = (derivedCoinvariantsIsoOfResolution K).inv ≫ derivedCoinvariantsTwistedMap
      (conjActionHom Λ hV γ) ≫ (derivedCoinvariantsIsoOfResolution K).hom
    rw [key, ← Functor.map_comp]
    congr 1
    rw [coinvariantsComplexMap, twistCoinvariantsComplexIso, Functor.mapIso_hom,
      ← Functor.map_comp]
    rfl

end Trace

end Stacks.GroupHomology.Procyclic

end
