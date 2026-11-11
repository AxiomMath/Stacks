module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.InflationDelta
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.RestrictedHomologyDelta
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.RestrictionCoinducedEffacement
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.HomologicalPostcompose
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.CoinvariantsAdjunction

/-!
# Homology of a finite group with finite coefficients is `Tor`

Let `Q` be a finite discrete group and `Λ` a finite ring. On finite `Λ`-modules `M` with an action
of `Q`, two homological δ-functors are defined in the library:

* `H_i(Q, M) = Hⁱ(Q, M^∨)^∨`, the character dual of the cohomology of the character module
  (`Stacks.ContinuousCohomology.restrictedHomologyDelta`);
* `Tor_i^{Λ[Q]}(M, Λ)`, the left derived functors of the coinvariants `N ↦ Λ ⊗_{Λ[[Q]]} N` of
  `Λ[[Q]]`-modules (`Stacks.GroupHomology.torDelta`, built on
  `Stacks.GroupHomology.finiteTypeGroupHomology`), where `Λ[[Q]] = Λ[Q]` for `Q` finite discrete
  (`Stacks.GroupHomology.eq_sum_const_mul_of`).

Both are universal: the first because one coinduced module `Coind_1 Y` kills all of `Hⁱ⁺¹(Q, Y)`
(`Stacks.GroupHomology.exists_mono_cohomologyDelta_map_eq_zero`), the second because the free
modules `Λ[Q]^k` (`Stacks.GroupHomology.freeModule`) cover every finite module and are projective
over `Λ[[Q]]` (`Stacks.GroupHomology.projective_freeModule`). Both are the coinvariants `M_Q` in
degree zero (`Stacks.GroupHomology.coinvariantsComparison`, using that `I M` is spanned by the
`g m - m`, `Stacks.GroupHomology.mem_augmentationSubmodule_iff`, and that the coinvariants are
right exact). Hence they are isomorphic as δ-functors (`Stacks.GroupHomology.homologyTorIso`).

## Main definitions

* `Stacks.GroupHomology.torDelta`: `M ↦ Tor_i^{Λ[Q]}(M, Λ)`, valued in `Λ`-modules.
* `Stacks.GroupHomology.homologyTorIso`: `H_i(Q, -) ≅ Tor_i^{Λ[Q]}(-, Λ)`.

## Main results

* `Stacks.GroupHomology.isUniversal_torDelta`,
  `Stacks.GroupHomology.isUniversal_restrictedHomologyDelta_id`.

## References

* [Stacks Project, Section 03VI](https://stacks.math.columbia.edu/tag/03VI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.ContinuousCohomology

universe w

namespace Stacks.GroupHomology

section Coeffaceable

variable (R : Type) [Ring R] [Finite R] (Q : Type w) [Group Q] [TopologicalSpace Q]
  [IsTopologicalGroup Q] [CompactSpace Q] [DiscreteTopology Q]

/-- The trivial subgroup of a discrete group, as an open subgroup. -/
def botOpenSubgroup : OpenSubgroup Q := ⟨⊥, isOpen_discrete _⟩

/-- **One coinduced module kills all the cohomology of a finite group.** For a finite discrete
group `Q`, the embedding of `Y` into the module `Coind_1 Y` of all functions `Q → Y` kills all of
`Hⁿ⁺¹(Q, Y)`: each class dies in `Coind_V Y` for some open subgroup `V`, and `Coind_V Y` maps to
`Coind_1 Y` compatibly with the embeddings. -/
theorem exists_mono_cohomologyDelta_map_eq_zero (Y : FiniteTypeContinuousModule.{0, w, w} R Q)
    (n : ℕ) :
    ∃ (I : FiniteTypeContinuousModule.{0, w, w} R Q) (ι : Y ⟶ I), Mono ι ∧
      ((cohomologyDelta R Q).functor (n + 1)).map ι = 0 := by
  have : Finite Q := finite_of_compact_of_discrete
  let B := botOpenSubgroup Q
  have : Finite (Q ⧸ (B : Subgroup Q)) := Finite.of_surjective _ QuotientGroup.mk_surjective
  have hFG : continuousModuleIsFG.{0, w, w} R Q
      ((coind.{0, w, w} R B).obj ((finiteTypeContinuousModuleι.{0, w, w} R Q).obj Y)) := by
    have : Module.Finite R Y.obj.obj.obj.V := Y.property
    change Module.Finite R (Q ⧸ (B : Subgroup Q) → Y.obj.obj.obj.V)
    infer_instance
  let I : FiniteTypeContinuousModule.{0, w, w} R Q := ⟨_, hFG⟩
  let u : Y ⟶ I := ObjectProperty.homMk (coindUnit.{0, w, w} R B
    ((finiteTypeContinuousModuleι.{0, w, w} R Q).obj Y))
  refine ⟨I, u, ?_, ?_⟩
  · have : Mono ((finiteTypeContinuousModuleι.{0, w, w} R Q).map u) :=
      inferInstanceAs (Mono (coindUnit.{0, w, w} R B _))
    exact (finiteTypeContinuousModuleι.{0, w, w} R Q).mono_of_mono_map this
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    obtain ⟨V, hV⟩ := exists_map_coindUnit_eq_zero.{0, w, w} R n
      ((finiteTypeContinuousModuleToRes R (ContinuousMonoidHom.id Q)).obj Y) c
    let s : Q ⧸ (B : Subgroup Q) → Q ⧸ (V : Subgroup Q) :=
      Quotient.map' id fun a b h ↦ by
        have h' : a⁻¹ * b ∈ (⊥ : Subgroup Q) := QuotientGroup.leftRel_apply.1 h
        rw [Subgroup.mem_bot] at h'
        exact QuotientGroup.leftRel_apply.2 (h' ▸ (V : Subgroup Q).one_mem)
    have hs : ∀ (g : Q) (x : Q ⧸ (B : Subgroup Q)),
        s (ContinuousMonoidHom.id Q g • x) = g • s x := by
      intro g x
      induction x using QuotientGroup.induction_on with
      | H q => rfl
    have key := coindUnit_comp_coindRestrictMap R (ContinuousMonoidHom.id Q) V B s hs
      ((finiteTypeContinuousModuleι.{0, w, w} R Q).obj Y)
    have h1 := ConcreteCategory.congr_hom
      (congrArg ((invariantsDelta.{0, w, w} R (G := Q)).functor (n + 1)).map key.symm) c
    let H := (invariantsDelta.{0, w, w} R (G := Q)).functor (n + 1)
    refine h1.trans ((ConcreteCategory.congr_hom (H.map_comp _ _) c).trans ?_)
    change H.map (coindRestrictMap R (ContinuousMonoidHom.id Q) V B s hs
      ((finiteTypeContinuousModuleι.{0, w, w} R Q).obj Y)) (H.map (coindUnit.{0, w, w} R V
        ((finiteTypeContinuousModuleToRes R (ContinuousMonoidHom.id Q)).obj Y)) c) = 0
    rw [hV]
    exact map_zero _

end Coeffaceable

section FiniteAlgebra

open CompletedGroupAlgebra MonoidAlgebra

variable (Λ : Type w) [Ring Λ] (Q : Type w) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [DiscreteTopology Q]

/-- The trivial subgroup of a discrete group, as an open normal subgroup. -/
def botOpenNormalSubgroup : OpenNormalSubgroup Q :=
  ⟨botOpenSubgroup Q, (inferInstance : (⊥ : Subgroup Q).Normal)⟩

variable {Λ Q}

omit [IsTopologicalGroup Q] in
/-- **For a discrete group, `Λ[[Q]] → Λ[Q]` is injective.** -/
theorem eval_bot_injective :
    Function.Injective (eval (botOpenNormalSubgroup Q) : CompletedGroupAlgebra Λ Q →+* _) := by
  intro a b h
  refine CompletedGroupAlgebra.ext fun U ↦ ?_
  have hU : botOpenNormalSubgroup Q ≤ U := fun g hg ↦ by
    rw [show g = 1 from Subgroup.mem_bot.1 hg]
    exact U.one_mem
  rw [← quotientAlgebraMap_eval hU a, ← quotientAlgebraMap_eval hU b, h]

/-- The coefficient of `a ∈ Λ[[Q]]` at `q ∈ Q`, `Q` discrete. -/
def coeffAt (a : CompletedGroupAlgebra Λ Q) (q : Q) : Λ :=
  (eval (botOpenNormalSubgroup Q) a).coeff (q : Q ⧸ ((botOpenNormalSubgroup Q : Subgroup Q)))

omit [IsTopologicalGroup Q] in
/-- The coefficients are additive. -/
theorem coeffAt_add (a b : CompletedGroupAlgebra Λ Q) (q : Q) :
    coeffAt (a + b) q = coeffAt a q + coeffAt b q := by
  simp [coeffAt, map_add, MonoidAlgebra.coeff_add]

variable [Finite Q]

omit [IsTopologicalGroup Q] [Finite Q] in
/-- The coefficient of `Σ_q c_q q` at `q₀` is `c_{q₀}`. -/
theorem coeffAt_sum_const_mul_of [Fintype Q] (c : Q → Λ) (q₀ : Q) :
    coeffAt (∑ q : Q, (const (c q) : CompletedGroupAlgebra Λ Q) * of q) q₀ = c q₀ := by
  rw [coeffAt, map_sum, MonoidAlgebra.coeff_sum, Finset.sum_apply']
  simp only [map_mul, eval_const, eval_of, MonoidAlgebra.single_mul_single, one_mul, mul_one,
    MonoidAlgebra.coeff_single]
  rw [Finset.sum_eq_single q₀]
  · exact Finsupp.single_eq_same
  · intro q _ hq
    rw [Finsupp.single_eq_of_ne]
    intro h
    apply hq
    have := QuotientGroup.eq.1 h
    exact (inv_mul_eq_one.1 (Subgroup.mem_bot.1 this)).symm
  · intro h
    exact absurd (Finset.mem_univ q₀) h

omit [IsTopologicalGroup Q] [Finite Q] in
/-- **An element of `Λ[[Q]]`, `Q` finite discrete, is `Σ_q a_q q`.** -/
theorem eq_sum_const_mul_of [Fintype Q] (a : CompletedGroupAlgebra Λ Q) :
    a = ∑ q : Q, const (coeffAt a q) * of q := by
  apply eval_bot_injective
  apply MonoidAlgebra.coeff_injective
  ext x
  induction x using QuotientGroup.induction_on with
  | H q₀ =>
    exact (coeffAt_sum_const_mul_of (coeffAt a) q₀).symm

end FiniteAlgebra

section Action

open CompletedGroupAlgebra

variable {Λ : Type} [Ring Λ] {Q : Type w} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]

/-- A group element of `Λ[[Q]]` acts on a finite module as the group element. -/
theorem finiteTypeCompletedAction_of (N : FiniteTypeContinuousModule.{0, w, w} Λ Q) (g : Q)
    (x : N.obj.obj.obj.V) :
    finiteTypeCompletedAction N (of g) x = finiteTypeContinuousModuleRepresentation Λ Q N g x := by
  let := finiteTypeDistribMulAction N
  have := finiteTypeSMulCommClass N
  exact CompletedGroupAlgebra.toAddMonoidEnd_of (Λ := ULift.{w} Λ) _
    (exists_openNormalSubgroup_smul_eq_finiteType N) g x

/-- A constant of `Λ[[Q]]` acts on a finite module as the scalar. -/
theorem finiteTypeCompletedAction_const (N : FiniteTypeContinuousModule.{0, w, w} Λ Q)
    (c : ULift.{w} Λ) (x : N.obj.obj.obj.V) :
    finiteTypeCompletedAction N (const c) x = c.down • x := by
  let := finiteTypeDistribMulAction N
  have := finiteTypeSMulCommClass N
  exact CompletedGroupAlgebra.toAddMonoidEnd_const (Λ := ULift.{w} Λ) _
    (exists_openNormalSubgroup_smul_eq_finiteType N) c x

variable [DiscreteTopology Q] [Finite Q]

omit [Finite Q] in
/-- **The action of `a = Σ_q a_q q ∈ Λ[[Q]]`** on a finite module is `x ↦ Σ_q a_q • q x`. -/
theorem finiteTypeCompletedAction_eq_sum [Fintype Q] (N : FiniteTypeContinuousModule.{0, w, w} Λ Q)
    (a : CompletedGroupAlgebra (ULift.{w} Λ) Q) (x : N.obj.obj.obj.V) :
    finiteTypeCompletedAction N a x =
      ∑ q : Q, (coeffAt a q).down • finiteTypeContinuousModuleRepresentation Λ Q N q x := by
  conv_lhs => rw [eq_sum_const_mul_of a]
  have key : ∀ t : Finset Q, finiteTypeCompletedAction N
      (∑ q ∈ t, const (coeffAt a q) * of q) x =
        ∑ q ∈ t, (coeffAt a q).down • finiteTypeContinuousModuleRepresentation Λ Q N q x := by
    intro t
    induction t using Finset.cons_induction with
    | empty => simp
    | cons q t hq ih =>
      rw [Finset.sum_cons, Finset.sum_cons, map_add, ← ih]
      change finiteTypeCompletedAction N (const (coeffAt a q) * of q) x + _ = _
      rw [map_mul]
      change finiteTypeCompletedAction N (const (coeffAt a q))
        (finiteTypeCompletedAction N (of q) x) + _ = _
      rw [finiteTypeCompletedAction_of, finiteTypeCompletedAction_const]
      rfl
  exact key Finset.univ

omit [IsTopologicalGroup Q] [Finite Q] in
/-- The augmentation of `a ∈ Λ[[Q]]` is the sum of its coefficients. -/
theorem augmentation_eq_sum_coeffAt [Fintype Q] (a : CompletedGroupAlgebra (ULift.{w} Λ) Q) :
    augmentation a = ∑ q : Q, coeffAt a q := by
  conv_lhs => rw [eq_sum_const_mul_of a]
  simp only [map_sum, map_mul, augmentation_const, augmentation_of, mul_one]

/-- **`I N` is the span of the differences `g x - x`**, for `Q` finite discrete. -/
theorem mem_augmentationSubmodule_iff (N : FiniteTypeContinuousModule.{0, w, w} Λ Q)
    (x : N.obj.obj.obj.V) :
    letI : Module (CompletedGroupAlgebra (ULift.{w} Λ) Q) N.obj.obj.obj.V :=
      Module.compHom _ (finiteTypeCompletedAction N)
    x ∈ augmentationSubmodule (ULift.{w} Λ) Q N.obj.obj.obj.V ↔
      x ∈ Stacks.Trace.coinvariantsKer (finiteTypeContinuousModuleRepresentation Λ Q N) := by
  let : Module (CompletedGroupAlgebra (ULift.{w} Λ) Q) N.obj.obj.obj.V :=
    Module.compHom _ (finiteTypeCompletedAction N)
  let := Fintype.ofFinite Q
  let σ := finiteTypeContinuousModuleRepresentation Λ Q N
  let K := Stacks.Trace.coinvariantsKer σ
  have hσ : ∀ (q : Q) (y : N.obj.obj.obj.V), y ∈ K → σ q y ∈ K := fun q y hy ↦ by
    have : σ q y - y ∈ K := Submodule.subset_span ⟨(q, y), rfl⟩
    simpa using K.add_mem this hy
  have hsmul : ∀ (a : CompletedGroupAlgebra (ULift.{w} Λ) Q) (y : N.obj.obj.obj.V), y ∈ K →
      a • y ∈ K := fun a y hy ↦ by
    change finiteTypeCompletedAction N a y ∈ K
    rw [finiteTypeCompletedAction_eq_sum]
    exact K.sum_mem fun q _ ↦ K.smul_mem _ (hσ q y hy)
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, n, rfl⟩ := hy
      change finiteTypeCompletedAction N a n ∈ K
      rw [finiteTypeCompletedAction_eq_sum]
      have h0 : ∑ q : Q, (coeffAt a q).down = 0 := by
        have := congrArg ULift.ringEquiv ((augmentation_eq_sum_coeffAt a).symm.trans ha)
        rw [map_sum, map_zero] at this
        exact this
      have : ∑ q : Q, (coeffAt a q).down • σ q n =
          ∑ q : Q, (coeffAt a q).down • (σ q n - n) + (∑ q : Q, (coeffAt a q).down) • n := by
        simp [smul_sub, Finset.sum_smul, Finset.sum_sub_distrib]
      rw [this, h0, zero_smul, add_zero]
      exact K.sum_mem fun q _ ↦ K.smul_mem _ (Submodule.subset_span ⟨(q, n), rfl⟩)
    | zero => exact K.zero_mem
    | add y z _ _ hy hz => exact K.add_mem hy hz
    | smul a y _ hy => exact hsmul a y hy
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨q, n⟩, rfl⟩ := hy
      change σ q n - n ∈ _
      have h : ((of q - 1 : CompletedGroupAlgebra (ULift.{w} Λ) Q)) • n = σ q n - n := by
        rw [sub_smul, one_smul]
        exact congrArg (· - n) (finiteTypeCompletedAction_of N q n)
      rw [← h]
      apply smul_mem_augmentationSubmodule
      rw [map_sub, augmentation_of, map_one, sub_self]
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      have : c • y = (const (ULift.up c) : CompletedGroupAlgebra (ULift.{w} Λ) Q) • y :=
        (finiteTypeCompletedAction_const N (ULift.up c) y).symm
      rw [this]
      exact Submodule.smul_mem _ _ hy

end Action

section FreeModule

open CompletedGroupAlgebra

variable (Λ : Type) [Ring Λ] [Finite Λ] (Q : Type w) [Group Q] [TopologicalSpace Q]
  [IsTopologicalGroup Q] [CompactSpace Q] [DiscreteTopology Q]

/-- The trivial module `Λ^k`, in the universe of `Q`. -/
abbrev trivialFree (k : ℕ) : Stacks.Injectives.ContinuousModule.{0, w, w} Λ Q :=
  (continuousModuleTrivialFunctor.{0, w, w} Λ Q).obj (ModuleCat.of Λ (Fin k → ULift.{w} Λ))

/-- **The free module `Λ[Q]^k`**: the functions `Q → Λ^k`, `Q` acting by translation. -/
def freeModule (k : ℕ) : FiniteTypeContinuousModule.{0, w, w} Λ Q :=
  ⟨(coind.{0, w, w} Λ (botOpenSubgroup Q)).obj (trivialFree Λ Q k), by
    have : Finite Q := finite_of_compact_of_discrete
    have : Finite (Q ⧸ (botOpenSubgroup Q : Subgroup Q)) :=
      Finite.of_surjective _ QuotientGroup.mk_surjective
    change Module.Finite Λ (Q ⧸ (botOpenSubgroup Q : Subgroup Q) → Fin k → ULift.{w} Λ)
    exact Module.Finite.of_finite⟩

variable {Λ Q}

/-- The map `Λ[Q]^k → X`, `f ↦ Σ_q Σ_j f(q)_j • q s_j`, for `s : Fin k → X`. -/
def freeModuleLinearMap [Fintype Q] (X : FiniteTypeContinuousModule.{0, w, w} Λ Q) {k : ℕ}
    (s : Fin k → X.obj.obj.obj.V) :
    (Q ⧸ (botOpenSubgroup Q : Subgroup Q) → Fin k → ULift.{w} Λ) →ₗ[Λ] X.obj.obj.obj.V where
  toFun f := ∑ q : Q, ∑ j, (f (q : Q ⧸ (botOpenSubgroup Q : Subgroup Q)) j).down •
    finiteTypeContinuousModuleRepresentation Λ Q X q (s j)
  map_add' f f' := by
    simp only [Pi.add_apply, ULift.add_down, add_smul, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [Pi.smul_apply, ULift.smul_down, smul_eq_mul, mul_smul, Finset.smul_sum,
      RingHom.id_apply]

omit [Finite Λ] [IsTopologicalGroup Q] [CompactSpace Q] in
/-- `f ↦ Σ_q Σ_j f(q)_j • q s_j` is equivariant. -/
theorem freeModuleLinearMap_equivariant [Fintype Q] (X : FiniteTypeContinuousModule.{0, w, w} Λ Q)
    {k : ℕ} (s : Fin k → X.obj.obj.obj.V) (g : Q)
    (f : Q ⧸ (botOpenSubgroup Q : Subgroup Q) → Fin k → ULift.{w} Λ) :
    freeModuleLinearMap X s (fun x ↦ f (g⁻¹ • x)) =
      finiteTypeContinuousModuleRepresentation Λ Q X g (freeModuleLinearMap X s f) := by
  simp only [freeModuleLinearMap, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul]
  rw [← Equiv.sum_comp (Equiv.mulLeft g)]
  refine Finset.sum_congr rfl fun q _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Equiv.coe_mulLeft, MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel_left, map_mul,
    Module.End.mul_apply]

omit [Finite Λ] [IsTopologicalGroup Q] [CompactSpace Q] in
/-- `f ↦ Σ_q Σ_j f(q)_j • q s_j` is surjective when the `s_j` generate `X`. -/
theorem freeModuleLinearMap_surjective [Fintype Q] (X : FiniteTypeContinuousModule.{0, w, w} Λ Q)
    {k : ℕ} (s : Fin k → X.obj.obj.obj.V) (hs : Submodule.span Λ (Set.range s) = ⊤) :
    Function.Surjective (freeModuleLinearMap X s) := by
  intro x
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Λ).1 (hs ▸ Submodule.mem_top (x := x))
  classical
  refine ⟨fun y j ↦ if y = ((1 : Q) : Q ⧸ (botOpenSubgroup Q : Subgroup Q)) then ULift.up (c j)
    else 0, ?_⟩
  simp only [freeModuleLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single 1]
  · simp only [↓reduceIte, map_one, Module.End.one_apply]
    exact hc
  · intro q _ hq
    have : (q : Q ⧸ (botOpenSubgroup Q : Subgroup Q)) ≠ ((1 : Q) : Q ⧸ _) := fun h ↦ hq (by
      have h' := QuotientGroup.eq.1 h
      exact inv_eq_one.1 ((mul_one q⁻¹).symm.trans (Subgroup.mem_bot.1 h')))
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ 1) h

/-- **The epimorphism `Λ[Q]^k → X`** given by generators `s` of `X`. -/
def freeModuleHom [Fintype Q] (X : FiniteTypeContinuousModule.{0, w, w} Λ Q) {k : ℕ}
    (s : Fin k → X.obj.obj.obj.V) : freeModule Λ Q k ⟶ X :=
  ObjectProperty.homMk ((Stacks.GroupCohomology.homEquiv Λ Q _ _).symm
    ⟨freeModuleLinearMap X s, fun g f ↦ freeModuleLinearMap_equivariant X s g f⟩)

/-- `Λ[Q]^k → X` is an epimorphism when the `s_j` generate `X`. -/
theorem epi_freeModuleHom [Fintype Q] (X : FiniteTypeContinuousModule.{0, w, w} Λ Q) {k : ℕ}
    (s : Fin k → X.obj.obj.obj.V) (hs : Submodule.span Λ (Set.range s) = ⊤) :
    Epi (freeModuleHom X s) := by
  have : Epi ((finiteTypeContinuousModuleι.{0, w, w} Λ Q).map (freeModuleHom X s)) :=
    (Stacks.ContinuousCohomology.epi_iff_surjective.{0, w, w} Λ _).2
      (freeModuleLinearMap_surjective X s hs)
  exact (finiteTypeContinuousModuleι.{0, w, w} Λ Q).epi_of_epi_map this

variable (Λ Q) in
/-- **`Λ[Q]^k` is a projective `Λ[[Q]]`-module**, `Q` finite discrete: `f ↦ (Σ_q f(q)_j q)_j` is an
isomorphism onto `Λ[[Q]]^k`, since `Λ[[Q]] = Λ[Q]`. -/
theorem projective_freeModule (k : ℕ) :
    Projective ((finiteTypeCompletedModule Λ Q).obj (freeModule Λ Q k)) := by
  have : Finite Q := finite_of_compact_of_discrete
  let := Fintype.ofFinite Q
  let N := freeModule Λ Q k
  let A := CompletedGroupAlgebra (ULift.{w} Λ) Q
  let : Module A N.obj.obj.obj.V := Module.compHom _ (finiteTypeCompletedAction N)
  have hof : ∀ (g : Q) (f : N.obj.obj.obj.V),
      (of g : A) • f = finiteTypeContinuousModuleRepresentation Λ Q N g f := by
    intro g f
    let := finiteTypeDistribMulAction N
    have := finiteTypeSMulCommClass N
    exact CompletedGroupAlgebra.toAddMonoidEnd_of (Λ := ULift.{w} Λ) _
      (exists_openNormalSubgroup_smul_eq_finiteType N) g f
  have hconst : ∀ (c : ULift.{w} Λ) (f : N.obj.obj.obj.V), (const c : A) • f = c • f := by
    intro c f
    let := finiteTypeDistribMulAction N
    have := finiteTypeSMulCommClass N
    exact CompletedGroupAlgebra.toAddMonoidEnd_const (Λ := ULift.{w} Λ) _
      (exists_openNormalSubgroup_smul_eq_finiteType N) c f
  let i₀ : N.obj.obj.obj.V → (Fin k → A) := fun f j ↦
    ∑ q : Q, const (f (q : Q ⧸ (botOpenSubgroup Q : Subgroup Q)) j) * of q
  have hi_add : ∀ f f', i₀ (f + f') = i₀ f + i₀ f' := by
    intro f f'
    funext j
    change ∑ q : Q, const (f (q : Q ⧸ (botOpenSubgroup Q : Subgroup Q)) j +
      f' (q : Q ⧸ (botOpenSubgroup Q : Subgroup Q)) j) * of q = i₀ f j + i₀ f' j
    simp only [i₀, map_add, add_mul, Finset.sum_add_distrib]
  have hi_of : ∀ (g : Q) f, i₀ ((of g : A) • f) = (of g : A) • i₀ f := by
    intro g f
    funext j
    rw [hof, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    change ∑ q : Q, const (f (g⁻¹ • (q : Q ⧸ (botOpenSubgroup Q : Subgroup Q))) j) * of q = _
    rw [← Equiv.sum_comp (Equiv.mulLeft g)]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [Equiv.coe_mulLeft, MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel_left, map_mul,
      ← mul_assoc, ← mul_assoc, const_mul_of]
  have hi_const : ∀ (c : ULift.{w} Λ) f, i₀ ((const c : A) • f) = (const c : A) • i₀ f := by
    intro c f
    funext j
    rw [hconst, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    change const (c * f (q : Q ⧸ (botOpenSubgroup Q : Subgroup Q)) j) * of q = _
    rw [map_mul, mul_assoc]
  let i : N.obj.obj.obj.V →ₗ[A] (Fin k → A) :=
    { toFun := i₀
      map_add' := hi_add
      map_smul' := fun a f ↦ by
        rw [RingHom.id_apply, eq_sum_const_mul_of a, Finset.sum_smul, Finset.sum_smul]
        have : ∀ (s : Finset Q) (F : Q → N.obj.obj.obj.V),
            i₀ (∑ q ∈ s, F q) = ∑ q ∈ s, i₀ (F q) := by
          intro s F
          induction s using Finset.cons_induction with
          | empty =>
            funext j
            change ∑ q : Q, const (0 : ULift.{w} Λ) * of q = 0
            simp
          | cons q s hq ih => rw [Finset.sum_cons, Finset.sum_cons, hi_add, ih]
        rw [this]
        refine Finset.sum_congr rfl fun q _ ↦ ?_
        rw [mul_smul, mul_smul, hi_const, hi_of] }
  have hinj : Function.Injective i := by
    intro f f' h
    funext x j
    induction x using QuotientGroup.induction_on with
    | H q =>
      have h1 := coeffAt_sum_const_mul_of
        (fun (q' : Q) ↦ f (q' : Q ⧸ (botOpenSubgroup Q : Subgroup Q)) j) q
      have h2 := coeffAt_sum_const_mul_of
        (fun (q' : Q) ↦ f' (q' : Q ⧸ (botOpenSubgroup Q : Subgroup Q)) j) q
      exact h1.symm.trans ((congrArg (fun v ↦ coeffAt (v j) q) h).trans h2)
  have hsurj : Function.Surjective i := by
    intro v
    refine ⟨fun x j ↦ (eval (botOpenNormalSubgroup Q) (v j)).coeff x, ?_⟩
    funext j
    exact (eq_sum_const_mul_of (v j)).symm
  have hP : Module.Projective A N.obj.obj.obj.V :=
    Module.Projective.of_equiv (LinearEquiv.ofBijective i ⟨hinj, hsurj⟩).symm
  exact @ModuleCat.projective_of_categoryTheory_projective A _
    ((finiteTypeCompletedModule Λ Q).obj (freeModule Λ Q k)) hP

end FreeModule

section Comparison

open CompletedGroupAlgebra Stacks.CategoryHomology

variable (Λ : Type) [Ring Λ] [Finite Λ] (Q : Type w) [Group Q] [TopologicalSpace Q]
  [IsTopologicalGroup Q] [CompactSpace Q] [DiscreteTopology Q]

/-- Restriction of scalars from `ULift Λ` to `Λ`, an equivalence. -/
abbrev uliftRestrict : ModuleCat.{w} (ULift.{w} Λ) ⥤ ModuleCat.{w} Λ :=
  ModuleCat.restrictScalars (ULift.ringEquiv.symm.toRingHom : Λ →+* ULift.{w} Λ)

/-- **`M ↦ Tor_i^{Λ[Q]}(M, Λ)`**, the left derived functors of the coinvariants of
`Λ[[Q]] = Λ[Q]`-modules, as a homological δ-functor with values in `Λ`-modules. -/
def torDelta :
    HomologicalDeltaFunctor (FiniteTypeContinuousModule.{0, w, w} Λ Q) (ModuleCat.{w} Λ) :=
  (finiteTypeGroupHomology (Λ := Λ) (ContinuousMonoidHom.id Q)).postcomp (uliftRestrict Λ)

/-- `Tor` is coeffaceable on finite modules: the free modules `Λ[Q]^k` cover and are projective. -/
theorem coeffaceable_finiteTypeGroupHomology :
    (finiteTypeGroupHomology (Λ := Λ) (ContinuousMonoidHom.id Q)).Coeffaceable :=
  HomologicalDeltaFunctor.Coeffaceable.of_exists_epi_isZero _ fun X n ↦ by
    have : Finite Q := finite_of_compact_of_discrete
    let := Fintype.ofFinite Q
    have : Module.Finite Λ X.obj.obj.obj.V := X.property
    obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := Λ) (M := X.obj.obj.obj.V)
    refine ⟨freeModule Λ Q k, freeModuleHom X s, epi_freeModuleHom X s hs, ?_⟩
    have := projective_freeModule Λ Q k
    exact Functor.isZero_leftDerived_obj_projective_succ (coinvariantsFunctor (ULift.{w} Λ) Q) n
      ((finiteTypeCompletedModule Λ Q).obj (freeModule Λ Q k))

/-- **`Tor_i^{Λ[Q]}(-, Λ)` is a universal homological δ-functor** on finite modules. -/
theorem isUniversal_torDelta : (torDelta Λ Q).IsUniversal :=
  have := coeffaceable_finiteTypeGroupHomology Λ Q
  have : (torDelta Λ Q).Coeffaceable := HomologicalDeltaFunctor.coeffaceable_postcomp
    (finiteTypeGroupHomology (Λ := Λ) (ContinuousMonoidHom.id Q)) (uliftRestrict Λ)
  HomologicalDeltaFunctor.isUniversal_of_coeffaceable _

/-- **`H_i(Q, -) = Hⁱ(Q, (-)^∨)^∨` is a universal homological δ-functor** on finite modules, for
`Q` finite discrete: one coinduced module kills all of `Hⁱ⁺¹(Q, -)`. -/
theorem isUniversal_restrictedHomologyDelta_id :
    (restrictedHomologyDelta Λ (ContinuousMonoidHom.id Q)).IsUniversal :=
  have : (finiteTypeContinuousModuleDualEquivalence.{0, w, w} Λ Q).functor.Additive :=
    finiteTypeContinuousModuleDual_additive Λ _
  have : (restrictedHomologyDelta Λ (ContinuousMonoidHom.id Q)).Coeffaceable :=
    HomologicalDeltaFunctor.coeffaceable_ofDeltaFunctorDual
      (restrictedCohomologyDelta Λᵐᵒᵖ (ContinuousMonoidHom.id Q))
      (finiteTypeContinuousModuleDualEquivalence.{0, w, w} Λ Q)
      fun Y n ↦ exists_mono_cohomologyDelta_map_eq_zero Λᵐᵒᵖ Q Y n
  HomologicalDeltaFunctor.isUniversal_of_coeffaceable _

variable {Λ Q}

/-- The two coinvariants of a finite module agree: `M_Q = Λ ⊗_{Λ[[Q]]} M`. -/
def coinvariantsLinearEquiv (N : FiniteTypeContinuousModule.{0, w, w} Λ Q) :
    (Stacks.ContinuousCohomology.restrictedCoinvariantsFunctor Λ
        (ContinuousMonoidHom.id Q)).obj N ≃ₗ[Λ]
      ((finiteTypeContinuousModuleRes.{0, w, w} Λ (ContinuousMonoidHom.id Q) ⋙
          finiteTypeCompletedModule Λ Q) ⋙ coinvariantsFunctor (ULift.{w} Λ) Q ⋙
        uliftRestrict Λ).obj N :=
  have : Finite Q := finite_of_compact_of_discrete
  letI : Module (CompletedGroupAlgebra (ULift.{w} Λ) Q) N.obj.obj.obj.V :=
    Module.compHom _ (finiteTypeCompletedAction N)
  have h : (Stacks.Trace.coinvariantsKer
        (finiteTypeContinuousModuleRepresentation Λ Q N)).toAddSubgroup =
      (augmentationSubmodule (ULift.{w} Λ) Q N.obj.obj.obj.V).toAddSubgroup :=
    AddSubgroup.ext fun x ↦ (mem_augmentationSubmodule_iff N x).symm
  { toFun := QuotientAddGroup.quotientAddEquivOfEq h
    invFun := (QuotientAddGroup.quotientAddEquivOfEq h).symm
    left_inv := (QuotientAddGroup.quotientAddEquivOfEq h).left_inv
    right_inv := (QuotientAddGroup.quotientAddEquivOfEq h).right_inv
    map_add' := map_add (QuotientAddGroup.quotientAddEquivOfEq h)
    map_smul' := fun c x ↦ by
      induction x using QuotientAddGroup.induction_on with
      | H y =>
        change (QuotientAddGroup.mk (c • y) : _ ⧸ (augmentationSubmodule (ULift.{w} Λ) Q
            N.obj.obj.obj.V).toAddSubgroup) =
          QuotientAddGroup.mk (finiteTypeCompletedAction N (const (ULift.up c)) y)
        exact (congrArg _ (finiteTypeCompletedAction_const N (ULift.up c) y)).symm }

/-- **`M_Q = Λ ⊗_{Λ[[Q]]} M`, naturally in `M`.** -/
def coinvariantsComparison :
    Stacks.ContinuousCohomology.restrictedCoinvariantsFunctor Λ (ContinuousMonoidHom.id Q) ≅
      (finiteTypeContinuousModuleRes.{0, w, w} Λ (ContinuousMonoidHom.id Q) ⋙
          finiteTypeCompletedModule Λ Q) ⋙ coinvariantsFunctor (ULift.{w} Λ) Q ⋙
        uliftRestrict Λ :=
  NatIso.ofComponents (fun N ↦ (coinvariantsLinearEquiv N).toModuleIso) fun {N N'} u ↦ by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H y => rfl

variable (Λ Q)

/-- `Tor_0^{Λ[Q]}(M, Λ) = M_Q`. -/
def torDeltaZeroIso :
    (torDelta Λ Q).functor 0 ≅
      ((finiteTypeContinuousModuleRes.{0, w, w} Λ (ContinuousMonoidHom.id Q) ⋙
          finiteTypeCompletedModule Λ Q) ⋙ coinvariantsFunctor (ULift.{w} Λ) Q) ⋙
        uliftRestrict Λ :=
  Functor.isoWhiskerRight (Functor.isoWhiskerLeft _
    (coinvariantsFunctor (ULift.{w} Λ) Q).leftDerivedZeroIsoSelf) _

/-- **For a finite discrete group `Q`, `H_i(Q, M) ≅ Tor_i^{Λ[Q]}(M, Λ)`** as homological
δ-functors on finite `Λ`-modules with `Q`-action: both are universal, and agree in degree zero,
where both are the coinvariants `M_Q`. -/
def homologyTorIso :
    restrictedHomologyDelta Λ (ContinuousMonoidHom.id Q) ≅ torDelta Λ Q :=
  haveI := isUniversal_restrictedHomologyDelta_id Λ Q
  haveI := isUniversal_torDelta Λ Q
  HomologicalDeltaFunctor.IsUniversal.isoOfIso
    (Stacks.ContinuousCohomology.restrictedHomologyZeroIso Λ (ContinuousMonoidHom.id Q) ≪≫
      coinvariantsComparison ≪≫ (torDeltaZeroIso Λ Q).symm)

end Comparison

end Stacks.GroupHomology

end
