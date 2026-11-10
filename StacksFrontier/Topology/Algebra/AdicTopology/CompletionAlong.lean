module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import StacksCore.Tactic.StacksAttribute

/-!
# Completion of a module along a descending system of submodules

The completion of a module `M` along a descending family of submodules is the inverse limit of
the quotients, topologized as a limit of discrete quotients.  This file constructs that limit,
shows the canonical map is injective with open range inducing the limit topology, and
identifies the induced topology in the adic case.

It then computes the quotients of the completion by the powers `I ^ n M^` of a finitely
generated ideal, obtaining `M^ / I ^ n M^ = M / I ^ n M`, and constructs the completion
`CompletionOverOpen R M` of `M` over *all* of its open submodules, identifying it with the
completion along the fundamental system `I ^ n N`.  Both conclusions of Tag 0F1S are restated
over that completion.

## References

* [Stacks Project, Tag 0F1S](https://stacks.math.columbia.edu/tag/0F1S)
-/

@[expose] public section

namespace TopologicalRing

section

open Filter Topology


universe u v


variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The transition map `M / I ^ n N → M / I ^ m N` for `m ≤ n`. -/
public abbrev completionAlongTransitionMap (I : Ideal R) (N : Submodule R M) {m n : ℕ} (h : m ≤ n) :
    M ⧸ (I ^ n • N : Submodule R M) →ₗ[R] M ⧸ (I ^ m • N : Submodule R M) :=
  Submodule.factor (Submodule.smul_mono (Ideal.pow_le_pow_right h) le_rfl)

/-- The compatible families defining the completion of `M` along `I ^ n N`. -/
public def completionAlongSubmodule (I : Ideal R) (N : Submodule R M) :
    Submodule R (∀ n : ℕ, M ⧸ (I ^ n • N : Submodule R M)) where
  carrier := { f | ∀ {m n : ℕ} (h : m ≤ n), completionAlongTransitionMap I N h (f n) = f m }
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg m n h
    simp only [Pi.add_apply, map_add, hf h, hg h]
  smul_mem' := by
    intro r f hf m n h
    simp only [Pi.smul_apply, map_smul, hf h]

/-- The completion of `M` along the filtration `I ^ n N`. -/
public abbrev CompletionAlong (I : Ideal R) (N : Submodule R M) : Type v :=
  completionAlongSubmodule I N

namespace CompletionAlong

/-- The inverse-limit topology on the completion along `N`, with discrete finite-level
quotients. -/
@[instance_reducible]
public noncomputable def limitTopology (I : Ideal R) (N : Submodule R M) :
    TopologicalSpace (CompletionAlong I N) :=
  TopologicalSpace.induced Subtype.val <|
    @Pi.topologicalSpace ℕ (fun n ↦ M ⧸ (I ^ n • N : Submodule R M)) (fun _ ↦ ⊥)

end CompletionAlong

/-- The inverse-limit topology on the ordinary adic completion of a module, with discrete
finite-level quotients. -/
@[instance_reducible]
public noncomputable def adicCompletionLimitTopology (I : Ideal R) (N : Submodule R M) :
    TopologicalSpace (AdicCompletion I N) :=
  TopologicalSpace.induced Subtype.val <|
    @Pi.topologicalSpace ℕ
      (fun n ↦ N ⧸ (I ^ n • ⊤ : Submodule R N)) (fun _ ↦ ⊥)

/-- The map on the `n`-th quotient induced by the inclusion `N → M`. -/
public def completionMapComponent (I : Ideal R) (N : Submodule R M) (n : ℕ) :
    N ⧸ (I ^ n • ⊤ : Submodule R N) →ₗ[R] M ⧸ (I ^ n • N : Submodule R M) :=
  Submodule.mapQ (I ^ n • ⊤ : Submodule R N) (I ^ n • N : Submodule R M) N.subtype <| by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'', Submodule.map_top,
      Submodule.range_subtype]

/-- The canonical map from the `I`-adic completion of `N` to the completion of `M` along
`I ^ n N`. -/
public noncomputable def completionMap (I : Ideal R) (N : Submodule R M) :
    AdicCompletion I N →ₗ[R] CompletionAlong I N where
  toFun f := ⟨fun n ↦ completionMapComponent I N n (AdicCompletion.eval I N n f), by
    intro m n h
    change completionAlongTransitionMap I N h
      (completionMapComponent I N n (AdicCompletion.eval I N n f)) =
        completionMapComponent I N m (AdicCompletion.eval I N m f)
    have heval : AdicCompletion.transitionMap I N h (AdicCompletion.eval I N n f) =
        AdicCompletion.eval I N m f := by
      simpa only [AdicCompletion.eval_apply] using
        AdicCompletion.transitionMap_comp_eval_apply I N h f
    rw [← heval]
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective (I ^ n • ⊤ : Submodule R N)
      (AdicCompletion.eval I N n f)
    rw [← hx]
    simp only [AdicCompletion.transitionMap, completionMapComponent, Submodule.mapQ_apply,
      completionAlongTransitionMap]
    rfl⟩
  map_add' f g := by
    apply Subtype.ext
    funext n
    change completionMapComponent I N n (AdicCompletion.eval I N n (f + g)) =
      completionMapComponent I N n (AdicCompletion.eval I N n f) +
        completionMapComponent I N n (AdicCompletion.eval I N n g)
    rw [map_add, map_add]
  map_smul' r f := by
    apply Subtype.ext
    funext n
    change completionMapComponent I N n (AdicCompletion.eval I N n (r • f)) =
      r • completionMapComponent I N n (AdicCompletion.eval I N n f)
    rw [map_smul, map_smul]

private lemma completionMapComponent_injective (I : Ideal R) (N : Submodule R M) (n : ℕ) :
    Function.Injective (completionMapComponent I N n) := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (I ^ n • ⊤ : Submodule R N) x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (I ^ n • ⊤ : Submodule R N) y
  rw [Submodule.Quotient.eq]
  have hxy' : Submodule.Quotient.mk (N.subtype x) =
      (Submodule.Quotient.mk (N.subtype y) : M ⧸ (I ^ n • N : Submodule R M)) := by
    simpa only [completionMapComponent, Submodule.mapQ_apply] using hxy
  rw [Submodule.Quotient.eq] at hxy'
  exact (Submodule.mem_smul_top_iff (I ^ n) N (x - y)).2 hxy'

/-- The canonical map from the completion of `N` is injective. -/
public lemma completionMap_injective (I : Ideal R) (N : Submodule R M) :
    Function.Injective (completionMap I N) := fun _ _ hfg ↦
  Subtype.ext <| funext fun n ↦
    completionMapComponent_injective I N n (congr_arg (fun x ↦ x.1 n) hfg)

private lemma range_completionMap_eq (I : Ideal R) (N : Submodule R M) :
    ((completionMap I N).range : Set (CompletionAlong I N)) = {f | f.1 0 = 0} := by
  classical
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    change completionMapComponent I N 0 (AdicCompletion.eval I N 0 g) = 0
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective
      (I ^ 0 • ⊤ : Submodule R N) (AdicCompletion.eval I N 0 g)
    rw [← hz]
    simp only [completionMapComponent, Submodule.mapQ_apply]
    apply (Submodule.Quotient.eq _).2
    simp
  · intro hf
    let x : ∀ n : ℕ, M := fun n ↦ Classical.choose
      (Submodule.Quotient.mk_surjective (I ^ n • N : Submodule R M) (f.1 n))
    have hx (n : ℕ) : Submodule.Quotient.mk (x n) = f.1 n :=
      Classical.choose_spec
        (Submodule.Quotient.mk_surjective (I ^ n • N : Submodule R M) (f.1 n))
    have hxN (n : ℕ) : x n ∈ N := by
      have hc := f.property (Nat.zero_le n)
      rw [← hx n, hf] at hc
      simp only [completionAlongTransitionMap, Submodule.factor,
        Submodule.mapQ_apply, LinearMap.id_apply] at hc
      rw [← Submodule.Quotient.mk_zero, Submodule.Quotient.eq] at hc
      simpa using hc
    let y : ∀ n : ℕ, N := fun n ↦ ⟨x n, hxN n⟩
    have hycompat {m n : ℕ} (h : m ≤ n) :
        AdicCompletion.transitionMap I N h
          (Submodule.Quotient.mk (y n)) = Submodule.Quotient.mk (y m) := by
      have hc := f.property h
      rw [← hx n, ← hx m] at hc
      simp only [AdicCompletion.transitionMap, Submodule.factorPow, Submodule.factor,
        Submodule.mapQ_apply, LinearMap.id_apply]
      rw [Submodule.Quotient.eq]
      simp only [completionAlongTransitionMap, Submodule.factor,
        Submodule.mapQ_apply, LinearMap.id_apply] at hc
      rw [Submodule.Quotient.eq] at hc
      exact (Submodule.mem_smul_top_iff (I ^ m) N (y n - y m)).2 hc
    let g : AdicCompletion I N := ⟨fun n ↦ Submodule.Quotient.mk (y n), fun h ↦ hycompat h⟩
    exact ⟨g, Subtype.ext (funext hx)⟩

/-- The completed image of `N` is open in the completion of `M` along `I ^ n N`. -/
public lemma isOpen_range_completionMap (I : Ideal R) (N : Submodule R M) :
    @IsOpen (CompletionAlong I N) (CompletionAlong.limitTopology I N)
      ((completionMap I N).range : Set (CompletionAlong I N)) := by
  rw [range_completionMap_eq]
  let (n : ℕ) : TopologicalSpace (M ⧸ (I ^ n • N : Submodule R M)) := ⊥
  rw [isOpen_induced_iff]
  refine ⟨{f : ∀ n : ℕ, M ⧸ (I ^ n • N : Submodule R M) | f 0 = 0}, ?_, rfl⟩
  exact isOpen_pi_iff.2 fun f hf ↦
    ⟨{0}, fun n ↦ if n = 0 then {0} else Set.univ, by
      refine ⟨?_, ?_⟩
      · intro n hn
        rw [Finset.mem_singleton] at hn
        subst n
        exact ⟨by trivial, by simpa using hf⟩
      · intro g hg
        have := hg 0 (by simp)
        simpa using this⟩

private lemma induced_bot_of_injective {X Y : Type*} (f : X → Y)
    (hf : Function.Injective f) : TopologicalSpace.induced f ⊥ = ⊥ :=
  TopologicalSpace.ext <| funext fun s ↦ propext
    ⟨fun _ ↦ by trivial, fun _ ↦ ⟨f '' s, by trivial, Set.preimage_image_eq s hf⟩⟩

/-- The topology induced on the completed copy of `N` is its inverse-limit topology. -/
public lemma induced_limitTopology_completionMap (I : Ideal R) (N : Submodule R M) :
    TopologicalSpace.induced (completionMap I N)
      (CompletionAlong.limitTopology I N) = adicCompletionLimitTopology I N := by
  let (n : ℕ) : TopologicalSpace (M ⧸ (I ^ n • N : Submodule R M)) := ⊥
  let (n : ℕ) : TopologicalSpace (N ⧸ (I ^ n • ⊤ : Submodule R N)) := ⊥
  unfold CompletionAlong.limitTopology adicCompletionLimitTopology
  rw [induced_compose, induced_to_pi]
  have hd := induced_to_pi (fun f : AdicCompletion I N ↦
    (f.1 : ∀ n : ℕ, N ⧸ (I ^ n • ⊤ : Submodule R N)))
  change _ = TopologicalSpace.induced
    (fun f : AdicCompletion I N ↦
      (f.1 : ∀ n : ℕ, N ⧸ (I ^ n • ⊤ : Submodule R N))) Pi.topologicalSpace
  rw [hd]
  apply iInf_congr
  intro n
  change TopologicalSpace.induced
      (fun f : AdicCompletion I N ↦
        completionMapComponent I N n (AdicCompletion.eval I N n f)) ⊥ =
    TopologicalSpace.induced (fun f : AdicCompletion I N ↦ AdicCompletion.eval I N n f) ⊥
  calc
    _ = TopologicalSpace.induced (fun f : AdicCompletion I N ↦ AdicCompletion.eval I N n f)
        (TopologicalSpace.induced (completionMapComponent I N n) ⊥) :=
      (induced_compose (f := fun f : AdicCompletion I N ↦ AdicCompletion.eval I N n f)
        (g := completionMapComponent I N n)).symm
    _ = _ := by rw [induced_bot_of_injective _ (completionMapComponent_injective I N n)]

section Topology

variable [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousSMul R M]

omit [TopologicalSpace R] [IsTopologicalRing R] [ContinuousSMul R M] in
/-- Every positive power `I ^ n N` is open in `M`. -/
public lemma isOpen_pow_smul (I : Ideal R) (N : Submodule R M) (hN : IsOpen (N : Set M))
    (hAdic : (𝓝 (0 : N)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ ((I ^ n • ⊤ : Submodule R N) : Set N)))
    (n : ℕ) (_hn : 1 ≤ n) : IsOpen ((I ^ n • N : Submodule R M) : Set M) := by
  have hmem : ((I ^ n • ⊤ : Submodule R N) : Set N) ∈ 𝓝 (0 : N) :=
    hAdic.mem_iff.2 ⟨n, trivial, Set.Subset.rfl⟩
  have hopenN : IsOpen ((I ^ n • ⊤ : Submodule R N) : Set N) :=
    (I ^ n • ⊤ : Submodule R N).toAddSubgroup.isOpen_of_mem_nhds hmem
  obtain ⟨U, hU, hpre⟩ := isOpen_induced_iff.1 hopenN
  have himage : N.subtype '' ((I ^ n • ⊤ : Submodule R N) : Set N) =
      ((I ^ n • N : Submodule R M) : Set M) := by
    rw [← Submodule.map_coe, Submodule.map_smul'', Submodule.map_top,
      Submodule.range_subtype]
  rw [← himage, ← hpre]
  convert hN.inter hU using 1
  ext x
  simp [and_comm]

omit [TopologicalSpace R] [IsTopologicalRing R] [ContinuousSMul R M] in
/-- The positive powers `I ^ n N` form a neighbourhood basis of zero in `M`. -/
public lemma hasBasis_pow_smul (I : Ideal R) (N : Submodule R M) (hN : IsOpen (N : Set M))
    (hAdic : (𝓝 (0 : N)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ ((I ^ n • ⊤ : Submodule R N) : Set N))) :
    (𝓝 (0 : M)).HasBasis (fun n : ℕ ↦ 1 ≤ n)
      (fun n ↦ ((I ^ n • N : Submodule R M) : Set M)) := by
  rw [Filter.hasBasis_iff]
  intro U
  constructor
  · intro hU
    have hpre : N.subtype ⁻¹' U ∈ 𝓝 (0 : N) := by
      rw [nhds_induced]
      exact preimage_mem_comap hU
    obtain ⟨n, -, hn⟩ := hAdic.mem_iff.1 hpre
    refine ⟨n + 1, Nat.le_add_left 1 n, ?_⟩
    intro x hx
    have hpow : I ^ (n + 1) • N ≤ I ^ n • N :=
      Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_succ n)) le_rfl
    exact hn ((Submodule.mem_smul_top_iff (I ^ n) N ⟨x, Submodule.smul_le_right hx⟩).2
      (hpow hx))
  · rintro ⟨n, hn, hsub⟩
    exact Filter.mem_of_superset
      ((isOpen_pow_smul I N hN hAdic n hn).mem_nhds (Submodule.zero_mem _)) hsub

end Topology

end

section

open Filter Topology


private lemma adicModuleTopology_nhds_hasBasis
    {R : Type*} [CommRing R] (I : Ideal R) {A : Type*}
    [AddCommGroup A] [Module R A] (x : A) :
    (@nhds A (I.adicModuleTopology A) x).HasBasis (fun _ : ℕ => True)
      (fun n => (fun y : A => x + y) ''
        (((I ^ n : Ideal R) • (⊤ : Submodule R A) : Submodule R A) : Set A)) := by
  let : TopologicalSpace R := I.adicTopology
  let B := I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis A)
  change (@nhds A B.topology x).HasBasis _ _
  rw [B.toAddGroupFilterBasis.nhds_eq]
  exact B.toAddGroupFilterBasis.hasBasis x |>.to_hasBasis
    (fun U hU => by
      rcases hU with ⟨n, rfl⟩
      exact ⟨n, trivial, Set.Subset.rfl⟩)
    (fun n _ => ⟨((I ^ n : Ideal R) • (⊤ : Submodule R A) : Submodule R A),
      ⟨n, rfl⟩, Set.Subset.rfl⟩)

private lemma adicCompletionLimitTopology_eq_adicModuleTopology
    {R : Type*} [CommRing R] (I : Ideal R) (hI : I.FG) {M : Type*}
    [AddCommGroup M] [Module R M] (N : Submodule R M) :
    TopologicalRing.adicCompletionLimitTopology I N =
      I.adicModuleTopology (AdicCompletion I N) := by
  classical
  let A := AdicCompletion I N
  let t := TopologicalRing.adicCompletionLimitTopology I N
  let s := I.adicModuleTopology A
  let (n : ℕ) : TopologicalSpace (N ⧸ (I ^ n • (⊤ : Submodule R N))) := ⊥
  let (n : ℕ) : DiscreteTopology (N ⧸ (I ^ n • (⊤ : Submodule R N))) :=
    discreteTopology_bot _
  have hlim (x : A) : (@nhds A t x).HasBasis (fun J : Set ℕ => J.Finite)
      (fun J => (fun y : A => y.1) ⁻¹' J.pi (fun n => ({x.1 n} : Set _))) := by
    change (@nhds A (TopologicalSpace.induced Subtype.val
      (@Pi.topologicalSpace ℕ (fun n => N ⧸ (I ^ n • (⊤ : Submodule R N)))
        (fun _ => ⊥))) x).HasBasis _ _
    rw [nhds_induced, nhds_pi]
    simp only [nhds_discrete]
    have hb := Filter.hasBasis_pi_principal
      (fun n : ℕ => ({x.1 n} : Set (N ⧸ (I ^ n • (⊤ : Submodule R N)))) )
    simpa only [← Filter.principal_singleton] using hb.comap (fun y : A => y.1)
  have hfilters (x : A) : @nhds A t x = @nhds A s x := by
    apply (hlim x).ext (adicModuleTopology_nhds_hasBasis I x)
    · intro J hJ
      let F := hJ.toFinset
      let n := F.sup id
      refine ⟨n, trivial, ?_⟩
      intro y hy
      obtain ⟨z, hz, rfl⟩ := hy
      have hn : z.1 n = 0 :=
        LinearMap.mem_ker.mp ((AdicCompletion.pow_smul_top_eq_ker_eval hI).le hz)
      change (x + z).1 ∈ J.pi (fun j => ({x.1 j} : Set _))
      apply Set.mem_pi.2
      intro i hi
      have hiF : i ∈ F := hJ.mem_toFinset.2 hi
      have hi_le : i ≤ n := by
        simpa only [id_eq] using (Finset.le_sup (s := F) (f := id) hiF)
      have hc := z.property hi_le
      change AdicCompletion.transitionMap I N hi_le (z.1 n) = z.1 i at hc
      rw [hn] at hc
      have hizero : z.1 i = 0 := by simpa using hc.symm
      change x.1 i + z.1 i = x.1 i
      simp [hizero]
    · intro n _
      refine ⟨{n}, Set.finite_singleton n, ?_⟩
      intro y hy
      change y.1 ∈ ({n} : Set ℕ).pi (fun j => ({x.1 j} : Set _)) at hy
      have heq : y.1 n = x.1 n := by simpa using (Set.mem_pi.1 hy) n (by simp)
      let z := y - x
      have hzeval : AdicCompletion.eval I N n z = 0 := by
        change y.1 n - x.1 n = 0
        rw [heq, sub_self]
      have hzpow : z ∈ I ^ n • (⊤ : Submodule R A) := by
        rw [AdicCompletion.pow_smul_top_eq_ker_eval hI]
        exact LinearMap.mem_ker.mpr hzeval
      exact ⟨z, hzpow, by simp [z]⟩
  exact TopologicalSpace.ext_nhds hfilters

private lemma adicModuleTopology_induced_linearEquiv
    {R : Type*} [CommRing R] (I : Ideal R) {A B : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (e : A ≃ₗ[R] B) :
    TopologicalSpace.induced e (I.adicModuleTopology B) = I.adicModuleTopology A := by
  classical
  let t := TopologicalSpace.induced e (I.adicModuleTopology B)
  let s := I.adicModuleTopology A
  let : TopologicalSpace A := I.adicModuleTopology A
  let : TopologicalSpace B := I.adicModuleTopology B
  have hA := adicModuleTopology_nhds_hasBasis I (A := A)
  have hB := adicModuleTopology_nhds_hasBasis I (A := B)
  have hmap (n : ℕ) :
      Submodule.map (e : A →ₗ[R] B) ((I ^ n : Ideal R) • (⊤ : Submodule R A)) =
        (I ^ n : Ideal R) • (⊤ : Submodule R B) := by
    rw [Submodule.map_smul'', Submodule.map_top, e.range]
  have hset (x : A) (n : ℕ) :
      e ⁻¹' ((fun y : B => e x + y) ''
        (((I ^ n : Ideal R) • (⊤ : Submodule R B) : Submodule R B) : Set B)) =
      (fun y : A => x + y) ''
        (((I ^ n : Ideal R) • (⊤ : Submodule R A) : Submodule R A) : Set A) := by
    ext y
    constructor
    · rintro ⟨z, hz, hy⟩
      refine ⟨y - x, ?_, by simp⟩
      have heq : e (y - x) = z := by
        rw [map_sub, ← hy]
        simp
      have hm : e (y - x) ∈ (I ^ n : Ideal R) • (⊤ : Submodule R B) := by rwa [heq]
      rw [← hmap, Submodule.mem_map_equiv] at hm
      simpa using hm
    · rintro ⟨z, hz, rfl⟩
      refine ⟨e z, ?_, by simp⟩
      rw [← hmap]
      exact Submodule.mem_map.mpr ⟨z, hz, rfl⟩
  have hfilters (x : A) : @nhds A t x = @nhds A s x := by
    rw [show t = TopologicalSpace.induced e (I.adicModuleTopology B) from rfl,
      nhds_induced]
    apply (hB (e x)).comap e |>.ext (hA x)
    · intro n _
      exact ⟨n, trivial, (hset x n).symm.subset⟩
    · intro n _
      exact ⟨n, trivial, (hset x n).subset⟩
  exact TopologicalSpace.ext_nhds hfilters

private lemma induced_topology_injective_of_injective
    {A B : Type*} (f : A → B) (_hf : Function.Injective f) (hsurj : Function.Surjective f)
    (t s : TopologicalSpace B)
  (h : TopologicalSpace.induced f t = TopologicalSpace.induced f s) : t = s := by
  apply TopologicalSpace.ext
  funext U
  apply propext
  have heq (r : TopologicalSpace B) :
      @IsOpen A (TopologicalSpace.induced f r) (f ⁻¹' U) ↔ @IsOpen B r U := by
    rw [isOpen_induced_iff]
    constructor
    · rintro ⟨V, hV, hpre⟩
      simpa [(Set.preimage_injective.mpr hsurj) hpre] using hV
    · exact fun hU => ⟨U, hU, rfl⟩
  exact (heq t).symm.trans ((Iff.of_eq (congrArg
    (fun r : TopologicalSpace A => @IsOpen A r (f ⁻¹' U)) h)).trans (heq s))

/-- The completion of a module containing an open `I`-adic submodule again contains an open
submodule with the `I`-adic topology. -/
@[stacks 0F1S "open_adic_completion"]
public lemma exists_isOpen_adic_submodule_completionAlong
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousSMul R M]
    (I : Ideal R) (hI : I.FG) (N : Submodule R M) (_hN : IsOpen (N : Set M))
    (_hAdic : (𝓝 (0 : N)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ ((I ^ n • ⊤ : Submodule R N) : Set N))) :
    ∃ P : Submodule R (TopologicalRing.CompletionAlong I N),
      @IsOpen (TopologicalRing.CompletionAlong I N)
          (TopologicalRing.CompletionAlong.limitTopology I N) (P : Set _) ∧
        TopologicalSpace.induced
          (fun p : P => (p : TopologicalRing.CompletionAlong I N))
          (TopologicalRing.CompletionAlong.limitTopology I N) = I.adicModuleTopology P := by
  classical
  let φ := TopologicalRing.completionMap I N
  let P := φ.range
  refine ⟨P, ?_, ?_⟩
  · simpa [φ] using TopologicalRing.isOpen_range_completionMap I N
  · let e : AdicCompletion I N ≃ₗ[R] P :=
      LinearEquiv.ofBijective (LinearMap.rangeRestrict φ)
        ⟨fun _ _ hxy ↦ TopologicalRing.completionMap_injective I N (congrArg Subtype.val hxy),
          LinearMap.surjective_rangeRestrict φ⟩
    have htransport : TopologicalSpace.induced e (I.adicModuleTopology P) =
        TopologicalRing.adicCompletionLimitTopology I N := by
      calc
        _ = I.adicModuleTopology (AdicCompletion I N) :=
          adicModuleTopology_induced_linearEquiv (R := R) I
            (A := AdicCompletion I N) (B := P) e
        _ = TopologicalRing.adicCompletionLimitTopology I N :=
          (adicCompletionLimitTopology_eq_adicModuleTopology I hI N).symm
    have hcompleted : TopologicalSpace.induced e
        (TopologicalSpace.induced (fun p : P => (p : TopologicalRing.CompletionAlong I N))
          (TopologicalRing.CompletionAlong.limitTopology I N)) =
        TopologicalRing.adicCompletionLimitTopology I N := by
      rw [induced_compose]
      change TopologicalSpace.induced φ (TopologicalRing.CompletionAlong.limitTopology I N) = _
      exact TopologicalRing.induced_limitTopology_completionMap I N
    exact (induced_topology_injective_of_injective e e.injective e.surjective
      (I.adicModuleTopology P)
      (TopologicalSpace.induced (fun p : P => (p : TopologicalRing.CompletionAlong I N))
        (TopologicalRing.CompletionAlong.limitTopology I N))
      (htransport.trans hcompleted.symm)).symm

end

section QuotientIdealPower

universe u v

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- An element lies in `Ideal.span s • P`, for a finite set of ring elements `s`, exactly when
it is a combination `∑ a ∈ s, a • c a` with all coefficients `c a` taken from `P`. -/
private lemma mem_finsetSpan_smul_iff (s : Finset R) (P : Submodule R M) (x : M) :
    x ∈ (Ideal.span (s : Set R)) • P ↔
      ∃ c : R → M, (∀ a : R, c a ∈ P) ∧ x = ∑ a ∈ s, a • c a := by
  classical
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr m hm
      obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 hr
      refine ⟨fun a => f a • m, fun a => P.smul_mem _ hm, ?_⟩
      rw [← hf, Finset.sum_smul]
      exact Finset.sum_congr rfl fun a _ => by
        simp only [smul_eq_mul, smul_smul, mul_comm]
    · rintro x y ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
      refine ⟨c + d, fun a => P.add_mem (hc a) (hd a), ?_⟩
      simp only [Pi.add_apply, smul_add]
      rw [Finset.sum_add_distrib]
  · rintro ⟨c, hc, rfl⟩
    exact Submodule.sum_mem _ fun a ha =>
      Submodule.smul_mem_smul (Ideal.subset_span (Finset.mem_coe.2 ha)) (hc a)

/-- A family in the completion along `I ^ n N` has representatives `a k` in `M` whose successive
differences `a k - a m`, for `m ≤ k`, lie in `I ^ m N`. -/
private lemma exists_rep_sub_mem_pow_smul (I : Ideal R) (N : Submodule R M)
    (x : CompletionAlong I N) :
    ∃ a : ℕ → M, (∀ k : ℕ, (Submodule.Quotient.mk (a k) : M ⧸ (I ^ k • N : Submodule R M)) =
        x.val k) ∧ ∀ {m k : ℕ}, m ≤ k → a k - a m ∈ (I ^ m • N : Submodule R M) := by
  choose a ha using fun k : ℕ => Submodule.Quotient.mk_surjective _ (x.val k)
  refine ⟨a, ha, fun {m k} h => ?_⟩
  have hc := x.property h
  rw [← ha k, ← ha m] at hc
  have hc' : (Submodule.Quotient.mk (a k) : M ⧸ (I ^ m • N : Submodule R M)) =
      Submodule.Quotient.mk (a m) := hc
  rwa [Submodule.Quotient.eq] at hc'

namespace CompletionAlong

/-- Evaluation of the completion of `M` along the filtration `I ^ n N` at level `n`. -/
public def eval (I : Ideal R) (N : Submodule R M) (n : ℕ) :
    CompletionAlong I N →ₗ[R] M ⧸ (I ^ n • N : Submodule R M) where
  toFun f := f.val n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The canonical map from the completion of `M` along the filtration `I ^ n N` to the
quotient `M / I ^ n M`. -/
public def evalPow (I : Ideal R) (N : Submodule R M) (n : ℕ) :
    CompletionAlong I N →ₗ[R] M ⧸ (I ^ n • ⊤ : Submodule R M) :=
  (Submodule.factor (Submodule.smul_mono le_rfl le_top)).comp (eval I N n)

/-- The canonical map to `M / I ^ n M` is surjective: the constant families are already
enough to hit every class. -/
public lemma evalPow_surjective (I : Ideal R) (N : Submodule R M) (n : ℕ) :
    Function.Surjective (evalPow I N n) := by
  intro y
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (I ^ n • ⊤ : Submodule R M) y
  refine ⟨⟨fun _ => Submodule.Quotient.mk a, ?_⟩, rfl⟩
  intro m k h
  rfl

/-- The submodule `I ^ n M^` is contained in the kernel of `M^ → M / I ^ n M`. -/
public lemma pow_smul_top_le_ker_evalPow (I : Ideal R) (N : Submodule R M) (n : ℕ) :
    (I ^ n • ⊤ : Submodule R (CompletionAlong I N)) ≤ (evalPow I N n).ker := by
  intro x hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr g _
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective
      (I ^ n • ⊤ : Submodule R M) (evalPow I N n g)
    rw [LinearMap.mem_ker, map_smul, ← ha, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · intro x y hx hy
    exact Submodule.add_mem _ hx hy

/-- The kernel of `M^ → M / I ^ n M` is contained in `I ^ n M^`.  Writing `I ^ n` with finitely
many generators, a compatible family killed at level `n` is assembled, generator by generator,
from a convergent sequence of successive lifts. -/
private lemma ker_evalPow_le_pow_smul_top (I : Ideal R) (hI : I.FG) (N : Submodule R M) (n : ℕ) :
    (evalPow I N n).ker ≤ (I ^ n • ⊤ : Submodule R (CompletionAlong I N)) := by
  classical
  intro x hx
  obtain ⟨s, hs⟩ := hI.pow (n := n)
  obtain ⟨a, ha, hdiff⟩ := exists_rep_sub_mem_pow_smul I N x
  -- the level-`n` representative lies in `I ^ n M`
  have hxn : a n ∈ (I ^ n • ⊤ : Submodule R M) := by
    have h0 : evalPow I N n x = 0 := hx
    rw [evalPow, LinearMap.comp_apply] at h0
    have h0' : (Submodule.Quotient.mk (a n) : M ⧸ (I ^ n • ⊤ : Submodule R M)) = 0 := by
      rw [← h0]
      change _ = Submodule.factor _ (x.val n)
      rw [← ha n]
      rfl
    rwa [Submodule.Quotient.mk_eq_zero] at h0'
  -- splitting the filtration step `I ^ (n + k) N` through the generators of `I ^ n`
  have hsplit : ∀ k : ℕ, (I ^ (n + k) • N : Submodule R M) =
      (Ideal.span (s : Set R)) • (I ^ k • N : Submodule R M) := by
    intro k
    rw [hs, ← Submodule.mul_smul, ← pow_add]
  have hinc : ∀ k : ℕ, ∃ c : R → M, (∀ t : R, c t ∈ (I ^ k • N : Submodule R M)) ∧
      a (n + k + 1) - a (n + k) = ∑ t ∈ s, t • c t := by
    intro k
    have h1 : a (n + k + 1) - a (n + k) ∈ (I ^ (n + k) • N : Submodule R M) :=
      hdiff (Nat.le_succ _)
    rw [hsplit k] at h1
    exact (mem_finsetSpan_smul_iff s _ _).1 h1
  choose c hc hceq using hinc
  obtain ⟨b₀, hb₀⟩ : ∃ b : R → M, a n = ∑ t ∈ s, t • b t := by
    have hmem : a n ∈ (Ideal.span (s : Set R)) • (⊤ : Submodule R M) := by
      rw [hs]; exact hxn
    obtain ⟨b, -, hb⟩ := (mem_finsetSpan_smul_iff s _ _).1 hmem
    exact ⟨b, hb⟩
  -- the successive lifts, one coefficient for each generator
  let B : ℕ → R → M := fun k => Nat.rec (motive := fun _ => R → M) b₀ (fun j prev => prev + c j) k
  have hBsucc : ∀ (j : ℕ) (t : R), B (j + 1) t = B j t + c j t := fun _ _ => rfl
  have hBsum : ∀ k : ℕ, ∑ t ∈ s, t • B k t = a (n + k) := by
    intro k
    induction k with
    | zero =>
      change ∑ t ∈ s, t • b₀ t = a n
      exact hb₀.symm
    | succ j ih =>
      have hsplit' : ∑ t ∈ s, t • B (j + 1) t
          = (∑ t ∈ s, t • B j t) + ∑ t ∈ s, t • c j t := by
        simp only [hBsucc, smul_add]
        rw [Finset.sum_add_distrib]
      rw [hsplit', ih, ← hceq j]
      abel
  have hBdiff : ∀ (m k : ℕ), m ≤ k → ∀ t : R,
      B k t - B m t ∈ (I ^ m • N : Submodule R M) := by
    intro m k h
    induction k, h using Nat.le_induction with
    | base => intro t; simp
    | succ j hj ih =>
      intro t
      have hstep : B (j + 1) t - B j t ∈ (I ^ m • N : Submodule R M) := by
        have h1 : B (j + 1) t - B j t = c j t := by rw [hBsucc]; abel
        rw [h1]
        exact Submodule.smul_mono (Ideal.pow_le_pow_right hj) le_rfl (hc j t)
      have hsum : B (j + 1) t - B m t = (B (j + 1) t - B j t) + (B j t - B m t) := by abel
      rw [hsum]
      exact Submodule.add_mem _ hstep (ih t)
  -- the assembled coefficients, as elements of the completion
  have hycompat : ∀ (t : R) {m k : ℕ} (h : m ≤ k),
      completionAlongTransitionMap I N h
          (Submodule.Quotient.mk (B k t) : M ⧸ (I ^ k • N : Submodule R M)) =
        Submodule.Quotient.mk (B m t) := by
    intro t m k h
    change (Submodule.Quotient.mk (B k t) : M ⧸ (I ^ m • N : Submodule R M)) =
      Submodule.Quotient.mk (B m t)
    rw [Submodule.Quotient.eq]
    exact hBdiff m k h t
  let y : R → CompletionAlong I N := fun t =>
    ⟨fun k => Submodule.Quotient.mk (B k t), fun h => hycompat t h⟩
  have hxsum : x = ∑ t ∈ s, t • y t := by
    apply Subtype.ext
    funext k
    have hval : ((∑ t ∈ s, t • y t : CompletionAlong I N) : ∀ j, M ⧸ (I ^ j • N : Submodule R M)) k
        = ∑ t ∈ s, t • (Submodule.Quotient.mk (B k t) : M ⧸ (I ^ k • N : Submodule R M)) := by
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, Finset.sum_apply,
        Pi.smul_apply]
      rfl
    rw [hval, ← ha k]
    have hshift : (Submodule.Quotient.mk (a k) : M ⧸ (I ^ k • N : Submodule R M)) =
        Submodule.Quotient.mk (a (n + k)) := by
      rw [Submodule.Quotient.eq]
      have := hdiff (m := k) (k := n + k) (Nat.le_add_left k n)
      simpa using Submodule.neg_mem _ this
    rw [hshift, ← hBsum k]
    simp only [← Submodule.mkQ_apply, map_sum, map_smul]
  have hmem : x ∈ (Ideal.span (s : Set R)) • (⊤ : Submodule R (CompletionAlong I N)) :=
    (mem_finsetSpan_smul_iff s ⊤ x).2 ⟨y, fun _ => Submodule.mem_top, hxsum⟩
  rwa [hs] at hmem

/-- For a finitely generated ideal `I`, the submodule `I ^ n M^` of the completion of `M` along
the filtration `I ^ n N` is exactly the kernel of the canonical map to `M / I ^ n M`. -/
public lemma pow_smul_top_eq_ker_evalPow (I : Ideal R) (hI : I.FG) (N : Submodule R M) (n : ℕ) :
    (I ^ n • ⊤ : Submodule R (CompletionAlong I N)) = (evalPow I N n).ker :=
  le_antisymm (pow_smul_top_le_ker_evalPow I N n) (ker_evalPow_le_pow_smul_top I hI N n)

/-- The second conclusion of Tag 0F1S at the level of the filtration `I ^ n N`:
`M^ / I ^ n M^ = M / I ^ n M`. -/
@[stacks 0F1S "completion_mod_ideal_power"]
public noncomputable def quotPowEquiv (I : Ideal R) (hI : I.FG) (N : Submodule R M) (n : ℕ) :
    ((CompletionAlong I N) ⧸ (I ^ n • ⊤ : Submodule R (CompletionAlong I N))) ≃ₗ[R]
      (M ⧸ (I ^ n • ⊤ : Submodule R M)) :=
  (Submodule.quotEquivOfEq _ _ (pow_smul_top_eq_ker_evalPow I hI N n)).trans
    ((evalPow I N n).quotKerEquivOfSurjective (evalPow_surjective I N n))

end CompletionAlong

end QuotientIdealPower

section OverOpenSubmodules

open Filter Topology

universe u v

/-- The index type of open submodules of a topological module: the canonical fundamental
system of a linearly topologized module. -/
public abbrev OpenSubmoduleIndex (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M]
    [Module R M] [TopologicalSpace M] : Type v :=
  { P : Submodule R M // IsOpen (P : Set M) }

/-- The compatible families defining the completion of `M` over all of its open submodules. -/
public def completionOverOpenSubmodule (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M]
    [Module R M] [TopologicalSpace M] :
    Submodule R (∀ P : OpenSubmoduleIndex R M, M ⧸ P.1) where
  carrier := { f | ∀ {P Q : OpenSubmoduleIndex R M} (h : P.1 ≤ Q.1),
    Submodule.factor h (f P) = f Q }
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg P Q h
    simp only [Pi.add_apply, map_add, hf h, hg h]
  smul_mem' := by
    intro r f hf P Q h
    simp only [Pi.smul_apply, map_smul, hf h]

/-- The completion `M^` of a topological module `M`: the inverse limit of the quotients
`M / P` over all open submodules `P` of `M`. -/
public abbrev CompletionOverOpen (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M]
    [Module R M] [TopologicalSpace M] : Type v :=
  completionOverOpenSubmodule R M

/-- Compatibility of a family in `M^` across an inclusion of open submodules. -/
public lemma CompletionOverOpen.factor_val {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] [TopologicalSpace M] {P Q : OpenSubmoduleIndex R M}
    (h : P.1 ≤ Q.1) (f : CompletionOverOpen R M) :
    Submodule.factor h (f.val P) = f.val Q :=
  f.property h

namespace CompletionOverOpen

/-- The inverse-limit topology on `M^`, with discrete quotients `M / P`. -/
@[instance_reducible]
public noncomputable def limitTopology (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M]
    [Module R M] [TopologicalSpace M] : TopologicalSpace (CompletionOverOpen R M) :=
  TopologicalSpace.induced Subtype.val <|
    @Pi.topologicalSpace (OpenSubmoduleIndex R M) (fun P ↦ M ⧸ P.1) (fun _ ↦ ⊥)

end CompletionOverOpen

variable {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  {M : Type v} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousSMul R M]

omit [TopologicalSpace R] [IsTopologicalRing R] [ContinuousSMul R M] in
/-- Every power `I ^ n N` of an open submodule carrying the `I`-adic topology is open,
including `n = 0`, where it is `N` itself. -/
public lemma isOpen_pow_smul_of_isOpen (I : Ideal R) (N : Submodule R M)
    (hN : IsOpen (N : Set M))
    (hAdic : (𝓝 (0 : N)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ ((I ^ n • ⊤ : Submodule R N) : Set N))) (n : ℕ) :
    IsOpen ((I ^ n • N : Submodule R M) : Set M) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    exact hN
  · exact isOpen_pow_smul I N hN hAdic n hn

/-- The open submodule `I ^ n N` of `M`, as a member of the fundamental system indexing `M^`. -/
public def powOpenSubmodule (I : Ideal R) (N : Submodule R M) (hN : IsOpen (N : Set M))
    (hAdic : (𝓝 (0 : N)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ ((I ^ n • ⊤ : Submodule R N) : Set N))) (n : ℕ) :
    OpenSubmoduleIndex R M :=
  ⟨I ^ n • N, isOpen_pow_smul_of_isOpen I N hN hAdic n⟩

omit [TopologicalSpace R] [IsTopologicalRing R] [ContinuousSMul R M] in
/-- The submodules `I ^ n N` are cofinal among the open submodules of `M`: this is the
assertion that they form a fundamental system of open submodules. -/
public lemma exists_pow_smul_le (I : Ideal R) (N : Submodule R M) (hN : IsOpen (N : Set M))
    (hAdic : (𝓝 (0 : N)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ ((I ^ n • ⊤ : Submodule R N) : Set N)))
    (P : Submodule R M) (hP : IsOpen (P : Set M)) :
    ∃ n : ℕ, (I ^ n • N : Submodule R M) ≤ P := by
  obtain ⟨n, -, hsub⟩ :=
    (hasBasis_pow_smul I N hN hAdic).mem_iff.1 (hP.mem_nhds P.zero_mem)
  exact ⟨n, hsub⟩

/-- Restriction of a compatible family over all open submodules of `M` to the fundamental
system `I ^ n N`. -/
public def restrictToPow (I : Ideal R) (N : Submodule R M) (hN : IsOpen (N : Set M))
    (hAdic : (𝓝 (0 : N)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ ((I ^ n • ⊤ : Submodule R N) : Set N))) :
    CompletionOverOpen R M →ₗ[R] CompletionAlong I N where
  toFun f := ⟨fun n ↦ f.val (powOpenSubmodule I N hN hAdic n), by
    intro m n h
    have hle : (powOpenSubmodule I N hN hAdic n).1 ≤ (powOpenSubmodule I N hN hAdic m).1 :=
      Submodule.smul_mono (Ideal.pow_le_pow_right h) le_rfl
    exact CompletionOverOpen.factor_val hle f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [TopologicalSpace R] [IsTopologicalRing R] [ContinuousSMul R M] in
/-- Restricting to the fundamental system `I ^ n N` loses nothing. -/
public lemma restrictToPow_injective (I : Ideal R) (N : Submodule R M) (hN : IsOpen (N : Set M))
    (hAdic : (𝓝 (0 : N)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ ((I ^ n • ⊤ : Submodule R N) : Set N))) :
    Function.Injective (restrictToPow I N hN hAdic) := by
  intro f g hfg
  apply Subtype.ext
  funext P
  obtain ⟨n, hn⟩ := exists_pow_smul_le I N hN hAdic P.1 P.2
  have hle : (powOpenSubmodule I N hN hAdic n).1 ≤ P.1 := hn
  rw [← CompletionOverOpen.factor_val hle f, ← CompletionOverOpen.factor_val hle g]
  exact congrArg (Submodule.factor hle) (congrArg (fun z : CompletionAlong I N ↦ z.val n) hfg)

omit [TopologicalSpace R] [IsTopologicalRing R] [ContinuousSMul R M] in
/-- Every compatible family over the fundamental system `I ^ n N` extends, uniquely, to a
compatible family over all open submodules of `M`. -/
public lemma restrictToPow_surjective (I : Ideal R) (N : Submodule R M) (hN : IsOpen (N : Set M))
    (hAdic : (𝓝 (0 : N)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ ((I ^ n • ⊤ : Submodule R N) : Set N))) :
    Function.Surjective (restrictToPow I N hN hAdic) := by
  classical
  intro g
  obtain ⟨a, ha, hdiff⟩ := exists_rep_sub_mem_pow_smul I N g
  have key : ∀ (m k : ℕ) (P : Submodule R M), (I ^ m • N : Submodule R M) ≤ P →
      (I ^ k • N : Submodule R M) ≤ P → a m - a k ∈ P := by
    intro m k P hm hk
    have h1 : a (max m k) - a m ∈ (I ^ m • N : Submodule R M) := hdiff (le_max_left m k)
    have h2 : a (max m k) - a k ∈ (I ^ k • N : Submodule R M) := hdiff (le_max_right m k)
    have h3 : a m - a k = (a (max m k) - a k) - (a (max m k) - a m) := by abel
    rw [h3]
    exact Submodule.sub_mem _ (hk h2) (hm h1)
  have hlev : ∀ P : OpenSubmoduleIndex R M, ∃ n : ℕ, (I ^ n • N : Submodule R M) ≤ P.1 :=
    fun P ↦ exists_pow_smul_le I N hN hAdic P.1 P.2
  choose lev hlevle using hlev
  refine ⟨⟨fun P ↦ Submodule.Quotient.mk (a (lev P)), ?_⟩, ?_⟩
  · intro P Q h
    change (Submodule.Quotient.mk (a (lev P)) : M ⧸ Q.1) = Submodule.Quotient.mk (a (lev Q))
    rw [Submodule.Quotient.eq]
    exact key _ _ Q.1 ((hlevle P).trans h) (hlevle Q)
  · apply Subtype.ext
    funext n
    change (Submodule.Quotient.mk (a (lev (powOpenSubmodule I N hN hAdic n))) :
      M ⧸ (I ^ n • N : Submodule R M)) = g.val n
    rw [← ha n, Submodule.Quotient.eq]
    exact key _ _ _ (hlevle (powOpenSubmodule I N hN hAdic n)) le_rfl

/-- The completion of `M` over all its open submodules is the completion of `M` along the
fundamental system `I ^ n N`. -/
public noncomputable def completionOverOpenEquiv (I : Ideal R) (N : Submodule R M)
    (hN : IsOpen (N : Set M))
    (hAdic : (𝓝 (0 : N)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ ((I ^ n • ⊤ : Submodule R N) : Set N))) :
    CompletionOverOpen R M ≃ₗ[R] CompletionAlong I N :=
  LinearEquiv.ofBijective (restrictToPow I N hN hAdic)
    ⟨restrictToPow_injective I N hN hAdic, restrictToPow_surjective I N hN hAdic⟩

omit [TopologicalSpace R] [IsTopologicalRing R] [ContinuousSMul R M] in
/-- The identification of the two completions is a homeomorphism for the inverse-limit
topologies. -/
public lemma induced_limitTopology_restrictToPow (I : Ideal R) (N : Submodule R M)
    (hN : IsOpen (N : Set M))
    (hAdic : (𝓝 (0 : N)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ ((I ^ n • ⊤ : Submodule R N) : Set N))) :
    TopologicalSpace.induced (restrictToPow I N hN hAdic) (CompletionAlong.limitTopology I N) =
      CompletionOverOpen.limitTopology R M := by
  let (n : ℕ) : TopologicalSpace (M ⧸ (I ^ n • N : Submodule R M)) := ⊥
  let (P : OpenSubmoduleIndex R M) : TopologicalSpace (M ⧸ P.1) := ⊥
  unfold CompletionAlong.limitTopology CompletionOverOpen.limitTopology
  rw [induced_compose, induced_to_pi, induced_to_pi]
  apply le_antisymm
  · refine le_iInf fun P ↦ ?_
    obtain ⟨n, hn⟩ := exists_pow_smul_le I N hN hAdic P.1 P.2
    have hle : (powOpenSubmodule I N hN hAdic n).1 ≤ P.1 := hn
    refine le_trans (iInf_le _ n) ?_
    have hfun : (fun f : CompletionOverOpen R M ↦ f.val P) =
        (Submodule.factor hle) ∘ (fun f : CompletionOverOpen R M ↦
          f.val (powOpenSubmodule I N hN hAdic n)) := by
      funext f
      exact (CompletionOverOpen.factor_val hle f).symm
    change TopologicalSpace.induced
        (fun f : CompletionOverOpen R M ↦ f.val (powOpenSubmodule I N hN hAdic n)) ⊥ ≤
      TopologicalSpace.induced (fun f : CompletionOverOpen R M ↦ f.val P) ⊥
    rw [hfun, ← induced_compose]
    exact induced_mono bot_le
  · exact le_iInf fun n ↦ iInf_le _ (powOpenSubmodule I N hN hAdic n)

/-- Tag 0F1S, first conclusion, over the completion of `M` taken over all of its open
submodules: `M^` has an open submodule whose topology is `I`-adic. -/
@[stacks 0F1S "open_adic_completion"]
public lemma exists_isOpen_adic_submodule_completionOverOpen (I : Ideal R) (hI : I.FG)
    (N : Submodule R M) (hN : IsOpen (N : Set M))
    (hAdic : (𝓝 (0 : N)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ ((I ^ n • ⊤ : Submodule R N) : Set N))) :
    ∃ P : Submodule R (CompletionOverOpen R M),
      @IsOpen (CompletionOverOpen R M) (CompletionOverOpen.limitTopology R M) (P : Set _) ∧
        TopologicalSpace.induced (fun p : P ↦ (p : CompletionOverOpen R M))
          (CompletionOverOpen.limitTopology R M) = I.adicModuleTopology P := by
  obtain ⟨P₀, hP₀open, hP₀top⟩ :=
    exists_isOpen_adic_submodule_completionAlong I hI N hN hAdic
  let e := completionOverOpenEquiv I N hN hAdic
  let P : Submodule R (CompletionOverOpen R M) :=
    P₀.comap (e : CompletionOverOpen R M →ₗ[R] CompletionAlong I N)
  refine ⟨P, ?_, ?_⟩
  · have hopen := (@isOpen_induced_iff (CompletionOverOpen R M) (CompletionAlong I N)
      (CompletionAlong.limitTopology I N) (P : Set (CompletionOverOpen R M))
      (restrictToPow I N hN hAdic)).2
        ⟨(P₀ : Set (CompletionAlong I N)), hP₀open, rfl⟩
    rwa [induced_limitTopology_restrictToPow I N hN hAdic] at hopen
  · let e' : P ≃ₗ[R] P₀ := e.ofSubmodule' P₀
    have h2 : TopologicalSpace.induced e'
          (TopologicalSpace.induced (fun p : P₀ ↦ (p : CompletionAlong I N))
            (CompletionAlong.limitTopology I N)) =
        TopologicalSpace.induced (fun p : P ↦ (p : CompletionOverOpen R M))
          (CompletionOverOpen.limitTopology R M) := by
      rw [induced_compose, ← induced_limitTopology_restrictToPow I N hN hAdic,
        induced_compose]
      rfl
    calc TopologicalSpace.induced (fun p : P ↦ (p : CompletionOverOpen R M))
          (CompletionOverOpen.limitTopology R M)
        = TopologicalSpace.induced e'
            (TopologicalSpace.induced (fun p : P₀ ↦ (p : CompletionAlong I N))
              (CompletionAlong.limitTopology I N)) := h2.symm
      _ = TopologicalSpace.induced e' (I.adicModuleTopology P₀) := by rw [hP₀top]
      _ = I.adicModuleTopology P :=
          adicModuleTopology_induced_linearEquiv I e'

/-- Tag 0F1S, second conclusion, over the completion of `M` taken over all of its open
submodules: `M^ / I ^ n M^ = M / I ^ n M` for every `n`, in particular for every `n ≥ 1`. -/
@[stacks 0F1S "completion_mod_ideal_power"]
public noncomputable def completionOverOpenQuotPowEquiv (I : Ideal R) (hI : I.FG)
    (N : Submodule R M) (hN : IsOpen (N : Set M))
    (hAdic : (𝓝 (0 : N)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ ((I ^ n • ⊤ : Submodule R N) : Set N))) (n : ℕ) :
    ((CompletionOverOpen R M) ⧸ (I ^ n • ⊤ : Submodule R (CompletionOverOpen R M))) ≃ₗ[R]
      (M ⧸ (I ^ n • ⊤ : Submodule R M)) :=
  (Submodule.Quotient.equiv _ _ (completionOverOpenEquiv I N hN hAdic) (by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range])).trans
      (CompletionAlong.quotPowEquiv I hI N n)

end OverOpenSubmodules

end TopologicalRing

end
