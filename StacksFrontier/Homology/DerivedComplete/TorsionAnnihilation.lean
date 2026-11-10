module

public import Mathlib
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.Homology.DerivedComplete
public import StacksFrontier.Homology.DerivedComplete.CompleteAdic
public import StacksFrontier.Homology.DerivedComplete.CompleteRestrictScalars
public import StacksFrontier.Homology.DerivedComplete.PrincipalAdicPresentation
public import StacksFrontier.Topology.Algebra.BaireLinearTopology
public import StacksFrontier.Topology.Algebra.OpenMapping
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Power torsion in a derived complete module is bounded

Let `I` be a finitely generated ideal in a commutative ring `A`. If a derived complete
`A`-module is `I`-power torsion, then one fixed power of `I` annihilates the whole module.

## Main results

* `exists_pow_smul_top_eq_bot_of_isDerivedCompleteModule_of_isIPowerTorsion`:
  power torsion in a derived complete module is bounded.

## Implementation notes

The submodule `IⁿM` is represented by `I ^ n • ⊤`, so its vanishing is equality with `⊥`. Derived
completeness is `IsDerivedCompleteModule` and ideal-power torsion is `IsIPowerTorsion`.

The argument reduces to a principal ideal `(f)`, where the point is that a derived complete
module is the cokernel of a map of `f`-adically complete, `f`-torsion-free modules. The open
mapping lemma for complete linearly topologized groups, together with the Baire-type statement
that a countable closed-subgroup cover of such a group contains an open member, then bounds the
`f`-power needed to hit the image. Passing to a principal ideal requires `f` to be a
nonzerodivisor; this is arranged by restricting scalars along the evaluation map from a
polynomial ring, where the variable is a nonzerodivisor, and using that restriction of scalars
detects derived completeness.

## References

* [The Stacks Project, Tag 0CQY](https://stacks.math.columbia.edu/tag/0CQY)
* [Bhatt--Scholze, *Projectivity of the Witt vector affine Grassmannian*][BS]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Filter Topology

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace DerivedCompleteTorsion

open DerivedCompleteRecurrence PrincipalAdicPresentation

/-- Countable products are exact in the category of `R`-modules. -/
local instance (R : Type*) [CommRing R] :
    HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{v} R) :=
  moduleCat_hasExactLimitsOfShape_discrete.{v} R ℕ

/-- The derived category of `R`-modules has countable products. -/
local instance (R : Type*) [CommRing R] :
    HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} R)) :=
  Stacks.DerivedProducts.hasProductsOfShape_derivedCategory

/-! ### The `f`-adic topology on a module

The submodules `fⁿ M` form a fundamental system of neighbourhoods of zero for a linear topology,
complete and separated when `M` is `f`-adically complete. These are the hypotheses of the open
mapping lemma.
-/

section AdicTopology

private lemma adicModule_hasBasis
    (R : Type*) [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] :
    @Filter.HasBasis M ℕ (@nhds M (I.adicModuleTopology M) 0)
      (fun _ => True) (fun n => ((I ^ n • (⊤ : Submodule R M) : Submodule R M) : Set M)) := by
  let : TopologicalSpace R := I.adicTopology
  let B := (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M))
    |>.toAddGroupFilterBasis
  refine B.nhds_zero_hasBasis.to_hasBasis ?_ ?_
  · intro U hU
    change ∃ n, U = ((I ^ n • (⊤ : Submodule R M) : Submodule R M) : Set M) at hU
    obtain ⟨n, rfl⟩ := hU
    exact ⟨n, trivial, Set.Subset.rfl⟩
  · intro n _
    refine ⟨((I ^ n • (⊤ : Submodule R M) : Submodule R M) : Set M), ?_, Set.Subset.rfl⟩
    exact ⟨n, rfl⟩

private lemma adicModule_t2Space
    (R : Type*) [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] (hM : IsHausdorff I M) :
    @T2Space M (I.adicModuleTopology M) := by
  let : TopologicalSpace R := I.adicTopology
  let : TopologicalSpace M := I.adicModuleTopology M
  let B := (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M))
    |>.toAddGroupFilterBasis
  rw [B.t2Space_iff_sInter_subset rfl]
  intro x hx
  simp only [Set.mem_sInter] at hx
  have hx' : ∀ n : ℕ, x ∈ I ^ n • (⊤ : Submodule R M) := fun n =>
    hx _ (show ∃ i, ((I ^ n • (⊤ : Submodule R M) : Submodule R M) : Set M) =
      ((I ^ i • (⊤ : Submodule R M) : Submodule R M) : Set M) from ⟨n, rfl⟩)
  have : x = 0 := hM.haus x fun n => by simpa [SModEq.zero] using hx' n
  simp [this]

private lemma adicModule_completeSpace
    (R : Type*) [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] (hM : IsPrecomplete I M) :
    let : TopologicalSpace M := I.adicModuleTopology M
    let : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
    CompleteSpace M := by
  let : TopologicalSpace M := I.adicModuleTopology M
  let : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  let : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
  have hb := adicModule_hasBasis R I M
  let _ : (nhds (0 : M)).IsCountablyGenerated := hb.isCountablyGenerated
  have : (uniformity M).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  exact UniformSpace.complete_of_cauchySeq_tendsto fun x hx => by
    have hc : ∀ i, ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
        x n - x m ∈ I ^ i • (⊤ : Submodule R M) := by
      simpa using hb.uniformity_of_nhds_zero.cauchySeq_iff.mp hx
    choose N hN using hc
    obtain ⟨L, hL⟩ := hM.prec (f := fun i => x ((Finset.Iic i).sup N))
      (fun {m n} hmn => by
        rw [SModEq.sub_mem]
        simpa using (I ^ m • (⊤ : Submodule R M)).neg_mem
          (hN m _ (Finset.le_sup (f := N) (Finset.mem_Iic.mpr le_rfl)) _
            (Finset.le_sup (f := N) (Finset.mem_Iic.mpr hmn)))
      )
    refine ⟨L, ?_⟩
    have hbL := hb.map (fun y => L + y)
    rw [map_add_left_nhds_zero L] at hbL
    rw [hbL.tendsto_right_iff]
    intro i _
    filter_upwards [eventually_ge_atTop ((Finset.Iic i).sup N)] with n hn
    have ha := hN i ((Finset.Iic i).sup N)
      (Finset.le_sup (f := N) (Finset.mem_Iic.mpr le_rfl)) n
      (le_trans (Finset.le_sup (f := N) (Finset.mem_Iic.mpr le_rfl)) hn)
    have hb' := hL i
    rw [SModEq.sub_mem] at hb'
    have := (I ^ i • (⊤ : Submodule R M)).add_mem ha hb'
    refine ⟨x n - L, ?_, by simp⟩
    change x n - L ∈ I ^ i • (⊤ : Submodule R M)
    simpa only [sub_add_sub_cancel] using this

private lemma adicModule_isGroupComplete
    (R : Type*) [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] (hM : IsAdicComplete I M) :
    let : TopologicalSpace M := I.adicModuleTopology M
    IsGroupComplete M := by
  let : TopologicalSpace M := I.adicModuleTopology M
  let : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  let : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace M := adicModule_completeSpace R I M hM.toIsPrecomplete
  refine ⟨adicModule_t2Space R I M hM.toIsHausdorff, fun F hF => ?_⟩
  exact CompleteSpace.complete ((IsUniformAddGroup.cauchy_iff_tendsto_swapped F).2
    ⟨hF.1, hF.2⟩)

private lemma adicModule_isOpen_pow
    (R : Type*) [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) :
    @IsOpen M (I.adicModuleTopology M)
      ((I ^ n • (⊤ : Submodule R M) : Submodule R M) : Set M) := by
  let : TopologicalSpace M := I.adicModuleTopology M
  exact (I ^ n • (⊤ : Submodule R M)).toAddSubgroup.isOpen_of_mem_nhds
    ((adicModule_hasBasis R I M).mem_of_mem trivial)

@[ega "0 7.2.10" "more general"]
private lemma adicModule_continuous_linearMap
    (R : Type*) [CommRing R] (I : Ideal R)
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    @Continuous M N (I.adicModuleTopology M) (I.adicModuleTopology N) f := by
  let : TopologicalSpace M := I.adicModuleTopology M
  let : TopologicalSpace N := I.adicModuleTopology N
  apply continuous_of_continuousAt_zero f
  change Tendsto f (nhds 0) (nhds (f 0))
  rw [map_zero, (adicModule_hasBasis R I M).tendsto_iff (adicModule_hasBasis R I N)]
  refine fun n _ => ⟨n, trivial, fun x hx => ?_⟩
  exact (show (I ^ n • (⊤ : Submodule R M)).map f ≤ I ^ n • (⊤ : Submodule R N) by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top) ⟨x, hx, rfl⟩

private lemma mem_principal_pow_smul_top
    (R : Type*) [CommRing R] (f : R)
    (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) (x : M) :
    x ∈ (Ideal.span {f}) ^ n • (⊤ : Submodule R M) ↔ ∃ y : M, f ^ n • y = x := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
  simpa using Submodule.mem_smul_pointwise_iff_exists x (f ^ n) (⊤ : Submodule R M)

private lemma adicModule_isOpenMap_pow_smul
    (R : Type*) [CommRing R] (f : R)
    (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) :
    @IsOpenMap M M ((Ideal.span {f}).adicModuleTopology M)
      ((Ideal.span {f}).adicModuleTopology M) (fun x : M => f ^ n • x) := by
  let I := Ideal.span {f}
  let : TopologicalSpace M := I.adicModuleTopology M
  apply isOpenMap_of_hasBasis_image_isOpen (LinearMap.lsmul R M (f ^ n)).toAddMonoidHom
    (adicModule_hasBasis R I M)
  intro k _
  have heq : (fun x : M => f ^ n • x) ''
      ((I ^ k • (⊤ : Submodule R M) : Submodule R M) : Set M) =
      ((I ^ (n + k) • (⊤ : Submodule R M) : Submodule R M) : Set M) := by
    ext x
    simp only [Set.mem_image, SetLike.mem_coe, I, mem_principal_pow_smul_top,
      exists_exists_eq_and, smul_smul, ← pow_add]
  change IsOpen ((fun x : M => f ^ n • x) ''
    ((I ^ k • (⊤ : Submodule R M) : Submodule R M) : Set M))
  rw [heq]
  exact adicModule_isOpen_pow R I M (n + k)

private lemma adicModule_isLinearlyTopologized
    (R : Type*) [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] :
    let : TopologicalSpace M := I.adicModuleTopology M
    IsLinearlyTopologized M := by
  let : TopologicalSpace M := I.adicModuleTopology M
  apply (adicModule_hasBasis R I M).to_hasBasis
  · intro n _
    exact ⟨(I ^ n • (⊤ : Submodule R M)).toAddSubgroup,
      adicModule_isOpen_pow R I M n, Set.Subset.rfl⟩
  · intro U hU
    exact (adicModule_hasBasis R I M).mem_iff.mp (hU.mem_nhds U.zero_mem)

/-- The bounded-power statement for a map of `f`-adically complete modules: if every element
of `L` is carried into the image of `i` by some power of `f`, then one power of `f` suffices. -/
private lemma exists_pow_smul_mem_range_of_isAdicComplete
    (R : Type*) [CommRing R] (f : R)
    {K L : Type*} [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    (i : K →ₗ[R] L)
    (hK : IsAdicComplete (Ideal.span {f}) K)
    (hL : IsAdicComplete (Ideal.span {f}) L)
    (ht : ∀ x : L, ∃ n : ℕ, f ^ n • x ∈ LinearMap.range i) :
    ∃ t : ℕ, ∀ x : L, f ^ t • x ∈ LinearMap.range i := by
  let I := Ideal.span {f}
  let : TopologicalSpace R := I.adicTopology
  let : TopologicalSpace K := I.adicModuleTopology K
  let : TopologicalSpace L := I.adicModuleTopology L
  let : T2Space L := adicModule_t2Space R I L hL.toIsHausdorff
  let : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  let : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace L := adicModule_completeSpace R I L hL.toIsPrecomplete
  let : IsLinearTopology ℤ L := IsLinearTopology.mk_of_hasBasis' ℤ
    (adicModule_hasBasis R I L) fun S r x hx => S.toAddSubgroup.zsmul_mem hx r
  let H : ℕ → AddSubgroup L := fun n =>
    ((LinearMap.range i).comap (LinearMap.lsmul R L (f ^ n))).toAddSubgroup
  let N : ℕ → AddSubgroup L := fun n => (H n).topologicalClosure
  have hcover : (⋃ n, (N n : Set L)) = Set.univ := Set.eq_univ_of_forall fun x =>
    (ht x).elim fun n hn => Set.mem_iUnion.mpr ⟨n, subset_closure hn⟩
  obtain ⟨n, hn⟩ := exists_isOpen_of_iUnion_eq_univ_of_complete_linearTopology
    (M := L) inferInstance (adicModule_hasBasis R I L).isCountablyGenerated
    N (fun n => (H n).isClosed_topologicalClosure) hcover
  have hopen : IsOpenMap i := by
    apply open_mapping_lemma_dichotomy i.toAddMonoidHom
      (adicModule_continuous_linearMap R I i)
      (adicModule_isGroupComplete R I K hK)
      (adicModule_isLinearlyTopologized R I K)
      (adicModule_hasBasis R I K).isCountablyGenerated
    intro V hV hnd
    obtain ⟨m, -, hm⟩ := (adicModule_hasBasis R I K).mem_iff.mp
      (hV.mem_nhds V.zero_mem)
    let g : L →ₗ[R] L := LinearMap.lsmul R L (f ^ (n + m))
    have hg : Continuous g := adicModule_continuous_linearMap R I g
    have hgo : IsOpenMap g := adicModule_isOpenMap_pow_smul R f L (n + m)
    have himage : g '' (H n : Set L) ⊆ i '' (V : Set K) := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy⟩ := hx
      refine ⟨f ^ m • y, hm ((mem_principal_pow_smul_top R f K m _).mpr ⟨y, rfl⟩), ?_⟩
      change i (f ^ m • y) = f ^ (n + m) • x
      rw [map_smul, hy, pow_add, mul_comm (f ^ n), mul_smul]
      rfl
    have hsub : g '' (N n : Set L) ⊆ closure (i '' (V : Set K)) :=
      (image_closure_subset_closure_image hg).trans (closure_mono himage)
    have hzero : (0 : L) ∈ g '' (N n : Set L) := ⟨0, (N n).zero_mem, map_zero g⟩
    have : (0 : L) ∈ interior (closure (i '' (V : Set K))) :=
      (interior_maximal hsub (hgo _ hn)) hzero
    change interior (closure (i '' (V : Set K))) = ∅ at hnd
    exact hnd.subset this
  have hrange : (LinearMap.range i : Set L) ∈ nhds (0 : L) := by
    simpa only [LinearMap.coe_range, Set.image_univ] using
      (hopen Set.univ isOpen_univ).mem_nhds ⟨0, Set.mem_univ _, map_zero i⟩
  obtain ⟨t, -, ht⟩ := (adicModule_hasBasis R I L).mem_iff.mp hrange
  exact ⟨t, fun x => ht ((mem_principal_pow_smul_top R f L t _).mpr ⟨x, rfl⟩)⟩

end AdicTopology

section ShortExact

/-- A module which is derived complete with respect to `(f)`, for `f` a nonzerodivisor, is the
cokernel of a map of `f`-adically complete modules on which multiplication by `f` is
injective. -/
private theorem exists_shortExact_isAdicComplete_of_isDerivedCompleteModule
    (A : Type u) [CommRing A] (f : A)
    (hf : Function.Injective (LinearMap.lsmul A A f)) (M : ModuleCat.{u} A)
    (hM : IsDerivedCompleteModule (Ideal.span {f}) M) :
    ∃ (K L : ModuleCat.{u} A) (i : K ⟶ L) (p : L ⟶ M) (w : i ≫ p = 0),
      (ShortComplex.mk i p w).ShortExact ∧
        IsAdicComplete (Ideal.span {f}) K ∧
        IsAdicComplete (Ideal.span {f}) L ∧
        Function.Injective (LinearMap.lsmul A K f) ∧
        Function.Injective (LinearMap.lsmul A L f) := by
  have hfg : (Ideal.span {f}).FG := Submodule.fg_span_singleton f
  have hMb : Function.Bijective (recurrence (A := A) (M := M) f) :=
    (isDerivedCompleteAt_single_iff_bijective_recurrence M f).mp
      (hM f (Ideal.mem_span_singleton_self f))
  let F := M →₀ A
  have hF : Function.Injective (LinearMap.lsmul A F f) := finsupp_smul_injective hf M
  let g : F →ₗ[A] M := Finsupp.linearCombination A id
  have hg : Function.Surjective g := fun m => ⟨Finsupp.single m 1, by
    simp only [g]
    exact (Finsupp.linearCombination_single A (v := (id : M → M)) 1 m).trans (one_smul A m)⟩
  let φ := completionLift hF hMb g
  have hφ : Function.Surjective φ := completionLift_surjective hF hMb hg
  let L : ModuleCat.{u} A := ModuleCat.of A (AdicCompletion (Ideal.span {f}) F)
  let K : ModuleCat.{u} A := ModuleCat.of A (LinearMap.ker φ)
  let i : K ⟶ L := ModuleCat.ofHom (LinearMap.ker φ).subtype
  let p : L ⟶ M := ModuleCat.ofHom φ
  have w : i ≫ p = 0 := by
    ext x
    exact x.2
  have hS : (ShortComplex.mk i p w).ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      exact LinearMap.exact_subtype_ker_map φ
    · exact (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
    · exact (ModuleCat.epi_iff_surjective _).2 hφ
  have hLc : IsAdicComplete (Ideal.span {f}) L :=
    AdicCompletion.isAdicComplete (M := F) hfg
  have hLi : Function.Injective (LinearMap.lsmul A L f) :=
    adicCompletion_smul_injective (F := F) hF
  have hKi : Function.Injective (LinearMap.lsmul A K f) := fun _ _ hxy =>
    Subtype.val_injective (hLi (congrArg Subtype.val hxy))
  have hLd : IsDerivedCompleteModule (Ideal.span {f}) L :=
    (isDerivedCompleteModule_of_isAdicComplete_and_adicCompletion_surjective A
      (Ideal.span {f}) (AdicCompletion (Ideal.span {f}) F)).1 hLc
  have hKd : IsDerivedCompleteModule (Ideal.span {f}) K := fun a ha =>
    isDerivedCompleteAt_of_distTriang hS.singleTriangle_distinguished (hLd a ha) (hM a ha)
  have hKs : ⨅ n : ℕ, (Ideal.span {f}) ^ n • (⊤ : Submodule A K) = ⊥ :=
    have : IsHausdorff (Ideal.span {f}) L := hLc.toIsHausdorff
    iInf_pow_smul_top_eq_bot_of_injective (Ideal.span {f}) (LinearMap.ker φ).subtype
      Subtype.val_injective
  have hKc : IsAdicComplete (Ideal.span {f}) K :=
    (isAdicComplete_iff_isDerivedCompleteModule_and_iInf_pow_smul_top_eq_bot A
      (Ideal.span {f}) hfg (LinearMap.ker φ)).mpr ⟨hKd, hKs⟩
  exact ⟨K, L, i, p, w, hS, hKc, hLc, hKi, hLi⟩

end ShortExact

/-! ### The annihilation statement -/

section Main

/-- For a nonzerodivisor `f`, a derived complete `f`-power torsion module is annihilated by a
single power of `f`. -/
private theorem exists_pow_smul_eq_zero_of_isDerivedCompleteModule_of_injective
    (A : Type u) [CommRing A] (f : A)
    (hf : Function.Injective (LinearMap.lsmul A A f)) (M : ModuleCat.{u} A)
    (hM : IsDerivedCompleteModule (Ideal.span {f}) M)
    (ht : ∀ x : M, ∃ n : ℕ, f ^ n • x = 0) :
    ∃ n : ℕ, ∀ x : M, f ^ n • x = 0 := by
  obtain ⟨K, L, i, p, w, hS, hK, hL, -, -⟩ :=
    exists_shortExact_isAdicComplete_of_isDerivedCompleteModule A f hf M hM
  obtain ⟨t, ht⟩ := exists_pow_smul_mem_range_of_isAdicComplete A f i.hom hK hL
    (fun x => by
      obtain ⟨n, hn⟩ := ht (p.hom x)
      refine ⟨n, ?_⟩
      rw [hS.exact.moduleCat_range_eq_ker]
      change p.hom (f ^ n • x) = 0
      rwa [map_smul])
  refine ⟨t, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := hS.moduleCat_surjective_g x
  obtain ⟨z, hz⟩ := ht y
  have hpz : p.hom (i.hom z) = 0 := by
    change (i ≫ p).hom z = 0
    rw [w]
    rfl
  rw [← p.hom.map_smul, ← hz]
  exact hpz

/-- A derived complete `f`-power torsion module is annihilated by a single power of `f`, with no
regularity assumption on `f`. -/
private theorem exists_pow_smul_eq_zero_of_isDerivedCompleteModule
    (A : Type u) [CommRing A] (f : A) (M : ModuleCat.{v} A)
    (hM : IsDerivedCompleteModule (Ideal.span {f}) M)
    (ht : ∀ x : M, ∃ n : ℕ, f ^ n • x = 0) :
    ∃ n : ℕ, ∀ x : M, f ^ n • x = 0 := by
  let B := Polynomial (ULift.{v} ℤ)
  let c : ULift.{v} ℤ →+* A := (Int.castRingHom A).comp ULift.ringEquiv.toRingHom
  let φ : B →+* A := Polynomial.eval₂RingHom c f
  let MB := (ModuleCat.restrictScalars φ).obj M
  have hφ : φ Polynomial.X = f :=
    (congrFun (Polynomial.coe_eval₂RingHom c f) Polynomial.X).trans
      (Polynomial.eval₂_X _ _)
  have hmap : (Ideal.span {Polynomial.X}).map φ = Ideal.span {f} := by
    rw [Ideal.map_span, Set.image_singleton, hφ]
  have hMB : IsDerivedCompleteModule (Ideal.span {Polynomial.X}) MB :=
    isDerivedComplete_of_iso
      ((ModuleCat.restrictScalars.{v} φ).mapDerivedCategorySingleFunctor 0 |>.app M)
      ((isDerivedComplete_restrictScalars_iff B A φ (Ideal.span {Polynomial.X})
        ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M)).mpr (by rwa [hmap]))
  have hx : Function.Injective (LinearMap.lsmul B B Polynomial.X) :=
    Polynomial.monic_X.isRegular.left
  have hsmul (n : ℕ) (x : MB) : (Polynomial.X : B) ^ n • x = f ^ n • (x : M) := by
    change φ (Polynomial.X ^ n) • (x : M) = _
    rw [map_pow, hφ]
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isDerivedCompleteModule_of_injective
    B Polynomial.X hx MB hMB fun x => (ht x).imp fun n hn => (hsmul n x).trans hn
  exact ⟨n, fun x => (hsmul n x).symm.trans (hn x)⟩

variable (A : Type u) [CommRing A]

/-- If `I` is finitely generated and `M` is both derived complete and `I`-power torsion, then a
single power of `I` annihilates all of `M`. -/
@[stacks 0CQY]
theorem exists_pow_smul_top_eq_bot_of_isDerivedCompleteModule_of_isIPowerTorsion
    (I : Ideal A) (M : ModuleCat.{v} A) (hI : I.FG)
    (hM : IsDerivedCompleteModule I M)
    (htors : IsIPowerTorsion A M I) :
    ∃ n : ℕ, I ^ n • (⊤ : Submodule A M) = ⊥ := by
  have hrad : I ≤ (Module.annihilator A M).radical := by
    intro f hf
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isDerivedCompleteModule A f M
      (fun a ha => hM a ((Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hf)) ha))
      (fun x => by
        obtain ⟨n, -, hn⟩ := htors x
        exact ⟨n, hn (f ^ n) (Ideal.pow_mem_pow hf n)⟩)
    exact ⟨n, Module.mem_annihilator.mpr hn⟩
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hI
  exact ⟨n, eq_bot_iff.mpr (Submodule.smul_le.mpr fun a ha x _ =>
    (Submodule.mem_bot A).mpr (Module.mem_annihilator.mp (hn ha) x))⟩

end Main

end DerivedCompleteTorsion

end
