module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.TorChangeOfRings
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.TorOneAugmentation

/-!
# Change of rings on `Tor₁` of the trivial module

Let `Λ` be a finite ring, `G` a compact group, `Q` a finite discrete group and `π : G → Q` a
continuous homomorphism, inducing `Λ[[G]] → Λ[[Q]] = Λ[Q]`. Let `X` be a finite `Λ`-module with
trivial `Q`-action, free of rank one on `n₀` (for instance `X = Λ`). By
`Stacks.GroupHomology.torOneMk`, `Tor₁^{Λ[[G]]}(X, Λ) = I_G / I_G²` and
`Tor₁^{Λ[Q]}(X, Λ) = I_Q / I_Q²`, `I` the augmentation ideals. This file shows that a morphism of
homological δ-functors `Tor_•^{Λ[[G]]}(res_π -, Λ) ⟶ Tor_•^{Λ[Q]}(-, Λ)` on finite modules which
is the projection of coinvariants in degree zero is, in degree one at `X`, the map
`I_G / I_G² → I_Q / I_Q²` induced by `π` (`app_one_trivialTorOneMk`). In particular this holds for
the change-of-rings map `torChangeOfRings` along `Λ[Q'] → Λ[Q]`
(`torChangeOfRings_app_one_trivialTorOneMk`).

The proof compares connecting maps. Over `Q` the sequence `0 → K → Λ[Q] → X → 0` of finite
modules with `Q`-action has `Tor₁^{Λ[Q]}(Λ[Q], Λ) = 0`, so its connecting map
`Tor₁^{Λ[Q]}(X, Λ) → Tor₀^{Λ[Q]}(K, Λ)` is injective. Restricted to `G`, the same sequence receives
a map from `0 → I_G → Λ[[G]] → X → 0` (`a ↦ a e` in the middle, `e ∈ Λ[Q]` a lift of `n₀`), so by
naturality of the connecting maps the class of `x ∈ I_G` goes to the class of `x e = π(x) e ∈ K`
(`leftDerivedδ_trivialTorOneMk`, `augmentationShortComplexHom_τ₁_augmentationIdealMap`).

All names are in the namespace `Stacks.GroupHomology`.

## Main definitions

* `trivialFiniteTypeModule Λ Γ`: `Λ` with trivial `Γ`-action.
* `trivialTorOneMk π X n₀`: the surjection `I_G → Tor₁^{Λ[[G]]}(res_π X, Λ)`.
* `augmentationIdealMap π`: `I_G → I_Q`, `x ↦ π(x)`.
* `IsCoinvariantsProjection π τ`: `τ` is the projection of coinvariants in degree zero.

## Main results

* `app_one_trivialTorOneMk`, `torChangeOfRings_app_one_trivialTorOneMk`.

## References

* [Stacks Project, Section 03VI](https://stacks.math.columbia.edu/tag/03VI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.ContinuousCohomology
  Stacks.CategoryHomology MonoidAlgebra

universe w

namespace Stacks.GroupHomology

open CompletedGroupAlgebra

section Action

variable {Λ : Type} [Ring Λ] {G : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Q : Type w} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]

attribute [local instance] finiteTypeDistribMulAction finiteTypeSMulCommClass

/-- On a module with trivial action, `a ∈ Λ[[G]]` acts as its augmentation. -/
theorem finiteTypeCompletedAction_of_forall_eq_one (N : FiniteTypeContinuousModule.{0, w, w} Λ G)
    (hN : ∀ g, N.obj.obj.obj.ρ g = 1) (a : CompletedGroupAlgebra (ULift.{w} Λ) G)
    (x : N.obj.obj.obj.V) :
    finiteTypeCompletedAction N a x = (augmentation a).down • x := by
  have hU : ∀ g ∈ (topSubgroup : OpenNormalSubgroup G), ∀ y : N.obj.obj.obj.V, g • y = y :=
    fun g _ y => by
      rw [finiteTypeSmul_def]
      change (N.obj.obj.obj.ρ g).asHom.hom y = y
      rw [hN g]
      rfl
  rw [finiteTypeCompletedAction, toAddMonoidEnd_eq _ _ topSubgroup hU,
    augmentation_eq topSubgroup]
  induction eval topSubgroup a using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero, map_zero, ULift.zero_down, zero_smul]; rfl
  | add p q hp hq =>
    rw [map_add, map_add, ULift.add_down, add_smul]
    exact congrArg₂ (· + ·) hp hq
  | single q c =>
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [quotientAlgebraAction_single, finiteAugmentation_single, hU g trivial x]
      rfl

/-- On the restriction of `N` along `π : G → Q`, `a ∈ Λ[[G]]` acts as its image in `Λ[[Q]]`. -/
theorem finiteTypeCompletedAction_res (π : G →ₜ* Q) (N : FiniteTypeContinuousModule.{0, w, w} Λ Q)
    (a : CompletedGroupAlgebra (ULift.{w} Λ) G) (x : N.obj.obj.obj.V) :
    finiteTypeCompletedAction ((finiteTypeContinuousModuleRes.{0, w, w} Λ π).obj N) a x =
      finiteTypeCompletedAction N (map (π : G →* Q) π.continuous a) x := by
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_smul_eq_finiteType N
  have hU' : ∀ g ∈ comapSubgroup (π : G →* Q) π.continuous U,
      ∀ y : ((finiteTypeContinuousModuleRes.{0, w, w} Λ π).obj N).obj.obj.obj.V, g • y = y :=
    fun g hg y => hU (π g) hg y
  have hsingle : ∀ (g : G) (c : ULift.{w} Λ),
      quotientAlgebraAction (Λ := ULift.{w} Λ) _ _ hU' (single (g : G ⧸
        ((comapSubgroup (π : G →* Q) π.continuous U : OpenNormalSubgroup G) : Subgroup G)) c) =
      ((quotientAlgebraAction (Λ := ULift.{w} Λ) _ U hU).comp (quotientMapAlgebra (π : G →* Q)
        (map_mem_of_mem_comapSubgroup _ π.continuous U))) (single (g : G ⧸
          ((comapSubgroup (π : G →* Q) π.continuous U : OpenNormalSubgroup G) : Subgroup G)) c) :=
    fun g c => by
      ext y
      have h2 := quotientMapAlgebra_single (Λ := ULift.{w} Λ) (π : G →* Q)
        (map_mem_of_mem_comapSubgroup _ π.continuous U) g c
      refine (quotientAlgebraAction_single _ _ hU' g c y).trans ?_
      exact ((congrArg (fun z => quotientAlgebraAction (Λ := ULift.{w} Λ) N.obj.obj.obj.V U hU z y)
        h2).trans (quotientAlgebraAction_single (Λ := ULift.{w} Λ) N.obj.obj.obj.V U hU (π g) c
          y)).symm
  have key : quotientAlgebraAction (Λ := ULift.{w} Λ) _ _ hU' =
      (quotientAlgebraAction (Λ := ULift.{w} Λ) _ U hU).comp
      (quotientMapAlgebra (π : G →* Q) (map_mem_of_mem_comapSubgroup _ π.continuous U)) := by
    refine MonoidAlgebra.ringHom_ext (fun c => ?_) (fun q => ?_)
    · have h := hsingle 1 c
      rw [QuotientGroup.mk_one] at h
      exact h
    · induction q using QuotientGroup.induction_on with
      | H g => exact hsingle g 1
  rw [finiteTypeCompletedAction, finiteTypeCompletedAction, toAddMonoidEnd_eq _ _ _ hU',
    toAddMonoidEnd_eq _ _ U hU,
    eval_map (π : G →* Q) π.continuous (map_mem_of_mem_comapSubgroup _ π.continuous U)]
  exact DFunLike.congr_fun (DFunLike.congr_fun key _) x

end Action

section Trivial

variable (Λ : Type) [Ring Λ] (Γ : Type w) [Group Γ] [TopologicalSpace Γ]

/-- **The trivial module `Λ`**, as a finite `Λ`-module with continuous (trivial) `Γ`-action. -/
def trivialFiniteTypeModule : FiniteTypeContinuousModule.{0, w, w} Λ Γ :=
  ⟨(continuousModuleTrivialFunctor.{0, w, w} Λ Γ).obj (ModuleCat.of Λ (ULift.{w} Λ)), by
    change Module.Finite Λ (ULift.{w} Λ)
    exact Module.Finite.equiv ULift.moduleEquiv.symm⟩

/-- `Γ` acts trivially on the trivial module. -/
theorem trivialFiniteTypeModule_ρ (g : Γ) : (trivialFiniteTypeModule Λ Γ).obj.obj.obj.ρ g = 1 :=
  rfl

/-- The generator `1` of the trivial module. -/
def trivialGenerator : (trivialFiniteTypeModule Λ Γ).obj.obj.obj.V :=
  ULift.up 1

/-- The trivial module is free of rank one on `1`. -/
theorem bijective_smul_trivialFiniteTypeModule :
    Function.Bijective fun c : Λ => c • trivialGenerator Λ Γ :=
  ⟨fun c c' h => by
    have h' := congrArg ULift.down h
    change c * 1 = c' * 1 at h'
    simpa using h', fun x => ⟨x.down, by
    change ULift.up (x.down * 1) = x
    rw [mul_one]
    rfl⟩⟩

end Trivial

section Augmentation

variable {Λ : Type} [Ring Λ] [Finite Λ] {Q : Type w} [Group Q] [TopologicalSpace Q]
  [IsTopologicalGroup Q] [CompactSpace Q] [DiscreteTopology Q]
  (X : FiniteTypeContinuousModule.{0, w, w} Λ Q) (n₀ : X.obj.obj.obj.V)
  (hn₀ : Function.Bijective fun c : Λ => c • n₀)

/-- The augmentation `Λ[Q] → X`, `f ↦ Σ_q f(q) • q n₀`, onto a module free of rank one on `n₀`. -/
def freeAugmentation : freeModule Λ Q 1 ⟶ X :=
  haveI : Finite Q := finite_of_compact_of_discrete
  letI := Fintype.ofFinite Q
  freeModuleHom X fun _ => n₀

include hn₀ in
/-- The augmentation `Λ[Q] → X` is surjective. -/
theorem freeAugmentation_surjective :
    Function.Surjective (freeAugmentation X n₀).hom.hom.hom.hom.hom := by
  have : Finite Q := finite_of_compact_of_discrete
  let := Fintype.ofFinite Q
  refine freeModuleLinearMap_surjective X (fun _ => n₀) ?_
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨c, rfl⟩ := hn₀.2 x
  exact Submodule.smul_mem _ c (Submodule.subset_span ⟨0, rfl⟩)

include hn₀ in
/-- The augmentation `Λ[Q] → X` is an epimorphism. -/
theorem epi_freeAugmentation : Epi (freeAugmentation X n₀) := by
  have : Finite Q := finite_of_compact_of_discrete
  let := Fintype.ofFinite Q
  refine epi_freeModuleHom X (fun _ => n₀) ?_
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨c, rfl⟩ := hn₀.2 x
  exact Submodule.smul_mem _ c (Submodule.subset_span ⟨0, rfl⟩)

/-- An element of `Λ[Q]` mapping to `n₀`. -/
def freeGenerator : (freeModule Λ Q 1).obj.obj.obj.V :=
  (freeAugmentation_surjective X n₀ hn₀ n₀).choose

/-- The generator maps to `n₀`. -/
theorem freeAugmentation_freeGenerator :
    (freeAugmentation X n₀).hom.hom.hom.hom.hom (freeGenerator X n₀ hn₀) = n₀ :=
  (freeAugmentation_surjective X n₀ hn₀ n₀).choose_spec

/-- **The augmentation sequence** `0 → K → Λ[Q] → X → 0` of finite modules with `Q`-action. -/
abbrev freeAugmentationShortComplex : ShortComplex (FiniteTypeContinuousModule.{0, w, w} Λ Q) :=
  ShortComplex.mk (kernel.ι (freeAugmentation X n₀)) (freeAugmentation X n₀) (kernel.condition _)

include hn₀ in
/-- The augmentation sequence is short exact. -/
theorem shortExact_freeAugmentationShortComplex :
    (freeAugmentationShortComplex X n₀).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  mono_f := inferInstance
  epi_g := epi_freeAugmentation X n₀ hn₀

end Augmentation

section Module

variable {Λ : Type} [Ring Λ] [Finite Λ] {Q : Type w} [Group Q] [TopologicalSpace Q]
  [IsTopologicalGroup Q] [CompactSpace Q] [DiscreteTopology Q]
  {G : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (π : G →ₜ* Q)

/-- `M ↦ res_π M`, as a `Λ[[G]]`-module. -/
abbrev resCompleted :
    FiniteTypeContinuousModule.{0, w, w} Λ Q ⥤
      ModuleCat.{w} (CompletedGroupAlgebra (ULift.{w} Λ) G) :=
  finiteTypeContinuousModuleRes.{0, w, w} Λ π ⋙ finiteTypeCompletedModule Λ G

/-- `res_π` preserves finite limits. -/
instance : PreservesFiniteLimits (resCompleted (Λ := Λ) π) := by
  have := preservesFiniteLimits_finiteTypeContinuousModuleRes (Λ := Λ) π
  have := preservesFiniteLimits_finiteTypeCompletedModule Λ G
  exact comp_preservesFiniteLimits _ _

/-- `res_π` preserves finite colimits. -/
instance : PreservesFiniteColimits (resCompleted (Λ := Λ) π) := by
  have := preservesFiniteColimits_finiteTypeContinuousModuleRes (Λ := Λ) π
  have := preservesFiniteColimits_finiteTypeCompletedModule Λ G
  exact comp_preservesFiniteColimits _ _

variable (X : FiniteTypeContinuousModule.{0, w, w} Λ Q) (n₀ : X.obj.obj.obj.V)
  (hn₀ : Function.Bijective fun c : Λ => c • n₀) (hX : ∀ q, X.obj.obj.obj.ρ q = 1)

/-- `a ↦ a e`, `e` the generator of `Λ[Q]` lifting `n₀`. -/
def freeGeneratorHom :
    ModuleCat.of (CompletedGroupAlgebra (ULift.{w} Λ) G) (CompletedGroupAlgebra (ULift.{w} Λ) G) ⟶
      (resCompleted π).obj (freeModule Λ Q 1) :=
  ModuleCat.ofHom (Y := (resCompleted π).obj (freeModule Λ Q 1))
    (LinearMap.toSpanSingleton _ _ (freeGenerator X n₀ hn₀))

/-- `a ↦ a n₀`, a surjection `Λ[[G]] → X` with kernel the augmentation ideal. -/
abbrev trivialProjection :
    ModuleCat.of (CompletedGroupAlgebra (ULift.{w} Λ) G) (CompletedGroupAlgebra (ULift.{w} Λ) G) ⟶
      (resCompleted π).obj X :=
  freeGeneratorHom π X n₀ hn₀ ≫ (resCompleted π).map (freeAugmentation X n₀)

include hX in
omit [CompactSpace G] in
/-- `a ∈ Λ[[G]]` maps to `ε(a) n₀`, `ε` the augmentation. -/
theorem trivialProjection_apply (a : CompletedGroupAlgebra (ULift.{w} Λ) G) :
    (trivialProjection π X n₀ hn₀).hom a = ((augmentation a).down • n₀ : X.obj.obj.obj.V) := by
  have h1 : ((resCompleted π).map (freeAugmentation X n₀)).hom (freeGenerator X n₀ hn₀) = n₀ :=
    freeAugmentation_freeGenerator X n₀ hn₀
  have h2 : (trivialProjection π X n₀ hn₀).hom a =
      ((resCompleted π).map (freeAugmentation X n₀)).hom
        (a • (show (resCompleted π).obj (freeModule Λ Q 1) from freeGenerator X n₀ hn₀)) := rfl
  rw [h2, map_smul, h1]
  exact finiteTypeCompletedAction_of_forall_eq_one
    ((finiteTypeContinuousModuleRes.{0, w, w} Λ π).obj X) (fun g => hX (π g)) a n₀

include hX in
omit [CompactSpace G] in
/-- `a ↦ a n₀` is surjective. -/
theorem trivialProjection_surjective : Function.Surjective (trivialProjection π X n₀ hn₀).hom :=
  fun y => by
    obtain ⟨c, rfl⟩ := hn₀.2 y
    exact ⟨const (ULift.up c), by rw [trivialProjection_apply π X n₀ hn₀ hX, augmentation_const]⟩

include hX in
omit [CompactSpace G] in
/-- The kernel of `a ↦ a n₀` is the augmentation ideal. -/
theorem ker_trivialProjection :
    LinearMap.ker (trivialProjection π X n₀ hn₀).hom =
      RingHom.ker (augmentation : CompletedGroupAlgebra (ULift.{w} Λ) G →+* ULift.{w} Λ) := by
  ext a
  rw [LinearMap.mem_ker, trivialProjection_apply π X n₀ hn₀ hX, RingHom.mem_ker]
  constructor
  · intro h
    exact ULift.ext (hn₀.1 (h.trans (zero_smul Λ n₀).symm))
  · intro h
    rw [h]
    exact zero_smul Λ n₀

/-- **`I → Tor₁^{Λ[[G]]}(res_π X, Λ)`**, for `X` free of rank one over `Λ` with trivial action. -/
abbrev trivialTorOneMk :
    augmentationIdealModule (ULift.{w} Λ) G →+
      ((coinvariantsFunctor (ULift.{w} Λ) G).leftDerived 1).obj ((resCompleted π).obj X) :=
  torOneMk (trivialProjection π X n₀ hn₀) (trivialProjection_surjective π X n₀ hn₀ hX)
    (ker_trivialProjection π X n₀ hn₀ hX)

include hn₀ in
/-- The sequence `0 → K → Λ[Q] → X → 0`, restricted to `G`, is short exact. -/
theorem shortExact_map_freeAugmentationShortComplex :
    ((freeAugmentationShortComplex X n₀).map (resCompleted π)).ShortExact :=
  (shortExact_freeAugmentationShortComplex X n₀ hn₀).map_of_exact _

/-- The map from `0 → I → Λ[[G]] → X → 0` to the restriction of `0 → K → Λ[Q] → X → 0`, given by
`a ↦ a e` in the middle. -/
def augmentationShortComplexHom :
    augmentationShortComplex (trivialProjection π X n₀ hn₀) (ker_trivialProjection π X n₀ hn₀ hX) ⟶
      (freeAugmentationShortComplex X n₀).map (resCompleted π) :=
  haveI := (shortExact_map_freeAugmentationShortComplex π X n₀ hn₀).mono_f
  { τ₁ := (shortExact_map_freeAugmentationShortComplex π X n₀ hn₀).exact.lift
      ((augmentationShortComplex (trivialProjection π X n₀ hn₀)
        (ker_trivialProjection π X n₀ hn₀ hX)).f ≫ freeGeneratorHom π X n₀ hn₀) (by
          rw [Category.assoc]
          exact (augmentationShortComplex (trivialProjection π X n₀ hn₀)
            (ker_trivialProjection π X n₀ hn₀ hX)).zero)
    τ₂ := freeGeneratorHom π X n₀ hn₀
    τ₃ := 𝟙 _
    comm₁₂ := ShortComplex.Exact.lift_f _ _ _
    comm₂₃ := by rw [Category.comp_id]; rfl }

/-- The map `I → K` of `augmentationShortComplexHom` is `x ↦ x e`. -/
theorem augmentationShortComplexHom_τ₁_apply (x : augmentationIdealModule (ULift.{w} Λ) G) :
    ((freeAugmentationShortComplex X n₀).map (resCompleted π)).f.hom
        ((augmentationShortComplexHom π X n₀ hn₀ hX).τ₁.hom x) =
      (x : CompletedGroupAlgebra (ULift.{w} Λ) G) •
        (show (resCompleted π).obj (freeModule Λ Q 1) from freeGenerator X n₀ hn₀) :=
  LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom (augmentationShortComplexHom π X n₀ hn₀ hX).comm₁₂) x

/-- **The connecting map of the restricted sequence on `I → Tor₁^{Λ[[G]]}(res_π X, Λ)`**: it
sends `x ∈ I` to the class of `x e ∈ K` in `Tor₀^{Λ[[G]]}(res_π K, Λ)`. -/
theorem leftDerivedδ_trivialTorOneMk (x : augmentationIdealModule (ULift.{w} Λ) G) :
    ((coinvariantsFunctor (ULift.{w} Λ) G).leftDerivedδ
        (shortExact_map_freeAugmentationShortComplex π X n₀ hn₀) 0).hom
        (trivialTorOneMk π X n₀ hn₀ hX x) =
      ((coinvariantsFunctor (ULift.{w} Λ) G).leftDerivedZeroIsoSelf.inv.app _).hom
        (coinvariantsMk _ _ ((augmentationShortComplexHom π X n₀ hn₀ hX).τ₁.hom x)) := by
  have nat := (coinvariantsFunctor (ULift.{w} Λ) G).leftDerivedδ_naturality
    (shortExact_augmentationShortComplex _ (trivialProjection_surjective π X n₀ hn₀ hX)
      (ker_trivialProjection π X n₀ hn₀ hX))
    (shortExact_map_freeAugmentationShortComplex π X n₀ hn₀)
    (augmentationShortComplexHom π X n₀ hn₀ hX) 0
  have nat' := (congrArg (fun f => f ≫ (coinvariantsFunctor (ULift.{w} Λ) G).leftDerivedδ
      (shortExact_map_freeAugmentationShortComplex π X n₀ hn₀) 0)
      (((coinvariantsFunctor (ULift.{w} Λ) G).leftDerived (0 + 1)).map_id _)).symm.trans nat
  have h := (coinvariantsFunctor (ULift.{w} Λ) G).leftDerivedZeroIsoSelf.inv.naturality
    (augmentationShortComplexHom π X n₀ hn₀ hX).τ₁
  exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom nat')
    (trivialTorOneMk π X n₀ hn₀ hX x)).trans
    ((congrArg (((coinvariantsFunctor (ULift.{w} Λ) G).leftDerived 0).map
      (augmentationShortComplexHom π X n₀ hn₀ hX).τ₁).hom
      (leftDerivedδ_torOneIso_inv_apply _ (trivialProjection_surjective π X n₀ hn₀ hX)
        (ker_trivialProjection π X n₀ hn₀ hX) (coinvariantsMk _ _ x))).trans
      (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) (coinvariantsMk _ _ x)).symm)

/-- The map `I_G → I_Q` of augmentation ideals induced by `π`. -/
def augmentationIdealMap :
    augmentationIdealModule (ULift.{w} Λ) G →+ augmentationIdealModule (ULift.{w} Λ) Q where
  toFun x := ⟨map (π : G →* Q) π.continuous x,
    (augmentation_map _ _ (x : CompletedGroupAlgebra (ULift.{w} Λ) G)).trans x.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ (x : CompletedGroupAlgebra (ULift.{w} Λ) G) y)

omit [Finite Λ] [CompactSpace Q] [DiscreteTopology Q] [CompactSpace G] in
/-- `augmentationIdealMap` is `map π` on the underlying elements. -/
theorem coe_augmentationIdealMap (x : augmentationIdealModule (ULift.{w} Λ) G) :
    (augmentationIdealMap π x : CompletedGroupAlgebra (ULift.{w} Λ) Q) =
      map (π : G →* Q) π.continuous x :=
  rfl

/-- `x e` computed over `G` is `π(x) e` computed over `Q`, in the kernel `K` of `Λ[Q] → X`. -/
theorem augmentationShortComplexHom_τ₁_augmentationIdealMap
    (x : augmentationIdealModule (ULift.{w} Λ) G) :
    (show (resCompleted (ContinuousMonoidHom.id Q)).obj (kernel (freeAugmentation X n₀)) from
      (augmentationShortComplexHom π X n₀ hn₀ hX).τ₁.hom x) =
      (augmentationShortComplexHom (ContinuousMonoidHom.id Q) X n₀ hn₀ hX).τ₁.hom
        (augmentationIdealMap π x) := by
  have hinj : Function.Injective
      ((freeAugmentationShortComplex X n₀).map (resCompleted (ContinuousMonoidHom.id Q))).f.hom :=
    (ModuleCat.mono_iff_injective _).1
      (shortExact_map_freeAugmentationShortComplex (ContinuousMonoidHom.id Q) X n₀ hn₀).mono_f
  refine hinj ?_
  have h1 := augmentationShortComplexHom_τ₁_apply π X n₀ hn₀ hX x
  have h2 := augmentationShortComplexHom_τ₁_apply (ContinuousMonoidHom.id Q) X n₀ hn₀ hX
    (augmentationIdealMap π x)
  have h3 := finiteTypeCompletedAction_res π (freeModule Λ Q 1)
    (x : CompletedGroupAlgebra (ULift.{w} Λ) G) (freeGenerator X n₀ hn₀)
  have h4 := finiteTypeCompletedAction_res (ContinuousMonoidHom.id Q) (freeModule Λ Q 1)
    (map (π : G →* Q) π.continuous x) (freeGenerator X n₀ hn₀)
  have h5 : map ((ContinuousMonoidHom.id Q : Q →ₜ* Q) : Q →* Q)
      (ContinuousMonoidHom.id Q).continuous (map (π : G →* Q) π.continuous
        (x : CompletedGroupAlgebra (ULift.{w} Λ) G)) =
      map (π : G →* Q) π.continuous x :=
    (map_congr _ continuous_id rfl _).trans (map_id _)
  exact h1.trans (h3.trans ((congrArg (fun b => finiteTypeCompletedAction (freeModule Λ Q 1) b
    (freeGenerator X n₀ hn₀)) h5.symm).trans (h4.symm.trans h2.symm)))

/-- A morphism `Tor_•^{Λ[[G]]}(res_π -, Λ) ⟶ Tor_•^{Λ[Q]}(-, Λ)` of δ-functors **is the projection
of coinvariants in degree zero**: it sends the class of `m` in `Λ ⊗_{Λ[[G]]} res_π M` to the class
of `m` in `Λ ⊗_{Λ[Q]} M`. -/
def IsCoinvariantsProjection
    (τ : (finiteTypeGroupHomology (Λ := Λ) π).postcomp (uliftRestrict Λ) ⟶ torDelta Λ Q) :
    Prop :=
  ∀ (Y : FiniteTypeContinuousModule.{0, w, w} Λ Q) (k : Y.obj.obj.obj.V),
    ((τ.app 0).app Y).hom (((coinvariantsFunctor (ULift.{w} Λ) G).leftDerivedZeroIsoSelf.inv.app
        ((resCompleted π).obj Y)).hom (coinvariantsMk _ _ (show (resCompleted π).obj Y from k))) =
      ((coinvariantsFunctor (ULift.{w} Λ) Q).leftDerivedZeroIsoSelf.inv.app
        ((resCompleted (ContinuousMonoidHom.id Q)).obj Y)).hom
          (coinvariantsMk _ _ (show (resCompleted (ContinuousMonoidHom.id Q)).obj Y from k))

/-- **Change of rings on `Tor₁` of the trivial module is `I/I² → I_Q/I_Q²`.** A morphism of
δ-functors `Tor_•^{Λ[[G]]}(res_π -, Λ) ⟶ Tor_•^{Λ[Q]}(-, Λ)` which is the projection of
coinvariants in degree zero sends the class of `x ∈ I_G` in `Tor₁^{Λ[[G]]}(X, Λ)` to the class of
`π(x) ∈ I_Q` in `Tor₁^{Λ[Q]}(X, Λ)`. -/
theorem app_one_trivialTorOneMk
    (τ : (finiteTypeGroupHomology (Λ := Λ) π).postcomp (uliftRestrict Λ) ⟶ torDelta Λ Q)
    (hτ : IsCoinvariantsProjection π τ) (x : augmentationIdealModule (ULift.{w} Λ) G) :
    ((τ.app 1).app X).hom (trivialTorOneMk π X n₀ hn₀ hX x) =
      trivialTorOneMk (ContinuousMonoidHom.id Q) X n₀ hn₀ hX (augmentationIdealMap π x) := by
  have hS := shortExact_freeAugmentationShortComplex X n₀ hn₀
  have hE := shortExact_map_freeAugmentationShortComplex (ContinuousMonoidHom.id Q) X n₀ hn₀
  have : Projective ((resCompleted (ContinuousMonoidHom.id Q)).obj (freeModule Λ Q 1)) :=
    projective_freeModule Λ Q 1
  have hmono : Mono ((coinvariantsFunctor (ULift.{w} Λ) Q).leftDerivedδ hE 0) :=
    ((coinvariantsFunctor (ULift.{w} Λ) Q).leftDerived_exact_δ₁ hE 0).mono_g
      (IsZero.eq_of_src
        ((coinvariantsFunctor (ULift.{w} Λ) Q).isZero_leftDerived_obj_projective_succ 0
          ((resCompleted (ContinuousMonoidHom.id Q)).obj (freeModule Λ Q 1))) _ _)
  have hinj := (ModuleCat.mono_iff_injective _).1 hmono
  refine hinj ?_
  have hcomm := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (τ.comm hS 0))
    (trivialTorOneMk π X n₀ hn₀ hX x)
  refine hcomm.symm.trans ?_
  refine (congrArg ((τ.app 0).app _).hom (leftDerivedδ_trivialTorOneMk π X n₀ hn₀ hX x)).trans ?_
  refine (hτ _ _).trans ?_
  refine Eq.trans ?_ (leftDerivedδ_trivialTorOneMk (ContinuousMonoidHom.id Q) X n₀ hn₀ hX
    (augmentationIdealMap π x)).symm
  exact congrArg (fun k => ((coinvariantsFunctor (ULift.{w} Λ) Q).leftDerivedZeroIsoSelf.inv.app
    ((resCompleted (ContinuousMonoidHom.id Q)).obj (kernel (freeAugmentation X n₀)))).hom
      (coinvariantsMk _ _ k)) (augmentationShortComplexHom_τ₁_augmentationIdealMap π X n₀ hn₀ hX x)

end Module

section Finite

variable (Λ : Type) [Ring Λ] [Finite Λ]
  {Q Q' : Type w} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q]
  [DiscreteTopology Q] [Group Q'] [TopologicalSpace Q'] [IsTopologicalGroup Q'] [CompactSpace Q']
  [DiscreteTopology Q'] (π : Q' →ₜ* Q)

/-- Restriction along `π` preserves finite limits (instance form). -/
local instance : PreservesFiniteLimits (finiteTypeContinuousModuleRes.{0, w, w} Λ π) :=
  preservesFiniteLimits_finiteTypeContinuousModuleRes π

/-- Restriction along `π` preserves finite colimits (instance form). -/
local instance : PreservesFiniteColimits (finiteTypeContinuousModuleRes.{0, w, w} Λ π) :=
  preservesFiniteColimits_finiteTypeContinuousModuleRes π

omit [DiscreteTopology Q] [DiscreteTopology Q'] in
/-- The source of `torChangeOfRings` is `Tor_•^{Λ[Q']}(res_π -, Λ)` in the form of
`finiteTypeGroupHomology`. -/
theorem torChangeOfRingsSource_eq :
    torChangeOfRingsSource Λ π = (finiteTypeGroupHomology (Λ := Λ) π).postcomp (uliftRestrict Λ) :=
  rfl

/-- `torChangeOfRings`, with its source written as `finiteTypeGroupHomology`. -/
abbrev torChangeOfRings' :
    (finiteTypeGroupHomology (Λ := Λ) π).postcomp (uliftRestrict Λ) ⟶ torDelta Λ Q :=
  eqToHom (torChangeOfRingsSource_eq Λ π).symm ≫ torChangeOfRings Λ π

/-- `torChangeOfRings'` is `torChangeOfRings` on elements. -/
theorem torChangeOfRings'_app_apply (n : ℕ) (Y : FiniteTypeContinuousModule.{0, w, w} Λ Q)
    (z : (((finiteTypeGroupHomology (Λ := Λ) π).postcomp (uliftRestrict Λ)).functor n).obj Y) :
    (((torChangeOfRings' Λ π).app n).app Y).hom z = (((torChangeOfRings Λ π).app n).app Y).hom z :=
  rfl

/-- **`torChangeOfRings` is the projection of coinvariants in degree zero**, on representatives. -/
theorem isCoinvariantsProjection_torChangeOfRings :
    IsCoinvariantsProjection π (torChangeOfRings' Λ π) := by
  intro Y k
  refine (torChangeOfRings'_app_apply Λ π 0 Y _).trans ?_
  rw [torChangeOfRings_app_zero]
  have e2 := congrArg (fun f => ModuleCat.Hom.hom f (coinvariantsMk _ _
      (show (resCompleted π).obj Y from k)))
    ((coinvariantsFunctor (ULift.{w} Λ) Q').leftDerivedZeroIsoSelf.inv_hom_id_app
      ((resCompleted π).obj Y))
  exact congrArg (fun z => ((torDeltaZeroIso Λ Q).inv.app Y).hom
    (((coinvariantsComparison (Λ := Λ) (Q := Q)).hom.app Y).hom
      (((coinvariantsProjection Λ π).app Y).hom
        (((coinvariantsComparison (Λ := Λ) (Q := Q')).inv.app
          ((finiteTypeContinuousModuleRes.{0, w, w} Λ π).obj Y)).hom z)))) e2

variable (X : FiniteTypeContinuousModule.{0, w, w} Λ Q) (n₀ : X.obj.obj.obj.V)
  (hn₀ : Function.Bijective fun c : Λ => c • n₀) (hX : ∀ q, X.obj.obj.obj.ρ q = 1)

/-- **Naturality of `Tor₁ = I/I²` for the change of rings `Λ[Q'] → Λ[Q]`.** For `X` free of rank
one over `Λ` with trivial action (for instance `X = Λ`), the change-of-rings map
`Tor₁^{Λ[Q']}(X, Λ) → Tor₁^{Λ[Q]}(X, Λ)` sends the class of `x ∈ I_{Q'}` to the class of
`π(x) ∈ I_Q`; that is, under `Tor₁ = I/I²` it is the map `I_{Q'}/I_{Q'}² → I_Q/I_Q²` induced by the
ring map `Λ[Q'] → Λ[Q]`. -/
theorem torChangeOfRings_app_one_trivialTorOneMk
    (x : augmentationIdealModule (ULift.{w} Λ) Q') :
    (((torChangeOfRings Λ π).app 1).app X).hom (trivialTorOneMk π X n₀ hn₀ hX x) =
      trivialTorOneMk (ContinuousMonoidHom.id Q) X n₀ hn₀ hX (augmentationIdealMap π x) :=
  (torChangeOfRings'_app_apply Λ π 1 X _).symm.trans
    (app_one_trivialTorOneMk π X n₀ hn₀ hX _ (isCoinvariantsProjection_torChangeOfRings Λ π) x)

end Finite

end Stacks.GroupHomology
