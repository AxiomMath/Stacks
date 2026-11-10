module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GroupRingRestrictConstituents
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LowerShriekLocallyConstantClosure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.Modules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.UnibranchContinuousModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafSideConditions

/-!
# Finite group-ring modules as finite locally constant sheaves, and their extensions

Let `G` be a topological group and `n > 0`. A finite `ℤ[G]`-module `M` killed by `n` whose
stabilizers are open is a finite `ℤ/n`-module with a continuous `G`-action
(`Stacks.EtaleCohomology.groupRingContinuousModule`), functorially in `ℤ[G]`-linear maps; a
submodule `U ⊆ M` gives a kernel and a cokernel `U → M → M / U` there
(`Stacks.EtaleCohomology.isLimit_groupRingKernelFork`,
`Stacks.EtaleCohomology.isColimit_groupRingCokernelCofork`).

On a connected scheme `X` with a geometric point `x̄`, Tag 0DV5 (3) turns such a module for
`G = π₁(X, x̄)` into a finite locally constant sheaf of `ℤ/n`-modules
(`Stacks.EtaleCohomology.groupRingSheaf`). The finite locally constant sheaves are closed under
kernels and cokernels, so `U → M → M / U` becomes a short exact sequence of sheaves. Hence, if `M`
has its constituents (`Stacks.EtaleCohomology.HasConstituentsIn`) in a family `𝓜`, its sheaf lies
in the closure under extensions and summands (`Stacks.EtaleCohomology.IsExtensionSummandClosure`)
of the sheaves of the `𝓜 i` (`Stacks.EtaleCohomology.isExtensionSummandClosure_groupRingSheaf`).

## Main definitions

* `Stacks.EtaleCohomology.groupRingContinuousModule`, `Stacks.EtaleCohomology.groupRingSheaf`.

## Main results

* `Stacks.EtaleCohomology.isExtensionSummandClosure_groupRingSheaf`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidAlgebra Stacks.GroupCohomology AlgebraicGeometry

universe u v w

namespace Stacks.EtaleCohomology

section ContinuousModule

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (n : ℕ) [NeZero n]

/-- The `G`-module structure of a `ℤ[G]`-module, as a representation over `ℤ/n`. -/
abbrev groupRingZModRepresentation (M : Type w) [AddCommGroup M] [Module (MonoidAlgebra ℤ G) M]
    [Module (ZMod n) M] : Representation (ZMod n) G M :=
  groupRingZModAction n

variable (G) in
/-- The open-stabilizer condition on a `ℤ[G]`-module. -/
def GroupRingIsContinuous (M : Type w) [AddCommGroup M] [Module (MonoidAlgebra ℤ G) M] : Prop :=
  ∀ m : M, IsOpen {g : G | of ℤ G g • m = m}

/-- **A finite `ℤ[G]`-module killed by `n` with open stabilizers, as a finite `ℤ/n`-module with a
continuous `G`-action.** -/
def groupRingContinuousModule (M : Type w) [AddCommGroup M] [Module (MonoidAlgebra ℤ G) M]
    [Module (ZMod n) M] [Finite M] (hM : GroupRingIsContinuous G M) :
    FiniteTypeContinuousModule.{0, v, w} (ZMod n) G :=
  ⟨ofRepresentation (groupRingZModRepresentation n M)
      ((isContinuous_actionOfRepresentation_iff _).2 hM),
    (ModuleCat.isFG_iff _).2 (inferInstanceAs (Module.Finite (ZMod n) M))⟩

/-- A `ℤ[G]`-linear map, as a morphism of continuous modules. -/
def groupRingContinuousModuleMap {M N : Type w} [AddCommGroup M] [Module (MonoidAlgebra ℤ G) M]
    [Module (ZMod n) M] [Finite M] [AddCommGroup N] [Module (MonoidAlgebra ℤ G) N]
    [Module (ZMod n) N] [Finite N] (hM : GroupRingIsContinuous G M) (hN : GroupRingIsContinuous G N)
    (f : M →ₗ[MonoidAlgebra ℤ G] N) :
    groupRingContinuousModule n M hM ⟶ groupRingContinuousModule n N hN :=
  ObjectProperty.homMk ((homEquiv (ZMod n) G _ _).symm
    ⟨f.toAddMonoidHom.toZModLinearMap n, fun g x => f.map_smul (of ℤ G g) x⟩)

/-- `groupRingContinuousModuleMap n hM hN f` acts on elements as `f`. -/
theorem groupRingContinuousModuleMap_apply {M N : Type w} [AddCommGroup M]
    [Module (MonoidAlgebra ℤ G) M] [Module (ZMod n) M] [Finite M] [AddCommGroup N]
    [Module (MonoidAlgebra ℤ G) N] [Module (ZMod n) N] [Finite N] (hM : GroupRingIsContinuous G M)
    (hN : GroupRingIsContinuous G N) (f : M →ₗ[MonoidAlgebra ℤ G] N) (x : M) :
    (groupRingContinuousModuleMap n hM hN f).hom.hom.hom.hom x = f x :=
  rfl

omit [IsTopologicalGroup G] [NeZero n] in
/-- Two morphisms out of a continuous module agreeing on elements are equal. -/
theorem continuousModule_hom_ext {A B : FiniteTypeContinuousModule.{0, v, w} (ZMod n) G}
    {f g : A ⟶ B} (h : ∀ x, f.hom.hom.hom.hom x = g.hom.hom.hom.hom x) : f = g := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply Action.hom_ext
  apply ModuleCat.hom_ext
  exact LinearMap.ext h

/-- The identity map of `M` gives the identity morphism. -/
theorem groupRingContinuousModuleMap_id {M : Type w} [AddCommGroup M]
    [Module (MonoidAlgebra ℤ G) M] [Module (ZMod n) M] [Finite M] (hM : GroupRingIsContinuous G M) :
    groupRingContinuousModuleMap n hM hM LinearMap.id = 𝟙 _ :=
  continuousModule_hom_ext n fun _ => rfl

/-- The morphism of a composite `g ∘ₗ f` is the composite of the morphisms of `f` and `g`. -/
theorem groupRingContinuousModuleMap_comp {M N P : Type w} [AddCommGroup M]
    [Module (MonoidAlgebra ℤ G) M] [Module (ZMod n) M] [Finite M] [AddCommGroup N]
    [Module (MonoidAlgebra ℤ G) N] [Module (ZMod n) N] [Finite N] [AddCommGroup P]
    [Module (MonoidAlgebra ℤ G) P] [Module (ZMod n) P] [Finite P] (hM : GroupRingIsContinuous G M)
    (hN : GroupRingIsContinuous G N) (hP : GroupRingIsContinuous G P)
    (f : M →ₗ[MonoidAlgebra ℤ G] N) (g : N →ₗ[MonoidAlgebra ℤ G] P) :
    groupRingContinuousModuleMap n hM hP (g ∘ₗ f) =
      groupRingContinuousModuleMap n hM hN f ≫ groupRingContinuousModuleMap n hN hP g :=
  continuousModule_hom_ext n fun _ => rfl

omit [IsTopologicalGroup G] [NeZero n] in
/-- The zero morphism of continuous modules sends every element to `0`. -/
theorem continuousModule_zero_apply {A B : FiniteTypeContinuousModule.{0, v, w} (ZMod n) G}
    (x : A.obj.obj.obj.V) : (0 : A ⟶ B).hom.hom.hom.hom x = 0 :=
  rfl

/-- The stabilizer of an element of a `ℤ[G]`-module. -/
def groupRingStabilizer {M : Type w} [AddCommGroup M] [Module (MonoidAlgebra ℤ G) M] (m : M) :
    Subgroup G where
  carrier := {g | of ℤ G g • m = m}
  one_mem' := by
    change of ℤ G 1 • m = m
    rw [map_one, one_smul]
  mul_mem' {a b} ha hb := by
    change of ℤ G (a * b) • m = m
    rw [map_mul, mul_smul]
    change of ℤ G b • m = m at hb
    change of ℤ G a • m = m at ha
    rw [hb, ha]
  inv_mem' {a} ha := by
    change of ℤ G a • m = m at ha
    change of ℤ G a⁻¹ • m = m
    conv_lhs => rw [← ha, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]

end ContinuousModule

/-! ### Kernels and cokernels -/

section KernelCokernel

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (n : ℕ) [NeZero n]
  {M : Type w} [AddCommGroup M] [Module (MonoidAlgebra ℤ G) M] [Module (ZMod n) M] [Finite M]
  (U : Submodule (MonoidAlgebra ℤ G) M)

/-- The `ℤ/n`-module structure of a `ℤ[G]`-submodule. -/
abbrev groupRingSubmoduleZModModule : Module (ZMod n) U :=
  inferInstanceAs (Module (ZMod n) (zmodSubmoduleOfGroupRing n U))

omit [TopologicalSpace G] [IsTopologicalGroup G] [NeZero n] [Finite M] in
/-- The quotient `M / U` of a module killed by `n` is killed by `n`. -/
theorem groupRingQuotient_nsmul_eq_zero (x : M ⧸ U) : n • x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    rw [← Submodule.Quotient.mk_smul, ← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self,
      zero_smul, Submodule.Quotient.mk_zero]

/-- The `ℤ/n`-module structure of a quotient. -/
abbrev groupRingQuotientZModModule : Module (ZMod n) (M ⧸ U) :=
  AddCommGroup.zmodModule (groupRingQuotient_nsmul_eq_zero n U)

/-- A quotient of a finite module is finite. -/
instance instFiniteGroupRingQuotient : Finite (M ⧸ U) :=
  Finite.of_surjective _ (Submodule.Quotient.mk_surjective U)

variable {U}

omit [IsTopologicalGroup G] [Finite M] in
/-- A submodule of a module with open stabilizers has open stabilizers. -/
theorem groupRingIsContinuous_submodule (hM : GroupRingIsContinuous G M) :
    GroupRingIsContinuous G U := fun m => by
  have : {g : G | of ℤ G g • m = m} = {g | of ℤ G g • (m : M) = m} :=
    Set.ext fun g => Subtype.ext_iff
  rw [this]
  exact hM m

omit [Finite M] in
/-- A quotient of a module with open stabilizers has open stabilizers. -/
theorem groupRingIsContinuous_quotient (hM : GroupRingIsContinuous G M) :
    GroupRingIsContinuous G (M ⧸ U) := fun x => by
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    refine Subgroup.isOpen_mono (H₁ := groupRingStabilizer y) (H₂ := groupRingStabilizer
      (Submodule.Quotient.mk y : M ⧸ U)) (fun g hg => ?_) (hM y)
    change of ℤ G g • (Submodule.Quotient.mk y : M ⧸ U) = Submodule.Quotient.mk y
    rw [← Submodule.Quotient.mk_smul]
    change of ℤ G g • y = y at hg
    rw [hg]

variable (U) (hM : GroupRingIsContinuous G M)

/-- The inclusion `U → M`, as a morphism of continuous modules. -/
def groupRingKernelι :
    letI := groupRingSubmoduleZModModule n U
    groupRingContinuousModule n U (groupRingIsContinuous_submodule hM) ⟶
      groupRingContinuousModule n M hM :=
  letI := groupRingSubmoduleZModModule n U
  groupRingContinuousModuleMap n _ hM U.subtype

/-- The projection `M → M / U`, as a morphism of continuous modules. -/
def groupRingCokernelπ :
    letI := groupRingQuotientZModModule n U
    groupRingContinuousModule n M hM ⟶
      groupRingContinuousModule n (M ⧸ U) (groupRingIsContinuous_quotient hM) :=
  letI := groupRingQuotientZModModule n U
  groupRingContinuousModuleMap n hM _ U.mkQ

/-- The composite `U → M → M / U` is zero. -/
theorem groupRingKernelι_comp_cokernelπ :
    groupRingKernelι n U hM ≫ groupRingCokernelπ n U hM = 0 :=
  continuousModule_hom_ext n fun x => (Submodule.Quotient.mk_eq_zero U).2 x.2

/-- **`U → M` is a kernel of `M → M / U`.** -/
def isLimit_groupRingKernelFork :
    IsLimit (KernelFork.ofι _ (groupRingKernelι_comp_cokernelπ n U hM)) := by
  letI := groupRingSubmoduleZModModule n U
  refine KernelFork.IsLimit.ofι _ _ (fun {W} k hk => ?_) (fun {W} k hk => ?_)
    (fun {W} k hk m hm => ?_)
  · have hmem : ∀ w, k.hom.hom.hom.hom w ∈ U := fun w => by
      have := congrArg (fun f => f.hom.hom.hom.hom w) hk
      exact (Submodule.Quotient.mk_eq_zero U).1 this
    exact ObjectProperty.homMk ((homEquiv (ZMod n) G _ _).symm
      ⟨LinearMap.codRestrict (zmodSubmoduleOfGroupRing n U) k.hom.hom.hom.hom.hom hmem,
        fun g w => Subtype.ext ((homEquiv (ZMod n) G _ _ k.hom).2 g w)⟩)
  · exact continuousModule_hom_ext n fun _ => rfl
  · exact continuousModule_hom_ext n fun w => Subtype.ext
      (congrArg (fun f => f.hom.hom.hom.hom w) hm)

/-- **`M → M / U` is a cokernel of `U → M`.** -/
def isColimit_groupRingCokernelCofork :
    IsColimit (CokernelCofork.ofπ _ (groupRingKernelι_comp_cokernelπ n U hM)) := by
  letI := groupRingQuotientZModModule n U
  refine CokernelCofork.IsColimit.ofπ _ _ (fun {W} k hk => ?_) (fun {W} k hk => ?_)
    (fun {W} k hk m hm => ?_)
  · have hker : U.toAddSubgroup ≤ (k.hom.hom.hom.hom.hom.toAddMonoidHom).ker := fun y hy => by
      have := congrArg (fun f => f.hom.hom.hom.hom ⟨y, hy⟩) hk
      exact this
    let L : (M ⧸ U) →+ W.obj.obj.obj.V :=
      QuotientAddGroup.lift U.toAddSubgroup k.hom.hom.hom.hom.hom.toAddMonoidHom hker
    have key : ∀ (g : G) (y : M), k.hom.hom.hom.hom (of ℤ G g • y) =
        (W.obj.obj.obj.ρ g).asHom.hom (k.hom.hom.hom.hom y) := fun g y =>
      ConcreteCategory.congr_hom (k.hom.hom.hom.comm g) y
    refine ObjectProperty.homMk ((homEquiv (ZMod n) G _ _).symm
      ⟨L.toZModLinearMap n, fun g x => ?_⟩)
    induction x using Submodule.Quotient.induction_on with
    | H y =>
      change L (Submodule.Quotient.mk (of ℤ G g • y)) =
        (W.obj.obj.obj.ρ g).asHom.hom (L (Submodule.Quotient.mk y))
      exact key g y
  · exact continuousModule_hom_ext n fun _ => rfl
  · refine continuousModule_hom_ext n fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H y => exact congrArg (fun f => f.hom.hom.hom.hom y) hm

end KernelCokernel


/-! ### The sheaves of finite group-ring modules -/

section Sheaf

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (n : ℕ) [NeZero n]

omit [ConnectedSpace X.1] [NeZero n] in
/-- Presheaves of `ℤ/n`-modules on the small étale site of `X` admit sheafification. -/
theorem groupRingSheaf_hasSheafify :
    HasSheafify (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} (ZMod n)) :=
  Stacks.ModuleSheaf.hasSheafify_moduleCat.{u + 1} (ZMod n) (SmallEtale.topology B X.1 X.2)

attribute [local instance] groupRingSheaf_hasSheafify

/-- The finite type locally constant sheaves of `ℤ/n`-modules on `X`. -/
abbrev groupRingSheafProperty :
    ObjectProperty (Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} (ZMod n))) :=
  fun F => Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod n)
    (SmallEtale.topology B X.1 X.2) F

/-- The finite type locally constant sheaves of `ℤ/n`-modules are closed under kernels. -/
instance instIsClosedUnderKernelsGroupRingSheafProperty :
    (groupRingSheafProperty B X n).IsClosedUnderKernels :=
  inferInstanceAs (ObjectProperty.IsClosedUnderKernels
    (Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0, 0}
      (SmallEtale.topology B X.1 X.2) (ZMod n)))

/-- The finite type locally constant sheaves of `ℤ/n`-modules are closed under cokernels. -/
instance instIsClosedUnderCokernelsGroupRingSheafProperty :
    (groupRingSheafProperty B X n).IsClosedUnderCokernels :=
  inferInstanceAs (ObjectProperty.IsClosedUnderCokernels
    (Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0, 0}
      (SmallEtale.topology B X.1 X.2) (ZMod n)))

/-- Tag 0DV5 (3) for `ℤ/n`, followed by the inclusion into all sheaves of `ℤ/n`-modules. -/
abbrev groupRingSheafFunctor :
    FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n) (EtaleFundamentalGroup X.1 x) ⥤
      Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} (ZMod n)) :=
  (AlgebraicGeometry.finiteTypeLocallyConstantModuleSheafEquivalence B X x (ZMod n)).inverse ⋙
    (groupRingSheafProperty B X n).ι

/-- **The finite locally constant sheaf of a finite `ℤ[π₁(X, x̄)]`-module killed by `n`.** -/
def groupRingSheaf (M : Type (u + 1)) [AddCommGroup M]
    [Module (MonoidAlgebra ℤ (EtaleFundamentalGroup X.1 x)) M] [Module (ZMod n) M] [Finite M]
    (hM : GroupRingIsContinuous (EtaleFundamentalGroup X.1 x) M) :
    Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} (ZMod n)) :=
  (groupRingSheafFunctor B X x n).obj (groupRingContinuousModule n M hM)

variable {M : Type (u + 1)} [AddCommGroup M]
  [Module (MonoidAlgebra ℤ (EtaleFundamentalGroup X.1 x)) M] [Module (ZMod n) M] [Finite M]
  (hM : GroupRingIsContinuous (EtaleFundamentalGroup X.1 x) M)
  (U : Submodule (MonoidAlgebra ℤ (EtaleFundamentalGroup X.1 x)) M)

/-- **`0 → U → M → M / U → 0` gives a short exact sequence of sheaves.** -/
theorem shortExact_groupRingSheaf :
    (ShortComplex.mk ((groupRingSheafFunctor B X x n).map (groupRingKernelι n U hM))
      ((groupRingSheafFunctor B X x n).map (groupRingCokernelπ n U hM))
      (by rw [← Functor.map_comp, groupRingKernelι_comp_cokernelπ,
        Functor.map_zero])).ShortExact := by
  have := (groupRingSheafProperty B X n).preservesKernels_ι
    ((AlgebraicGeometry.finiteTypeLocallyConstantModuleSheafEquivalence B X x (ZMod n)).inverse.map
      (groupRingCokernelπ n U hM))
  have := (groupRingSheafProperty B X n).preservesCokernels_ι
    ((AlgebraicGeometry.finiteTypeLocallyConstantModuleSheafEquivalence B X x (ZMod n)).inverse.map
      (groupRingKernelι n U hM))
  have hk := KernelFork.mapIsLimit _ (KernelFork.mapIsLimit _ (isLimit_groupRingKernelFork n U hM)
    (AlgebraicGeometry.finiteTypeLocallyConstantModuleSheafEquivalence B X x (ZMod n)).inverse)
    (groupRingSheafProperty B X n).ι
  have hc := CokernelCofork.mapIsColimit _ (CokernelCofork.mapIsColimit _
    (isColimit_groupRingCokernelCofork n U hM)
    (AlgebraicGeometry.finiteTypeLocallyConstantModuleSheafEquivalence B X x (ZMod n)).inverse)
    (groupRingSheafProperty B X n).ι
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ hk)
    (mono_of_isLimit_fork hk) (epi_of_isColimit_cofork hc)

/-- The sheaf of a `ℤ[G]`-linear map. -/
def groupRingSheafMap {N : Type (u + 1)} [AddCommGroup N]
    [Module (MonoidAlgebra ℤ (EtaleFundamentalGroup X.1 x)) N] [Module (ZMod n) N] [Finite N]
    (hN : GroupRingIsContinuous (EtaleFundamentalGroup X.1 x) N)
    (f : M →ₗ[MonoidAlgebra ℤ (EtaleFundamentalGroup X.1 x)] N) :
    groupRingSheaf B X x n M hM ⟶ groupRingSheaf B X x n N hN :=
  (groupRingSheafFunctor B X x n).map (groupRingContinuousModuleMap n hM hN f)

/-- The identity map of `M` gives the identity morphism of its sheaf. -/
theorem groupRingSheafMap_id :
    groupRingSheafMap B X x n hM hM LinearMap.id = 𝟙 _ := by
  rw [groupRingSheafMap, groupRingContinuousModuleMap_id]
  exact (groupRingSheafFunctor B X x n).map_id _

/-- The sheaf map of a composite `g ∘ₗ f` is the composite of the sheaf maps of `f` and `g`. -/
theorem groupRingSheafMap_comp {N P : Type (u + 1)} [AddCommGroup N]
    [Module (MonoidAlgebra ℤ (EtaleFundamentalGroup X.1 x)) N] [Module (ZMod n) N] [Finite N]
    [AddCommGroup P] [Module (MonoidAlgebra ℤ (EtaleFundamentalGroup X.1 x)) P]
    [Module (ZMod n) P] [Finite P]
    (hN : GroupRingIsContinuous (EtaleFundamentalGroup X.1 x) N)
    (hP : GroupRingIsContinuous (EtaleFundamentalGroup X.1 x) P)
    (f : M →ₗ[MonoidAlgebra ℤ (EtaleFundamentalGroup X.1 x)] N)
    (g : N →ₗ[MonoidAlgebra ℤ (EtaleFundamentalGroup X.1 x)] P) :
    groupRingSheafMap B X x n hM hP (g ∘ₗ f) =
      groupRingSheafMap B X x n hM hN f ≫ groupRingSheafMap B X x n hN hP g := by
  rw [groupRingSheafMap, groupRingContinuousModuleMap_comp n hM hN hP]
  exact (groupRingSheafFunctor B X x n).map_comp _ _

/-- If `g ∘ₗ f = id`, then the sheaf map of `g` is a retraction of the sheaf map of `f`. -/
private theorem groupRingSheafMap_comp_eq_id {N : Type (u + 1)} [AddCommGroup N]
    [Module (MonoidAlgebra ℤ (EtaleFundamentalGroup X.1 x)) N] [Module (ZMod n) N] [Finite N]
    (hN : GroupRingIsContinuous (EtaleFundamentalGroup X.1 x) N)
    {f : M →ₗ[MonoidAlgebra ℤ (EtaleFundamentalGroup X.1 x)] N}
    {g : N →ₗ[MonoidAlgebra ℤ (EtaleFundamentalGroup X.1 x)] M} (h : g ∘ₗ f = LinearMap.id) :
    groupRingSheafMap B X x n hM hN f ≫ groupRingSheafMap B X x n hN hM g = 𝟙 _ := by
  rw [← groupRingSheafMap_comp, h, groupRingSheafMap_id]

/-- The sheaf of a trivial module is zero. -/
theorem isZero_groupRingSheaf [Subsingleton M] : IsZero (groupRingSheaf B X x n M hM) := by
  rw [IsZero.iff_id_eq_zero, ← groupRingSheafMap_id]
  have h0 : groupRingContinuousModuleMap n hM hM LinearMap.id = 0 :=
    continuousModule_hom_ext n fun y => Subsingleton.elim (α := M) _ _
  rw [groupRingSheafMap, h0]
  exact (groupRingSheafFunctor B X x n).map_zero _ _

/-- **The sheaf of a module with its constituents in `𝓜` lies in the closure under extensions
and summands of the sheaves of the `𝓜 i`.** -/
theorem isExtensionSummandClosure_groupRingSheaf {ι : Type*} (𝓜 : ι → Type (u + 1))
    [∀ i, AddCommGroup (𝓜 i)] [∀ i, Module (MonoidAlgebra ℤ (EtaleFundamentalGroup X.1 x)) (𝓜 i)]
    [∀ i, Module (ZMod n) (𝓜 i)] [∀ i, Finite (𝓜 i)]
    (h𝓜 : ∀ i, GroupRingIsContinuous (EtaleFundamentalGroup X.1 x) (𝓜 i))
    (S : ObjectProperty (Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} (ZMod n))))
    (hS : ∀ i, S (groupRingSheaf B X x n (𝓜 i) (h𝓜 i))) (i₀ : ι)
    (hcon : HasConstituentsIn (MonoidAlgebra ℤ (EtaleFundamentalGroup X.1 x)) 𝓜 M) :
    IsExtensionSummandClosure S (groupRingSheaf B X x n M hM) := by
  let P : ∀ (Y : Type (u + 1)) [AddCommGroup Y]
      [Module (MonoidAlgebra ℤ (EtaleFundamentalGroup X.1 x)) Y], Prop := fun Y _ _ =>
    ∀ (_ : Module (ZMod n) Y) (_ : Finite Y)
      (h : GroupRingIsContinuous (EtaleFundamentalGroup X.1 x) Y),
      IsExtensionSummandClosure S (groupRingSheaf B X x n Y h)
  suffices H : P M from H _ inferInstance hM
  refine HasConstituentsIn.prop P ?_ ?_ ?_ ?_ M hcon
  · intro Y Z _ _ _ _ e hY instZ finZ hZ
    let : Module (ZMod n) Y := AddCommGroup.zmodModule fun y => e.injective (by
      rw [map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul, map_zero])
    have : Finite Y := Finite.of_equiv _ e.toEquiv.symm
    have hYc : GroupRingIsContinuous (EtaleFundamentalGroup X.1 x) Y := fun m => by
      have : {g : EtaleFundamentalGroup X.1 x | of ℤ _ g • m = m} =
          {g | of ℤ _ g • e m = e m} := Set.ext fun g => by
        simp only [Set.mem_ofPred_eq, ← map_smul, e.injective.eq_iff]
      rw [this]; exact hZ (e m)
    exact .of_iso ⟨groupRingSheafMap B X x n hYc hZ e.toLinearMap,
      groupRingSheafMap B X x n hZ hYc e.symm.toLinearMap,
      groupRingSheafMap_comp_eq_id B X x n hYc hZ e.symm_comp,
      groupRingSheafMap_comp_eq_id B X x n hZ hYc e.comp_symm⟩
      (hY inferInstance inferInstance hYc)
  · intro Y _ _ hY _ _ h
    exact .of_retract 0 0 ((isZero_groupRingSheaf B X x n h).eq_of_src _ _)
      (.of_mem (hS i₀))
  · intro Y _ _ _ i f g hgf _ _ h
    refine .of_retract (groupRingSheafMap B X x n h (h𝓜 i) f)
      (groupRingSheafMap B X x n (h𝓜 i) h g) 
      (groupRingSheafMap_comp_eq_id B X x n _ _ hgf) (.of_mem (hS i))
  · intro Y _ _ _ U hU hQ _ _ h
    let := groupRingSubmoduleZModModule n U
    let := groupRingQuotientZModModule n U
    exact .of_shortExact (shortExact_groupRingSheaf B X x n h U)
      (hU _ inferInstance (groupRingIsContinuous_submodule h))
      (hQ _ inferInstance (groupRingIsContinuous_quotient h))

end Sheaf

end Stacks.EtaleCohomology

end
