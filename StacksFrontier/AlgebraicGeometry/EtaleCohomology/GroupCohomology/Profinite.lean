module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.Continuous
public import StacksFrontier.Topology.Algebra.ProfiniteGroup

/-!
# Higher cohomology of a profinite group

The positive-degree continuous cohomology groups of a profinite group with discrete
coefficients are torsion. They vanish when the coefficient module is a rational vector space.

## Main results

* `continuousGroupCohomology_isTorsion` states that positive-degree continuous group cohomology
  is torsion.
* `isZero_continuousGroupCohomology_of_module_rat` states the corresponding vanishing for
  rational vector-space coefficients.

## References

* [Stacks Project, Tag 0DV3](https://stacks.math.columbia.edu/tag/0DV3)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Pretriangulated
open _root_.DerivedCategory

universe u v

/-- `ℤ`-modules are given the discrete topology when forming continuous actions. -/
local instance : HasForget₂ (ModuleCat.{v} ℤ) TopCat.{v} :=
  { forget₂ := forget (ModuleCat.{v} ℤ) ⋙ TopCat.discrete
    forget_comp := rfl }

private lemma finite_orbit_sum_fixed
    {G A B : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    [AddCommGroup A] [Module ℤ A] [AddCommGroup B] [Module ℤ B]
    [DistribMulAction G A] [DistribMulAction G B]
    [TopologicalSpace A] [DiscreteTopology A]
    (hcont : Continuous fun p : G × A => p.1 • p.2)
    (d : A →+ B) (hd : ∀ (g : G) (a : A), d (g • a) = g • d a)
    (x : A) (hy : ∀ (g : G), g • d x = d x) :
    ∃ n : ℕ, 0 < n ∧ ∃ z : A, (∀ (g : G), g • z = z) ∧
      d z = (n : ℤ) • d x := by
  let f : G → A := fun g ↦ g • x
  let s : Set A := Set.range f
  let : CompactSpace s := isCompact_iff_compactSpace.mp
    (isCompact_range (hcont.comp (by fun_prop : Continuous fun g : G ↦ (g, x))))
  let : Finite s := finite_of_compact_of_discrete
  let : Fintype s := Fintype.ofFinite s
  let z : A := ∑ a : s, (a : A)
  have hz : ∀ (g : G), g • z = z := by
    intro g
    let e : s ≃ s :=
      { toFun a := ⟨g • (a : A), by obtain ⟨_, h, rfl⟩ := a; exact ⟨g * h, mul_smul g h x⟩⟩
        invFun a := ⟨g⁻¹ • (a : A), by obtain ⟨_, h, rfl⟩ := a; exact ⟨g⁻¹ * h, mul_smul _ h x⟩⟩
        left_inv a := Subtype.ext (inv_smul_smul g _)
        right_inv a := Subtype.ext (smul_inv_smul g _) }
    dsimp only [z]
    rw [Finset.smul_sum]
    exact Fintype.sum_equiv e _ _ fun _ ↦ rfl
  refine ⟨Fintype.card s, Fintype.card_pos_iff.mpr ⟨⟨x, 1, by simp [f]⟩⟩, z, hz, ?_⟩
  dsimp only [z]
  rw [map_sum, Fintype.sum_congr _ (fun _ ↦ d x) fun ⟨_, g, rfl⟩ ↦ (hd g x).trans (hy g)]
  simp

private lemma exists_invariant_multiple_of_action_hom
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : Stacks.Chapter05.Tag_0BR1.IsProfiniteTop G)
    (A B : Action (ModuleCat.{v} ℤ) G)
    (hAcont : A.IsContinuous)
    (hAdisc : DiscreteTopology ((forget₂ (Action (ModuleCat.{v} ℤ) G) TopCat).obj A))
    (f : A ⟶ B) (x : ↑A.V)
    (hy : ∀ (g : G), ConcreteCategory.hom (B.ρ g).asHom
      (ConcreteCategory.hom f.hom x) = ConcreteCategory.hom f.hom x) :
    ∃ n : ℕ, 0 < n ∧ ∃ z : ↑A.V,
      (∀ g, ConcreteCategory.hom (A.ρ g).asHom z = z) ∧
        ConcreteCategory.hom f.hom z = (n : ℤ) • ConcreteCategory.hom f.hom x := by
  let : CompactSpace G := hG.1
  let : TopologicalSpace (↑A.V) := ((forget₂ (ModuleCat.{v} ℤ) TopCat).obj A.V).str
  let : DiscreteTopology (↑A.V) := hAdisc
  let : MulAction G (↑A.V) :=
    { smul g x := ConcreteCategory.hom (A.ρ g).asHom x
      one_smul x := by change ConcreteCategory.hom (A.ρ 1).asHom x = x; simp
      mul_smul g h x := by
        show ConcreteCategory.hom (A.ρ (g * h)).asHom x =
          ConcreteCategory.hom (A.ρ g).asHom (ConcreteCategory.hom (A.ρ h).asHom x)
        rw [map_mul]
        rfl }
  let : DistribMulAction G (↑A.V) :=
    { smul_zero g := map_zero (ConcreteCategory.hom (A.ρ g).asHom)
      smul_add g := map_add (ConcreteCategory.hom (A.ρ g).asHom) }
  let : MulAction G (↑B.V) :=
    { smul g x := ConcreteCategory.hom (B.ρ g).asHom x
      one_smul x := by change ConcreteCategory.hom (B.ρ 1).asHom x = x; simp
      mul_smul g h x := by
        show ConcreteCategory.hom (B.ρ (g * h)).asHom x =
          ConcreteCategory.hom (B.ρ g).asHom (ConcreteCategory.hom (B.ρ h).asHom x)
        rw [map_mul]
        rfl }
  let : DistribMulAction G (↑B.V) :=
    { smul_zero g := map_zero (ConcreteCategory.hom (B.ρ g).asHom)
      smul_add g := map_add (ConcreteCategory.hom (B.ρ g).asHom) }
  let : ContinuousSMul G (↑A.V) := ⟨(Action.isContinuous_def A).mp hAcont⟩
  let f' : A.V ⟶ B.V := f.hom
  let d : (↑A.V) →+ (↑B.V) :=
    { toFun := f'.hom
      map_zero' := f'.hom.map_zero
      map_add' := f'.hom.map_add }
  have hd : ∀ (g : G) (a : ↑A.V), d (g • a) = g • d a := by
    intro g a
    show f'.hom (ConcreteCategory.hom (A.ρ g).asHom a) =
      ConcreteCategory.hom (B.ρ g).asHom (f'.hom a)
    simpa [f'] using ConcreteCategory.congr_hom (f.comm g) a
  exact finite_orbit_sum_fixed continuous_smul d hd x hy

private lemma surjective_action_forget_map_of_epi
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {X Y : ContinuousGModule.{u, max u v} G} (f : X ⟶ Y) (hf : Epi f) :
    Function.Surjective ((Action.forget (ModuleCat.{max u v} ℤ) G).map
      ((ObjectProperty.ι (Action.IsContinuous (V := ModuleCat.{max u v} ℤ) (G := G))).map
        ((ObjectProperty.ι (ContAction.IsDiscrete
          (V := ModuleCat.{max u v} ℤ) (G := G))).map f))) := by
  let P₁ := ContAction.IsDiscrete (V := ModuleCat.{max u v} ℤ) (G := G)
  let P₂ := Action.IsContinuous (V := ModuleCat.{max u v} ℤ) (G := G)
  let F₁ := ObjectProperty.ι P₁
  let F₂ := ObjectProperty.ι P₂
  have : Functor.PreservesEpimorphisms F₁ :=
    ObjectProperty.preservesEpimorphisms_ι_of_isNormalMonoCategory P₁
  have : Functor.PreservesEpimorphisms F₂ :=
    ObjectProperty.preservesEpimorphisms_ι_of_isNormalMonoCategory P₂
  have : Epi (F₁.map f) := @Functor.map_epi _ _ _ _ F₁ inferInstance X Y f hf
  have hL : Epi ((F₁ ⋙ F₂).map f) := Functor.PreservesEpimorphisms.preserves (F := F₂) (F₁.map f)
  exact (ModuleCat.epi_iff_surjective _).mp
    (@Functor.map_epi _ _ _ _ (Action.forget (ModuleCat.{max u v} ℤ) G) inferInstance _ _ _ hL)

private lemma exists_preimage_of_exact_addCommGrpCat
    {S : ShortComplex AddCommGrpCat} (hS : S.Exact)
    (x : ↑S.X₂) (hx : S.g.hom x = 0) :
    ∃ y : ↑S.X₁, S.f.hom y = x := by
  let kx : ↑(S.g.hom.ker) := ⟨x, hx⟩
  let kx' : ↑(kernel S.g) := (AddCommGrpCat.kernelIsoKer S.g).inv kx
  have hepi : Epi (kernel.lift S.g S.f S.zero) := S.exact_iff_epi_kernel_lift.mp hS
  obtain ⟨y, hy⟩ := (AddCommGrpCat.epi_iff_surjective _).mp hepi kx'
  have hk : (kernel.ι S.g).hom kx' = x := by
    show ((AddCommGrpCat.kernelIsoKer S.g).inv ≫ kernel.ι S.g).hom kx = x
    rw [AddCommGrpCat.kernelIsoKer_inv_comp_ι]
    rfl
  refine ⟨y, ?_⟩
  calc
    S.f.hom y = (kernel.ι S.g).hom ((kernel.lift S.g S.f S.zero).hom y) :=
      congrArg (fun m : S.X₁ ⟶ S.X₂ ↦ m.hom y) (kernel.lift_ι S.g S.f S.zero).symm
    _ = (kernel.ι S.g).hom kx' := congrArg (kernel.ι S.g).hom hy
    _ = x := hk

attribute [local instance] HasDerivedCategory.standard

private noncomputable def invariantsUnitAppSingle {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [EnoughInjectives C] :
    HomotopyCategory.Plus.singleFunctor C 0 ⋙ F.mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.homologyFunctor D 0 ⟶
      HomotopyCategory.Plus.singleFunctor C 0 ⋙ DerivedCategory.Plus.Qh ⋙
        F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor D 0 :=
  Functor.whiskerLeft (HomotopyCategory.Plus.singleFunctor C 0)
    (Functor.whiskerRight F.rightDerivedFunctorPlusUnith
      (DerivedCategory.Plus.homologyFunctor D 0))

private noncomputable def invariantsRightDerivedZeroIso {C D : Type*} [Category C]
    [Category D] [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] :
    F ≅ F.rightDerivedPlus 0 := by
  have hunit : IsIso (invariantsUnitAppSingle F) := by
    have : ∀ X, IsIso ((invariantsUnitAppSingle F).app X) :=
      (Functor.isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits
        F F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnith).2.2.2 inferInstance
    exact NatIso.isIso_of_isIso_app _
  exact
    (Functor.isoWhiskerRight (Functor.mapSingleFunctorCompQhIso F)
      (DerivedCategory.Plus.homologyFunctor D 0) ≪≫
      Functor.isoWhiskerLeft F (DerivedCategory.singleFunctorCompHomologyFunctorIso D 0) ≪≫
      Functor.rightUnitor F).symm ≪≫
    asIso (invariantsUnitAppSingle F) ≪≫
    (Functor.isoWhiskerRight (Functor.singleFunctorPlusIsoCompQh 0)
      (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor D 0)).symm

@[instance_reducible]
private noncomputable def derivedRightDerivedCommShift {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [EnoughInjectives C] :
    F.rightDerivedFunctorPlus.CommShift ℤ :=
  Functor.IsRightDerivedFunctor.commShift _ F.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso C) ℤ

attribute [local instance] derivedRightDerivedCommShift

private lemma derivedRightDerivedUnitCommShift {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [EnoughInjectives C] :
    NatTrans.CommShift F.rightDerivedFunctorPlusUnith ℤ :=
  Functor.IsRightDerivedFunctor.natTrans_commShift F.rightDerivedFunctorPlus
    F.rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso C) ℤ

attribute [local instance] derivedRightDerivedUnitCommShift

private lemma derivedRightDerivedTriangulated {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [EnoughInjectives C] :
    F.rightDerivedFunctorPlus.IsTriangulated :=
  Functor.isTriangulated_of_isRightDerivedFunctor_mapHomotopyCategoryPlus F _
    F.rightDerivedFunctorPlusUnith

attribute [local instance] derivedRightDerivedTriangulated

private noncomputable def baseSingleTrianglePlus {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {S : ShortComplex C} (hS : S.ShortExact) :
    Triangle (Plus C) :=
  Triangle.mk ((Plus.singleFunctor C 0).map S.f)
    ((Plus.singleFunctor C 0).map S.g)
    (Plus.ι.preimage
      (hS.singleδ ≫ (Plus.ι.commShiftIso (1 : ℤ)).inv.app
        ((Plus.singleFunctor C 0).obj S.X₁)))

/-- Composing a morphism with the inverse and then the forward component of a natural
isomorphism at an object leaves it unchanged. -/
private lemma comp_inv_app_comp_hom_app {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) (X : C) {W : D} (h : W ⟶ G.obj X) :
    (h ≫ e.inv.app X) ≫ e.hom.app X = h := by
  simp

private lemma ι_map_baseSingleTrianglePlus {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {S : ShortComplex C} (hS : S.ShortExact) :
    Plus.ι.mapTriangle.obj (baseSingleTrianglePlus hS) = hS.singleTriangle := by
  rw [Functor.mapTriangle_obj]
  dsimp only [baseSingleTrianglePlus, Triangle.mk_mor₁, Triangle.mk_mor₂, Triangle.mk_mor₃,
    Triangle.mk_obj₁]
  rw [Functor.map_preimage]
  exact congrArg (Triangle.mk ((singleFunctor C 0).map S.f) ((singleFunctor C 0).map S.g))
    (comp_inv_app_comp_hom_app (Plus.ι.commShiftIso (1 : ℤ))
      ((Plus.singleFunctor C 0).obj S.X₁) hS.singleδ)

private lemma baseSingleTrianglePlus_distinguished {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {S : ShortComplex C} (hS : S.ShortExact) :
    baseSingleTrianglePlus hS ∈ distTriang (DerivedCategory.Plus C) := by
  show DerivedCategory.Plus.ι.mapTriangle.obj (baseSingleTrianglePlus hS) ∈
    distTriang (DerivedCategory C)
  rw [ι_map_baseSingleTrianglePlus hS]
  exact hS.singleTriangle_distinguished

private noncomputable def derivedSingleTriangle {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [EnoughInjectives C]
    {S : ShortComplex C} (hS : S.ShortExact) : Triangle (DerivedCategory.Plus D) :=
  F.rightDerivedFunctorPlus.mapTriangle.obj (baseSingleTrianglePlus hS)

private lemma derivedSingleTriangle_distinguished {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [EnoughInjectives C]
    {S : ShortComplex C} (hS : S.ShortExact) :
    derivedSingleTriangle F hS ∈ distTriang (DerivedCategory.Plus D) :=
  F.rightDerivedFunctorPlus.map_distinguished _ (baseSingleTrianglePlus_distinguished hS)

private noncomputable def derivedDeltaShortComplex {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [EnoughInjectives C]
    {S : ShortComplex C} (hS : S.ShortExact) (n : ℤ) : ShortComplex D :=
  let T := derivedSingleTriangle F hS
  ShortComplex.mk
    ((DerivedCategory.Plus.homologyFunctor D 0).homologySequenceδ T n (n + 1) rfl)
    (((DerivedCategory.Plus.homologyFunctor D 0).shift (n + 1)).map T.mor₁)
    ((DerivedCategory.Plus.homologyFunctor D 0).homologySequenceδ_comp T
      (derivedSingleTriangle_distinguished F hS) n (n + 1) rfl)

private lemma derivedDeltaShortComplex_exact {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [EnoughInjectives C]
    {S : ShortComplex C} (hS : S.ShortExact) (n : ℤ) :
    (derivedDeltaShortComplex F hS n).Exact :=
  (DerivedCategory.Plus.homologyFunctor D 0).homologySequence_exact₁
    (derivedSingleTriangle F hS) (derivedSingleTriangle_distinguished F hS) n (n + 1) rfl

/-- Every object embeds in an injective object with short exact cokernel sequence. -/
private lemma exists_shortExact_injective_presentation
    {C : Type*} [Category C] [Abelian C] [EnoughInjectives C] (M : C) :
    ∃ (J : C) (f : M ⟶ J), Injective J ∧
      (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact := by
  let P : InjectivePresentation M := Classical.choice (EnoughInjectives.presentation M)
  have : Mono P.f := P.mono
  exact ⟨P.J, P.f, P.injective, ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel P.f))
    (by infer_instance) (by infer_instance)⟩

/-- A class in the middle term of `derivedDeltaShortComplex` lifts to the first term when the
middle object of the short exact sequence is injective. -/
private lemma exists_preimage_derivedDelta_of_injective
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [EnoughInjectives C] (F : C ⥤ AddCommGrpCat.{v}) [F.Additive]
    {S : ShortComplex C} (hS : S.ShortExact) [Injective S.X₂] (n : ℤ) (hn : n + 1 ≠ 0)
    (c : ↑(derivedDeltaShortComplex F hS n).X₂) :
    ∃ y, (derivedDeltaShortComplex F hS n).f.hom y = c := by
  have hJ : IsZero ((F.rightDerivedPlus (n + 1)).obj S.X₂) :=
    Functor.isZero_rightDerivedPlus_obj_injective F (n + 1) hn S.X₂
  exact exists_preimage_of_exact_addCommGrpCat (derivedDeltaShortComplex_exact F hS n) c
    (ConcreteCategory.congr_hom (hJ.eq_of_tgt (derivedDeltaShortComplex F hS n).g 0) c)

private lemma exists_annihilator_degree_one
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : Stacks.Chapter05.Tag_0BR1.IsProfiniteTop G)
    (M : ContinuousGModule.{u, max u v} G)
    (c : ↑(((continuousGModuleInvariants G).rightDerivedPlus (1 : ℤ)).obj M)) :
    ∃ n : ℕ, 0 < n ∧ (n : ℤ) • c = 0 := by
  let P₁ := ContAction.IsDiscrete (V := ModuleCat.{max u v} ℤ) (G := G)
  let P₂ := Action.IsContinuous (V := ModuleCat.{max u v} ℤ) (G := G)
  let F₁ := ObjectProperty.ι P₁
  let F₂ := ObjectProperty.ι P₂
  let : ∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F₁ :=
    fun f ↦ ObjectProperty.preservesKernels_ι P₁ f
  let : ∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F₂ :=
    fun f ↦ ObjectProperty.preservesKernels_ι P₂ f
  let : PreservesFiniteLimits F₁ := F₁.preservesFiniteLimits_of_preservesKernels
  let : PreservesFiniteLimits F₂ := F₂.preservesFiniteLimits_of_preservesKernels
  let F := continuousGModuleInvariants G
  let : PreservesFiniteLimits (Rep.ActionToRep ℤ G) := inferInstance
  let : PreservesFiniteLimits (Rep.invariantsFunctor ℤ G) := inferInstance
  let : PreservesFiniteLimits (forget₂ (ModuleCat.{max u v} ℤ) AddCommGrpCat) := inferInstance
  let : PreservesFiniteLimits (F₁ ⋙ F₂) :=
    Limits.comp_preservesFiniteLimits F₁ F₂
  let : PreservesFiniteLimits ((F₁ ⋙ F₂) ⋙ Rep.ActionToRep ℤ G) :=
    Limits.comp_preservesFiniteLimits (F₁ ⋙ F₂) (Rep.ActionToRep ℤ G)
  let : PreservesFiniteLimits
      (((F₁ ⋙ F₂) ⋙ Rep.ActionToRep ℤ G) ⋙ Rep.invariantsFunctor ℤ G) :=
    Limits.comp_preservesFiniteLimits
      ((F₁ ⋙ F₂) ⋙ Rep.ActionToRep ℤ G) (Rep.invariantsFunctor ℤ G)
  let : PreservesFiniteLimits F := by
    dsimp [F, continuousGModuleInvariants]
    exact Limits.comp_preservesFiniteLimits
      (((F₁ ⋙ F₂) ⋙ Rep.ActionToRep ℤ G) ⋙ Rep.invariantsFunctor ℤ G)
      (forget₂ (ModuleCat.{max u v} ℤ) AddCommGrpCat)
  obtain ⟨J, f, _, hS⟩ := exists_shortExact_injective_presentation M
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  let T := derivedDeltaShortComplex F hS 0
  obtain ⟨y, hy⟩ := exists_preimage_derivedDelta_of_injective F hS 0 (by norm_num) c
  let e := invariantsRightDerivedZeroIso F
  let y0 := (e.app S.X₃).inv.hom y
  let A : Action (ModuleCat.{max u v} ℤ) G := F₂.obj (F₁.obj S.X₂)
  let B : Action (ModuleCat.{max u v} ℤ) G := F₂.obj (F₁.obj S.X₃)
  let gA : A ⟶ B := F₂.map (F₁.map S.g)
  let RB := (Rep.ActionToRep ℤ G).obj B
  let RBInv := (Rep.invariantsFunctor ℤ G).obj RB
  change ↑RBInv at y0
  obtain ⟨x, hx⟩ := surjective_action_forget_map_of_epi S.g hS.epi_g y0.1
  have hx' : ConcreteCategory.hom gA.hom x = y0.1 := hx
  have hy0 : ∀ g : G,
      ConcreteCategory.hom (B.ρ g).asHom (ConcreteCategory.hom gA.hom x) =
        ConcreteCategory.hom gA.hom x := by
    intro g
    rw [hx']
    show (RB.ρ g) y0.1 = y0.1
    exact y0.2 g
  obtain ⟨n, hn, z, hz, hgz⟩ := exists_invariant_multiple_of_action_hom hG A B
    (F₁.obj S.X₂).property S.X₂.property gA x hy0
  let RA := (Rep.ActionToRep ℤ G).obj A
  let : Module ℤ (↑RA) := RA.hV2
  let z0 : ↑RA.ρ.invariants := ⟨z, hz⟩
  have hmap : (F.map S.g).hom z0 = (n : ℤ) • y0 := by
    apply Subtype.ext
    show ConcreteCategory.hom gA.hom z = (n : ℤ) • y0.1
    rw [hgz, hx']
    rfl
  have hcomp : F.map S.g ≫ (e.app S.X₃).hom ≫ T.f = 0 := by
    have hδR : (F.rightDerivedPlus (0 : ℤ)).map S.g ≫ T.f = 0 :=
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat 0).comp_homologySequenceδ
        (derivedSingleTriangle F hS) (derivedSingleTriangle_distinguished F hS) (0 : ℤ) (1 : ℤ) rfl
    have hnat : F.map S.g ≫ (e.app S.X₃).hom =
        (e.app S.X₂).hom ≫ (F.rightDerivedPlus (0 : ℤ)).map S.g := e.hom.naturality S.g
    calc F.map S.g ≫ (e.app S.X₃).hom ≫ T.f
      _ = (e.app S.X₂).hom ≫ (F.rightDerivedPlus (0 : ℤ)).map S.g ≫ T.f :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ T.f) hnat).trans (Category.assoc _ _ _))
      _ = 0 := by rw [hδR, comp_zero]
  have hm : T.f.hom ((e.app S.X₃).hom.hom ((F.map S.g).hom z0)) = 0 :=
    congrArg (fun f ↦ f.hom z0) hcomp
  have hy0e : (e.app S.X₃).hom.hom y0 = y := Iso.inv_hom_id_apply (e.app S.X₃) y
  rw [hmap, map_zsmul, hy0e] at hm
  refine ⟨n, hn, ?_⟩
  rw [← hy]
  exact (_root_.map_zsmul T.f.hom (n : ℤ) y).symm.trans hm

private lemma isTorsion_rightDerivedPlus_succ
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [EnoughInjectives C] (F : C ⥤ AddCommGrpCat.{v}) [F.Additive]
    (i : ℤ) (hi : i + 1 ≠ 0)
    (h : ∀ M, Module.IsTorsion ℤ ((F.rightDerivedPlus i).obj M))
    (M : C) : Module.IsTorsion ℤ ((F.rightDerivedPlus (i + 1)).obj M) := by
  obtain ⟨J, f, _, hS⟩ := exists_shortExact_injective_presentation M
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  let T := derivedDeltaShortComplex F hS i
  intro c
  obtain ⟨y, hy⟩ := exists_preimage_derivedDelta_of_injective F hS i hi c
  obtain ⟨a, ha⟩ := h S.X₃ (x := y)
  refine ⟨a, ?_⟩
  show (a : ℤ) • c = 0
  rw [← hy]
  exact (_root_.map_zsmul T.f.hom (a : ℤ) y).symm.trans
    ((congrArg T.f.hom ha).trans (map_zero T.f.hom))

private lemma isIso_zsmul_id_of_module_rat
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : ContinuousGModule.{u, max u v} G) [Module ℚ M.1.1.V]
    (n : ℤ) (hn : n ≠ 0) : IsIso (n • 𝟙 M) := by
  let P₁ := ContAction.IsDiscrete (V := ModuleCat.{max u v} ℤ) (G := G)
  let P₂ := Action.IsContinuous (V := ModuleCat.{max u v} ℤ) (G := G)
  let f₁ := (ObjectProperty.ι P₁).map (n • 𝟙 M)
  let f₂ := (ObjectProperty.ι P₂).map f₁
  have : IsIso f₂.hom := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    show Function.Bijective (fun x : M.1.1.V ↦ n • x)
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    simpa only [Int.cast_smul_eq_zsmul] using
      ((isUnit_iff_ne_zero.mpr hnq).smul_bijective (β := M.1.1.V))
  have : IsIso f₂ := Action.isIso_of_hom_isIso f₂
  have : IsIso f₁ := isIso_of_reflects_iso f₁ (ObjectProperty.ι P₂)
  exact (ObjectProperty.fullyFaithfulι P₁).isIso_of_isIso_map (n • 𝟙 M)

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private lemma isTorsion_rightDerivedPlus_nat
    (hG : Stacks.Chapter05.Tag_0BR1.IsProfiniteTop G) (i : ℕ) (hi : 0 < i)
    (M : ContinuousGModule.{u, max u v} G) :
    Module.IsTorsion ℤ
      (((continuousGModuleInvariants G).rightDerivedPlus (i : ℤ)).obj M) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  clear hi
  induction k generalizing M with
  | zero =>
      intro c
      obtain ⟨n, hn, hc⟩ := exists_annihilator_degree_one hG M c
      exact ⟨⟨(n : ℤ), mem_nonZeroDivisors_iff_ne_zero.mpr (by omega)⟩, hc⟩
  | succ k ih =>
      exact isTorsion_rightDerivedPlus_succ _ (↑(k + 1) : ℤ) (by omega) ih M

/-- Positive-degree continuous cohomology of a profinite group with discrete
coefficients is a torsion abelian group. -/
@[stacks 0DV3 "part (1)"]
public theorem continuousGroupCohomology_isTorsion
    (hG : Stacks.Chapter05.Tag_0BR1.IsProfiniteTop G) (i : ℕ) (hi : 0 < i)
    (M : ContinuousGModule.{u, max u v} G) :
    Module.IsTorsion ℤ (continuousGroupCohomology G i M) := by
  exact isTorsion_rightDerivedPlus_nat G hG i hi M

/-- Positive-degree continuous cohomology of a profinite group vanishes when
the discrete coefficient module is a rational vector space. -/
@[stacks 0DV3 "part (2)"]
public theorem isZero_continuousGroupCohomology_of_module_rat
    (hG : Stacks.Chapter05.Tag_0BR1.IsProfiniteTop G) (i : ℕ) (hi : 0 < i)
    (M : ContinuousGModule.{u, max u v} G) [Module ℚ M.1.1.V] :
    IsZero (continuousGroupCohomology G i M) := by
  let F := continuousGroupCohomologyFunctor G i
  have : F.Additive := by
    dsimp [F, continuousGroupCohomologyFunctor, Functor.rightDerivedPlus,
      DerivedCategory.Plus.homologyFunctor]
    infer_instance
  apply (IsZero.iff_id_eq_zero _).mpr
  ext x
  obtain ⟨n, hn⟩ := continuousGroupCohomology_isTorsion G hG i hi M (x := x)
  have : IsIso ((n : ℤ) • 𝟙 M) :=
    isIso_zsmul_id_of_module_rat M n (mem_nonZeroDivisors_iff_ne_zero.mp n.2)
  have : IsIso ((n : ℤ) • 𝟙 (F.obj M)) := by
    rw [← F.map_id, ← F.map_zsmul]
    infer_instance
  apply (AddCommGrpCat.mono_iff_injective ((n : ℤ) • 𝟙 (F.obj M))).mp
    (inferInstance : Mono ((n : ℤ) • 𝟙 (F.obj M)))
  show (n : ℤ) • x = (n : ℤ) • 0
  rwa [smul_zero]

