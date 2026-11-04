module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.TFAE
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Purity
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentIffFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.Topology.Sheaves.Modules.Coherent
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
import StacksFrontier.AlgebraicGeometry.FlatBaseChange.Descent
import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.StructureSheafCoherent

/-! # Stacks Tag 01XZ
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.FlatBaseChange (overPost_isContinuous_of_equivalence)

universe u

namespace StacksDraft.AlgebraicGeometry.CoherenceCriteria.FiniteTildeTFAE

/-- Pushforward along the slice functor `Over.post G ⋙ Over.map f` preserves colimits. -/
private theorem preservesColimits_pushforward_slice
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X, HasSheafify (K.over X) AddCommGrpCat.{u}]
    [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)
    (hφ : IsIso φ)
    [G.IsLeftAdjoint]
    [∀ X, (Over.post (X := X) G).IsContinuous (K.over X) (J.over (G.obj X))]
    [HasPullbacks C] [HasPullbacks D]
    (X : D) (Y : C) (f : G.obj X ⟶ Y) :
    PreservesColimitsOfSize.{u, u} <|
      SheafOfModules.pushforward.{u} (R := R.over Y)
        (F := Over.post (X := X) G ⋙ Over.map f)
        (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ) := by
  let G' := Over.post (X := X) G ⋙ Over.map f
  have : G'.IsContinuous (K.over X) (J.over Y) :=
    Functor.isContinuous_comp _ _ _ (J.over _) _
  have : G'.IsCocontinuous (K.over X) (J.over Y) :=
    isCocontinuous_comp _ _ _ (J.over _)
  let a : S.over X ⟶
      (G'.sheafPushforwardContinuous RingCat.{u} (K.over X) (J.over Y)).obj (R.over Y) :=
    ((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ
  have : IsIso a :=
    inferInstanceAs (IsIso
      (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ))
  have : (SheafOfModules.pushforward.{u} a).IsLeftAdjoint :=
    SheafOfModules.isLeftAdjoint_pushforward_of_isIso a
  exact inferInstanceAs (PreservesColimitsOfSize.{u, u} (SheafOfModules.pushforward.{u} a))

private theorem finiteType_pushforward
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X, HasSheafify (K.over X) AddCommGrpCat.{u}]
    [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)
    (η : (SheafOfModules.pushforward φ).obj (SheafOfModules.unit R) ≅
      SheafOfModules.unit S)
    (hφ : IsIso φ)
    [G.IsLeftAdjoint]
    [∀ X, (Over.post (X := X) G).IsContinuous (K.over X) (J.over (G.obj X))]
    [HasPullbacks C] [HasPullbacks D]
    (M : SheafOfModules.{u} R) (hM : M.IsFiniteType) :
    ((SheafOfModules.pushforward φ).obj M).IsFiniteType := by
  obtain ⟨P, hP⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  let Q : ((SheafOfModules.pushforward φ).obj M).LocalGeneratorsData := {
    I := Σ (X : D) (i : P.I), G.obj X ⟶ P.X i
    X i := i.1
    coversTop Y := by
      refine K.superset_covering ?_ (G.cover_lift K _ (P.coversTop (G.obj Y)))
      intro Z g ⟨i, ⟨v⟩⟩
      exact ⟨⟨Z, i, v⟩, ⟨𝟙 _⟩⟩
    generators i := by
      let G' := Over.post (X := i.1) G ⋙ Over.map i.2.2
      have : G'.IsContinuous (K.over i.1) (J.over (P.X i.2.1)) :=
        Functor.isContinuous_comp _ _ _ (J.over _) _
      have : G'.IsCocontinuous (K.over i.1) (J.over (P.X i.2.1)) :=
        isCocontinuous_comp _ _ _ (J.over _)
      let ψ : S.over i.1 ⟶ (G'.sheafPushforwardContinuous RingCat.{u}
          (K.over i.1) (J.over (P.X i.2.1))).obj (R.over (P.X i.2.1)) :=
        ((Over.forget i.1).sheafPushforwardContinuous RingCat.{u} (K.over i.1) K).map φ
      have := preservesColimits_pushforward_slice G φ hφ i.1 (P.X i.2.1) i.2.2
      let overS : SheafOfModules.{u} S ⥤ SheafOfModules.{u} (S.over i.1) :=
        SheafOfModules.pushforward (𝟙 _)
      let e : (SheafOfModules.pushforward ψ).obj (SheafOfModules.unit (R.over (P.X i.2.1))) ≅
          SheafOfModules.unit (S.over i.1) := overS.mapIso η
      exact (P.generators i.2.1).map (SheafOfModules.pushforward ψ) e.symm }
  refine SheafOfModules.IsFiniteType.mk.{u, u, u} ⟨Q, ?_⟩
  constructor
  intro i
  constructor
  exact (hP.isFiniteType i.2.1).finite

private theorem finitePresentation_pushforward
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X, HasSheafify (K.over X) AddCommGrpCat.{u}]
    [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)
    (η : (SheafOfModules.pushforward φ).obj (SheafOfModules.unit R) ≅
      SheafOfModules.unit S)
    (hφ : IsIso φ)
    [G.IsLeftAdjoint]
    [∀ X, (Over.post (X := X) G).IsContinuous (K.over X) (J.over (G.obj X))]
    [HasPullbacks C] [HasPullbacks D]
    (M : SheafOfModules.{u} R) (hM : M.IsFinitePresentation) :
    ((SheafOfModules.pushforward φ).obj M).IsFinitePresentation := by
  obtain ⟨P, hP⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  have h := preservesColimits_pushforward_slice G φ hφ
  refine SheafOfModules.IsFinitePresentation.mk.{u, u, u}
    ⟨P.pushforward G φ η h, ⟨fun i => ?_⟩⟩
  have := hP.isFinite_presentation i.2.1
  -- `Presentation.map` carries its sheafification instances as arguments, and they are the ones
  -- the transported presentation in the goal was built with.  Applying the transport lemma with
  -- every such argument left to unification reads them off the goal, instead of re-synthesizing
  -- them for the slice site `K.over i.1`; only the colimit-preservation witness is supplied.
  dsimp [SheafOfModules.QuasicoherentData.pushforward]
  exact @_root_.Presentation.IsFinite.map _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (h i.1 (P.X i.2.1) i.2.2) _ _

private noncomputable def bindLocalGeneratorsData {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
    [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} R} {I : Type u} (Xc : I → C)
    (hX : J.CoversTop Xc)
    (D : ∀ i, (M.over (Xc i)).LocalGeneratorsData.{u, u, u, u}) :
    M.LocalGeneratorsData.{u, u, u, u} where
  I := Σ i, (D i).I
  X ij := ((D ij.1).X ij.2).left
  coversTop := hX.over (fun i => (D i).coversTop)
  generators ij := by
    letI e := SheafOfModules.pushforwardPushforwardEquivalence
      (Over.iteratedSliceEquiv ((D ij.1).X ij.2))
      (S := (R.over (Xc ij.1)).over ((D ij.1).X ij.2))
      (R := R.over ((D ij.1).X ij.2).left) (𝟙 _) (𝟙 _)
      (by ext : 2; exact R.1.map_id _)
      (by ext : 2; exact R.1.map_id _)
    have : e.inverse.IsEquivalence := e.isEquivalence_inverse
    have : PreservesColimitsOfSize.{u, u} e.inverse := inferInstance
    let g : (e.inverse.obj ((M.over (Xc ij.1)).over ((D ij.1).X ij.2))).GeneratingSections :=
      SheafOfModules.GeneratingSections.map
        (R := (R.over (Xc ij.1)).over ((D ij.1).X ij.2))
        (S := R.over ((D ij.1).X ij.2).left)
        ((D ij.1).generators ij.2) e.inverse (Iso.refl _)
    let a := e.unitIso.app (M.over ((D ij.1).X ij.2).left)
    exact (SheafOfModules.GeneratingSections.equivOfIso
      (R := R.over ((D ij.1).X ij.2).left) a.symm) g

private theorem bindLocalGeneratorsData_isFiniteType {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
    [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} R} {I : Type u} (Xc : I → C)
    (hX : J.CoversTop Xc)
    (D : ∀ i, (M.over (Xc i)).LocalGeneratorsData.{u, u, u, u})
    (hD : ∀ i, (D i).IsFiniteType) :
    (bindLocalGeneratorsData (M := M) Xc hX D).IsFiniteType := by
  constructor
  intro ij
  constructor
  change Finite ((D ij.1).generators ij.2).I
  exact ((hD ij.1).isFiniteType ij.2).finite

private theorem finiteType_of_iso {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} R} (e : M ≅ N) (hM : M.IsFiniteType) : N.IsFiniteType := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  let q' : N.LocalGeneratorsData := {
    I := q.I
    X := q.X
    coversTop := q.coversTop
    generators := fun i => (q.generators i).ofEpi (e.hom.over (q.X i)) }
  exact SheafOfModules.IsFiniteType.mk.{u, u, u} ⟨q', ⟨fun i => ⟨(hq.isFiniteType i).finite⟩⟩⟩

private theorem finiteType_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) [M.IsFiniteType] :
    (M.restrict f).IsFiniteType := by
  have h : ((Scheme.Modules.pullback f).obj M).IsFiniteType :=
    AlgebraicGeometry.SheafOfModules.pullback_isFiniteType f.toLRSHom.toShHom M
  exact finiteType_of_iso.{u} ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm h

private alias finitePresentation_restrict :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isFinitePresentation_restrict

private alias finiteType_overEquiv_inverse :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_overEquiv_inverse

private theorem finitePresentation_overEquiv_inverse {X : Scheme.{u}} (U : X.Opens)
    (M : U.toScheme.Modules) [M.IsFinitePresentation] :
    ((Scheme.Modules.overEquiv U).inverse.obj M).IsFinitePresentation := by
  have := overPost_isContinuous_of_equivalence (J := (Opens.grothendieckTopology X).over U)
    (K := Opens.grothendieckTopology (↥(U : Opens X))) U.overEquivalence
  exact finitePresentation_pushforward U.overEquivalence.functor
    (U.sheafRestrictSheafEquivOver.app X.ringCatSheaf).inv
    (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf)
    (Iso.isIso_inv (U.sheafRestrictSheafEquivOver.app X.ringCatSheaf)) M
    ‹M.IsFinitePresentation›

private alias finiteType_of_cover :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_cover

private theorem finitePresentation_of_cover {X : Scheme.{u}} (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U)
    (hM : ∀ i, (M.restrict (U i).ι).IsFinitePresentation) : M.IsFinitePresentation := by
  have hlocal (i : ι) : (M.over (U i)).IsFinitePresentation := by
    have := hM i
    have := finitePresentation_overEquiv_inverse (U i) (M.restrict (U i).ι)
    exact (SheafOfModules.isFinitePresentation.{u, u, u} _).prop_of_iso
      (((Scheme.Modules.overEquiv (U i)).inverse.mapIso
        ((Scheme.Modules.overFunctorEquiv (U i)).app M).symm) ≪≫
        ((Scheme.Modules.overEquiv (U i)).unitIso.app (M.over (U i))).symm) this
  choose D hD using fun i ↦ (hlocal i).exists_quasicoherentData
  exact SheafOfModules.IsFinitePresentation.mk.{u, u, u}
    ⟨SheafOfModules.QuasicoherentData.bind M U ((Opens.coversTop_iff X U).2 hU) D,
    bind_isFinitePresentation M U ((Opens.coversTop_iff X U).2 hU) D⟩

private theorem kernel_toUnit_tilde_finiteModule (R : CommRingCat.{u})
    [IsNoetherianRing R] {I : Type u} [Finite I]
    (φ : (SheafOfModules.free.{u} (R := (Spec R).ringCatSheaf) I) ⟶
      SheafOfModules.unit.{u} (Spec R).ringCatSheaf) :
    ∃ M : ModuleCat.{u} R, Module.Finite R M ∧
      Nonempty (AlgebraicGeometry.tilde M ≅ kernel φ) := by
  classical
  let eF := AlgebraicGeometry.tildeFinsupp (R := R) I
  let eO := AlgebraicGeometry.tildeSelf (R := R)
  let ψ : AlgebraicGeometry.tilde (ModuleCat.of R (I →₀ R)) ⟶
      AlgebraicGeometry.tilde (ModuleCat.of R R) := eF.hom ≫ φ ≫ eO.inv
  let g : ModuleCat.of R (I →₀ R) ⟶ ModuleCat.of R R :=
    (AlgebraicGeometry.tilde.functor R).preimage ψ
  have hψ : (AlgebraicGeometry.tilde.functor R).map g = ψ :=
    (AlgebraicGeometry.tilde.functor R).map_preimage ψ
  let e₁ := kernel.mapIso φ ψ eF.symm eO.symm (by
    change φ ≫ eO.inv = eF.inv ≫ (eF.hom ≫ (φ ≫ eO.inv))
    exact (Iso.inv_hom_id_assoc eF (φ ≫ eO.inv)).symm)
  let e₂ : AlgebraicGeometry.tilde (ModuleCat.of R (LinearMap.ker g.hom)) ≅ kernel ψ :=
    ((AlgebraicGeometry.tilde.functor R).mapIso (ModuleCat.kernelIsoKer g)).symm ≪≫
      PreservesKernel.iso (AlgebraicGeometry.tilde.functor R) g ≪≫
        kernel.mapIso ((AlgebraicGeometry.tilde.functor R).map g) ψ
          (Iso.refl _) (Iso.refl _) hψ
  have hker : Module.Finite R (LinearMap.ker g.hom) := by
    have : Module.Finite R (I →₀ R) := by infer_instance
    infer_instance
  exact ⟨ModuleCat.of R (LinearMap.ker g.hom), hker, ⟨e₂ ≪≫ e₁.symm⟩⟩

private theorem kernel_toUnit_finiteType_spec (R : CommRingCat.{u})
    [IsNoetherianRing R] {I : Type u} [Finite I]
    (φ : (SheafOfModules.free.{u} (R := (Spec R).ringCatSheaf) I) ⟶
      SheafOfModules.unit.{u} (Spec R).ringCatSheaf) : (kernel φ).IsFiniteType := by
  obtain ⟨M, hM, ⟨e⟩⟩ := kernel_toUnit_tilde_finiteModule R φ
  exact finiteType_of_iso.{u} e ((AlgebraicGeometry.tilde_isFiniteType_iff M).2 hM)

private alias schemeRestrict_preservesFiniteLimits :=
    Stacks.AlgebraicGeometry.CoherentTFAE.preservesFiniteLimits_restrictFunctor

private alias schemeRestrict_preservesColimits :=
    Stacks.AlgebraicGeometry.CoherentTFAE.preservesColimits_restrictFunctor

private alias schemeRestrict_preservesZeroMorphisms :=
    Stacks.AlgebraicGeometry.CoherentTFAE.preservesZeroMorphisms_restrictFunctor

private noncomputable def kernelFreeUnitIso
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    [PreservesColimitsOfSize.{u, u} F] [PreservesFiniteLimits F]
    [F.PreservesZeroMorphisms]
    (η : F.obj (SheafOfModules.unit R) ≅ SheafOfModules.unit S)
    {I : Type u} (φ : SheafOfModules.free I ⟶ SheafOfModules.unit R) :
    F.obj (kernel φ) ≅ kernel
      ((SheafOfModules.mapFreeIso F I η.symm).hom ≫ F.map φ ≫ η.hom) :=
  PreservesKernel.iso F φ ≪≫ kernel.mapIso _ _
    (SheafOfModules.mapFreeIso F I η.symm).symm η (by simp)

/-- If kernels of maps `free I ⟶ unit` are of finite type on `Y`, then the restriction along an
open immersion `f : Y ⟶ X` of the kernel of such a map on `X` is of finite type. -/
private theorem restrict_kernel_finiteType {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    {I : Type u} [Finite I] (φ : SheafOfModules.free (R := X.ringCatSheaf) I ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (h : ∀ ψ : SheafOfModules.free (R := Y.ringCatSheaf) I ⟶ SheafOfModules.unit Y.ringCatSheaf,
      (kernel ψ).IsFiniteType) :
    ((Scheme.Modules.restrictFunctor f).obj (kernel φ)).IsFiniteType := by
  -- Name the functor at the site-level type `mapFreeIso` expects, so that the
  -- `PreservesColimitsOfShape (Discrete I)` instance below is found at that spelling.
  let F : SheafOfModules.{u} X.ringCatSheaf ⥤ SheafOfModules.{u} Y.ringCatSheaf :=
    Scheme.Modules.restrictFunctor f
  have hFcolimits : PreservesColimitsOfSize.{u, u} F := schemeRestrict_preservesColimits f
  have hFlimits : PreservesFiniteLimits F := schemeRestrict_preservesFiniteLimits f
  have : F.PreservesZeroMorphisms := schemeRestrict_preservesZeroMorphisms f
  let η := Scheme.Modules.restrictUnitIso f
  exact finiteType_of_iso.{u} (kernelFreeUnitIso.{u} F η φ).symm (h _)

private theorem kernel_toUnit_finiteType_affine (Y : Scheme.{u}) [IsAffine Y]
    [IsLocallyNoetherian Y] {I : Type u} [Finite I]
    (φ : SheafOfModules.free (R := Y.ringCatSheaf) I ⟶
      SheafOfModules.unit Y.ringCatSheaf) : (kernel φ).IsFiniteType := by
  let R : CommRingCat := CommRingCat.of Γ(Y, ⊤)
  let e : Y ≅ Spec R := Y.isoSpec
  have : IsNoetherianRing R :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  have := restrict_kernel_finiteType e.inv φ (kernel_toUnit_finiteType_spec R)
  exact finiteType_of_iso.{u}
    (((Scheme.Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.hom_inv_id ≪≫
      Scheme.Modules.restrictFunctorId).app (kernel φ))
    (finiteType_restrict e.hom _)

private theorem kernel_toUnit_finiteType (X : Scheme.{u}) [IsLocallyNoetherian X]
    {I : Type u} [Finite I]
    (φ : SheafOfModules.free (R := X.ringCatSheaf) I ⟶
      SheafOfModules.unit X.ringCatSheaf) : (kernel φ).IsFiniteType := by
  obtain ⟨S, hS, hcov⟩ := Opens.isBasis_iff_cover.mp X.isBasis_affineOpens ⊤
  let U : S → X.Opens := fun i ↦ i.1
  have cov : IsOpenCover U := (sSup_eq_iSup' S).symm.trans hcov.symm
  apply finiteType_of_cover (kernel φ) U cov
  intro i
  have : IsAffine (U i).toScheme := hS i.2
  exact restrict_kernel_finiteType (U i).ι φ (kernel_toUnit_finiteType_affine (U i).toScheme)

private alias unit_isCoherent := Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit

/-- A sheaf is the sheaf associated to a finite module on an affine open. -/
def IsFiniteTildeOn {X : Scheme.{u}} (F : X.Modules)
    (U : X.Opens) (hU : IsAffineOpen U) : Prop :=
  ∃ M : ModuleCat.{u} (CommRingCat.of Γ(X, U)),
    Module.Finite Γ(X, U) M ∧
      Nonempty (F.restrict U.ι ≅
        (Scheme.Modules.pullback hU.isoSpec.hom).obj (tilde M))

/-- **Stacks Project, Tag 01XZ.** The five characterizations of a coherent module
on a locally Noetherian scheme. -/
theorem coherent_tfae (X : Scheme.{u}) [IsLocallyNoetherian X]
    (F : X.Modules) :
    List.TFAE [
      F.IsCoherent,
      F.IsQuasicoherent ∧ F.IsFiniteType,
      F.IsFinitePresentation,
      ∀ (U : X.Opens) (hU : IsAffineOpen U), IsFiniteTildeOn F U hU,
      ∃ (ι : Type u) (U : ι → X.Opens),
        IsOpenCover U ∧ ∀ i, ∃ hU : IsAffineOpen (U i), IsFiniteTildeOn F (U i) hU
    ] := by
  classical
  tfae_have 1 → 3 := fun _ ↦ isFinitePresentation_of_isCoherent F
  tfae_have 3 → 2 := fun _ ↦ ⟨SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F,
    SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F⟩
  tfae_have 2 → 4 := by
    rintro ⟨hqc, hft⟩ U hU
    let e := hU.isoSpec
    have : (F.restrict U.ι).IsFiniteType := finiteType_restrict U.ι F
    let G := (F.restrict U.ι).restrict e.inv
    have : G.IsQuasicoherent := inferInstance
    have : G.IsFiniteType := finiteType_restrict e.inv _
    let M := moduleSpecΓFunctor.obj G
    refine ⟨M, (AlgebraicGeometry.tilde_isFiniteType_iff M).mp
      (finiteType_of_iso.{u} (asIso G.fromTildeΓ).symm inferInstance), ⟨?_⟩⟩
    exact (((Scheme.Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.hom_inv_id ≪≫
      Scheme.Modules.restrictFunctorId).app (F.restrict U.ι)).symm ≪≫
      (Scheme.Modules.restrictFunctor e.hom).mapIso (asIso G.fromTildeΓ).symm ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback e.hom).app (tilde M)
  tfae_have 4 → 5 := by
    intro h
    obtain ⟨S, hS, hcov⟩ := Opens.isBasis_iff_cover.mp X.isBasis_affineOpens ⊤
    exact ⟨S, fun i ↦ i.1, (sSup_eq_iSup' S).symm.trans hcov.symm,
      fun i ↦ ⟨hS i.2, h i.1 (hS i.2)⟩⟩
  tfae_have 5 → 3 := by
    rintro ⟨ι, U, hcov, h⟩
    apply finitePresentation_of_cover F U hcov
    intro i
    obtain ⟨hU, M, hM, ⟨e⟩⟩ := h i
    have : IsNoetherianRing Γ(X, U i) :=
      IsLocallyNoetherian.component_noetherian ⟨U i, hU⟩
    have : Module.FinitePresentation Γ(X, U i) M :=
      Module.finitePresentation_of_finite Γ(X, U i) M
    have : (tilde M).IsFinitePresentation :=
      (AlgebraicGeometry.tilde_isFinitePresentation_iff M).mpr this
    have := finitePresentation_restrict hU.isoSpec.hom (tilde M)
    exact (SheafOfModules.isFinitePresentation.{u, u, u} _).prop_of_iso
      (((Scheme.Modules.restrictFunctorIsoPullback hU.isoSpec.hom).app (tilde M)) ≪≫
        e.symm) this
  tfae_have 3 → 1 := by
    intro h
    have hu := unit_isCoherent X
    have : Stacks.SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf) :=
      ⟨hu.isFiniteType, hu.kernel_isFiniteType⟩
    have hc := (Stacks.SheafOfModules.isCoherent_iff_isFinitePresentation
      X.ringCatSheaf F).mpr h
    exact ⟨hc.isFiniteType, hc.kernel_isFiniteType⟩
  tfae_finish

/-- On a locally Noetherian scheme the structure sheaf is coherent. -/
@[instance]
alias structureSheaf_isCoherent := Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit

/-- A finite locally free module on a locally Noetherian scheme is coherent. -/
@[instance]
theorem isCoherent_of_isFiniteLocallyFree (X : Scheme.{u}) [IsLocallyNoetherian X]
    (F : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
      (C := Opens X) (J := Opens.grothendieckTopology X) F] :
    F.IsCoherent := by
  obtain ⟨q, hlocal, hfinite⟩ :=
    (inferInstance : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
      (C := Opens X) (J := Opens.grothendieckTopology X) F).exists_isFiniteLocallyFreeData
  have hcoh : (F.IsQuasicoherent ∧ F.IsFiniteType) ↔ F.IsCoherent :=
    (coherent_tfae X F).out 2 1
  exact hcoh.mp
    ⟨q.quasiCoherentData.isQuasicoherent, SheafOfModules.IsFiniteType.mk.{u, u, u} ⟨q, hfinite⟩⟩

end StacksDraft.AlgebraicGeometry.CoherenceCriteria.FiniteTildeTFAE
