module

public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceProperIso
public import StacksFrontier.Homology.Devissage.HomBijectionDevissage
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQCohCoproducts
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.CompactPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.LocallySmall

/-!
# The sheafy trace of a proper morphism is an isomorphism on all of `D_QCoh`

Let `f : X ⟶ Y` be a proper morphism of Noetherian schemes, `a` the right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` and `K ∈ D^+_QCoh(𝒪_Y)`. The sheafy trace map
`Rf_*R𝓗om(L, a(K)) ⟶ R𝓗om(Rf_*L, K)` of [Stacks, Tag 0B6H] is an isomorphism for every
`L ∈ D_QCoh(𝒪_X)`, not only for `L ∈ D^-_Coh` ([Stacks, Tag 0GEW]); this is what the second
isomorphism of [Stacks, Tag 0B6X] asserts.

Precomposition with the trace map is identified, for every `M ∈ D(𝒪_Y)`, with the map
`ψ_L : Hom(Lf^*M ⊗ L, a K) ⟶ Hom(M ⊗ Rf_*L, K)`, `v ↦ π ≫ Rf_*v ≫ ε`, where `π` is the
projection-formula map and `ε` the counit; the trace map is invertible exactly when every `ψ`
is bijective. The family `ψ` is natural and additive in `L`, so the dévissage of
`StacksDraft.CompactDevissage.bijective_of_isCompactlyGenerated` along the compact generators of
`D_QCoh(𝒪_X)`, which are perfect ([Stacks, Tag 09M1]), reduces the statement to perfect `L`.

## Main results

* `Stacks.Duality.homEquiv_comp_sheafyTrace_eq` — the identification of precomposition with the
  trace map.
* `Stacks.Duality.isIso_sheafyTrace_iff_bijective` — the trace map is invertible exactly when
  every `ψ` is bijective.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
  Opposite TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces renaming derivedPullback → derivedPullbackRS,
  derivedAdjunction → derivedAdjunctionRS
open Stacks.Cohomology.DerivedRelativeCupProduct
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi
open Stacks.DerivedTensor.RingedSite

namespace Stacks.Duality

universe u

attribute [local instance 10000] HasDerivedCategory.standard

section General

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
  (adj : quasiCoherentDerivedPushforward f hpush ⊣ a)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (DX : TensorHomAdjunction (derivedTensorProductFunctor X.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom X.sheaf))
  (DY : TensorHomAdjunction (derivedTensorProductFunctor Y.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom Y.sheaf))

/-- The map `ψ_N : Hom(Lf^*M ⊗ N, a K) ⟶ Hom(M ⊗ Rf_*N, K)`, `v ↦ π ≫ Rf_*v ≫ ε`, for an object
`N` of `D(𝒪_X)`: the projection-formula map, then `Rf_*` of `v`, then the counit of `Rf_* ⊣ a`. -/
def traceHomMap (K : quasiCoherentDerivedCategory Y) (M : DerivedCategory Y.Modules)
    (N : DerivedCategory X.Modules)
    (v : ((derivedTensorProductFunctor X.sheaf).obj
      ((derivedPullbackRS f.toLRSHom.toShHom).obj M)).obj N ⟶
        (StacksDraft.DerivedModel.schemeModulesComparison X).inverse.obj (a.obj K).obj) :
    ((derivedTensorProductFunctor Y.sheaf).obj M).obj ((derivedPushforward f).obj N) ⟶
      (StacksDraft.DerivedModel.schemeModulesComparison Y).inverse.obj K.obj :=
  pullbackProjectionFormulaMap f M N ≫ (derivedPushforward f).map v ≫ (ι _).map (adj.counit.app K)

include DX in
/-- **Precomposition with the sheafy trace map, read through the adjunctions.** For `M` in
`D(𝒪_Y)` and `g : M ⟶ Rf_*R𝓗om(L, a K)`, the tensor–internal-Hom bijection on `Y` sends `g`
followed by the trace map to `traceHomMap` of the adjunct of `g`. -/
theorem homEquiv_comp_sheafyTrace_eq (L : quasiCoherentDerivedCategory X)
    (K : quasiCoherentDerivedCategory Y) (M : DerivedCategory Y.Modules)
    (g : M ⟶ (derivedPushforward f).obj
      (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj (a.obj K).obj)) :
    DY.homEquiv M ((derivedPushforward f).obj L.obj) K.obj
        (g ≫ sheafyTrace f DX DY hpush adj L K) =
      traceHomMap f hpush adj K M L.obj
        (DX.homEquiv ((derivedPullbackRS f.toLRSHom.toShHom).obj M) L.obj (a.obj K).obj
          (((derivedAdjunctionRS f.toLRSHom.toShHom).homEquiv M
            (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj
              (a.obj K).obj)).symm g)) := by
  set u := ((derivedAdjunctionRS f.toLRSHom.toShHom).homEquiv M
    (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj (a.obj K).obj)).symm g
  have hev : ((derivedTensorProductFunctor X.sheaf).map u).app L.obj ≫
      DX.evaluation L.obj (a.obj K).obj =
      DX.homEquiv ((derivedPullbackRS f.toLRSHom.toShHom).obj M) L.obj (a.obj K).obj u :=
    (DX.homEquiv_naturality_source u (𝟙 _)).symm.trans
      (congrArg (DX.homEquiv _ L.obj (a.obj K).obj) (Category.comp_id u))
  have hmap : (derivedPushforward f).map
        (((derivedTensorProductFunctor X.sheaf).map u).app L.obj) ≫
      (derivedPushforward f).map (DX.evaluation L.obj (a.obj K).obj) =
      (derivedPushforward f).map
        (DX.homEquiv ((derivedPullbackRS f.toLRSHom.toShHom).obj M) L.obj (a.obj K).obj u) :=
    ((derivedPushforward f).map_comp _ _).symm.trans
      (congrArg (fun z => (derivedPushforward f).map z) hev)
  refine Eq.trans (homEquiv_comp_sheafyTrace f hpush adj DX DY L K M g) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun t => t ≫ _) (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (congrArg (fun t => (t ≫ _) ≫ _)
    (pullbackProjectionFormulaMap_comp_adjunct f M L.obj g)) ?_
  refine Eq.trans (congrArg (fun t => t ≫ _) (Category.assoc _ _ _)) ?_
  refine Eq.trans (congrArg (fun t => (_ ≫ t) ≫ _) hmap) ?_
  exact Category.assoc _ _ _

include DX DY in
/-- **The sheafy trace map is invertible exactly when every `ψ` is bijective.** -/
theorem isIso_sheafyTrace_iff_bijective (L : quasiCoherentDerivedCategory X)
    (K : quasiCoherentDerivedCategory Y) :
    IsIso (sheafyTrace f DX DY hpush adj L K) ↔
      ∀ M : DerivedCategory Y.Modules, Function.Bijective (traceHomMap f hpush adj K M L.obj) := by
  refine (isIso_iff_yoneda_map_bijective (sheafyTrace f DX DY hpush adj L K)).trans
    (forall_congr' fun M => ?_)
  let e₁ := ((derivedAdjunctionRS f.toLRSHom.toShHom).homEquiv M
      (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj
        (a.obj K).obj)).symm.trans
    (DX.homEquiv ((derivedPullbackRS f.toLRSHom.toShHom).obj M) L.obj (a.obj K).obj)
  let e₂ := DY.homEquiv M ((derivedPushforward f).obj L.obj) K.obj
  have key : (fun g => g ≫ sheafyTrace f DX DY hpush adj L K) =
      e₂.symm ∘ traceHomMap f hpush adj K M L.obj ∘ e₁ := by
    funext g
    exact (Equiv.eq_symm_apply e₂).2 (homEquiv_comp_sheafyTrace_eq f hpush adj DX DY L K M g)
  rw [key]
  exact (Equiv.comp_bijective _ e₂.symm).trans (Equiv.bijective_comp e₁ _)

/-- The projection-formula map is natural in the object of `D(𝒪_X)`. -/
theorem pullbackProjectionFormulaMap_natural_right (M : DerivedCategory Y.Modules)
    {N N' : DerivedCategory X.Modules} (ℓ : N ⟶ N') :
    ((derivedTensorProductFunctor Y.sheaf).obj M).map ((derivedPushforward f).map ℓ) ≫
        pullbackProjectionFormulaMap f M N' =
      pullbackProjectionFormulaMap f M N ≫ (derivedPushforward f).map
        (((derivedTensorProductFunctor X.sheaf).obj
          ((derivedPullbackRS f.toLRSHom.toShHom).obj M)).map ℓ) := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun t => t ≫ relativeCupProduct f.toLRSHom.toShHom
      ((derivedPullbackRS f.toLRSHom.toShHom).obj M) N')
    (((derivedTensorProductFunctor Y.sheaf).map
      ((derivedAdjunctionRS f.toLRSHom.toShHom).unit.app M)).naturality
        ((derivedPushforward f).map ℓ))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun t => _ ≫ t)
    (relativeCupProduct_natural_right f.toLRSHom.toShHom
      ((derivedPullbackRS f.toLRSHom.toShHom).obj M) ℓ)) ?_
  exact (Category.assoc _ _ _).symm

/-- `ψ` is natural in the object of `D(𝒪_X)`. -/
theorem traceHomMap_natural (K : quasiCoherentDerivedCategory Y) (M : DerivedCategory Y.Modules)
    {N N' : DerivedCategory X.Modules} (ℓ : N ⟶ N')
    (v : ((derivedTensorProductFunctor X.sheaf).obj
      ((derivedPullbackRS f.toLRSHom.toShHom).obj M)).obj N' ⟶
        (StacksDraft.DerivedModel.schemeModulesComparison X).inverse.obj (a.obj K).obj) :
    traceHomMap f hpush adj K M N
        (((derivedTensorProductFunctor X.sheaf).obj
          ((derivedPullbackRS f.toLRSHom.toShHom).obj M)).map ℓ ≫ v) =
      ((derivedTensorProductFunctor Y.sheaf).obj M).map ((derivedPushforward f).map ℓ) ≫
        traceHomMap f hpush adj K M N' v := by
  unfold traceHomMap
  refine Eq.trans (congrArg (fun t => pullbackProjectionFormulaMap f M N ≫ t ≫ _)
    ((derivedPushforward f).map_comp _ _)) ?_
  refine Eq.trans (congrArg (fun t => pullbackProjectionFormulaMap f M N ≫ t)
    (Category.assoc _ _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun t => t ≫ _)
    (pullbackProjectionFormulaMap_natural_right f M ℓ).symm) ?_
  exact Category.assoc _ _ _

end General

/-! ### The comparison of models is exact -/

section Comparison

variable (Z : Scheme.{u})

/-- `Qh` of the locally small model followed by the comparison to the standard model is `Qh` of
the standard model. -/
instance comparisonInverseLifting :
    Localization.Lifting
      (@DerivedCategory.Qh Z.Modules _ _ (Scheme.Modules.hasDerivedCategory Z))
      (HomotopyCategory.subcategoryAcyclic Z.Modules).trW
      (@DerivedCategory.Qh Z.Modules _ _ (HasDerivedCategory.standard Z.Modules))
      (StacksDraft.DerivedModel.schemeModulesComparison Z).inverse :=
  ⟨Functor.isoWhiskerRight (StacksDraft.DerivedModel.shrinkComparisonQhIso Z.Modules) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (StacksDraft.DerivedModel.schemeModulesComparison Z).unitIso.symm ≪≫
    Functor.rightUnitor _⟩

/-- The comparison from the locally small model to the standard model commutes with shifts. -/
@[instance_reducible]
def comparisonInverseCommShift :
    (StacksDraft.DerivedModel.schemeModulesComparison Z).inverse.CommShift ℤ :=
  Functor.commShiftOfLocalization
    (@DerivedCategory.Qh Z.Modules _ _ (Scheme.Modules.hasDerivedCategory Z))
    (HomotopyCategory.subcategoryAcyclic Z.Modules).trW ℤ
    (@DerivedCategory.Qh Z.Modules _ _ (HasDerivedCategory.standard Z.Modules))
    (StacksDraft.DerivedModel.schemeModulesComparison Z).inverse

attribute [local instance] comparisonInverseCommShift

/-- Shifts on the derived category are additive, for any model of the derived category. -/
private theorem shiftFunctor_additive_derivedCategory {C : Type*} [Category C] [Abelian C]
    (h : HasDerivedCategory C) (n : ℤ) : (shiftFunctor (@DerivedCategory C _ _ h) n).Additive := by
  let := h
  infer_instance

/-- The comparison from the locally small model to the standard model is exact. -/
theorem comparisonInverse_isTriangulated :
    letI : ∀ n : ℤ, (shiftFunctor (@DerivedCategory Z.Modules _ _
        (Scheme.Modules.hasDerivedCategory Z)) n).Additive := by
      let := Scheme.Modules.hasDerivedCategory Z; infer_instance
    letI : ∀ n : ℤ, (shiftFunctor (@DerivedCategory Z.Modules _ _
        (HasDerivedCategory.standard Z.Modules)) n).Additive := by
      let := HasDerivedCategory.standard Z.Modules; infer_instance
    (StacksDraft.DerivedModel.schemeModulesComparison Z).inverse.IsTriangulated := by
  have := shiftFunctor_additive_derivedCategory (Scheme.Modules.hasDerivedCategory Z)
  have := shiftFunctor_additive_derivedCategory (HasDerivedCategory.standard Z.Modules)
  exact Functor.isTriangulated_of_precomp_iso
    (Localization.Lifting.iso
      (@DerivedCategory.Qh Z.Modules _ _ (Scheme.Modules.hasDerivedCategory Z))
      (HomotopyCategory.subcategoryAcyclic Z.Modules).trW
      (@DerivedCategory.Qh Z.Modules _ _ (HasDerivedCategory.standard Z.Modules))
      (StacksDraft.DerivedModel.schemeModulesComparison Z).inverse)

/-- The two comparisons of the standard model with the locally small one, the one that is the
identity on objects and the one of `StacksDraft.DerivedModel.modelEquiv`, are isomorphic: both
lift the localization functor of the locally small model. -/
def comparisonFunctorIsoModelEquiv :
    (StacksDraft.DerivedModel.schemeModulesComparison Z).functor ≅
      (StacksDraft.DerivedModel.modelEquiv (HasDerivedCategory.standard Z.Modules)
        (Scheme.Modules.hasDerivedCategory Z)).functor :=
  letI : Localization.Lifting (@DerivedCategory.Q Z.Modules _ _ (HasDerivedCategory.standard _))
      (HomologicalComplex.quasiIso Z.Modules (ComplexShape.up ℤ))
      (@DerivedCategory.Q Z.Modules _ _ (Scheme.Modules.hasDerivedCategory Z))
      (StacksDraft.DerivedModel.schemeModulesComparison Z).functor :=
    ⟨Iso.refl _⟩
  letI : Localization.Lifting (@DerivedCategory.Q Z.Modules _ _ (HasDerivedCategory.standard _))
      (HomologicalComplex.quasiIso Z.Modules (ComplexShape.up ℤ))
      (@DerivedCategory.Q Z.Modules _ _ (Scheme.Modules.hasDerivedCategory Z))
      (StacksDraft.DerivedModel.modelEquiv (HasDerivedCategory.standard Z.Modules)
        (Scheme.Modules.hasDerivedCategory Z)).functor :=
    ⟨StacksDraft.DerivedModel.modelCompQIso _ _⟩
  Localization.liftNatIso (@DerivedCategory.Q Z.Modules _ _ (HasDerivedCategory.standard _))
    (HomologicalComplex.quasiIso Z.Modules (ComplexShape.up ℤ))
    (@DerivedCategory.Q Z.Modules _ _ (Scheme.Modules.hasDerivedCategory Z))
    (@DerivedCategory.Q Z.Modules _ _ (Scheme.Modules.hasDerivedCategory Z)) _ _ (Iso.refl _)

end Comparison

/-- `p ≫ G(x + x') ≫ c = p ≫ G(x) ≫ c + p ≫ G(x') ≫ c` for an additive functor `G`. -/
theorem comp_map_add_comp {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {A B : C} {P Q : D} (G : C ⥤ D) [G.Additive] (p : P ⟶ G.obj A) (c : G.obj B ⟶ Q)
    (x x' : A ⟶ B) :
    p ≫ G.map (x + x') ≫ c = p ≫ G.map x ≫ c + p ≫ G.map x' ≫ c := by
  rw [G.map_add, Preadditive.add_comp, Preadditive.comp_add]

/-! ### The dévissage -/

section Devissage

attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective
attribute [local instance] comparisonInverseCommShift

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
  (adj : quasiCoherentDerivedPushforward f
    (StandardModel.isQuasicoherent_homology_derivedPushforward f) ⊣ a)

/-- The locally small model of `D_QCoh(𝒪_Z)`, at which direct sums exist and compact generation is
proved. -/
abbrev QCohLS (Z : Scheme.{u}) : Type (u + 1) :=
  @quasiCoherentDerivedCategory Z (Scheme.Modules.hasDerivedCategory Z)

/-- An object of the locally small model of `D_QCoh(𝒪_Z)`, read at the standard model. -/
def QCohLS.toStd {Z : Scheme.{u}} (L : QCohLS Z) : quasiCoherentDerivedCategory Z :=
  ⟨L.obj, fun i => (AlgebraicGeometry.PerfectApproximation.isQuasicoherent_homology_standard_iff
    L.obj i).2 (L.2 i)⟩

include adj in
/-- The sheafy trace map is invertible at every compact object of `D_QCoh(𝒪_X)`, for `f` proper
between Noetherian schemes and `K` bounded below: compact objects are pseudo-coherent. -/
theorem isIso_sheafyTrace_of_isCompactObject [IsProper f] [IsNoetherian X] [IsNoetherian Y]
    (L : QCohLS X) (hL : IsCompactObject.{u} L)
    (K : quasiCoherentDerivedCategory Y) (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    IsIso (sheafyTrace f
      (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite X.sheaf))
      (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite Y.sheaf))
      (StandardModel.isQuasicoherent_homology_derivedPushforward f) adj L.toStd K) := by
  have hLp : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) L.toStd.obj :=
    (AlgebraicGeometry.PerfectApproximation.isPseudoCoherent_standard_iff L.obj).2
      (isPseudoCoherent_of_isCompactObject (h := Scheme.Modules.hasDerivedCategory X) L hL)
  exact isIso_sheafyTrace_of_isPseudoCoherent f _ _ _ adj (Adjunction.ofIsLeftAdjoint _) _ K
    (isBoundedBelow_rightAdjoint_obj_of_adjunction f adj K)
    (isIso_coherator_map_sheafyTrace_of_adjunction f adj _ K) hK hLp
    (isPseudoCoherent_derivedPushforward_standard_of_isProper f _ hLp)

/-- `Rf_*` at the standard model, preceded by the comparison from the locally small model, carries
direct sums of objects with quasi-coherent cohomology to direct sums ([Stacks, Tag 08DZ]): followed
by the comparison back to the locally small model it is `Rf_*` there. -/
theorem preservesColimitsOfShape_comparison_derivedPushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y] (J : Type u) :
    PreservesColimitsOfShape (Discrete J)
      (ObjectProperty.ι (@DerivedCategoryB.derivedCategoryB X.Modules _ _
          (Scheme.Modules.hasDerivedCategory X) (SheafOfModules.isQuasicoherent X.ringCatSheaf)) ⋙
        (StacksDraft.DerivedModel.schemeModulesComparison X).inverse ⋙ derivedPushforward f) := by
  have := Stacks.Duality.DerivedPushforward.derivedQuasicoherent_isClosedUnderCoproducts X J
  have := Stacks.Duality.DerivedPushforward.derivedQuasicoherent_isClosedUnderCoproducts Y J
  let ιX := ObjectProperty.ι (@DerivedCategoryB.derivedCategoryB X.Modules _ _
    (Scheme.Modules.hasDerivedCategory X) (SheafOfModules.isQuasicoherent X.ringCatSheaf))
  let ιY := ObjectProperty.ι (@DerivedCategoryB.derivedCategoryB Y.Modules _ _
    (Scheme.Modules.hasDerivedCategory Y) (SheafOfModules.isQuasicoherent Y.ringCatSheaf))
  let gX := StacksDraft.DerivedModel.schemeModulesComparison X
  let gY := StacksDraft.DerivedModel.schemeModulesComparison Y
  let RLS := @derivedPushforward X Y f (Scheme.Modules.hasDerivedCategory X)
    (Scheme.Modules.hasDerivedCategory Y)
  have h₁ : PreservesColimitsOfShape (Discrete J) (ιX ⋙ RLS) :=
    inferInstanceAs (PreservesColimitsOfShape (Discrete J)
      (Stacks.Duality.DerivedPushforward.qcqsRestrictedDerivedPushforward f ⋙ ιY))
  let eR : derivedPushforward f ⋙ gY.functor ≅ gX.functor ⋙ RLS :=
    Functor.isoWhiskerLeft _ (comparisonFunctorIsoModelEquiv Y) ≪≫
      StandardModel.derivedPushforwardModelIso f ≪≫
      Functor.isoWhiskerRight (comparisonFunctorIsoModelEquiv X).symm _
  let e : (ιX ⋙ gX.inverse ⋙ derivedPushforward f) ⋙ gY.functor ≅ ιX ⋙ RLS :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft ιX (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft gX.inverse eR ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight gX.counitIso RLS ≪≫ Functor.leftUnitor _)
  have : PreservesColimitsOfShape (Discrete J)
      ((ιX ⋙ gX.inverse ⋙ derivedPushforward f) ⋙ gY.functor) :=
    preservesColimitsOfShape_of_natIso e.symm
  exact preservesColimitsOfShape_of_reflects_of_preserves _ gY.functor

include adj in
/-- **The dévissage.** For `f` proper between Noetherian schemes, `K ∈ D^+_QCoh(𝒪_Y)` and any
`M ∈ D(𝒪_Y)`, the map `ψ` is bijective at every object of `D_QCoh(𝒪_X)`. -/
theorem bijective_traceHomMap_of_isProper [IsProper f] [IsNoetherian X] [IsNoetherian Y]
    (K : quasiCoherentDerivedCategory Y) (hK : DerivedCategoryB.IsBoundedBelow K.obj)
    (M : DerivedCategory Y.Modules) (L : QCohLS X) :
    Function.Bijective (traceHomMap f (StandardModel.isQuasicoherent_homology_derivedPushforward f)
      adj K M L.obj) := by
  obtain ⟨ι', Gen, hGc, hG⟩ := QcqsGeneration.isCompactlyGenerated_quasiCoherentDerivedCategory X
  have := Stacks.Duality.DerivedPushforward.hasCoproducts_quasiCoherentDerivedCategory X
  have := shiftFunctor_additive_derivedCategory (Scheme.Modules.hasDerivedCategory X)
  have : ∀ n : ℤ, (shiftFunctor (QCohLS X) n).Additive := by
    let := Scheme.Modules.hasDerivedCategory X
    infer_instance
  have : (@DerivedCategoryB.derivedCategoryB X.Modules _ _ (Scheme.Modules.hasDerivedCategory X)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).IsTriangulated := by
    let := Scheme.Modules.hasDerivedCategory X
    exact DerivedCategoryB.derivedCategoryB_isTriangulated _
      (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X)
  have : ObjectProperty.IsTriangulated (IsCompactObject.{u, _, _} (C := QCohLS X)) :=
    (isClosedUnderIsomorphisms_isTriangulated_isSaturated_and_isIdempotentComplete_isCompactObject
      (D := QCohLS X)).2.1
  let TX : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _) ⥤
      DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules X.sheaf) :=
    (derivedTensorProductFunctor X.sheaf).obj ((derivedPullbackRS f.toLRSHom.toShHom).obj M)
  let TY : @DerivedCategory Y.Modules _ _ (HasDerivedCategory.standard _) ⥤
      DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules Y.sheaf) :=
    (derivedTensorProductFunctor Y.sheaf).obj M
  let : TX.CommShift ℤ := (canonicalDerivedTensorProduct X.sheaf).commShift_right _
  have : TX.IsTriangulated := (canonicalDerivedTensorProduct X.sheaf).exact_right _
  let : TY.CommShift ℤ := (canonicalDerivedTensorProduct Y.sheaf).commShift_right _
  have : TY.IsTriangulated := (canonicalDerivedTensorProduct Y.sheaf).exact_right _
  let : (derivedPushforward f).CommShift ℤ :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift
      f.toLRSHom.toShHom
  have : (derivedPushforward f).IsTriangulated :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward_isTriangulated
      f.toLRSHom.toShHom
  have := comparisonInverse_isTriangulated X
  let ιX := ObjectProperty.ι (@DerivedCategoryB.derivedCategoryB X.Modules _ _
    (Scheme.Modules.hasDerivedCategory X) (SheafOfModules.isQuasicoherent X.ringCatSheaf))
  let G := (StacksDraft.DerivedModel.schemeModulesComparison X).inverse
  let hιs : ιX.CommShift ℤ := by
    let := Scheme.Modules.hasDerivedCategory X
    infer_instance
  have hιt : ιX.IsTriangulated := by
    let := Scheme.Modules.hasDerivedCategory X
    infer_instance
  let hGTX : (G ⋙ TX).CommShift ℤ := Functor.CommShift.comp G TX
  let hE : (ιX ⋙ G ⋙ TX).CommShift ℤ := Functor.CommShift.comp ιX (G ⋙ TX)
  let hGR : (G ⋙ derivedPushforward f).CommShift ℤ := Functor.CommShift.comp G _
  let hιGR : (ιX ⋙ G ⋙ derivedPushforward f).CommShift ℤ := Functor.CommShift.comp ιX _
  let hF : ((ιX ⋙ G ⋙ derivedPushforward f) ⋙ TY).CommShift ℤ := Functor.CommShift.comp _ TY
  let E : QCohLS X ⥤ _ := ιX ⋙ G ⋙ TX
  let F : QCohLS X ⥤ _ := (ιX ⋙ G ⋙ derivedPushforward f) ⋙ TY
  have hEc : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) E := fun J => by
    have := Stacks.Duality.DerivedPushforward.derivedQuasicoherent_isClosedUnderCoproducts X J
    have : PreservesColimitsOfShape (Discrete J) TX :=
      Stacks.Cohomology.ProjectionFormulaQCohCoproducts.preservesColimitsOfShape_derivedTensor_obj
        X.toRingedSpace J ((derivedPullbackRS f.toLRSHom.toShHom).obj M)
    have h₁ : PreservesColimitsOfShape (Discrete J) ιX := by
      let := Scheme.Modules.hasDerivedCategory X
      infer_instance
    exact Limits.comp_preservesColimitsOfShape ιX (G ⋙ TX)
  have hFc : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) F := fun J => by
    have := preservesColimitsOfShape_comparison_derivedPushforward f J
    have : PreservesColimitsOfShape (Discrete J) TY :=
      Stacks.Cohomology.ProjectionFormulaQCohCoproducts.preservesColimitsOfShape_derivedTensor_obj
        Y.toRingedSpace J M
    exact Limits.comp_preservesColimitsOfShape (ιX ⋙ G ⋙ derivedPushforward f) TY
  refine StacksDraft.CompactDevissage.bijective_of_isCompactlyGenerated E F
    (fun L x => traceHomMap f (StandardModel.isQuasicoherent_homology_derivedPushforward f) adj
      K M L.obj x)
    (fun ℓ x => traceHomMap_natural f _ adj K M (G.map (ιX.map ℓ)) x)
    (fun L x x' => comp_map_add_comp (derivedPushforward f) _ _ x x')
    Gen hGc hG (fun i n => ?_) L
  exact (isIso_sheafyTrace_iff_bijective f _ adj _ _ (QCohLS.toStd ((Gen i)⟦n⟧)) K).1
    (isIso_sheafyTrace_of_isCompactObject f adj _
      (ObjectProperty.le_shift (IsCompactObject.{u, _, _} (C := QCohLS X)) n _ (hGc i)) K hK) M

include adj in
/-- **The sheafy trace map of a proper morphism is an isomorphism on all of `D_QCoh`.** Let
`f : X ⟶ Y` be a proper morphism of Noetherian schemes, `a` any right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, `L ∈ D_QCoh(𝒪_X)` and `K ∈ D^+_QCoh(𝒪_Y)`. Then the map
`Rf_*R𝓗om(L, a(K)) ⟶ R𝓗om(Rf_*L, K)` of [Stacks, Tag 0B6H] is an isomorphism. -/
theorem isIso_sheafyTrace_of_isProper_of_isBoundedBelow [IsProper f] [IsNoetherian X]
    [IsNoetherian Y] (L : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y)
    (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    IsIso (sheafyTrace f
      (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite X.sheaf))
      (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite Y.sheaf))
      (StandardModel.isQuasicoherent_homology_derivedPushforward f) adj L K) :=
  (isIso_sheafyTrace_iff_bijective f _ adj _ _ L K).2 fun M =>
    bijective_traceHomMap_of_isProper f adj K hK M
      ⟨L.obj, fun i => (AlgebraicGeometry.PerfectApproximation.isQuasicoherent_homology_standard_iff
        L.obj i).1 (L.2 i)⟩

end Devissage

end Stacks.Duality
