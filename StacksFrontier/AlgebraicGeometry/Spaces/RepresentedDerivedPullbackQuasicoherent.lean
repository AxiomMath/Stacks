module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleEtalePullback
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSmallModelPullbackExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.SiteEquivalenceKFlatTransport
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesCompare
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentAbelian

/-!
# Derived pullback between represented algebraic spaces preserves `D_QCoh`

This is the case of a morphism of schemes in the proof of Stacks 08F4: for a morphism
`h : h_{U'} ⟶ h_U` of algebraic spaces represented by a morphism of the big fppf site, with
underlying morphism of schemes `r : T' ⟶ T`, degreewise pullback along `h` of a K-flat complex
with flat terms and quasi-coherent cohomology has quasi-coherent cohomology.  It is Stacks 08DW
part (1) for `r`, which is stated on the Zariski sites, transported to the small étale sites.

## Main results

* `AlgebraicGeometry.Space.isKFlat_representedAssociatedModule`: `ε^*` carries K-flat complexes
  with flat terms on `T_Zar` to K-flat complexes with flat terms on the small étale site of
  `h_U`, by Stacks 0G7E for `ε` and the reindexing along the equivalence of the small étale site
  of `h_U` with that of `T`.
* `AlgebraicGeometry.Space.derivedPullbackObjIsoOfIsKFlat`: `Lf^*` of a K-flat complex with flat
  terms is computed degreewise, for any morphism `f` of algebraic spaces (Stacks 06YY).
* `AlgebraicGeometry.Space.representedAssociatedModulePullbackFunctorIso`: `h^* ∘ ε^* ≅ ε^* ∘ r^*`.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_homology_pullbackModules_representedSpaceMap`:
  the case of a morphism of schemes.

## Implementation notes

By Stacks 071Q the class of the complex is `ε^*ω` for `ω ∈ D_QCoh(𝒪_T)`; a K-flat representative
`K` of `ω` gives a second K-flat representative `ε^*K`, so both compute `Lh^*`, and
`h^*ε^*K ≅ ε^*r^*K` reduces the claim to Stacks 08DW part (1) for `r` in its K-flat form,
`Stacks.Duality.isQuasicoherent_homology_modulePullback_of_kFlat`.

The global instance `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` is switched off in the
two sections, as in
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedAssociatedModuleEtalePullback.lean`: it answers
`Abelian` for these categories of modules at a universe join that is never the universe of the
schemes.  For the same reason of instance search, the sheafification instances of the small étale
site of `h_U` are supplied by hand where the reindexing is applied: the default ones found at the
concrete universes produce a term the kernel rejects.

## References

* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)


section KFlat

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (T : BigFppfOver B S hS)

/-- The small étale ringed topos of the scheme `T` underlying an object of the big fppf site,
over the big étale site carried by the same category of schemes. -/
abbrev representedSchemeRingedTopos : RingedTopos.{u, u + 1, u} :=
  _root_.AlgebraicGeometry.SmallEtale.ringedTopos (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj T) T.left.property

/-- Sheafification of presheaves of abelian groups exists on the small étale site of `T`. -/
instance : HasSheafify (representedSchemeRingedTopos B S hS T).J AddCommGrpCat.{u} :=
  (inferInstance : HasSheafify (_root_.AlgebraicGeometry.SmallEtale.topology
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
      AddCommGrpCat.{u})

/-- Sheafification of presheaves of sets exists on the small étale site of `T`. -/
instance : HasSheafify (representedSchemeRingedTopos B S hS T).J (Type u) :=
  (inferInstance : HasSheafify (_root_.AlgebraicGeometry.SmallEtale.topology
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property) (Type u))

/-- The functor of the equivalence between the small étale site of `h_U` and that of `T` is
continuous. -/
instance : (representedSmallEtaleEquivalence B S hS T).functor.IsContinuous
    (SmallEtale.topology B S hS (yoneda.obj T)) (representedSchemeRingedTopos B S hS T).J :=
  isContinuous_representedSmallEtaleEquivalence_functor B S hS T

/-- The inverse of the equivalence between the small étale site of `h_U` and that of `T` is
continuous. -/
instance : (representedSmallEtaleEquivalence B S hS T).inverse.IsContinuous
    (representedSchemeRingedTopos B S hS T).J (SmallEtale.topology B S hS (yoneda.obj T)) :=
  isContinuous_representedSmallEtaleEquivalence_inverse B S hS T

/-- The functor of the equivalence between the small étale site of `h_U` and that of `T` is
cocontinuous. -/
instance : (representedSmallEtaleEquivalence B S hS T).functor.IsCocontinuous
    (SmallEtale.topology B S hS (yoneda.obj T)) (representedSchemeRingedTopos B S hS T).J :=
  (inferInstance : (representedSmallEtaleEquivalence B S hS T).functor.IsCocontinuous
    (SmallEtale.topology B S hS (yoneda.obj T)) (representedSchemeSmallEtaleTopology B S hS T))

/-- The morphism of ringed topoi `ε : (T_étale, 𝒪) ⟶ (T_Zar, 𝒪_T)` of Stacks 08H7 for the scheme
`T` underlying an object of the big fppf site, in the two-field form of Stacks 01D3 (2). -/
abbrev representedToZariski :
    RingedToposHom
      (_root_.AlgebraicGeometry.SmallEtale.ringedTopos (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
      ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedTopos :=
  _root_.AlgebraicGeometry.SmallEtale.toZariskiAbstractRingedToposHom (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj T) T.left.property

/-- The degreewise pullback of complexes along `ε` is the degreewise associated-module functor of
Stacks 03DU (4): the two are left adjoints of the same direct image
(`AlgebraicGeometry.SmallEtale.assocIso`). -/
def representedToZariskiPullbackIso :
    (representedToZariski B S hS T).toModulesHom.pullbackModules ≅
      _root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property :=
  eqToIso (by
    have h := RingedToposHom.toModulesHom_eq_toRingedToposModulesHom (representedToZariski B S hS T)
    unfold _root_.AlgebraicGeometry.SmallEtale.toZariskiModulePullback
    congr 1) ≪≫
    _root_.AlgebraicGeometry.SmallEtale.assocIso (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property

/-- **`ε^*` carries K-flat complexes with flat terms to K-flat complexes with flat terms**, from
the Zariski site of the scheme `T` underlying an object of the big fppf site to its small étale
site.  This is Stacks 0G7E for the morphism of ringed topoi `ε`
(`Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isKFlat_pullbackMapHomotopy`), read
through the identification of the pullback along `ε` with the associated-module functor. -/
theorem isKFlat_associatedModule_mapHomologicalComplex
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedTopos.O)) ℤ)
    (hK : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedTopos)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) :
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := representedSchemeRingedTopos B S hS T)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)) := by
  have h₁ := Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isKFlat_pullbackMapHomotopy
    (representedToZariski B S hS T) _ hK
  let iso₁ : ((representedToZariski B S hS T).toModulesHom.pullbackModules.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K ≅
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i => (representedToZariskiPullbackIso B S hS T).app (K.X i))
      (fun i j _ => ((representedToZariskiPullbackIso B S hS T).hom.naturality (K.d i j)).symm)
  exact ⟨CochainComplex.KFlatBifunctor.KFlat.of_iso _ h₁.1 iso₁, fun i =>
    Stacks.SheafOfModules.FlatRetract.isFlat_of_iso _
      ((representedToZariskiPullbackIso B S hS T).app (K.X i)) (h₁.2 i)⟩

/-- **The comparison of the small étale site of `yoneda.obj T` with that of its scheme carries
K-flat complexes with flat terms to K-flat complexes with flat terms.**  This is the reindexing
along the equivalence of the two sites
(`Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.kFlat_reindexMod_mapHomologicalComplex`,
`Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.isFlat_reindexMod_functor_obj`). -/
theorem isKFlat_representedModulePushforward_mapHomologicalComplex
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (representedSchemeRingedTopos B S hS T).O)) ℤ)
    (hL : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := representedSchemeRingedTopos B S hS T)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)) :
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((representedModulePushforward B S hS T).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L)) :=
  have : HasSheafify (SmallEtale.topology B S hS (yoneda.obj T)) AddCommGrpCat.{u} :=
    SmallEtale.instHasSheafify B S hS _ _
  have : (SmallEtale.topology B S hS (yoneda.obj T)).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    SmallEtale.instWEqualsLocallyBijective B S hS _ _
  ⟨Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.kFlat_reindexMod_mapHomologicalComplex
      (SmallEtale.topology B S hS (yoneda.obj T)) (representedSmallEtaleEquivalence B S hS T)
      (show Sheaf (representedSchemeSmallEtaleTopology B S hS T) CommRingCat.{u} from
        (representedSchemeRingedTopos B S hS T).O) L hL.1,
    fun i => Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.isFlat_reindexMod_functor_obj
      (SmallEtale.topology B S hS (yoneda.obj T)) (representedSmallEtaleEquivalence B S hS T)
      (show Sheaf (representedSchemeSmallEtaleTopology B S hS T) CommRingCat.{u} from
        (representedSchemeRingedTopos B S hS T).O) (L.X i) (hL.2 i)⟩

/-- **`ε^*` carries K-flat complexes with flat terms on the Zariski site of the scheme `T`
underlying an object of the big fppf site to K-flat complexes with flat terms on the small étale
site of the algebraic space `T` represents**: the composite of
`AlgebraicGeometry.Space.isKFlat_associatedModule_mapHomologicalComplex` and
`AlgebraicGeometry.Space.isKFlat_representedModulePushforward_mapHomologicalComplex`. -/
theorem isKFlat_representedAssociatedModule
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedTopos.O)) ℤ)
    (hK : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedTopos)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) :
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((representedAssociatedModule B S hS T
            (isAlgebraicSpace_yoneda B S hS T)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)) := by
  have h₁ := isKFlat_associatedModule_mapHomologicalComplex B S hS T K hK
  have h₂ := isKFlat_representedModulePushforward_mapHomologicalComplex B S hS T _ h₁
  exact h₂

end KFlat

/-- Equal functors induce the same functor on complexes, whatever the zero-morphism instances
used to form it, so a property of `F(K)` holds for `G(K)` when `F = G`. -/
theorem mapHomologicalComplex_obj_congr {C₁ C₂ : Type*} [Category C₁] [Category C₂]
    [Abelian C₁] [Abelian C₂] {F G : C₁ ⥤ C₂} [F.PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] (h : F = G) (K : CochainComplex C₁ ℤ)
    (P : CochainComplex C₂ ℤ → Prop) :
    P ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ↔
      P ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  subst h
  rfl

section Derived

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard

/-- Pullback of modules along a morphism of algebraic spaces, in the spelling of the morphism of
small étale ringed topoi, is additive (`AlgebraicGeometry.RingedToposHom.pullbackModules_additive`,
restated at this spelling for instance search). -/
instance pullbackModules_smallEtaleRingedToposHom_additive {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) : (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.Additive :=
  RingedToposHom.pullbackModules_additive (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)

/-- Pullback of modules along a morphism of algebraic spaces, in the spelling of the morphism of
small étale ringed topoi that the derived pullback is built from, is the pullback of modules of
Stacks 03LU. -/
theorem pullbackModules_eq_modulePullback {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    ((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules :
      Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS X.1 X.2) =
      modulePullback B S hS f := by
  have h := RingedToposHom.toModulesHom_eq_toRingedToposModulesHom
    (smallEtaleRingedToposHom B S hS f)
  unfold modulePullback smallEtaleRingedToposModulesHom
  congr 1

/-- Quasi-coherence of the cohomology of a degreewise pullback does not depend on which of the two
spellings of the pullback of modules is used. -/
theorem isQuasicoherentOnSite_homology_pullbackModules_iff {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS Y).O)) ℤ) (i : ℤ) :
    ((((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C).homology i).IsQuasicoherentOnSite ↔
      ((((modulePullback B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj C).homology
        i).IsQuasicoherentOnSite :=
  @mapHomologicalComplex_obj_congr _ _ _ _ _ _ _ _
    (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
      (pullbackModules_smallEtaleRingedToposHom_additive B S hS f))
    (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ (modulePullback B S hS f)
      (modulePullback_additive f))
    (pullbackModules_eq_modulePullback B S hS f) C
    (fun M => SheafOfModules.IsQuasicoherentOnSite (M.homology i))

/-- **`Lf^*` of a K-flat complex with flat terms is computed degreewise**, for an arbitrary
morphism `f : X ⟶ Y` of algebraic spaces: this is the computation clause of Stacks 06YY for the
morphism of small étale ringed topoi of `f`, at the resolving class of Stacks 06YS. -/
def derivedPullbackObjIsoOfIsKFlat {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS Y).O)) ℤ)
    (hP : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS Y)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) :
    (smallEtaleDerivedModulePullback B S hS f).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
  have hres : Stacks.Cohomology.DerivedPullbackOfToposHom.HasResolutions
      (Y := smallEtaleRingedTopos B S hS Y)
      (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
        (Y := smallEtaleRingedTopos B S hS Y)) := fun N => by
    obtain ⟨K, hK, t, ht⟩ :=
      Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat
        (Y := smallEtaleRingedTopos B S hS Y) N
    exact ⟨K, hK, t, ht⟩
  have := Stacks.Cohomology.DerivedPullbackOfToposHom.isIso_derivedPullbackComparison_app
    (smallEtaleRingedToposHom B S hS f) _ hres
    (Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackInvertsQuasiIso_isKFlat
      (smallEtaleRingedToposHom B S hS f)) _ hP
  (smallEtaleDerivedModulePullback B S hS f).mapIso
      ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫
    asIso ((smallEtaleDerivedModulePullbackComparison B S hS f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≪≫
    DerivedCategory.Qh.mapIso
      ((((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).app P).symm) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)

/-- Pullback of modules along a morphism of represented algebraic spaces preserves zero
morphisms, being additive; restated at the represented spelling for instance search. -/
instance pullbackModules_representedSpaceMap_preservesZeroMorphisms :
    (smallEtaleRingedToposHom B S hS
      (representedSpaceMap B S hS g)).toModulesHom.pullbackModules.PreservesZeroMorphisms :=
  have := pullbackModules_smallEtaleRingedToposHom_additive B S hS (representedSpaceMap B S hS g)
  Functor.preservesZeroMorphisms_of_additive _

/-- The inverse image of modules along a morphism of represented algebraic spaces preserves zero
morphisms, being additive; restated at the represented spelling for instance search. -/
instance modulePullback_representedSpaceMap_preservesZeroMorphisms :
    (modulePullback B S hS (representedSpaceMap B S hS g)).PreservesZeroMorphisms :=
  have := modulePullback_additive (representedSpaceMap B S hS g)
  Functor.preservesZeroMorphisms_of_additive _

/-- **`ε^*` commutes with pullback along a morphism of represented algebraic spaces**, on
modules: for `g : U' ⟶ U` in the big fppf site with underlying morphism of schemes `r`,
`h^*(ε^*𝓕) ≅ ε^*(r^*𝓕)` naturally in the `𝒪_T`-module `𝓕`, where `h` is the morphism of
represented algebraic spaces.  It is the comparison of the small étale site of `h_U` with that of
its scheme (`AlgebraicGeometry.Space.representedModuleEquivalencePullbackSquare`) followed by
Stacks 03LC (1) for the small étale sites of the two schemes
(`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso`). -/
def representedAssociatedModulePullbackFunctorIso :
    representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T) ⋙
        modulePullback B S hS (representedSpaceMap B S hS g) ≅
      Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g) ⋙
        representedAssociatedModule B S hS T' (isAlgebraicSpace_yoneda B S hS T') :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (representedModuleEquivalencePullbackSquare B S hS g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (_root_.AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso
      (associatedBigEtaleSite B) g.left).symm _ ≪≫
    Functor.associator _ _ _

/-- `ε^*` commutes with pullback along a morphism of represented algebraic spaces, degreewise on
complexes: the module square
`AlgebraicGeometry.Space.representedAssociatedModulePullbackFunctorIso` applied to each term. -/
def representedAssociatedModulePullbackComplexIso
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedTopos.O)) ℤ) :
    ((modulePullback B S hS (representedSpaceMap B S hS g)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        (((representedAssociatedModule B S hS T
            (isAlgebraicSpace_yoneda B S hS T)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≅
      ((representedAssociatedModule B S hS T'
        (isAlgebraicSpace_yoneda B S hS T')).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) :=
  let sq := representedAssociatedModulePullbackFunctorIso B S hS g
  HomologicalComplex.Hom.isoOfComponents (fun i => sq.app (K.X i))
    (fun i j _ => (sq.hom.naturality (K.d i j)).symm)

/-- **Stacks 08DW part (1) for a morphism of represented algebraic spaces, on K-flat complexes.**
Let `h : h_{U'} ⟶ h_U` be the morphism of algebraic spaces represented by a morphism `g` of the big
fppf site and let `P` be a K-flat complex with flat terms of `𝒪_{h_U}`-modules all of whose
cohomology sheaves are quasi-coherent.  Then every cohomology sheaf of the degreewise pullback
`h^*P` is quasi-coherent.

By Stacks 071Q the class of `P` is `ε^*ω` for `ω` in `D_QCoh` of the scheme `T` underlying `U`
(`AlgebraicGeometry.Space.exists_representedDerivedAssociatedModule_iso`); represent `ω` by a
K-flat complex `K` (Stacks 06YF).  Then `ε^*K` is again K-flat with flat terms, so both `h^*P` and
`h^*(ε^*K)` compute `Lh^*` of the same object, and `h^*(ε^*K) ≅ ε^*(r^*K)` degreewise.  The
cohomology of `r^*K` is quasi-coherent by Stacks 08DW part (1) for the morphism of schemes `r`
(`Stacks.Duality.isQuasicoherent_homology_modulePullback_of_kFlat`), and `ε^*` is exact and
preserves quasi-coherence. -/
theorem isQuasicoherentOnSite_homology_pullbackModules_representedSpaceMap
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩).O)) ℤ)
    (hP : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))
    (hPq : ∀ j : ℤ, (P.homology j).IsQuasicoherentOnSite) (i : ℤ) :
    ((((smallEtaleRingedToposHom B S hS
        (representedSpaceMap B S hS g)).toModulesHom.pullbackModules.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P).homology i).IsQuasicoherentOnSite := by
  have hE : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj T)
          (isAlgebraicSpace_yoneda B S hS T)).O))) (DerivedCategory.Q.obj P) := fun n =>
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((DerivedCategory.homologyFunctorFactors _ n).app P).symm (hPq n)
  obtain ⟨ω, hω, ⟨e⟩⟩ := exists_representedDerivedAssociatedModule_iso B S hS T _ hE
  obtain ⟨K, k, hK, hKf, hk, -⟩ := Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution
    ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace (DerivedCategory.Q.objPreimage ω)
  have := hk
  let eK : DerivedCategory.Q.obj K ≅ ω :=
    asIso (DerivedCategory.Q.map k) ≪≫ DerivedCategory.Q.objObjPreimageIso ω
  have hKq : ∀ j : ℤ, (K.homology j).IsQuasicoherent := fun j =>
    (SheafOfModules.isQuasicoherent _).prop_of_iso
      (((DerivedCategory.homologyFunctor _ j).mapIso eK).symm ≪≫
        (DerivedCategory.homologyFunctorFactors _ j).app K) (hω j)
  let M := ((representedAssociatedModule B S hS T
      (isAlgebraicSpace_yoneda B S hS T)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let eM : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj M :=
    e.symm ≪≫ (representedDerivedAssociatedModule B S hS T).mapIso eK.symm ≪≫
      (representedAssociatedModule B S hS T
        (isAlgebraicSpace_yoneda B S hS T)).mapDerivedCategoryFactors.app K
  have hM : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M) :=
    isKFlat_representedAssociatedModule B S hS T K ⟨hK, hKf⟩
  have := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS
    (representedSpaceMap B S hS g)
  let e₁ := (derivedPullbackObjIsoOfIsKFlat B S hS (representedSpaceMap B S hS g) P hP).symm ≪≫
    (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).mapIso eM ≪≫
    derivedPullbackObjIsoOfIsKFlat B S hS (representedSpaceMap B S hS g) M hM
  let G := ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K
  let e₂ := representedAssociatedModulePullbackComplexIso B S hS g K
  let e₃ : G ≅ (((RingedSpaceModuleAdjunction.modulePullback
      ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i => (Stacks.ProjectiveBundleQuotients.pullbackIso
        ((BigFppfOver.toScheme B S hS).map g)).app (K.X i))
      (fun i j _ => ((Stacks.ProjectiveBundleQuotients.pullbackIso
        ((BigFppfOver.toScheme B S hS).map g)).hom.naturality (K.d i j)).symm)
  have hG : ∀ j : ℤ, (G.homology j).IsQuasicoherent := fun j =>
    (SheafOfModules.isQuasicoherent _).prop_of_iso
      ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j).mapIso e₃).symm
      (Stacks.Duality.isQuasicoherent_homology_modulePullback_of_kFlat
        ((BigFppfOver.toScheme B S hS).map g) K hK hKq j)
  have hεG : (((representedAssociatedModule B S hS T'
      (isAlgebraicSpace_yoneda B S hS T')).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        G |>.homology i).IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      (((representedAssociatedModule B S hS T'
        (isAlgebraicSpace_yoneda B S hS T')).mapHomologicalComplexHomologyIso
          (ComplexShape.up ℤ) i).app G).symm
      (isQuasicoherentOnSite_representedAssociatedModule B S hS T' _ _ (hG i))
  have hfin' := SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) i).mapIso e₂).symm hεG
  have hfin := (isQuasicoherentOnSite_homology_pullbackModules_iff B S hS
    (representedSpaceMap B S hS g) M i).2 hfin'
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (((DerivedCategory.homologyFunctorFactors _ i).app _).symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso e₁.symm ≪≫
        (DerivedCategory.homologyFunctorFactors _ i).app _) hfin

end Derived

end AlgebraicGeometry.Space

end
