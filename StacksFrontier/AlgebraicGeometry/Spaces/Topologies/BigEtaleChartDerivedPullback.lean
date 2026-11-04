module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSiteChartSlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.RestrictionToSlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOnRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSiteHomOfRingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.BoundedBelowDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.BoundedBelowEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Homology.PseudoCoherent.Locality

/-!
# The derived pullback along `π_X`, restricted to an étale chart

Let `X` be an algebraic space, `K` an object of `D(X_{spaces,étale}, 𝒪_X)` and `Q` an object of
the spaces-étale site of `X`, with underlying algebraic space `Y`. Restricting `Lπ_X^*K` to the
slice of the big étale site at `Q` and reading the result on the big étale site of `Y` gives
`Lπ_Y^*K_Q`, where `K_Q` is the restriction of `K` to `Q` read on the spaces-étale site of `Y`.

The argument: the derived pullback commutes with localization (Stacks 04J0 and its derived form,
`AlgebraicGeometry.RingedSite.Hom.nonempty_derivedPullbackLocalizedIso_of_noFiniteLimits`), the
localization of `π_X` at `Q` is `π_Y` through the two slice identifications
(`AlgebraicGeometry.BigEtaleSpaceSite.localized_spacesEtaleRestriction_comp_smallSlice`), and the
derived pullbacks along these identifications, which are equivalences, are computed degreewise
(Stacks 0D6D for the two composites).

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.exists_slice_homology_derivedPullback_iso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

namespace AlgebraicGeometry.RingedSite.Hom

variable {X Y Z : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The derived pullback along a morphism of ringed sites exists. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_toRingedToposSiteHom (f : RingedSite.Hom X Y) :
    (pullbackOnHomotopy f.toRingedToposSiteHom).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSite.ringedTopos.{u, u, u} Y).O))
        (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy.{u} _
    f.isMorphismOfSites

/-- Derived pullbacks along equal morphisms of ringed sites agree. -/
def derivedPullbackObjIsoOfEq {f g : RingedSite.Hom X Y} (h : f = g)
    (K : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSite.ringedTopos.{u, u, u} Y).O))) :
    (derivedPullback f.toRingedToposSiteHom).obj K ≅
      (derivedPullback g.toRingedToposSiteHom).obj K := by
  subst h
  exact Iso.refl _

/-- **Stacks 0D6D for morphisms of ringed sites**: `L(g ∘ f)^* ≅ Lf^* ∘ Lg^*`. -/
def derivedPullbackCompObjIso (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y Z)
    (K : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSite.ringedTopos.{u, u, u} Z).O))) :
    (derivedPullback (f.comp g).toRingedToposSiteHom).obj K ≅
      (derivedPullback f.toRingedToposSiteHom).obj
        ((derivedPullback g.toRingedToposSiteHom).obj K) :=
  haveI : (pullbackOnHomotopy
        (g.toRingedToposSiteHom.comp f.toRingedToposSiteHom)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSite.ringedTopos.{u, u, u} Z).O))
        (ComplexShape.up ℤ)) :=
    hasLeftDerivedFunctor_pullbackOnHomotopy_toRingedToposSiteHom (f.comp g)
  haveI := Stacks.Cohomology.DerivedPullbackCompositionOnTopoi.isIso_derivedPullbackCompComparison
    f.toRingedToposSiteHom g.toRingedToposSiteHom f.isMorphismOfSites g.isMorphismOfSites
  (asIso ((Stacks.Cohomology.DerivedPullbackCompositionOnTopoi.derivedPullbackCompComparison
    f.toRingedToposSiteHom g.toRingedToposSiteHom).app K)).symm

end AlgebraicGeometry.RingedSite.Hom

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (E : BigEtaleSpaceSite S) {X : E.Spaces}

/-- The direct image along the slice identification of the big étale site is an equivalence:
it is the inverse of the equivalence of module categories induced by the iterated slice
equivalence. -/
instance isEquivalence_sliceRingedSiteHom_pushforwardTopos (W : Over X) :
    (sliceRingedSiteHom E W).toRingedToposSiteHom.pushforwardTopos.IsEquivalence :=
  letI : (Over.iteratedSliceEquiv W).functor.IsContinuous ((E.bigEtaleRingedSite X).over W).J
      (E.bigEtaleRingedSite W.left).J :=
    inferInstanceAs ((Over.iteratedSliceForward W).IsContinuous ((E.topology.over X).over W)
      (E.topology.over W.left))
  letI : (Over.iteratedSliceEquiv W).inverse.IsContinuous (E.bigEtaleRingedSite W.left).J
      ((E.bigEtaleRingedSite X).over W).J :=
    (sliceRingedSiteHom E W).isMorphismOfSites.isContinuous
  (SheafOfModules.pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv W)
    (S := Stacks.SheafOfModules.Tensor.ringSheaf ((E.bigEtaleRingedSite X).over W).O)
    (R := Stacks.SheafOfModules.Tensor.ringSheaf (E.bigEtaleRingedSite W.left).O)
    (𝟙 _) (sliceRingedSiteHom E W).toRingedToposSiteHom.fSharpRing
    (by ext : 2; exact (Stacks.SheafOfModules.Tensor.ringSheaf
      (E.bigEtaleRingedSite W.left).O).1.map_id _)
    (by ext : 2; exact (Stacks.SheafOfModules.Tensor.ringSheaf
      ((E.bigEtaleRingedSite X).over W).O).1.map_id _)).isEquivalence_inverse

/-- The direct image along the slice identification of the spaces-étale site is an
equivalence. -/
instance isEquivalence_smallSliceRingedSiteHom_pushforwardTopos
    (Q : Space.SpacesEtale E.fppfSite S E.fppf_mem X) :
    (smallSliceRingedSiteHom E Q).toRingedToposSiteHom.pushforwardTopos.IsEquivalence :=
  letI : (Space.SpacesEtale.sliceEquivSmall E.fppfSite S E.fppf_mem Q).functor.IsContinuous
      ((Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem X).over Q).J
      (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem Q.obj.left).J :=
    inferInstanceAs ((Space.SpacesEtale.sliceToSmall E.fppfSite S E.fppf_mem Q).IsContinuous
      ((Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X).over Q)
      (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Q.obj.left))
  letI : (Space.SpacesEtale.sliceEquivSmall E.fppfSite S E.fppf_mem Q).inverse.IsContinuous
      (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem Q.obj.left).J
      ((Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem X).over Q).J :=
    (smallSliceRingedSiteHom E Q).isMorphismOfSites.isContinuous
  Equivalence.isEquivalence_inverse (SheafOfModules.pushforwardPushforwardEquivalence
    (Space.SpacesEtale.sliceEquivSmall E.fppfSite S E.fppf_mem Q)
    (S := Stacks.SheafOfModules.Tensor.ringSheaf
      ((Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem X).over Q).O)
    (R := Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem Q.obj.left).O)
    (𝟙 _) (smallSliceRingedSiteHom E Q).toRingedToposSiteHom.fSharpRing
    (by ext : 2; exact (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem Q.obj.left).O).1.map_id _)
    (by ext : 2; exact (Stacks.SheafOfModules.Tensor.ringSheaf
      ((Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem X).over Q).O).1.map_id _))

/-- The inverse image along the slice identification of the big étale site is an equivalence. -/
instance isEquivalence_sliceRingedSiteHom_pullbackTopos (W : Over X) :
    (sliceRingedSiteHom E W).toRingedToposSiteHom.pullbackTopos.IsEquivalence :=
  Adjunction.isEquivalence_left_of_isEquivalence_right
    (sliceRingedSiteHom E W).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos

/-- The inverse image along the slice identification of the spaces-étale site is an
equivalence. -/
instance isEquivalence_smallSliceRingedSiteHom_pullbackTopos
    (Q : Space.SpacesEtale E.fppfSite S E.fppf_mem X) :
    (smallSliceRingedSiteHom E Q).toRingedToposSiteHom.pullbackTopos.IsEquivalence :=
  Adjunction.isEquivalence_left_of_isEquivalence_right
    (smallSliceRingedSiteHom E Q).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos

/-- `Lπ_X^*` exists. -/
instance hasLeftDerivedFunctor_spacesEtaleRestriction (Y : E.Spaces) :
    (pullbackOnHomotopy
        (spacesEtaleRestrictionRingedSiteHom E Y).toRingedToposSiteHom).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
          (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem Y)).O)) (ComplexShape.up ℤ)) :=
  RingedSite.Hom.hasLeftDerivedFunctor_pullbackOnHomotopy_toRingedToposSiteHom _

/-- The derived pullback along the slice identification of the big étale site exists. -/
instance hasLeftDerivedFunctor_sliceRingedSiteHom (W : Over X) :
    (pullbackOnHomotopy (sliceRingedSiteHom E W).toRingedToposSiteHom).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (E.bigEtaleRingedSite W.left)).O))
        (ComplexShape.up ℤ)) :=
  RingedSite.Hom.hasLeftDerivedFunctor_pullbackOnHomotopy_toRingedToposSiteHom _

/-- The derived pullback along the slice identification of the spaces-étale site exists. -/
instance hasLeftDerivedFunctor_smallSliceRingedSiteHom
    (Q : Space.SpacesEtale E.fppfSite S E.fppf_mem X) :
    (pullbackOnHomotopy (smallSliceRingedSiteHom E Q).toRingedToposSiteHom).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
          (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem Q.obj.left)).O))
        (ComplexShape.up ℤ)) :=
  RingedSite.Hom.hasLeftDerivedFunctor_pullbackOnHomotopy_toRingedToposSiteHom _

/-- The direct image along the slice identification of the big étale site is additive. -/
instance sliceRingedSiteHom_pushforwardTopos_additive (W : Over X) :
    (sliceRingedSiteHom E W).toRingedToposSiteHom.pushforwardTopos.Additive :=
  RingedToposSiteHom.pushforwardTopos_additive _

/-- The direct image along the slice identification of the spaces-étale site is additive. -/
instance smallSliceRingedSiteHom_pushforwardTopos_additive
    (Q : Space.SpacesEtale E.fppfSite S E.fppf_mem X) :
    (smallSliceRingedSiteHom E Q).toRingedToposSiteHom.pushforwardTopos.Additive :=
  RingedToposSiteHom.pushforwardTopos_additive _

/-- The inverse image along the slice identification of the big étale site is additive. -/
instance sliceRingedSiteHom_pullbackTopos_additive (W : Over X) :
    (sliceRingedSiteHom E W).toRingedToposSiteHom.pullbackTopos.Additive :=
  Adjunction.left_adjoint_additive
    (sliceRingedSiteHom E W).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos

/-- The inverse image along the slice identification of the spaces-étale site is additive. -/
instance smallSliceRingedSiteHom_pullbackTopos_additive
    (Q : Space.SpacesEtale E.fppfSite S E.fppf_mem X) :
    (smallSliceRingedSiteHom E Q).toRingedToposSiteHom.pullbackTopos.Additive :=
  Adjunction.left_adjoint_additive
    (smallSliceRingedSiteHom E Q).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos

attribute [local instance] Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits

/-- **The derived pullback along `π_X`, restricted to an object `Q` of the spaces-étale site and
read on the big étale site of `Q`, is the derived pullback along `π_Q`** of an object `K_Q` whose
cohomology sheaves are those of `K`, restricted to `Q` and read on the spaces-étale site of `Q`. -/
theorem exists_slice_homology_derivedPullback_iso
    (Q : Space.SpacesEtale E.fppfSite S E.fppf_mem X)
    (K : DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem X).O))) :
    ∃ KQ : DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem Q.obj.left).O)),
      (∀ i : ℤ, Nonempty ((DerivedCategory.homologyFunctor _ i).obj KQ ≅
        (smallSliceRingedSiteHom E Q).toRingedToposSiteHom.pushforwardTopos.obj
          ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
            (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem X).O) Q).obj
            ((DerivedCategory.homologyFunctor _ i).obj K)))) ∧
      ∀ q : ℤ, Nonempty ((sliceRingedSiteHom E Q.obj).toRingedToposSiteHom.pushforwardTopos.obj
          ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
            (E.bigEtaleRingedSite X).O) Q.obj).obj ((DerivedCategory.homologyFunctor _ q).obj
            ((derivedPullback (spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom).obj
              K))) ≅
        (DerivedCategory.homologyFunctor _ q).obj
          ((derivedPullback
              (spacesEtaleRestrictionRingedSiteHom E Q.obj.left).toRingedToposSiteHom).obj
            KQ)) := by
  let K' := (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
    (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem X).O) Q).mapDerivedCategory.obj K
  let C := DerivedCategory.Q.objPreimage K'
  let eC : DerivedCategory.Q.obj C ≅ K' := DerivedCategory.Q.objObjPreimageIso K'
  let KQ := DerivedCategory.Q.obj
    (((smallSliceRingedSiteHom E Q).toRingedToposSiteHom.pushforwardTopos.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C)
  -- `Le_S^* K_Q ≅ K'`
  let adjS := (smallSliceRingedSiteHom E Q).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos
  have : IsIso adjS.counit := adjS.counit_isIso_of_R_fully_faithful
  let eK : (derivedPullback (smallSliceRingedSiteHom E Q).toRingedToposSiteHom).obj KQ ≅ K' :=
    Stacks.Cohomology.CohomologicalDescent.derivedPullbackObjIso
        (smallSliceRingedSiteHom E Q).toRingedToposSiteHom KQ ≪≫
      (Functor.mapDerivedCategoryFactors
        (smallSliceRingedSiteHom E Q).toRingedToposSiteHom.pullbackTopos).app _ ≪≫
      DerivedCategory.Q.mapIso (HomologicalComplex.Hom.isoOfComponents
        (C₁ := (Functor.mapHomologicalComplex
            (smallSliceRingedSiteHom E Q).toRingedToposSiteHom.pullbackTopos
            (ComplexShape.up ℤ)).obj
          ((Functor.mapHomologicalComplex
            (smallSliceRingedSiteHom E Q).toRingedToposSiteHom.pushforwardTopos
            (ComplexShape.up ℤ)).obj C)) (C₂ := C)
        (fun n ↦ (asIso adjS.counit).app (C.X n))
        (fun i j _ ↦ (adjS.counit.naturality (C.d i j)).symm)) ≪≫ eC
  refine ⟨KQ, fun i ↦ ?_, fun q ↦ ?_⟩
  · have : IsIso adjS.unit := adjS.unit_isIso_of_L_fully_faithful
    exact ⟨(asIso (adjS.unit.app _)) ≪≫
      (smallSliceRingedSiteHom E Q).toRingedToposSiteHom.pushforwardTopos.mapIso
        ((Stacks.Cohomology.CohomologicalDescent.derivedPullbackHomologyObjIso
            (smallSliceRingedSiteHom E Q).toRingedToposSiteHom KQ i).symm ≪≫
          (DerivedCategory.homologyFunctor _ i).mapIso eK ≪≫
          (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
            (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
              (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem X).O) Q) i).app K)⟩
  · have := RingedSite.Hom.hasLeftDerivedFunctor_pullbackOnHomotopy_toRingedToposSiteHom
      ((spacesEtaleRestrictionRingedSiteHom E X).localized Q)
    obtain ⟨eR⟩ := RingedSite.Hom.nonempty_derivedPullbackLocalizedIso_of_noFiniteLimits.{u + 1}
      (spacesEtaleRestrictionRingedSiteHom E X) Q K
    have hsq := localized_spacesEtaleRestriction_comp_smallSlice E Q
    let adjB := (sliceRingedSiteHom E Q.obj).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos
    have : IsIso adjB.unit := adjB.unit_isIso_of_L_fully_faithful
    exact ⟨(sliceRingedSiteHom E Q.obj).toRingedToposSiteHom.pushforwardTopos.mapIso
        (((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
            (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
              (E.bigEtaleRingedSite X).O) Q.obj) q).app _).symm ≪≫
          (DerivedCategory.homologyFunctor
            (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
              (RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
                ((E.bigEtaleRingedSite X).over Q.obj)).O)) q).mapIso (eR.symm ≪≫
      (derivedPullback
        ((spacesEtaleRestrictionRingedSiteHom E X).localized Q).toRingedToposSiteHom).mapIso
          eK.symm ≪≫
        (RingedSite.Hom.derivedPullbackCompObjIso _ _ KQ).symm ≪≫
        RingedSite.Hom.derivedPullbackObjIsoOfEq hsq KQ ≪≫
        RingedSite.Hom.derivedPullbackCompObjIso _ _ KQ) ≪≫
          Stacks.Cohomology.CohomologicalDescent.derivedPullbackHomologyObjIso
            (sliceRingedSiteHom E Q.obj).toRingedToposSiteHom _ q) ≪≫
      (asIso (adjB.unit.app _)).symm⟩

end AlgebraicGeometry.BigEtaleSpaceSite

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) {X : T.Spaces}

/-- The direct image along the slice identification of the big fppf site is an equivalence. -/
instance isEquivalence_sliceRingedSiteHom_pushforwardTopos (W : Over X) :
    (sliceRingedSiteHom T W).toRingedToposSiteHom.pushforwardTopos.IsEquivalence :=
  letI : (Over.iteratedSliceEquiv W).functor.IsContinuous ((bigFppfRingedSite T X).over W).J
      (bigFppfRingedSite T W.left).J :=
    inferInstanceAs ((Over.iteratedSliceForward W).IsContinuous ((T.topology.over X).over W)
      (T.topology.over W.left))
  letI : (Over.iteratedSliceEquiv W).inverse.IsContinuous (bigFppfRingedSite T W.left).J
      ((bigFppfRingedSite T X).over W).J :=
    (sliceRingedSiteHom T W).isMorphismOfSites.isContinuous
  (SheafOfModules.pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv W)
    (S := Stacks.SheafOfModules.Tensor.ringSheaf ((bigFppfRingedSite T X).over W).O)
    (R := Stacks.SheafOfModules.Tensor.ringSheaf (bigFppfRingedSite T W.left).O)
    (𝟙 _) (sliceRingedSiteHom T W).toRingedToposSiteHom.fSharpRing
    (by ext : 2; exact (Stacks.SheafOfModules.Tensor.ringSheaf
      (bigFppfRingedSite T W.left).O).1.map_id _)
    (by ext : 2; exact (Stacks.SheafOfModules.Tensor.ringSheaf
      ((bigFppfRingedSite T X).over W).O).1.map_id _)).isEquivalence_inverse

/-- The inverse image along the slice identification of the big fppf site is an equivalence. -/
instance isEquivalence_sliceRingedSiteHom_pullbackTopos (W : Over X) :
    (sliceRingedSiteHom T W).toRingedToposSiteHom.pullbackTopos.IsEquivalence :=
  Adjunction.isEquivalence_left_of_isEquivalence_right
    (sliceRingedSiteHom T W).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos

end AlgebraicGeometry.BigFppfSpaceSite

end
