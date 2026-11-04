module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RepresentedDerivedPullbackComparisonConstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackCompositionCanonicalAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackSquareComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackDataCompIso
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleAssociatedModuleBaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatSource.UnderivedComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHomQuotient
public import StacksFrontier.CategoryTheory.Localization.UnderivedCompCoherenceTransport

/-!
# The underived identifications `h^* ∘ ε^* ≅ ε^* ∘ r^*` are compatible with composition

For a morphism `g : T' ⟶ T` of the big fppf site, with underlying morphism of schemes `r` and
represented morphism of algebraic spaces `h_g`,
`AlgebraicGeometry.Space.representedAssociatedModulePullbackModulesIso` identifies
`h_g^* ∘ ε_T^*` with `ε_{T'}^* ∘ r^*` on modules (Stacks 03LC (1), read through the comparison of
the small étale site of a represented algebraic space with that of its scheme).  This file proves
that these identifications are compatible with the compositors on both sides, on modules and then
on the unbounded homotopy categories: the compositor of
Stacks 03D6 followed by the 2-isomorphism of Stacks 03G8 on the small étale sites, and the
compositor of the inverse images of modules on the Zariski sites.

The identification is a pasting of three squares, and each square composes:

* the square of `AlgebraicGeometry.Space.representedModuleEquivalencePullbackSquare`, by the
  pasting coherence `AlgebraicGeometry.Space.representedModulePullbackIso_comp` read through the
  equivalences of the sites
  (`CategoryTheory.Functor.underivedCompCoherence_equivalenceConjSquare`);
* the square of Stacks 03LC (1), by
  `AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso_comp`;
* the two changes of spelling of the pullbacks, by
  `AlgebraicGeometry.Space.pullbackComp_pullbackIso_compCoherence` (Zariski) and by
  `AlgebraicGeometry.Space.modulePullbackDataTopos_compIso_symm_eq` (small étale).

Nothing here is registered.

## Main results

* `AlgebraicGeometry.Space.representedAssociatedModulePullbackModulesIso_compCoherence`: the
  compatibility on modules, as `CategoryTheory.Functor.UnderivedCompCoherence`.
* `AlgebraicGeometry.Space.representedHomotopyPullbackCoherence`: the same on the unbounded
  homotopy categories, the proposition
  `AlgebraicGeometry.Space.RepresentedHomotopyPullbackCoherence`.
* `AlgebraicGeometry.Space.representedDerivedPullbackComparisonCanonicalUnconditional`: hence the
  datum `AlgebraicGeometry.Space.RepresentedDerivedPullbackComparison` for the canonical
  pseudofunctoriality of the derived pullback, with no hypotheses.

## References

* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 6000] preadditive_smallEtaleModules_model

attribute [local instance]
  _root_.AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The Zariski side -/

section Zariski

variable {X Y Z : Scheme.{u}}

/-- The compositor `Scheme.Modules.pullbackComp` of the pullbacks of modules on schemes and the
compositor of the inverse images of modules on ringed spaces correspond under
`Stacks.ProjectiveBundleQuotients.pullbackIso`: all of them are comparisons of left adjoints of
the same direct images. -/
theorem pullbackComp_pullbackIso_compCoherence (a : X ⟶ Y) (b : Y ⟶ Z) (h : a ≫ b = a ≫ b)
    (M : Z.Modules) :
    (Scheme.Modules.pullbackComp a b).hom.app M ≫
        (Stacks.ProjectiveBundleQuotients.pullbackIso (a ≫ b)).hom.app M =
      (Stacks.ProjectiveBundleQuotients.pullbackIso a).hom.app
          ((Scheme.Modules.pullback b).obj M) ≫
        (RingedSpaceModuleAdjunction.modulePullback a.toLRSHom.toShHom).map
          ((Stacks.ProjectiveBundleQuotients.pullbackIso b).hom.app M) ≫
        (schemeFactorModulePullbackIso a b (a ≫ b) h).hom.app M :=
  Functor.leftAdjointUniq_compCoherence (Scheme.Modules.pullbackPushforwardAdjunction a)
    (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction a.toLRSHom.toShHom)
    (Scheme.Modules.pullbackPushforwardAdjunction b)
    (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction b.toLRSHom.toShHom)
    (Scheme.Modules.pullbackPushforwardAdjunction (a ≫ b))
    (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
      (a.toLRSHom.toShHom ≫ b.toLRSHom.toShHom))
    (Scheme.Modules.pullbackComp a b)
    (Stacks.DerivedPullback.Composition.modulePullbackComp a.toLRSHom.toShHom b.toLRSHom.toShHom)
    (Scheme.Modules.pushforwardComp a b) (Scheme.Modules.conjugateEquiv_pullbackComp_inv a b)
    (Stacks.AlgebraicGeometry.FlatSourceBaseChange.conjugateEquiv_modulePullbackComp_inv _ _) M

end Zariski

/-! ### The small étale side -/

section Etale

attribute [local instance 20000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  hasSheafCompose_smallEtale_forget₂_ringCat

/-- At the image of a complex, `AlgebraicGeometry.Space.smallEtalePullbackMapHomotopyFactorIso`
is the image of the underived compositor of Stacks 03D6 followed by the 2-isomorphism of
Stacks 03G8, applied degreewise. -/
theorem smallEtalePullbackMapHomotopyFactorIso_hom_app_quotient {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (N : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)) ℤ) :
    (smallEtalePullbackMapHomotopyFactorIso f g k h).hom.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map ((NatTrans.mapHomologicalComplex
        (((RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS f)
          (smallEtaleRingedToposHom B S hS g)).symm ≪≫
          (smallEtaleRingedToposHom_compTwoIso B S hS f g).pullbackModulesIso) ≪≫
          eqToIso (congrArg (fun m : X ⟶ Z ↦
            (smallEtaleRingedToposHom B S hS m).toModulesHom.pullbackModules) h)).hom
          (ComplexShape.up ℤ)).app N) := by
  subst h
  open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom in
  have := pullbackMapHomotopyCompIso_trans_hom_app_quotient
    (smallEtaleRingedToposHom B S hS f) (smallEtaleRingedToposHom B S hS g)
    (smallEtaleRingedToposHom_compTwoIso B S hS f g).pullbackModulesIso N
    (((RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS f)
          (smallEtaleRingedToposHom B S hS g)).symm ≪≫
          (smallEtaleRingedToposHom_compTwoIso B S hS f g).pullbackModulesIso) ≪≫
          eqToIso rfl).hom (by simp)
  rw [← this]
  simp [smallEtalePullbackMapHomotopyFactorIso]

end Etale

/-! ### The compositors of the pullbacks of modules on the small étale sites -/

section EtaleComp

attribute [local instance 20000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  hasSheafCompose_smallEtale_forget₂_ringCat

variable {X Y Z : AlgebraicSpaces B S hS}

/-- The compositor of Stacks 03D6 followed by the 2-isomorphism of Stacks 03G8, on the pullbacks
of modules along the morphisms of small étale ringed topoi, is the composition comparison
`AlgebraicGeometry.Space.modulePullbackCompIso` of Stacks 03LU read through the two spellings of
the pullbacks (`AlgebraicGeometry.Space.modulePullbackDataTopos_compIso_symm_eq`). -/
theorem pullbackModulesCompIso_symm_trans_compTwoIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    (RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS f)
        (smallEtaleRingedToposHom B S hS g)).symm ≪≫
      (smallEtaleRingedToposHom_compTwoIso B S hS f g).pullbackModulesIso =
      (eqToIso (toModulesHom_pullbackModules_eq_modulePullback B S hS (f ≫ g)) ≪≫
        (modulePullbackCompIso B S hS f g).symm ≪≫
        eqToIso (congrArg₂ (fun (a : Modules.{u, u} B S hS Z.1 Z.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2)
          (b : Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS X.1 X.2) => a ⋙ b)
          (toModulesHom_pullbackModules_eq_modulePullback B S hS g).symm
          (toModulesHom_pullbackModules_eq_modulePullback B S hS f).symm)).symm := by
  rw [pullbackModulesIso_compTwoIso, ← modulePullbackDataTopos_compIso_symm_eq]
  rfl

end EtaleComp

/-! ### The represented morphisms -/

section Represented

variable {T'' T' T : BigFppfOver B S hS} (f : T'' ⟶ T') (g : T' ⟶ T)

/-- The squares `AlgebraicGeometry.Space.representedModuleEquivalencePullbackSquare` compose:
`AlgebraicGeometry.Space.representedModulePullbackIso_comp` read through the equivalences of the
small étale sites of the represented algebraic spaces with those of their schemes. -/
theorem representedModuleEquivalencePullbackSquare_compCoherence :
    Functor.UnderivedCompCoherence (representedModuleEquivalencePullbackSquare B S hS g)
      (representedModuleEquivalencePullbackSquare B S hS f)
      (representedModuleEquivalencePullbackSquare B S hS (f ≫ g))
      (representedSchemeModulePullbackCompIso B S hS f g).hom
      (representedModulePullbackCompIso B S hS f g).hom :=
  Functor.underivedCompCoherence_equivalenceConjSquare _ _ _
    (representedModulePullbackIso_comp B S hS f g (relativelyRepresentable_yoneda_map B S hS f)
      (relativelyRepresentable_yoneda_map B S hS g)
      (relativelyRepresentable_yoneda_map B S hS (f ≫ g)))

/-- The identifications `AlgebraicGeometry.Space.representedAssociatedModulePullbackFunctorIso`
compose: the squares of the comparison of the sites compose, and so do the identifications of
Stacks 03LC (1) (`AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso_comp`). -/
theorem representedAssociatedModulePullbackFunctorIso_compCoherence :
    Functor.UnderivedCompCoherence (representedAssociatedModulePullbackFunctorIso B S hS g)
      (representedAssociatedModulePullbackFunctorIso B S hS f)
      (representedAssociatedModulePullbackFunctorIso B S hS (f ≫ g))
      (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map f)
        ((BigFppfOver.toScheme B S hS).map g)).hom
      (representedModulePullbackCompIso B S hS f g).hom :=
  Functor.underivedCompCoherence_pastedUnderivedSquare
    (representedModuleEquivalencePullbackSquare_compCoherence f g)
    (fun M => _root_.AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso_comp
      (associatedBigEtaleSite B) f.left g.left M)

/-- **The identifications `h_g^* ∘ ε^* ≅ ε^* ∘ r^*` on modules are compatible with the
compositors**: the compositor of Stacks 03D6 followed by the 2-isomorphism of Stacks 03G8 on the
small étale sides, and the compositor of the inverse images of modules on the Zariski sides. -/
theorem representedAssociatedModulePullbackModulesIso_compCoherence :
    Functor.UnderivedCompCoherence (representedAssociatedModulePullbackModulesIso g)
      (representedAssociatedModulePullbackModulesIso f)
      (representedAssociatedModulePullbackModulesIso (f ≫ g))
      (schemeFactorModulePullbackIso ((BigFppfOver.toScheme B S hS).map f)
        ((BigFppfOver.toScheme B S hS).map g) ((BigFppfOver.toScheme B S hS).map (f ≫ g))
        (toScheme_map_comp_eq B S hS f g (f ≫ g) rfl)).hom
      (((RingedToposHom.pullbackModulesCompIso
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS f))
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g))).symm ≪≫
        (smallEtaleRingedToposHom_compTwoIso B S hS (representedSpaceMap B S hS f)
          (representedSpaceMap B S hS g)).pullbackModulesIso) ≪≫
        eqToIso (congrArg (fun m ↦ (smallEtaleRingedToposHom B S hS m).toModulesHom.pullbackModules)
          (representedSpaceMap_comp_eq B S hS f g (f ≫ g) rfl))).hom :=
  Functor.underivedCompCoherence_transferredUnderivedSquare_eqToIso _ _
    (toModulesHom_pullbackModules_eq_modulePullback B S hS
      (representedSpaceMap B S hS f ≫ representedSpaceMap B S hS g)) _ _ _
    (congrArg₂ (fun (a : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) ⥤
          Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
        (b : Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T') ⥤
          Modules.{u, u} B S hS (yoneda.obj T'') (isAlgebraicSpace_yoneda B S hS T'')) => a ⋙ b)
      (toModulesHom_pullbackModules_eq_modulePullback B S hS (representedSpaceMap B S hS g)).symm
      (toModulesHom_pullbackModules_eq_modulePullback B S hS (representedSpaceMap B S hS f)).symm)
    (modulePullbackCompIso B S hS (representedSpaceMap B S hS f) (representedSpaceMap B S hS g)) _
    (pullbackModulesCompIso_symm_trans_compTwoIso (representedSpaceMap B S hS f)
      (representedSpaceMap B S hS g))
    (representedAssociatedModulePullbackFunctorIso_compCoherence f g)
    (fun M => pullbackComp_pullbackIso_compCoherence _ _ _ M)

end Represented

/-! ### The homotopy categories -/

section Homotopy

attribute [local instance 20000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  hasSheafCompose_smallEtale_forget₂_ringCat

/-- `AlgebraicGeometry.Space.representedAssociatedModulePullbackModulesIso_compCoherence` on the
unbounded homotopy categories: every identification and compositor involved is, at the image of
a complex, the image of its underived counterpart applied degreewise. -/
theorem representedHomotopyPullbackCoherence_app {T'' T' T : BigFppfOver B S hS} (f : T'' ⟶ T')
    (g : T' ⟶ T) :
    Functor.UnderivedCompCoherence (representedAssociatedModulePullbackHomotopyIso g)
      (representedAssociatedModulePullbackHomotopyIso f)
      (representedAssociatedModulePullbackHomotopyIso (f ≫ g))
      (schemeFactorMapHomotopyIso ((BigFppfOver.toScheme B S hS).map f)
        ((BigFppfOver.toScheme B S hS).map g) ((BigFppfOver.toScheme B S hS).map (f ≫ g))
        (toScheme_map_comp_eq B S hS f g (f ≫ g) rfl)).hom
      (smallEtalePullbackMapHomotopyFactorIso (representedSpaceMap B S hS f)
        (representedSpaceMap B S hS g) (representedSpaceMap B S hS (f ≫ g))
        (representedSpaceMap_comp_eq B S hS f g (f ≫ g) rfl)).hom := by
  refine Functor.underivedCompCoherence_mapHomotopyCategory
    (ug := representedAssociatedModulePullbackModulesIso g)
    (uf := representedAssociatedModulePullbackModulesIso f)
    (uk := representedAssociatedModulePullbackModulesIso (f ≫ g))
    (cA := (schemeFactorModulePullbackIso ((BigFppfOver.toScheme B S hS).map f)
        ((BigFppfOver.toScheme B S hS).map g) ((BigFppfOver.toScheme B S hS).map (f ≫ g))
        (toScheme_map_comp_eq B S hS f g (f ≫ g) rfl)).hom)
    (cE := (((RingedToposHom.pullbackModulesCompIso
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS f))
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g))).symm ≪≫
        (smallEtaleRingedToposHom_compTwoIso B S hS (representedSpaceMap B S hS f)
          (representedSpaceMap B S hS g)).pullbackModulesIso) ≪≫
        eqToIso (congrArg (fun m ↦ (smallEtaleRingedToposHom B S hS m).toModulesHom.pullbackModules)
          (representedSpaceMap_comp_eq B S hS f g (f ≫ g) rfl))).hom)
    ?_ ?_ ?_ ?_ ?_ ?_
  iterate 3 exact fun K => Functor.mapHomotopyCategoryUnderivedIso_hom_app_quotient _ _ K
  · exact fun K => schemeFactorMapHomotopyIso_hom_app_quotient _ _ _ _ K
  · intro K
    convert smallEtalePullbackMapHomotopyFactorIso_hom_app_quotient (representedSpaceMap B S hS f)
      (representedSpaceMap B S hS g) (representedSpaceMap B S hS (f ≫ g))
      (representedSpaceMap_comp_eq B S hS f g (f ≫ g) rfl) K using 1
  · exact representedAssociatedModulePullbackModulesIso_compCoherence f g

variable (B S hS) in
/-- **The underived identifications are compatible with the underived compositors**: the
proposition `AlgebraicGeometry.Space.RepresentedHomotopyPullbackCoherence`. -/
theorem representedHomotopyPullbackCoherence : RepresentedHomotopyPullbackCoherence B S hS :=
  fun f g => representedHomotopyPullbackCoherence_app f g

variable (B S hS) in
/-- **`ε^*` intertwines the derived pullbacks of the Zariski and the small étale sites,
coherently**, for the canonical pseudofunctoriality of the derived pullback on the small étale
topoi of algebraic spaces, with no hypotheses. -/
def representedDerivedPullbackComparisonCanonicalUnconditional :
    RepresentedDerivedPullbackComparison B S hS (DerivedPullbackComposition.canonical B S hS) :=
  representedDerivedPullbackComparisonCanonical (representedHomotopyPullbackCoherence B S hS)

end Homotopy

end AlgebraicGeometry.Space

end
