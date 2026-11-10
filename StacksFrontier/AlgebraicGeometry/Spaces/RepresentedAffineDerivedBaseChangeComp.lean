module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackCompAssoc
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChangeComp
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapMate
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsCentral
public import StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewisePathComparison
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquareTransport
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# Composition of affine base change isomorphisms, up to a unit

For a commutative square `g₀' ≫ f₀ = f₀' ≫ g₀` of morphisms between objects of the big fppf site
with affine underlying schemes, the two ways of composing the affine base change isomorphisms
`Lg^* Φ_R ≅ Φ_{R'}(- ⊗ᴸ_R R')` of
`AlgebraicGeometry.Space.representedAffineDerivedBaseChangeIso` around the square agree up to
multiplication by a unit of the ring of global functions of the last corner. This file proves the
underived statement: the two composites of the isomorphisms `g^*(M^~) ≅ (R' ⊗_R M)^~` differ by
a unit, because the associated module is fully faithful and every natural endomorphism of
extension of scalars is a scalar multiplication.

The comparisons are stated with target the modules over the structure sheaf of the small étale
ringed topos (`AlgebraicGeometry.Space.representedAffineToposAssociated` and the objects after it),
the spelling in which the derived pullback of algebraic spaces is formed.

## Main results

* `AlgebraicGeometry.Space.representedAffineDerivedBaseChangeIso_hom_app_comparison`: the derived
  isomorphism is computed on complexes by the underived one; in the ringed-topos spelling,
  `AlgebraicGeometry.Space.representedAffineToposDerivedBaseChangeIso_hom_app_comparison`.
* `AlgebraicGeometry.Space.exists_isUnit_representedAffinePath`: the two underived composites
  around the square differ by a unit.
* `AlgebraicGeometry.Space.unitCentralIso`: multiplication by a unit, as a central automorphism of
  `D(A)`.
* `AlgebraicGeometry.Space.representedAffineToposDerivedBaseChange_compat_of_path` and
  `AlgebraicGeometry.Space.exists_representedAffineToposDerivedBaseChange_compat`: the derived
  base change isomorphisms compose around the square up to the same unit.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

/- The filtered colimits used to form the étale sheafification, through Mathlib's instance, so that
the derived categories of `𝒪`-modules below are spelled as in the files of the derived pullback. -/
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance] additive_extendScalars_representedAffineRingHom
  additive_pullbackModules_representedSpaceMap

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The additive structure of `𝒪_X`-modules, the instance with which the homotopy categories of
degreewise pullback are formed. -/
local instance (priority := 6000) preadditive_smallEtaleModules (X : AlgebraicSpaces B S hS) :
    Preadditive (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
  SheafOfModules.instPreadditive _

section Edge

variable {U' U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] (g : U' ⟶ U)

/-- **The affine base change isomorphism is induced by the underived one**: after the comparison
of derived extension of scalars, it is the comparison of the derived pullback followed by the
degreewise isomorphism `g^*(M^~) ≅ (R' ⊗_R M)^~`. -/
theorem representedAffineDerivedBaseChangeIso_hom_app_comparison
    (K : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (representedAffineDerivedBaseChangeIso B S hS g).hom.app (DerivedCategory.Q.obj K) ≫
        (representedAffineDerivedAssociated B S hS U').map
          ((representedAffineDerivedExtension B S hS g).comparison.app K) =
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).map
          ((representedAffineDerivedAssociatedFactors B S hS U).hom.app K) ≫
        (smallEtaleDerivedModulePullbackComparison B S hS (representedSpaceMap B S hS g)).app
          ((representedAffineHomotopyAssociated B S hS U).obj K) ≫
        DerivedCategory.Qh.map ((representedAffineHomotopyPullbackIso B S hS g).hom.app K) ≫
        (representedAffineDerivedAssociatedFactors B S hS U').inv.app
          (((ModuleCat.extendScalars.{u, u, u}
            (representedAffineCommRingCatHom B S hS g).hom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) := by
  have h := Functor.leftDerived_fac_app _ ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (representedAffineDerivedExtension B S hS g).comparison
        (representedAffineDerivedAssociated B S hS U'))
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _
    (representedAffineBaseChangeComparison B S hS g) K
  simp only [NatTrans.comp_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    Category.id_comp] at h
  exact h.trans (representedAffineBaseChangeComparison_app B S hS g K)

end Edge

section Composition

variable {T'' T' T : BigFppfOver B S hS}

/-- The map of rings of global functions of a composite is the composite of the maps. -/
theorem representedAffineRingHom_comp (a : T'' ⟶ T') (b : T' ⟶ T) :
    (representedAffineCommRingCatHom B S hS (a ≫ b)).hom =
      (representedAffineCommRingCatHom B S hS a).hom.comp
        (representedAffineCommRingCatHom B S hS b).hom := by
  simp only [representedAffineCommRingCatHom, Functor.map_comp, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp]

end Composition

/-! ### The ringed-topos spelling

The associated module and its derived version, stated with target the modules over the structure
sheaf of the small étale ringed topos, which is the spelling of the derived pullback. Each object
is the corresponding one of
`StacksFrontier/AlgebraicGeometry/Spaces/AffineQuasicoherentDerivedBaseChange.lean`;
stating them once in this spelling keeps the comparisons below inside one spelling. -/

section Topos

/-- Pullback of modules along the morphisms `X ⟶ Y` of algebraic spaces, as a family of functors
indexed by the morphisms. -/
def smallEtaleModulePullbackFamily (X Y : AlgebraicSpaces B S hS) (f : X ⟶ Y) :
    SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y) ⥤
      SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X) :=
  Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f).toModulesHom

instance additive_smallEtaleModulePullbackFamily (X Y : AlgebraicSpaces B S hS) (f : X ⟶ Y) :
    (smallEtaleModulePullbackFamily B S hS X Y f).Additive :=
  pullbackModules_smallEtale_additive f

variable (W : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]

/-- The associated module `M ↦ M^~`, in the ringed-topos spelling. -/
def representedAffineToposAssociated :
    ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) ⥤
      SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
        ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩) :=
  representedAffineAssociated B S hS W

instance additive_representedAffineToposAssociated :
    (representedAffineToposAssociated B S hS W).Additive :=
  additive_representedAffineAssociated B S hS W

/-- The associated module is fully faithful, in the ringed-topos spelling. -/
def representedAffineToposAssociatedFullyFaithful :
    (representedAffineToposAssociated B S hS W).FullyFaithful :=
  representedAffineAssociatedFullyFaithful B S hS W

/-- The degreewise associated module in the homotopy category, in the ringed-topos spelling. -/
abbrev representedAffineToposHomotopyAssociated :
    CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)) ℤ ⥤
      HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
        ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)) (ComplexShape.up ℤ) :=
  (representedAffineToposAssociated B S hS W).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomotopyCategory.quotient _ _

/-- `Φ : D(R) ⥤ D(𝒪)`, in the ringed-topos spelling. -/
def representedAffineToposDerivedAssociated :
    DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)) ⥤
      DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
        ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)) :=
  representedAffineDerivedAssociated B S hS W

/-- `Φ` on a localized complex is the localization of the degreewise associated module, in the
ringed-topos spelling. -/
def representedAffineToposDerivedFactors :
    DerivedCategory.Q ⋙ representedAffineToposDerivedAssociated B S hS W ≅
      representedAffineToposHomotopyAssociated B S hS W ⋙ DerivedCategory.Qh :=
  representedAffineDerivedAssociatedFactors B S hS W

end Topos

section ToposEdge

variable {U' U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] (g : U' ⟶ U)

/-- `g^*(M^~) ≅ (R' ⊗_R M)^~`, in the ringed-topos spelling. -/
def representedAffineToposPullbackIso :
    representedAffineToposAssociated B S hS U ⋙
        Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          (X := smallEtaleRingedTopos B S hS _)
          (Y := smallEtaleRingedTopos B S hS _)
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)).toModulesHom ≅
      ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g).hom ⋙
        representedAffineToposAssociated B S hS U' :=
  representedAffineAssociatedPullbackIso B S hS g

/-- The degreewise pullback isomorphism of the homotopy categories is induced degreewise by
`AlgebraicGeometry.Space.representedAffineToposPullbackIso`. -/
theorem representedAffineHomotopyPullbackIso_hom_eq :
    (representedAffineHomotopyPullbackIso B S hS g).hom =
      (Stacks.Homology.homotopyEdgeIso (representedAffineToposPullbackIso B S hS g)).hom :=
  rfl

/-- The affine base change isomorphism `Lg^* Φ_R ≅ Φ_{R'}(- ⊗ᴸ_R R')`, in the ringed-topos
spelling. -/
def representedAffineToposDerivedBaseChangeIso :
    representedAffineToposDerivedAssociated B S hS U ⋙
        smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g) ≅
      (representedAffineDerivedExtension B S hS g).functor ⋙
        representedAffineToposDerivedAssociated B S hS U' :=
  representedAffineDerivedBaseChangeIso B S hS g

/-- `AlgebraicGeometry.Space.representedAffineDerivedBaseChangeIso_hom_app_comparison` in the
ringed-topos spelling. -/
theorem representedAffineToposDerivedBaseChangeIso_hom_app_comparison
    (K : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (representedAffineToposDerivedBaseChangeIso B S hS g).hom.app (DerivedCategory.Q.obj K) ≫
        (representedAffineToposDerivedAssociated B S hS U').map
          ((representedAffineDerivedExtension B S hS g).comparison.app K) =
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).map
          ((representedAffineToposDerivedFactors B S hS U).hom.app K) ≫
        (smallEtaleDerivedModulePullbackComparison B S hS (representedSpaceMap B S hS g)).app
          ((representedAffineToposHomotopyAssociated B S hS U).obj K) ≫
        DerivedCategory.Qh.map ((Stacks.Homology.homotopyEdgeIso
          (representedAffineToposPullbackIso B S hS g)).hom.app K) ≫
        (representedAffineToposDerivedFactors B S hS U').inv.app
          (((ModuleCat.extendScalars.{u, u, u}
            (representedAffineCommRingCatHom B S hS g).hom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) := by
  have h := representedAffineDerivedBaseChangeIso_hom_app_comparison B S hS g K
  rw [representedAffineHomotopyPullbackIso_hom_eq] at h
  exact h

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] in
/-- Derived extension of scalars followed by `Φ_{R'}` is a left derived functor, in the
ringed-topos spelling. -/
theorem isLeftDerivedFunctor_representedAffineToposDerivedExtension_comp :
    ((representedAffineDerivedExtension B S hS g).functor ⋙
        representedAffineToposDerivedAssociated B S hS U').IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (representedAffineDerivedExtension B S hS g).comparison
          (representedAffineToposDerivedAssociated B S hS U'))
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) :=
  isLeftDerivedFunctor_representedAffineDerivedExtension_comp B S hS g

end ToposEdge

section ToposSquare

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)

/-- Degreewise pullback around a commutative square, compared with degreewise pullback along
`f' ≫ g`, is induced by the composition law of pullbacks of modules followed by the transport
along `g' ≫ f = f' ≫ g`. -/
theorem smallEtaleUnderivedPullbackSquareIso_eq_mapHomotopyCategoryCompIso :
    smallEtaleUnderivedPullbackSquareIso B S hS f g f' g' w =
      Functor.mapHomotopyCategoryCompIso (smallEtaleModulePullbackCompIso B S hS g' f)
          (ComplexShape.up ℤ) ≪≫
        eqToIso (congrArg
          (fun t => (smallEtaleModulePullbackFamily B S hS X' Y t).mapHomotopyCategory
          (ComplexShape.up ℤ)) w) := by
  rw [smallEtaleUnderivedPullbackSquareIso_eq, smallEtaleUnderivedPullbackCompIso_eq]
  rfl

end ToposSquare

section Square

variable {U V U' V' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
  (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U) (w₀ : g₀' ≫ f₀ = f₀' ≫ g₀)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V')] in
include w₀ in
theorem representedSpaceMap_square :
    representedSpaceMap B S hS g₀' ≫ representedSpaceMap B S hS f₀ =
      representedSpaceMap B S hS f₀' ≫ representedSpaceMap B S hS g₀ := by
  rw [representedSpaceMap_comp, w₀, ← representedSpaceMap_comp]

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V')] in
include w₀ in
theorem representedAffineRingHom_square :
    (representedAffineCommRingCatHom B S hS g₀').hom.comp
        (representedAffineCommRingCatHom B S hS f₀).hom =
      (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom := by
  rw [← representedAffineRingHom_comp, w₀]


/-- The module-level comparison along the path through `V'`. -/
def representedAffinePathLeft :
    representedAffineToposAssociated B S hS V ⋙
      Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS _) (Y := smallEtaleRingedTopos B S hS _)
        (smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS f₀' ≫ representedSpaceMap B S hS g₀)).toModulesHom ⟶
      ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom ⋙
        representedAffineToposAssociated B S hS U' :=
  Stacks.Homology.pathNatTrans (smallEtaleModulePullbackCompIso B S hS
      (representedSpaceMap B S hS f₀') (representedSpaceMap B S hS g₀))
    (representedAffineToposPullbackIso B S hS g₀)
    (representedAffineToposPullbackIso B S hS f₀')
    (RingTheory.TorIndependence.extendScalarsCompInvOfEq.{u, u, u, u}
      (representedAffineCommRingCatHom B S hS g₀).hom
      (representedAffineCommRingCatHom B S hS f₀').hom
      (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom
      (representedAffineRingHom_comp B S hS f₀' g₀).symm)

instance isIso_representedAffinePathLeft : IsIso (representedAffinePathLeft B S hS g₀ f₀') :=
  have : IsIso (RingTheory.TorIndependence.extendScalarsCompInvOfEq.{u, u, u, u}
      (representedAffineCommRingCatHom B S hS g₀).hom
      (representedAffineCommRingCatHom B S hS f₀').hom
      (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom
      (representedAffineRingHom_comp B S hS f₀' g₀).symm) := by
    unfold RingTheory.TorIndependence.extendScalarsCompInvOfEq
    infer_instance
  Stacks.Homology.isIso_pathNatTrans _ _ _ _

/-- The module-level comparison along the path through `U`, transported along the commutativity
of the square. -/
def representedAffinePathRight :
    representedAffineToposAssociated B S hS V ⋙
      Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS _) (Y := smallEtaleRingedTopos B S hS _)
        (smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS f₀' ≫ representedSpaceMap B S hS g₀)).toModulesHom ⟶
      ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom ⋙
        representedAffineToposAssociated B S hS U' :=
  Functor.whiskerLeft (representedAffineToposAssociated B S hS V)
      (eqToHom (congrArg (smallEtaleModulePullbackFamily B S hS _ _)
        (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀).symm)) ≫
    Stacks.Homology.pathNatTrans (smallEtaleModulePullbackCompIso B S hS
      (representedSpaceMap B S hS g₀') (representedSpaceMap B S hS f₀))
    (representedAffineToposPullbackIso B S hS f₀)
    (representedAffineToposPullbackIso B S hS g₀')
    (RingTheory.TorIndependence.extendScalarsCompInvOfEq.{u, u, u, u}
      (representedAffineCommRingCatHom B S hS f₀).hom
      (representedAffineCommRingCatHom B S hS g₀').hom
      (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom
      (representedAffineRingHom_square B S hS f₀ g₀ f₀' g₀' w₀))

instance isIso_representedAffinePathRight :
    IsIso (representedAffinePathRight B S hS f₀ g₀ f₀' g₀' w₀) :=
  have : IsIso (RingTheory.TorIndependence.extendScalarsCompInvOfEq.{u, u, u, u}
      (representedAffineCommRingCatHom B S hS f₀).hom
      (representedAffineCommRingCatHom B S hS g₀').hom
      (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom
      (representedAffineRingHom_square B S hS f₀ g₀ f₀' g₀' w₀)) := by
    unfold RingTheory.TorIndependence.extendScalarsCompInvOfEq
    infer_instance
  @IsIso.comp_isIso _ _ _ _ _ _ _
    (Functor.isoWhiskerLeft (representedAffineToposAssociated B S hS V)
      (eqToIso (congrArg (smallEtaleModulePullbackFamily B S hS _ _)
        (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀).symm))).isIso_hom
    (Stacks.Homology.isIso_pathNatTrans _ _ _ _)

/-- **The two module-level paths differ by a unit.**  They are two isomorphisms
`g'^* f^*` and `f'^* g^*` of `M^~` with `(A' ⊗_R M)^~`; the associated module is fully faithful
and every natural endomorphism of extension of scalars is a scalar multiplication. -/
theorem exists_isUnit_representedAffinePath :
    ∃ c : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤), IsUnit c ∧
      ∀ M, (representedAffinePathLeft B S hS g₀ f₀').app M =
        (representedAffinePathRight B S hS f₀ g₀ f₀' g₀' w₀).app M ≫
          (representedAffineToposAssociated B S hS U').map (c • 𝟙 _) := by
  let hF := representedAffineToposAssociatedFullyFaithful B S hS U'
  obtain ⟨δ, hδ⟩ := Stacks.Homology.exists_app_eq_comp_map
    (F₀ := representedAffineToposAssociated B S hS V)
    (F₂ := representedAffineToposAssociated B S hS U')
    (yc := ModuleCat.extendScalars.{u, u, u}
      (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom)
    (representedAffinePathLeft B S hS g₀ f₀') (representedAffinePathRight B S hS f₀ g₀ f₀' g₀' w₀)
    (isIso_representedAffinePathRight B S hS f₀ g₀ f₀' g₀' w₀) hF
  obtain ⟨δ', hδ'⟩ := Stacks.Homology.exists_app_eq_comp_map
    (F₀ := representedAffineToposAssociated B S hS V)
    (F₂ := representedAffineToposAssociated B S hS U')
    (yc := ModuleCat.extendScalars.{u, u, u}
      (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom)
    (representedAffinePathRight B S hS f₀ g₀ f₀' g₀' w₀) (representedAffinePathLeft B S hS g₀ f₀')
    (isIso_representedAffinePathLeft B S hS g₀ f₀') hF
  obtain ⟨c, hc⟩ := ModuleCat.ExtendScalars.natTrans_app_eq_smul
    (f := (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom)
    (P := (⊤ : ObjectProperty (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))))
    trivial (Functor.whiskerLeft (⊤ : ObjectProperty _).ι δ)
  obtain ⟨d, hd⟩ := ModuleCat.ExtendScalars.natTrans_app_eq_smul
    (f := (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom)
    (P := (⊤ : ObjectProperty (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))))
    trivial (Functor.whiskerLeft (⊤ : ObjectProperty _).ι δ')
  have hcM : ∀ M, δ.app M = c • 𝟙 ((ModuleCat.extendScalars.{u, u, u}
      (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom).obj M) := fun M => hc ⟨M, trivial⟩
  have hdM : ∀ M, δ'.app M = d • 𝟙 ((ModuleCat.extendScalars.{u, u, u}
      (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom).obj M) := fun M => hd ⟨M, trivial⟩
  refine ⟨c, ?_, fun M => (hδ M).trans (congrArg (CategoryStruct.comp
    ((representedAffinePathRight B S hS f₀ g₀ f₀' g₀' w₀).app M))
    (congrArg (representedAffineToposAssociated B S hS U').map (hcM M)))⟩
  refine IsUnit.of_mul_eq_one (b := d) ?_
  let R := ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
  have hLR : IsIso ((representedAffinePathLeft B S hS g₀ f₀').app R) :=
    @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ (isIso_representedAffinePathLeft B S hS g₀ f₀') R
  have h₁ : (representedAffinePathLeft B S hS g₀ f₀').app R ≫ 𝟙 _ =
      (representedAffinePathLeft B S hS g₀ f₀').app R ≫
        ((representedAffineToposAssociated B S hS U').map (δ'.app R) ≫
          (representedAffineToposAssociated B S hS U').map (δ.app R)) :=
    (Category.comp_id _).trans ((hδ R).trans ((eq_whisker (hδ' R) _).trans (Category.assoc _ _ _)))
  have h₂ := (@cancel_epi _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _ hLR) _ _).1 h₁
  have h₃ : δ'.app R ≫ δ.app R = 𝟙 _ :=
    hF.map_injective (((representedAffineToposAssociated B S hS U').map_comp _ _).trans
      (h₂.symm.trans ((representedAffineToposAssociated B S hS U').map_id _).symm))
  rw [hcM, hdM, Linear.smul_comp, Category.id_comp, smul_smul] at h₃
  rw [mul_comm]
  exact ModuleCat.ExtendScalars.eq_one_of_smul_id_eq_id _ h₃

/-- Multiplication by a scalar on the degreewise image of a complex is the degreewise image of
multiplication by the scalar. -/
theorem toCatCenter_app_mapHomologicalComplex {A : Type u} [CommRing A] {D : Type*} [Category D]
    [Preadditive D] (F : D ⥤ ModuleCat.{u} A) [F.Additive] (c : A) (K : CochainComplex D ℤ) :
    (Linear.toCatCenter A (CochainComplex (ModuleCat.{u} A) ℤ) c).app
        ((F.mapHomologicalComplex _).obj K) =
      (NatTrans.mapHomologicalComplex (c • 𝟙 F) (ComplexShape.up ℤ)).app K := by
  ext n
  simp

/-- Multiplication by a unit, as a central automorphism of `D(A)`. -/
def unitCentralIso {A : Type u} [CommRing A] (c : A) (hc : IsUnit c) :
    𝟭 (DerivedCategory (ModuleCat.{u} A)) ≅ 𝟭 _ where
  hom := (Linear.toCatCenter A _ c).asHom
  inv := (Linear.toCatCenter A _ (hc.unit⁻¹ : Aˣ)).asHom
  hom_inv_id := by
    ext X
    simp [smul_smul]
  inv_hom_id := by
    ext X
    simp [smul_smul]

include w₀ in
/-- **The affine base change isomorphisms compose around a square, up to a unit `c`**, as soon as
the two underived composites around the square differ by `c`. -/
theorem representedAffineToposDerivedBaseChange_compat_of_path
    (c : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) (hc : IsUnit c)
    (hpath : representedAffinePathLeft B S hS g₀ f₀' =
      representedAffinePathRight B S hS f₀ g₀ f₀' g₀' w₀ ≫
        Functor.whiskerRight (c • 𝟙 (ModuleCat.extendScalars.{u, u, u}
          (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom))
          (representedAffineToposAssociated B S hS U'))
    (N : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) :
    (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS f₀')).map
          ((representedAffineToposDerivedBaseChangeIso B S hS g₀).hom.app N) ≫
        (representedAffineToposDerivedBaseChangeIso B S hS f₀').hom.app
          ((representedAffineDerivedExtension B S hS g₀).functor.obj N) ≫
        (representedAffineToposDerivedAssociated B S hS U').map
          ((RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
              (representedAffineCommRingCatHom B S hS g₀).hom
              (representedAffineCommRingCatHom B S hS f₀').hom
              (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom
              (representedAffineRingHom_comp B S hS f₀' g₀).symm).hom.app N) =
      (smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS f₀')
          (representedSpaceMap B S hS g₀)).hom.app
          ((representedAffineToposDerivedAssociated B S hS V).obj N) ≫
        (smallEtaleDerivedModulePullbackSquareIso B S hS (representedSpaceMap B S hS f₀)
          (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
          (representedSpaceMap B S hS g₀')
          (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)).inv.app
          ((representedAffineToposDerivedAssociated B S hS V).obj N) ≫
        (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).map
          ((representedAffineToposDerivedBaseChangeIso B S hS f₀).hom.app N) ≫
        (representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app
          ((representedAffineDerivedExtension B S hS f₀).functor.obj N) ≫
        (representedAffineToposDerivedAssociated B S hS U').map
          ((RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
              (representedAffineCommRingCatHom B S hS f₀).hom
              (representedAffineCommRingCatHom B S hS g₀').hom
              (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom
              (representedAffineRingHom_square B S hS f₀ g₀ f₀' g₀' w₀)).hom.app N) ≫
        (representedAffineToposDerivedAssociated B S hS U').map
          ((unitCentralIso c hc).hom.app
            ((representedAffineDerivedExtension B S hS (f₀' ≫ g₀)).functor.obj N)) := by
  have : ∀ t : (⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩,
      (smallEtaleModulePullbackFamily B S hS _ _ t).Additive := fun t =>
    additive_smallEtaleModulePullbackFamily B S hS _ _ t
  refine Stacks.Homology.paths_comp_eq_quotient
    (Ψ := smallEtaleModulePullbackFamily B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩
      ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
    (fun f ↦ smallEtaleDerivedModulePullback B S hS f)
    (fun f ↦ smallEtaleDerivedModulePullbackComparison B S hS f)
    (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)
    (smallEtaleModulePullbackCompIso B S hS (representedSpaceMap B S hS f₀')
      (representedSpaceMap B S hS g₀))
    (smallEtaleModulePullbackCompIso B S hS (representedSpaceMap B S hS g₀')
      (representedSpaceMap B S hS f₀))
    (representedAffineToposPullbackIso B S hS g₀) (representedAffineToposPullbackIso B S hS f₀')
    (representedAffineToposPullbackIso B S hS f₀) (representedAffineToposPullbackIso B S hS g₀')
    (RingTheory.TorIndependence.extendScalarsCompInvOfEq.{u, u, u, u}
      (representedAffineCommRingCatHom B S hS g₀).hom
      (representedAffineCommRingCatHom B S hS f₀').hom
      (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom
      (representedAffineRingHom_comp B S hS f₀' g₀).symm)
    (RingTheory.TorIndependence.extendScalarsCompInvOfEq.{u, u, u, u}
      (representedAffineCommRingCatHom B S hS f₀).hom
      (representedAffineCommRingCatHom B S hS g₀').hom
      (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom
      (representedAffineRingHom_square B S hS f₀ g₀ f₀' g₀' w₀))
    (c • 𝟙 (ModuleCat.extendScalars.{u, u, u}
        (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom))
    rfl rfl (smallEtaleUnderivedPullbackCompIso_eq B S hS _ _)
    (smallEtaleUnderivedPullbackCompIso_eq B S hS _ _)
    (Q₀ := DerivedCategory.Q) (P₀ := DerivedCategory.Qh)
    (e₀ := representedAffineToposDerivedFactors B S hS V)
    (e₁ := representedAffineToposDerivedFactors B S hS V')
    (e₁' := representedAffineToposDerivedFactors B S hS U)
    (e₂ := representedAffineToposDerivedFactors B S hS U')
    (κ₁ := (representedAffineDerivedExtension B S hS g₀).comparison)
    (κ₂ := (representedAffineDerivedExtension B S hS f₀').comparison)
    (κ₁' := (representedAffineDerivedExtension B S hS f₀).comparison)
    (κ₂' := (representedAffineDerivedExtension B S hS g₀').comparison)
    (κ := (representedAffineDerivedExtension B S hS (f₀' ≫ g₀)).comparison)
    (ℓ₁ := smallEtaleDerivedModulePullbackComparison B S hS (representedSpaceMap B S hS g₀))
    (ℓ₂ := smallEtaleDerivedModulePullbackComparison B S hS (representedSpaceMap B S hS f₀'))
    (ℓ₁' := smallEtaleDerivedModulePullbackComparison B S hS (representedSpaceMap B S hS f₀))
    (ℓ₂' := smallEtaleDerivedModulePullbackComparison B S hS (representedSpaceMap B S hS g₀'))
    (β₁ := representedAffineToposDerivedBaseChangeIso B S hS g₀)
    (β₂ := representedAffineToposDerivedBaseChangeIso B S hS f₀')
    (β₁' := representedAffineToposDerivedBaseChangeIso B S hS f₀)
    (β₂' := representedAffineToposDerivedBaseChangeIso B S hS g₀')
    (g := smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS f₀')
      (representedSpaceMap B S hS g₀))
    (g₁ := smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS g₀')
      (representedSpaceMap B S hS f₀))
    (g' := smallEtaleDerivedModulePullbackSquareIso B S hS (representedSpaceMap B S hS f₀)
      (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
      (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀))
    (γ := smallEtaleUnderivedPullbackCompIso B S hS (representedSpaceMap B S hS f₀')
      (representedSpaceMap B S hS g₀))
    (γ₁ := smallEtaleUnderivedPullbackCompIso B S hS (representedSpaceMap B S hS g₀')
      (representedSpaceMap B S hS f₀))
    (γ' := smallEtaleUnderivedPullbackSquareIso B S hS (representedSpaceMap B S hS f₀)
      (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
      (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀))
    (ε := (RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
              (representedAffineCommRingCatHom B S hS g₀).hom
              (representedAffineCommRingCatHom B S hS f₀').hom
              (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom
              (representedAffineRingHom_comp B S hS f₀' g₀).symm).hom)
    (ε' := (RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
              (representedAffineCommRingCatHom B S hS f₀).hom
              (representedAffineCommRingCatHom B S hS g₀').hom
              (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom
              (representedAffineRingHom_square B S hS f₀ g₀ f₀' g₀' w₀)).hom)
    (t := (unitCentralIso c hc).hom)
    (τ := (Linear.toCatCenter Γ((BigFppfOver.toScheme B S hS).obj U', ⊤) _ c).asHom)
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (isLeftDerivedFunctor_representedAffineToposDerivedExtension_comp B S hS (f₀' ≫ g₀))
    ?ht ?hg ?h₁ (toCatCenter_app_mapHomologicalComplex _ c)
    (Stacks.Homology.app_eq_of_pathNatTrans_eq
        (Ψ := smallEtaleModulePullbackFamily B S hS
          ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩
          ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
        (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀) _ _ _ _ _ _ _ _ _ hpath)
    ?hε ?hβ₁ ?hβ₂ ?hε' ?hβ₁' ?hβ₂' N
  case hg =>
    exact smallEtaleDerivedModulePullbackCompIso_hom_app_comparison B S hS
      (representedSpaceMap B S hS f₀') (representedSpaceMap B S hS g₀)
  case h₁ =>
    exact smallEtaleDerivedModulePullbackCompIso_hom_app_comparison B S hS
      (representedSpaceMap B S hS g₀') (representedSpaceMap B S hS f₀)
  case hβ₁ =>
    exact representedAffineToposDerivedBaseChangeIso_hom_app_comparison B S hS g₀
  case hβ₂ =>
    exact representedAffineToposDerivedBaseChangeIso_hom_app_comparison B S hS f₀'
  case hβ₁' =>
    exact representedAffineToposDerivedBaseChangeIso_hom_app_comparison B S hS f₀
  case hβ₂' =>
    exact representedAffineToposDerivedBaseChangeIso_hom_app_comparison B S hS g₀'
  case hε =>
    exact RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq_hom_app_comparison
      _ _ _ _
  case hε' =>
    exact RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq_hom_app_comparison
      _ _ _ _
  case ht =>
    intro K
    have h₃ : DerivedCategory.Q.map (c • 𝟙 K) =
        (unitCentralIso c hc).hom.app (DerivedCategory.Q.obj K) := by
      rw [Functor.map_smul, CategoryTheory.Functor.map_id]
      rfl
    have h₂ := (representedAffineToposDerivedFactors B S hS U').inv.naturality (c • 𝟙 K)
    have h₄ := congrArg (representedAffineToposDerivedAssociated B S hS U').map h₃
    exact (congrArg (CategoryStruct.comp ((representedAffineToposDerivedFactors B S hS U').inv.app
      K)) h₄.symm).trans h₂.symm

include w₀ in
/-- **The affine base change isomorphisms compose around a square, up to a unit.** -/
theorem exists_representedAffineToposDerivedBaseChange_compat :
    ∃ t : 𝟭 (DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U', ⊤))) ≅ 𝟭 _,
      ∀ N, (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS f₀')).map
          ((representedAffineToposDerivedBaseChangeIso B S hS g₀).hom.app N) ≫
        (representedAffineToposDerivedBaseChangeIso B S hS f₀').hom.app
          ((representedAffineDerivedExtension B S hS g₀).functor.obj N) ≫
        (representedAffineToposDerivedAssociated B S hS U').map
          ((RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
              (representedAffineCommRingCatHom B S hS g₀).hom
              (representedAffineCommRingCatHom B S hS f₀').hom
              (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom
              (representedAffineRingHom_comp B S hS f₀' g₀).symm).hom.app N) =
      (smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS f₀')
          (representedSpaceMap B S hS g₀)).hom.app
          ((representedAffineToposDerivedAssociated B S hS V).obj N) ≫
        (smallEtaleDerivedModulePullbackSquareIso B S hS (representedSpaceMap B S hS f₀)
          (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
          (representedSpaceMap B S hS g₀')
          (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)).inv.app
          ((representedAffineToposDerivedAssociated B S hS V).obj N) ≫
        (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).map
          ((representedAffineToposDerivedBaseChangeIso B S hS f₀).hom.app N) ≫
        (representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app
          ((representedAffineDerivedExtension B S hS f₀).functor.obj N) ≫
        (representedAffineToposDerivedAssociated B S hS U').map
          ((RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
              (representedAffineCommRingCatHom B S hS f₀).hom
              (representedAffineCommRingCatHom B S hS g₀').hom
              (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom
              (representedAffineRingHom_square B S hS f₀ g₀ f₀' g₀' w₀)).hom.app N) ≫
        (representedAffineToposDerivedAssociated B S hS U').map
          (t.hom.app ((representedAffineDerivedExtension B S hS (f₀' ≫ g₀)).functor.obj N)) := by
  obtain ⟨c, hc, hpath⟩ := exists_isUnit_representedAffinePath B S hS f₀ g₀ f₀' g₀' w₀
  exact ⟨unitCentralIso c hc, representedAffineToposDerivedBaseChange_compat_of_path B S hS f₀ g₀
    f₀' g₀' w₀ c hc (NatTrans.ext (funext fun M => (hpath M).trans rfl))⟩

end Square

end AlgebraicGeometry.Space

end
