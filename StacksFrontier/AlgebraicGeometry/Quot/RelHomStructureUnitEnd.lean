module

public import StacksFrontier.AlgebraicGeometry.Quot.NegativeExtLocusHomFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRingHomComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRingHomSiteSections
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsTerminalChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedExtLeray

/-!
# Endomorphisms of the structure object and the derived pullback

For an algebraic space `X` the endomorphisms of the structure object `𝒪_X[0]` of `D(𝒪_X)` are the
global regular functions of `X` (`AlgebraicGeometry.Space.structureEndEquiv`), compatibly with
the ring operations.  This file shows that the derived pullback along a morphism `f : X ⟶ Y` acts
on them, read through `Lf^*𝒪_Y ≅ 𝒪_X`, by the ring map on global regular functions of
Stacks 0732, and that for the algebraic space of a scheme `T` of the site the global regular
functions are `Γ(T, 𝒪_T)`, the ring map along a morphism of schemes being pullback of functions.
These are the inputs of the naturality, in the test scheme, of the computation of step (L) of the
proof of Stacks 0DLC, part (3).  Nothing is registered.

## Main results

* `AlgebraicGeometry.Space.structureEndEquiv` and `structureEndEquiv_mul`, `_add`, `_zero`,
  `_one`.
* `AlgebraicGeometry.Space.smallEtaleDerivedPullStructureIso_conj_pull_map_structureEndEquiv`:
  `Lf^*` acts on `End(𝒪_Y[0])` by `globalSectionsRingHomSite f`.
* `AlgebraicGeometry.Space.schemeGlobalSectionsEquiv` and
  `AlgebraicGeometry.Space.schemeGlobalSectionsEquiv_naturality`.

## References

* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

section UnitIsoNaturality

universe c c'

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] HasDerivedCategory.standard hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X : AlgebraicGeometry.RingedTopos.{u, c, u}}
  {Y : AlgebraicGeometry.RingedTopos.{u, c', u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (f : AlgebraicGeometry.RingedToposHom X Y)

/-- **The identification `Lf^*(O_D[0]) ≅ O_C[0]` is natural in endomorphisms of `O_D`**: the
derived pullback of an endomorphism `φ` of the free module of rank one in degree zero is, under
`derivedPullbackUnitIsoGeneral`, the endomorphism `f^*φ` transported to `O_C` through
`f^*O_D ≅ O_C`. -/
theorem derivedPullbackUnitIsoGeneral_hom_naturality
    (φ : _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
      _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (derivedPullback f).map ((DerivedCategory.singleFunctor _ 0).map φ) ≫
        (derivedPullbackUnitIsoGeneral f).hom =
      (derivedPullbackUnitIsoGeneral f).hom ≫
        (DerivedCategory.singleFunctor _ 0).map
          ((Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso f.toModulesHom).hom ≫
            f.toModulesHom.pullbackModules.map φ ≫
              (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso
                f.toModulesHom).inv) := by
  have h1 := (DerivedCategory.singleFunctorIsoCompQ
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).hom.naturality φ
  have h2 := fun hK hflat => flatPullbackIso_naturality f
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map φ) hK hK hflat hflat
  have h3 := (HomologicalComplex.singleMapHomologicalComplex f.toModulesHom.pullbackModules
    (ComplexShape.up ℤ) 0).hom.naturality φ
  have h4 := (DerivedCategory.singleFunctorIsoCompQ
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).inv.naturality
      (f.toModulesHom.pullbackModules.map φ)
  simp only [Functor.comp_map] at h1 h3 h4
  simp only [derivedPullbackUnitIsoGeneral, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, Iso.app_inv, Category.assoc]
  rw [← Functor.map_comp_assoc, h1, Functor.map_comp_assoc]
  rw (transparency := .default) [reassoc_of% (h2 _ _)]
  rw [← Functor.map_comp_assoc DerivedCategory.Q, h3, Functor.map_comp_assoc]
  rw (transparency := .default) [reassoc_of% h4]
  rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_assoc]

/-- **The identification `Lf^*(O_D[0]) ≅ O_C[0]` carries multiplication by a global section to
multiplication by its image**: the derived pullback of multiplication by a global section `a` of
`O_D` is, under `derivedPullbackUnitIsoGeneral`, multiplication by the image of `a` under the ring
map `Γ(D, O_D) ⟶ Γ(C, O_C)` of `f`. -/
theorem derivedPullbackUnitIsoGeneral_hom_naturality_unitEnd
    (a : RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj) :
    (derivedPullback f).map ((DerivedCategory.singleFunctor _ 0).map
        (Stacks.Cohomology.SiteModules.unitEnd _ a)) ≫ (derivedPullbackUnitIsoGeneral f).hom =
      (derivedPullbackUnitIsoGeneral f).hom ≫
        (DerivedCategory.singleFunctor _ 0).map (Stacks.Cohomology.SiteModules.unitEnd _
          (Stacks.Cohomology.SiteModules.globalSectionsRingHom f.toRingedToposModulesHom a)) := by
  rw [Stacks.Cohomology.SiteModules.unitEnd_globalSectionsRingHom,
    Stacks.Cohomology.SiteModules.pushforwardUnitEndMap,
    ← AlgebraicGeometry.RingedToposHom.toModulesHom_eq_toRingedToposModulesHom]
  exact derivedPullbackUnitIsoGeneral_hom_naturality f _

end UnitIsoNaturality

end Stacks.Cohomology.DerivedPullbackOfToposHom

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (B S hS) in
/-- Global regular functions as endomorphisms of the structure object in degree zero. -/
def structureEndEquiv (X : AlgebraicSpaces B S hS) :
    RingCat.sectionsSubring (structureRingSheaf B S hS X).obj ≃
      (structureObject B S hS X ⟶ structureObject B S hS X) :=
  (Stacks.Cohomology.SiteModules.unitEndEquiv (structureRingSheaf B S hS X)).trans
    (Functor.FullyFaithful.ofFullyFaithful
      (DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0)).homEquiv

/-- `structureEndEquiv` is the image in degree zero of multiplication by the global section. -/
theorem structureEndEquiv_apply (X : AlgebraicSpaces B S hS)
    (a : RingCat.sectionsSubring (structureRingSheaf B S hS X).obj) :
    structureEndEquiv B S hS X a =
      (DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).map
        (Stacks.Cohomology.SiteModules.unitEnd (structureRingSheaf B S hS X) a) :=
  rfl

/-- `AlgebraicGeometry.Space.structureEndEquiv` turns multiplication into composition. -/
theorem structureEndEquiv_mul (X : AlgebraicSpaces B S hS)
    (a b : RingCat.sectionsSubring (structureRingSheaf B S hS X).obj) :
    structureEndEquiv B S hS X (a * b) = structureEndEquiv B S hS X a
        ≫ structureEndEquiv B S hS X b := by
  rw [structureEndEquiv_apply, structureEndEquiv_apply, structureEndEquiv_apply,
    Stacks.Cohomology.SiteModules.unitEnd_mul]
  exact CategoryTheory.Functor.map_comp _ _ _

/-- `AlgebraicGeometry.Space.structureEndEquiv` is additive. -/
theorem structureEndEquiv_add (X : AlgebraicSpaces B S hS)
    (a b : RingCat.sectionsSubring (structureRingSheaf B S hS X).obj) :
    structureEndEquiv B S hS X (a + b) = structureEndEquiv B S hS X a + structureEndEquiv B S hS X
        b := by
  rw [structureEndEquiv_apply, structureEndEquiv_apply, structureEndEquiv_apply,
    Stacks.Cohomology.SiteModules.unitEnd_add]
  exact CategoryTheory.Functor.map_add _

/-- `AlgebraicGeometry.Space.structureEndEquiv` sends zero to zero. -/
theorem structureEndEquiv_zero (X : AlgebraicSpaces B S hS) :
    structureEndEquiv B S hS X 0 = 0 := by
  rw [structureEndEquiv_apply, Stacks.Cohomology.SiteModules.unitEnd_zero]
  exact CategoryTheory.Functor.map_zero _ _ _

/-- `AlgebraicGeometry.Space.structureEndEquiv` sends one to the identity. -/
theorem structureEndEquiv_one (X : AlgebraicSpaces B S hS) :
    structureEndEquiv B S hS X 1 = 𝟙 _ := by
  rw [structureEndEquiv_apply, Stacks.Cohomology.SiteModules.unitEnd_one]
  exact CategoryTheory.Functor.map_id _ _

/-- **The derived pullback acts on the endomorphisms of the structure object by the ring map on
global regular functions** (Stacks 0732): conjugating `Lf^*` of the endomorphism of `𝒪_Y[0]`
given by `a` by `Lf^*𝒪_Y ≅ 𝒪_X` gives the endomorphism of `𝒪_X[0]` given by the image of `a`. -/
theorem smallEtaleDerivedPullStructureIso_conj_pull_map_structureEndEquiv
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (a : RingCat.sectionsSubring (structureRingSheaf B S hS Y).obj) :
    (smallEtaleDerivedPullStructureIso B S hS f).inv ≫
      ((smallEtaleDerivedPullbackData B S hS).pull f).map (structureEndEquiv B S hS Y a) ≫
        (smallEtaleDerivedPullStructureIso B S hS f).hom =
      structureEndEquiv B S hS X (globalSectionsRingHomSite B S hS f a) := by
  rw [Iso.inv_comp_eq]
  have h :=
    Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackUnitIsoGeneral_hom_naturality_unitEnd
      (smallEtaleRingedToposHom B S hS f) a
  refine (Eq.trans ?_ h).trans ?_
  · rfl
  · have e' : Stacks.Cohomology.SiteModules.unitEnd (structureRingSheaf B S hS X)
          (globalSectionsRingHomSite B S hS f a) =
        Stacks.Cohomology.SiteModules.unitEnd
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)
          (Stacks.Cohomology.SiteModules.globalSectionsRingHom
            (smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom a) := rfl
    rw [structureEndEquiv_apply X (globalSectionsRingHomSite B S hS f a), e']
    rfl

variable (B S hS) in
/-- The global regular functions of the algebraic space of a scheme `T` of the site are
`Γ(T, 𝒪_T)`: evaluation at the terminal chart. -/
def schemeGlobalSectionsEquiv (T : BigFppfOver B S hS) :
    RingCat.sectionsSubring (structureRingSheaf B S hS ((schemeSpaceFunctor B S hS).obj T)).obj ≃+*
      Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
  globalSectionsChartRingEquiv B S hS ((schemeSpaceFunctor B S hS).obj T)
    (isTerminalIdEtaleChart B S hS T)

/-- The ring map on global regular functions along a morphism of schemes of the site is
pullback of functions. -/
theorem schemeGlobalSectionsEquiv_naturality {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (a : RingCat.sectionsSubring (structureRingSheaf B S hS
        ((schemeSpaceFunctor B S hS).obj T)).obj) :
    schemeGlobalSectionsEquiv B S hS T'
        (globalSectionsRingHomSite B S hS ((schemeSpaceFunctor B S hS).map g) a) =
      ((BigFppfOver.toScheme B S hS).map g).appTop (schemeGlobalSectionsEquiv B S hS T a) := by
  let d : ChartDiagram B S hS ((schemeSpaceFunctor B S hS).obj T').1
      ((schemeSpaceFunctor B S hS).obj T).1 ((schemeSpaceFunctor B S hS).map g).hom :=
    { U := idEtaleChart B S hS T'
      V := idEtaleChart B S hS T
      g := g
      comm := (Category.id_comp _).trans (Category.comp_id _).symm }
  exact globalSectionsRingHomSite_val_chartDiagram B S hS ((schemeSpaceFunctor B S hS).map g) a d

end AlgebraicGeometry.Space

end
