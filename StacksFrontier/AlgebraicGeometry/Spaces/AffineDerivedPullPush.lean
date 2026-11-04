module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedPushforwardPullbackTensorIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRepresentability
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.QcqsOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedIsoLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackTensorComp
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMapSndBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSetBaseChangeMateIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.InterfaceUnitNaturality

/-!
# `Rf_*Lf^*E = E ⊗^L f_*𝒪_X` for an affine morphism of algebraic spaces (Stacks 08IJ)

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces and `E` in `D_QCoh(𝒪_Y)`. The canonical
map `E ⊗^L f_*𝒪_X ⟶ Rf_*Lf^*E` is an isomorphism.

## Main results

* `AlgebraicGeometry.Space.isIso_derivedPushforwardStructureTensorMap`: the map
  `E ⊗^L Rf_*𝒪_X ⟶ Rf_*Lf^*E` is an isomorphism.
* `AlgebraicGeometry.Space.isIso_affinePullPushMap`: the map `E ⊗^L f_*𝒪_X ⟶ Rf_*Lf^*E` is an
  isomorphism.
* `AlgebraicGeometry.Space.affinePullPushIso`: `Rf_*Lf^*E ≅ E ⊗^L f_*𝒪_X`.

## References

* [Stacks Project, Tag 08IJ](https://stacks.math.columbia.edu/tag/08IJ)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 0E48](https://stacks.math.columbia.edu/tag/0E48)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 08GE](https://stacks.math.columbia.edu/tag/08GE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)
open scoped CategoryTheory.Prod

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] isGrothendieckAbelian_modules_ringUniverse
  Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- A bifunctor carries a pair of isomorphisms to an isomorphism. -/
private lemma isIso_map_prodMk {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C × D ⥤ E) {a a' : C} {b b' : D} (x : a ⟶ a') (y : b ⟶ b') (hx : IsIso x)
    (hy : IsIso y) : IsIso (F.map ((x ×ₘ y) : ((a, b) : C × D) ⟶ (a', b'))) := by
  have : IsIso ((x ×ₘ y) : ((a, b) : C × D) ⟶ (a', b')) := (isIso_prod_iff _ _).mpr ⟨hx, hy⟩
  infer_instance

/-- An isomorphism through a commutative square with three invertible sides. -/
private lemma isIso_of_comp_eq_comp {C : Type*} [Category C] {P Q R T : C} {p : P ⟶ Q}
    {q : Q ⟶ T} {r : P ⟶ R} {s : R ⟶ T} (h : p ≫ q = r ≫ s) (hp : IsIso p) (hq : IsIso q)
    (hs : IsIso s) : IsIso r := by
  have : IsIso (r ≫ s) := h ▸ inferInstance
  exact IsIso.of_isIso_comp_right r s

/-- An isomorphism through a commutative hexagon with five invertible sides. -/
private lemma isIso_of_comp_eq_comp₃ {C : Type*} [Category C] {P Q R T U V : C} {a : P ⟶ Q}
    {b : Q ⟶ R} {c : R ⟶ T} {d : P ⟶ U} {e : U ⟶ V} {g : V ⟶ T} (h : a ≫ b ≫ c = d ≫ e ≫ g)
    (ha : IsIso a) (hb : IsIso b) (hc : IsIso c) (he : IsIso e) (hg : IsIso g) : IsIso d := by
  have : IsIso (d ≫ e ≫ g) := h ▸ inferInstance
  exact IsIso.of_isIso_comp_right d (e ≫ g)

/-- The pushforward of the unit isomorphism of the derived tensor product at `Lf^*E` is an
isomorphism. -/
private lemma isIso_derivedPushforward_unit_map (f : X ⟶ Y)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    IsIso ((derivedPushforward (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).map
      (((smallEtaleDerivedTensorProduct B S hS X).unitNatIso _).hom.app
        ((smallEtaleDerivedModulePullback B S hS f).obj E))) :=
  ((derivedPushforward (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).mapIso
      (((smallEtaleDerivedTensorProduct B S hS X).unitNatIso _).app
        ((smallEtaleDerivedModulePullback B S hS f).obj E))).isIso_hom

/-- The projection-formula map with the counit in the second factor at `(E, 𝒪_X[0])`, the first
factor of `derivedPushforwardStructureTensorMap`, is an isomorphism for an affine morphism `f` to
an affine algebraic space and `E` in `D_QCoh(𝒪_Y)`. -/
theorem isIso_adjunctionTensorMapSnd_structureDerived_of_isAffineSpace (f : X ⟶ Y)
    (hf : IsAffineHom B S hS f.hom) (hY : IsAffineSpace B S hS Y.1)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hE : QcohDerived B S hS Y E) :
    IsIso (Stacks.ProjectionFormula.adjunctionTensorMapSnd
      (smallEtaleDerivedModuleAdjunction B S hS f)
      (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
      (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
      (smallEtaleDerivedPullbackTensorIso f).hom E (structureDerived X)) := by
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (isIso_derivedPushforward_unit_map f E)
    (isIso_derivedPushforwardStructureTensorMap_of_isAffineSpace f hf hY E hE)

/-- **The projection-formula map at `(E, 𝒪_X[0])` is an isomorphism** for an affine morphism `f`
and `E` in `D_QCoh(𝒪_Y)`. -/
theorem isIso_adjunctionTensorMapSnd_structureDerived (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hE : QcohDerived B S hS Y E) :
    IsIso (Stacks.ProjectionFormula.adjunctionTensorMapSnd
      (smallEtaleDerivedModuleAdjunction B S hS f)
      (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
      (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
      (smallEtaleDerivedPullbackTensorIso f).hom E (structureDerived X)) := by
  refine isIso_of_isIso_smallEtaleDerivedModulePullback_chartToSpace B S hS
    (SmallEtale.coversTop_affineCharts B S hS Y.1) _ fun ⟨A, hA⟩ => ?_
  have sq := isPullback_chartBaseChangeInclusion B S hS f A
  have hj := isEtale_chartToSpace B S hS Y A
  have hrep := relativelyRepresentable_chartToSpace B S hS Y A
  have hf' : IsAffineHom B S hS (chartBaseChangeProjection B S hS f A).hom :=
    IsAffineHom.of_isPullback (AlgebraicSpaces.isPullback_hom B S hS sq) hf
  have hU := isAffineSpace_chartSpace B S hS Y A hA
  have key := Stacks.AffineProjectionFormula.adjunctionTensorMapSnd_baseChange_square
    (smallEtaleDerivedModuleAdjunction B S hS f)
    (smallEtaleDerivedModuleAdjunction B S hS (chartBaseChangeProjection B S hS f A))
    (smallEtaleDerivedModulePullbackCompIso B S hS (chartBaseChangeProjection B S hS f A)
      (chartToSpace B S hS Y A))
    (smallEtaleDerivedModulePullbackSquareIso B S hS f (chartToSpace B S hS Y A)
      (chartBaseChangeProjection B S hS f A) (chartBaseChangeInclusion B S hS f A) sq.w)
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS (chartSpace B S hS Y A)))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS (chartBaseChangeSpace B S hS f A)))
    (smallEtaleDerivedPullbackTensorIso f).hom
    (smallEtaleDerivedPullbackTensorIso (chartBaseChangeProjection B S hS f A)).hom
    (smallEtaleDerivedPullbackTensorIso (chartToSpace B S hS Y A)).hom
    (smallEtaleDerivedPullbackTensorIso (chartBaseChangeInclusion B S hS f A)).hom
    E (structureDerived X)
    (tensorComparisonCompatible_smallEtaleDerivedPullbackTensorIso f (chartToSpace B S hS Y A)
      (chartBaseChangeProjection B S hS f A) (chartBaseChangeInclusion B S hS f A) sq.w E _)
  let j := chartToSpace B S hS Y A
  let j' := chartBaseChangeInclusion B S hS f A
  let f' := chartBaseChangeProjection B S hS f A
  have hBC := isIso_smallEtaleDerivedBaseChangeMap_of_isEtale B S hS f j f' j' sq hj hrep
  have hE' : QcohDerived B S hS (chartSpace B S hS Y A)
      ((smallEtaleDerivedModulePullback B S hS j).obj E) :=
    derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ j E hE
  have h₀ := isIso_adjunctionTensorMapSnd_structureDerived_of_isAffineSpace f' hf' hU _ hE'
  have hnat := Stacks.ProjectionFormula.adjunctionTensorMapSnd_natural
    (smallEtaleDerivedModuleAdjunction B S hS f')
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS (chartSpace B S hS Y A)))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS (chartBaseChangeSpace B S hS f A)))
    (smallEtaleDerivedPullbackTensorIso f').hom
    (𝟙 ((smallEtaleDerivedModulePullback B S hS j).obj E))
    (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) j').hom
  have hc := isIso_of_comp_eq_comp hnat
    (isIso_map_prodMk _ _ _ (IsIso.id _) (Functor.map_isIso _ _)) h₀
    (@Functor.map_isIso _ _ _ _ _ _ _ _
      (isIso_map_prodMk _ _ _ (@Functor.map_isIso _ _ _ _ _ _ _ _ (IsIso.id _))
        (Iso.isIso_hom _)))
  exact isIso_of_comp_eq_comp₃ key
    (Iso.isIso_hom ((smallEtaleDerivedPullbackTensorIso j).app _))
    (isIso_map_prodMk _ _ _ (IsIso.id _) (hBC _)) hc (hBC _)
    (@Functor.map_isIso _ _ _ _ _ _ _ _
      (@IsIso.comp_isIso _ _ _ _ _ _ _
        (Iso.isIso_hom ((smallEtaleDerivedPullbackTensorIso j').app _))
        (isIso_map_prodMk _ _ _ (NatIso.isIso_app_of_isIso _ _) (IsIso.id _))))

/-- **The map `E ⊗^L Rf_*𝒪_X ⟶ Rf_*Lf^*E` is an isomorphism** for an affine morphism `f` of
algebraic spaces and `E` in `D_QCoh(𝒪_Y)`. -/
theorem isIso_derivedPushforwardStructureTensorMap (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hE : QcohDerived B S hS Y E) :
    IsIso (derivedPushforwardStructureTensorMap f E) := by
  have h₁ := isIso_adjunctionTensorMapSnd_structureDerived f hf E hE
  have h₂ := isIso_derivedPushforward_unit_map f E
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂

/-- **The canonical map `E ⊗^L f_*𝒪_X ⟶ Rf_*Lf^*E`** of Stacks 08IJ for an affine morphism `f`:
the identification `f_*𝒪_X ≅ Rf_*𝒪_X` of Stacks 073H in the second factor, followed by the
transpose of `Lf^*(E ⊗^L Rf_*𝒪_X) ≅ Lf^*E ⊗^L Lf^*Rf_*𝒪_X ⟶ Lf^*E ⊗^L 𝒪_X = Lf^*E`. -/
def affinePullPushMap (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    ((smallEtaleDerivedTensor B S hS Y).obj E).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((modulePushforward B S hS f).obj
          (structureModule X))) ⟶
      (derivedPushforward (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).obj
        ((smallEtaleDerivedModulePullback B S hS f).obj E) :=
  ((smallEtaleDerivedTensor B S hS Y).obj E).map
      (derivedModulePushforwardStructureModuleIso B S hS f hf).inv ≫
    derivedPushforwardStructureTensorMap f E

/-- **Stacks 08IJ.** Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over `S`. For `E`
in `D_QCoh(𝒪_Y)` the canonical map `E ⊗^L f_*𝒪_X ⟶ Rf_*Lf^*E` is an isomorphism, so
`Rf_*Lf^*E = E ⊗^L_{𝒪_Y} f_*𝒪_X`. -/
@[stacks 08IJ]
theorem isIso_affinePullPushMap (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hE : QcohDerived B S hS Y E) :
    IsIso (affinePullPushMap f hf E) := by
  have h₂ := isIso_derivedPushforwardStructureTensorMap f hf E hE
  have h₁ : IsIso (((smallEtaleDerivedTensor B S hS Y).obj E).map
      (derivedModulePushforwardStructureModuleIso B S hS f hf).inv) :=
    (((smallEtaleDerivedTensor B S hS Y).obj E).mapIso
      (derivedModulePushforwardStructureModuleIso B S hS f hf).symm).isIso_hom
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂

/-- The identification `Rf_*Lf^*E ≅ E ⊗^L f_*𝒪_X` of Stacks 08IJ, the inverse of
`AlgebraicGeometry.Space.affinePullPushMap`. -/
def affinePullPushIso (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hE : QcohDerived B S hS Y E) :
    (derivedPushforward (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).obj
        ((smallEtaleDerivedModulePullback B S hS f).obj E) ≅
      ((smallEtaleDerivedTensor B S hS Y).obj E).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((modulePushforward B S hS f).obj
          (structureModule X))) :=
  haveI := isIso_affinePullPushMap f hf E hE
  (asIso (affinePullPushMap f hf E)).symm

end AlgebraicGeometry.Space
