module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedQuasicoherentPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtalePullback
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
public import StacksFrontier.Homology.Injectives.KInjective.RightAdjointOfExact
public import StacksFrontier.CategoryTheory.Triangulated.AdmissibleSubcategories

/-!
# The derived direct image along a morphism of algebraic spaces, at the standard model

For a morphism `f : X ⟶ Y` of algebraic spaces this module defines the unbounded derived direct
image `Rf_* : D(𝒪_X) ⥤ D(𝒪_Y)` at the standard model `spaceDerivedCategory`, and proves:

* `Rf_*` is computed by K-injective complexes and is an exact functor;
* for `f` étale, `Rf_*` carries the right orthogonal of `D_QCoh(𝒪_X)` into the right orthogonal
  of `D_QCoh(𝒪_Y)`.

## Main definitions

* `AlgebraicGeometry.Space.spaceDerivedPushforward f`: `Rf_*`.
* `AlgebraicGeometry.Space.spaceDerivedPushforwardQIso`: for a K-injective complex `I`, the
  isomorphism of `Rf_*I` with the degreewise direct image `f_*I`.
* `AlgebraicGeometry.Space.spaceCoreflective X`: the objects `K` of `D(𝒪_X)` sitting in a
  distinguished triangle `E ⟶ K ⟶ Q ⟶ E[1]` with `E` in `D_QCoh(𝒪_X)` and `Q` right orthogonal to
  `D_QCoh(𝒪_X)`. By [Stacks, Tag 0CQS] the coherator of `X` exists exactly when every object is
  of this form.

## Main results

* `AlgebraicGeometry.Space.rightOrthogonal_spaceDerivedPushforward`: for `f` étale, `Rf_*`
  carries objects right orthogonal to `D_QCoh(𝒪_X)` to objects right orthogonal to
  `D_QCoh(𝒪_Y)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] isGrothendieckAbelian_modules enoughInjectives_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Coreflective objects -/

/-- The objects of `D(𝒪_X)` with a coreflection into `D_QCoh(𝒪_X)`: those sitting in a
distinguished triangle `E ⟶ K ⟶ Q ⟶ E[1]` with `E` in `D_QCoh(𝒪_X)` and `Q` right orthogonal to
`D_QCoh(𝒪_X)`. -/
abbrev spaceCoreflective (X : AlgebraicSpaces B S hS) :
    ObjectProperty (spaceDerivedCategory B S hS X) :=
  (spaceQuasicoherentProp B S hS X).extensionProduct
    (spaceQuasicoherentProp B S hS X).rightOrthogonal

/-- **[Stacks, Tag 0CQR]**: the coreflective objects form a triangulated subcategory. -/
instance isTriangulated_spaceCoreflective (X : AlgebraicSpaces B S hS) :
    (spaceCoreflective B S hS X).IsTriangulated :=
  ObjectProperty.isTriangulated_extensionProduct_of_le_rightOrthogonal _ _ le_rfl

/-! ### The derived direct image -/

variable {X Y : AlgebraicSpaces B S hS}

/-- The degreewise direct image followed by the localization to `D(𝒪_Y)`. -/
abbrev spacePushforwardOnHomotopy (f : X ⟶ Y) :
    HomotopyCategory (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ) ⥤
      spaceDerivedCategory B S hS Y :=
  (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    @DerivedCategory.Qh _ _ _ (spaceHasDerivedCategory B S hS Y)

/-- The degreewise direct image followed by the localization to `D(𝒪_Y)` has a right derived
functor with respect to the quasi-isomorphisms. -/
theorem spacePushforwardOnHomotopy_hasRightDerivedFunctor (f : X ⟶ Y) :
    (spacePushforwardOnHomotopy B S hS f).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) :=
  let := spaceHasDerivedCategory B S hS Y
  hasRightDerivedFunctor_modulePushforward B S hS f

/-- **The derived direct image `Rf_* : D(𝒪_X) ⥤ D(𝒪_Y)`** along a morphism of algebraic spaces,
at the standard model: the total right derived functor of the degreewise direct image. -/
def spaceDerivedPushforward (f : X ⟶ Y) :
    spaceDerivedCategory B S hS X ⥤ spaceDerivedCategory B S hS Y :=
  letI := spaceHasDerivedCategory B S hS X
  letI := spacePushforwardOnHomotopy_hasRightDerivedFunctor B S hS f
  (spacePushforwardOnHomotopy B S hS f).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))

/-- The derivation unit of `Rf_*`. -/
def spaceDerivedPushforwardUnit (f : X ⟶ Y) :
    spacePushforwardOnHomotopy B S hS f ⟶
      @DerivedCategory.Qh _ _ _ (spaceHasDerivedCategory B S hS X) ⋙
        spaceDerivedPushforward B S hS f :=
  letI := spaceHasDerivedCategory B S hS X
  letI := spacePushforwardOnHomotopy_hasRightDerivedFunctor B S hS f
  (spacePushforwardOnHomotopy B S hS f).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))

/-- `Rf_*`, with its derivation unit, is a right derived functor of the degreewise direct image
with respect to the quasi-isomorphisms. -/
instance isRightDerivedFunctor_spaceDerivedPushforward (f : X ⟶ Y) :
    letI := spaceHasDerivedCategory B S hS X
    (spaceDerivedPushforward B S hS f).IsRightDerivedFunctor
      (spaceDerivedPushforwardUnit B S hS f)
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) := by
  let := spaceHasDerivedCategory B S hS X
  let := spacePushforwardOnHomotopy_hasRightDerivedFunctor B S hS f
  unfold spaceDerivedPushforward spaceDerivedPushforwardUnit
  infer_instance

/-- `Rf_*` commutes with the shift. -/
instance (f : X ⟶ Y) : (spaceDerivedPushforward B S hS f).CommShift ℤ :=
  letI := spaceHasDerivedCategory B S hS X
  letI := spaceHasDerivedCategory B S hS Y
  Functor.IsRightDerivedFunctor.commShift (spaceDerivedPushforward B S hS f)
    (spaceDerivedPushforwardUnit B S hS f)
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) ℤ

/-- `Rf_*` is an exact functor. -/
instance (f : X ⟶ Y) : (spaceDerivedPushforward B S hS f).IsTriangulated :=
  letI := spaceHasDerivedCategory B S hS X
  letI := spaceHasDerivedCategory B S hS Y
  Stacks.DerivedAcyclic.isTriangulated_of_isRightDerivedFunctor (modulePushforward B S hS f)
    (spaceDerivedPushforward B S hS f) (spaceDerivedPushforwardUnit B S hS f)

/-- **`Rf_*` is computed by K-injective complexes**: for a K-injective complex `I` of
`𝒪_X`-modules, `Rf_*I` is the degreewise direct image `f_*I`. -/
def spaceDerivedPushforwardQIso (f : X ⟶ Y) (I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hI : I.IsKInjective) :
    (spaceDerivedPushforward B S hS f).obj ((spaceDerivedQ B S hS X).obj I) ≅
      (spaceDerivedQ B S hS Y).obj
        (((modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  letI := spaceHasDerivedCategory B S hS X
  letI := spaceHasDerivedCategory B S hS Y
  haveI : IsIso ((spaceDerivedPushforwardUnit B S hS f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
    isIso_app_of_isKInjective_modulePushforward B S hS f _ _ _ I hI
  (spaceDerivedPushforward B S hS f).mapIso ((DerivedCategory.quotientCompQhIso _).app I).symm ≪≫
    (asIso ((spaceDerivedPushforwardUnit B S hS f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))).symm ≪≫
    (DerivedCategory.quotientCompQhIso _).app _

/-- **For an étale `f`, `Rf_*` preserves right orthogonality to `D_QCoh`.** If `Q` is right
orthogonal to `D_QCoh(𝒪_X)` then `Rf_*Q` is right orthogonal to `D_QCoh(𝒪_Y)`. -/
theorem rightOrthogonal_spaceDerivedPushforward (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (Q' : spaceDerivedCategory B S hS X)
    (hQ : (spaceQuasicoherentProp B S hS X).rightOrthogonal Q') :
    (spaceQuasicoherentProp B S hS Y).rightOrthogonal
      ((spaceDerivedPushforward B S hS f).obj Q') := by
  let := spaceHasDerivedCategory B S hS X
  let := spaceHasDerivedCategory B S hS Y
  let := etaleModulePullback_additive B S hS f hf
  let := preservesFiniteLimits_etaleModulePullback B S hS f hf
  let := preservesFiniteColimits_etaleModulePullback B S hS f hf
  obtain ⟨J, g, hJ, hg⟩ := exists_quasiIso_isKInjective_modules B S hS X.1 X.2
    (DerivedCategory.Q.objPreimage Q')
  have := hJ
  have : IsIso (DerivedCategory.Q.map g) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ g).2 hg
  let eQ : DerivedCategory.Q.obj J ≅ Q' :=
    (asIso (DerivedCategory.Q.map g)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso Q'
  refine ObjectProperty.prop_of_iso _ ((spaceDerivedPushforwardQIso B S hS f J hJ).symm ≪≫
    (spaceDerivedPushforward B S hS f).mapIso eQ) ?_
  have hfJ : CochainComplex.IsKInjective
      (((modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) :=
    Stacks.Injectives.isKInjective_mapHomologicalComplex_of_adjunction _ _
      (etaleModulePullbackAdjunction B S hS f hf) J
  intro M φ hM
  let Mh := DerivedCategory.Qh.objPreimage M
  let eM : DerivedCategory.Qh.obj Mh ≅ M := DerivedCategory.Qh.objObjPreimageIso M
  let eJ := (DerivedCategory.quotientCompQhIso (Modules.{u, u} B S hS Y.1 Y.2)).app
    (((modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)
  obtain ⟨φ₀, hφ₀⟩ := (CochainComplex.IsKInjective.Qh_map_bijective Mh
    (((modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)).2
      (eM.hom ≫ φ ≫ eJ.inv)
  let adj := (etaleModulePullbackAdjunction B S hS f hf).mapHomotopyCategory (ComplexShape.up ℤ)
  let φ₁ := (adj.homEquiv Mh ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj J)).symm φ₀
  have hqc : spaceQuasicoherentProp B S hS X
      (DerivedCategory.Qh.obj
        (((etaleModulePullback B S hS f hf).mapHomotopyCategory (ComplexShape.up ℤ)).obj Mh)) :=
    ObjectProperty.prop_of_iso _
      (((etaleModulePullback B S hS f hf).mapDerivedCategoryFactorsh.app Mh).symm ≪≫
        (etaleModulePullback B S hS f hf).mapDerivedCategory.mapIso eM).symm
      (derivedQuasicoherent_etaleModulePullback B S hS f hf M hM)
  have h1 : DerivedCategory.Qh.map φ₁ ≫
      ((DerivedCategory.quotientCompQhIso _).app J).hom ≫ eQ.hom = 0 :=
    hQ _ hqc
  have h2 : DerivedCategory.Qh.map φ₁ = DerivedCategory.Qh.map 0 := by
    rw [Functor.map_zero]
    simpa using h1
  have h3 : φ₁ = 0 := (CochainComplex.IsKInjective.Qh_map_bijective _ J).1 h2
  have h4 : φ₀ = 0 := by
    have : φ₀ = adj.homEquiv _ _ φ₁ := ((adj.homEquiv _ _).apply_symm_apply φ₀).symm
    rw [this, h3, Adjunction.homEquiv_apply, Functor.map_zero, comp_zero]
  have h5 : eM.hom ≫ φ ≫ eJ.inv = 0 := by rw [← hφ₀, h4, Functor.map_zero]
  simpa using h5

end AlgebraicGeometry.Space

end
