module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RetractionModulePullback
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFibreStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Quot.DerivedPullbackPseudofunctor
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DerivedEquivalence
public import StacksFrontier.Homology.TorAmplitude.Comparison

/-!
# Derived pullback along `X ⟶ X'` as derived extension of scalars along `𝒪_X[𝒪_X ⊗_k V] ⟶ 𝒪_X`

Let `X ⟶ X' ⟶ X` be the base change of `Spec k ⟶ Spec k[V] ⟶ Spec k`. Through the equivalence
of derived categories induced by `AlgebraicGeometry.Space.squareZeroModuleEquivalence`
(`AlgebraicGeometry.Space.squareZeroDerivedEquivalence`), the derived pullback along `i : X ⟶ X'`
is a derived base change along the projection `𝒪_X[𝒪_X ⊗_k V] ⟶ 𝒪_X`
(`AlgebraicGeometry.Space.squareZeroDerivedExtensionOfScalars`), hence it is isomorphic to every
derived base change along it (`AlgebraicGeometry.Space.squareZeroDerivedPullbackIso`). This is
the comparison `c2` in the proof of Stacks 0DLL. On the way, the derived pullback along a morphism
of algebraic spaces is a left derived functor of degreewise pullback along the localization of
cochain complexes (`AlgebraicGeometry.Space.isLeftDerivedFunctor_derivedPullComparison`).

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin Deformation.ComplexLift
  Stacks.TensorByBaseModule

universe d u

namespace AlgebraicGeometry.Space

section DerivedPull

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- Degreewise pullback of modules along `f` read on the homotopy category and localized,
precomposed with the homotopy quotient, is degreewise pullback followed by the localization. -/
def quotientCompModulePullbackIso :
    HomotopyCategory.quotient (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ) ⋙
        (((modulePullbackDataTopos B S hS).pull f).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ≅
      ((modulePullbackDataTopos B S hS).pull f).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerRight
      (((modulePullbackDataTopos B S hS).pull f).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso (Modules.{u, u} B S hS X.1 X.2))

/-- The comparison of the derived pullback along `f` with degreewise pullback, on the homotopy
category: that of `AlgebraicGeometry.Space.derivedModulePullbackLeftDerived`. -/
def derivedPullComparisonHomotopy :
    DerivedCategory.Qh ⋙ derivedPull B S hS (hasDerivedModulePullbacks B S hS) f ⟶
      ((modulePullbackDataTopos B S hS).pull f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh :=
  (derivedModulePullbackLeftDerived B S hS).α f

/-- The derived pullback along `f` is a left derived functor of degreewise pullback on the homotopy
category, along its localization at the quasi-isomorphisms, with the comparison
`AlgebraicGeometry.Space.derivedPullComparisonHomotopy`. -/
instance isLeftDerivedFunctor_derivedPullComparisonHomotopy :
    (derivedPull B S hS (hasDerivedModulePullbacks B S hS) f).IsLeftDerivedFunctor
      (derivedPullComparisonHomotopy B S hS f)
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)) :=
  (derivedModulePullbackLeftDerived B S hS).isLeftDerivedFunctor f

/-- **The comparison of the derived pullback along `f` with degreewise pullback**, on cochain
complexes: the comparison of `AlgebraicGeometry.Space.derivedModulePullbackLeftDerived` on the
homotopy category, precomposed with the homotopy quotient. -/
def derivedPullComparison :
    DerivedCategory.Q ⋙ derivedPull B S hS (hasDerivedModulePullbacks B S hS) f ⟶
      ((modulePullbackDataTopos B S hS).pull f).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso (Modules.{u, u} B S hS Y.1 Y.2)).inv
      (derivedPull B S hS (hasDerivedModulePullbacks B S hS) f) ≫
    Functor.whiskerLeft (HomotopyCategory.quotient (Modules.{u, u} B S hS Y.1 Y.2)
      (ComplexShape.up ℤ)) (derivedPullComparisonHomotopy B S hS f) ≫
    (quotientCompModulePullbackIso B S hS f).hom

/-- **The derived pullback along `f` is a left derived functor of degreewise pullback** along the
localization of cochain complexes at the quasi-isomorphisms, with the comparison
`AlgebraicGeometry.Space.derivedPullComparison`. -/
instance isLeftDerivedFunctor_derivedPullComparison :
    (derivedPull B S hS (hasDerivedModulePullbacks B S hS) f).IsLeftDerivedFunctor
      (derivedPullComparison B S hS f)
      (HomologicalComplex.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)) :=
  StacksDraft.TorAmplitude.isLeftDerivedFunctor_of_homotopyCategory _ _
    (quotientCompModulePullbackIso B S hS f) _ (derivedPullComparisonHomotopy B S hS f)
    (derivedPullComparison B S hS f) (by
      unfold derivedPullComparison
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [← Category.assoc, ← Functor.whiskerRight_comp, Iso.hom_inv_id,
        Functor.whiskerRight_id', Category.id_comp])

end DerivedPull

section Retraction

attribute [local instance 10000] HasDerivedCategory.standard

variable {k : Type u} [CommRing k] {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of k) ⟶ S} {hk : B.Contains (Spec (.of k))} {V : SiteModule k B}
  {X X' : AlgebraicSpaces B S hS} {i : X ⟶ X'} (hi : IsThickeningHom B S hS i)
  {q : X' ⟶ X} (h : i ≫ q = 𝟙 X) {hq : yoneda.relativelyRepresentable q.hom}
  {p : X.1 ⟶ yoneda.obj (algebraOver k B S hS toS hk)}
  {p' : X'.1 ⟶ yoneda.obj (squareZeroOver k B S hS toS V)}
  {τ : squareZeroOver k B S hS toS V ⟶ algebraOver k B S hS toS hk}
  (hip : i.hom ≫ p' = p ≫ yoneda.map (squareZeroArrow k B S hS toS hk V))
  (hpb : IsPullback q.hom p' p (yoneda.map τ))
  (hβτ : squareZeroArrow k B S hS toS hk V ≫ τ = 𝟙 _)

/-- The equivalence `AlgebraicGeometry.Space.squareZeroModuleEquivalence` is additive. -/
instance squareZeroModuleEquivalence_functor_additive :
    (squareZeroModuleEquivalence (hq := hq) hi h hip hpb hβτ).functor.Additive := by
  change (_ ⋙ SheafOfModules.restrictScalars _).Additive
  infer_instance

variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj))))]

/-- **The derived equivalence `D(𝒪_X[𝒪_X ⊗_k V]) ≌ D(𝒪_{X'})`**:
`AlgebraicGeometry.Space.squareZeroModuleEquivalence` on derived categories. The source has any
model, the target is `AlgebraicGeometry.Space.derivedModules`. -/
def squareZeroDerivedEquivalence :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
          ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))) ≌
      derivedModules B S hS X' :=
  @Stacks.DerivedQCoh.Equivalence.mapDerivedCategory _ _ _ _ _ _ _ _
    (squareZeroModuleEquivalence (hq := hq) hi h hip hpb hβτ)
    (squareZeroModuleEquivalence_functor_additive (hq := hq) hi h hip hpb hβτ)

/-- Degreewise extension of scalars along the projection, localized, is the equivalence of
complexes followed by degreewise pullback along `i`, localized: the underived comparison
`AlgebraicGeometry.Space.squareZeroPullbackIso` applied degreewise. -/
def squareZeroComplexPullbackIso :
    extensionOfScalarsCochainComplex (SmallEtale.topology B S hS X.1)
        (sqZeroExtSheafAnySiteProj ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)) ⋙ DerivedCategory.Q ≅
      (squareZeroModuleEquivalence (hq := hq) hi h hip hpb hβτ).functor.mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        (((modulePullbackDataTopos B S hS).pull i).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q) :=
  Functor.isoWhiskerRight (@Functor.mapHomologicalComplexCompIso ℤ _ _ _ _ _ _ _ _ _ _ _ _
    (squareZeroPullbackIso (hq := hq) hi h hip hpb hβτ)
    (squareZeroModuleEquivalence_functor_additive (hq := hq) hi h hip hpb hβτ)
    (modulePullbackDataTopos_additive B S hS i) (additive_extensionOfScalars _)
    (ComplexShape.up ℤ)).symm
    DerivedCategory.Q ≪≫
    Functor.associator _ _ _

/-- The comparison of the derived pullback along `i`, precomposed with the derived equivalence,
with degreewise extension of scalars along the projection. -/
def squareZeroDerivedComparison :
    DerivedCategory.Q ⋙ ((squareZeroDerivedEquivalence (hq := hq) hi h hip hpb hβτ).functor ⋙
        derivedPull B S hS (hasDerivedModulePullbacks B S hS) i) ⟶
      extensionOfScalarsCochainComplex (SmallEtale.topology B S hS X.1)
        (sqZeroExtSheafAnySiteProj ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)) ⋙ DerivedCategory.Q :=
  Functor.whiskerLeft DerivedCategory.Q
      (Iso.refl ((squareZeroDerivedEquivalence (hq := hq) hi h hip hpb hβτ).functor ⋙
        derivedPull B S hS (hasDerivedModulePullbacks B S hS) i)).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _
      (squareZeroModuleEquivalence (hq := hq) hi h hip hpb hβτ).functor
      (squareZeroModuleEquivalence_functor_additive (hq := hq) hi h hip hpb hβτ) _ _).symm.inv
      (derivedPull B S hS (hasDerivedModulePullbacks B S hS) i) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft
      ((squareZeroModuleEquivalence (hq := hq) hi h hip hpb hβτ).functor.mapHomologicalComplex
        (ComplexShape.up ℤ))
      (derivedPullComparison B S hS i) ≫
    (squareZeroComplexPullbackIso (hq := hq) hi h hip hpb hβτ).inv

/-- **The derived pullback along `i`, read through the derived equivalence, is a derived base
change along the projection `𝒪_X[𝒪_X ⊗_k V] ⟶ 𝒪_X`**: it is the left derived functor of
degreewise extension of scalars, since the derived pullback is the left derived functor of
degreewise pullback (`AlgebraicGeometry.Space.isLeftDerivedFunctor_derivedPullComparison`), and
degreewise pullback precomposed with the equivalence of complexes is degreewise extension of
scalars (`AlgebraicGeometry.Space.squareZeroPullbackIso`). -/
def squareZeroDerivedExtensionOfScalars :
    DerivedExtensionOfScalars.{d, u + 1} (sqZeroExtSheafAnySiteProj
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)) where
  baseChange := (squareZeroDerivedEquivalence (hq := hq) hi h hip hpb hβτ).functor ⋙
    derivedPull B S hS (hasDerivedModulePullbacks B S hS) i
  comparison := squareZeroDerivedComparison (hq := hq) hi h hip hpb hβτ
  isLeftDerived := by
    have := Functor.IsLeftDerivedFunctor.isRightKanExtension _ (derivedPullComparison B S hS i)
      (HomologicalComplex.quasiIso (Modules.{u, u} B S hS X'.1 X'.2) (ComplexShape.up ℤ))
    exact ⟨(@Functor.isRightKanExtension_iff_precomp_equivalence _ _ _ _ _ _ _ _ _ _ _ _ _
      (squareZeroDerivedComparison (hq := hq) hi h hip hpb hβτ) _ _ _
      (derivedPullComparison B S hS i) _ _
      (@CategoryTheory.Equivalence.mapHomologicalComplex _ _ _ _ _ _ _
        (squareZeroModuleEquivalence (hq := hq) hi h hip hpb hβτ)
        (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
          (squareZeroModuleEquivalence_functor_additive (hq := hq) hi h hip hpb hβτ))
        (ComplexShape.up ℤ)).isEquivalence_functor
      (squareZeroDerivedEquivalence (hq := hq) hi h hip hpb hβτ).isEquivalence_functor
      (@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _
        (squareZeroModuleEquivalence (hq := hq) hi h hip hpb hβτ).functor
        (squareZeroModuleEquivalence_functor_additive (hq := hq) hi h hip hpb hβτ) _ _).symm
      (squareZeroComplexPullbackIso (hq := hq) hi h hip hpb hβτ) (Iso.refl _) rfl).1
      inferInstance⟩

/-- **Stacks 0DLL, `c2`: every derived base change along the projection
`𝒪_X[𝒪_X ⊗_k V] ⟶ 𝒪_X` is the derived pullback along `i : X ⟶ X'`**, read through the derived
equivalence `AlgebraicGeometry.Space.squareZeroDerivedEquivalence`, by uniqueness of left derived
functors. -/
def squareZeroDerivedPullbackIso
    (T : DerivedExtensionOfScalars.{d, u + 1} (sqZeroExtSheafAnySiteProj
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj))) :
    T.baseChange ≅ (squareZeroDerivedEquivalence (hq := hq) hi h hip hpb hβτ).functor ⋙
      derivedPull B S hS (hasDerivedModulePullbacks B S hS) i :=
  DerivedExtensionOfScalars.baseChangeIso T
    (squareZeroDerivedExtensionOfScalars (hq := hq) hi h hip hpb hβτ)

end Retraction

section TestScheme

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace CoherentSituation

variable (D : CoherentSituation B S hS) {T₀ T : SchemesOver D.Y}
  {k : Type u} [CommRing k] {toS : Spec (.of k) ⟶ S} {hk : B.Contains (Spec (.of k))}
  {V : SiteModule k B} {b : T₀ ⟶ T} {t : T ⟶ T₀}
  (hbt : b ≫ t = 𝟙 T₀) (hb : IsSquareZeroClosedImmersion B S hS b.left)
  (hT₀ : T₀.left = algebraOver k B S hS toS hk) (hT : T.left = squareZeroOver k B S hS toS V)
  (hβ : eqToHom hT₀.symm ≫ b.left ≫ eqToHom hT = squareZeroArrow k B S hS toS hk V)
  [hDer : HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (sqZeroExtSheafAnySite (structureSheaf B S hS (D.space T₀).1 (D.space T₀).2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS (D.space T₀).1)
        (structureSheaf B S hS (D.space T₀).1 (D.space T₀).2) (SheafOfModules.unit _)
        (squareZeroCoefficientMap k B S hS toS hk
          ((D.projection T₀).hom ≫ yoneda.map (eqToHom hT₀)))).obj V.obj))))]

/-- **The derived pullback along `X_b : X_{T₀} ⟶ X_T` is a derived base change along the
projection** `𝒪_{X_{T₀}}[𝒪_{X_{T₀}} ⊗_k V] ⟶ 𝒪_{X_{T₀}}`, for test schemes `T₀ = Spec k`,
`T = Spec k[V]` over `Y` with a section `b` and a retraction `t`:
`AlgebraicGeometry.Space.squareZeroDerivedExtensionOfScalars` for `X_b`, `X_t`. -/
def testSchemeDerivedExtensionOfScalars :
    DerivedExtensionOfScalars.{d, u + 1} (sqZeroExtSheafAnySiteProj
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS (D.space T₀).1)
        (structureSheaf B S hS (D.space T₀).1 (D.space T₀).2) (SheafOfModules.unit _)
        (squareZeroCoefficientMap k B S hS toS hk
          ((D.projection T₀).hom ≫ yoneda.map (eqToHom hT₀)))).obj V.obj)) :=
  squareZeroDerivedExtensionOfScalars (hq := relativelyRepresentable_baseChangeMap B S hS D.f t)
    (IsFirstOrderThickeningHom.isThickeningHom B S hS
      (isFirstOrderThickeningHom_relativeMap D b hb))
    (relativeMap_section_comp_retraction D hbt)
    (comp_yoneda_map_eqToHom hT hT₀ _ _ _ _ _ hβ (relativeMap_hom_comp_projection D b))
    (isPullback_yoneda_map_eqToHom hT hT₀ _ _ _ _ (isPullback_relativeMap_hom D t))
    (eqToHom_conj_comp_eqToHom_conj hT₀ hT _ _ (congrArg CommaMorphism.left hbt) _ hβ)

end CoherentSituation

end TestScheme

end AlgebraicGeometry.Space

end
