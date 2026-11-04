module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RetractionStructureSheafSquareZero
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFibreThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatDimensionStagePresentation

/-!
# The structure sheaf of `X_V` on the small étale site of `X₀`, for the test schemes of a fibre

Let `D` be a coherent situation `f : X ⟶ Y`, and let `b : T₀ ⟶ T`, `t : T ⟶ T₀` be morphisms of
test schemes over `Y` with `b ≫ t = 𝟙`. Base change gives `X_{T₀} ⟶ X_T ⟶ X_{T₀}` with composite
the identity (`AlgebraicGeometry.Space.CoherentSituation.relativeMap_section_comp_retraction`), the
square of `t` is cartesian on presheaves
(`AlgebraicGeometry.Space.CoherentSituation.isPullback_relativeMap_hom`) and `X_b` lies over `b`
(`AlgebraicGeometry.Space.CoherentSituation.relativeMap_hom_comp_projection`). When `T₀ = Spec k`,
`T = Spec k[V]` and `b` is the closed immersion, this is the input of
`AlgebraicGeometry.Space.squareZeroRetractionRingIso`: the structure sheaf of `X_T` on the small
étale site of `X_{T₀}` is `𝒪_{X_{T₀}}[𝒪_{X_{T₀}} ⊗_k V]`
(`AlgebraicGeometry.Space.CoherentSituation.testSchemeRetractionRingIso`).

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin Deformation.ComplexLift
  Stacks.TensorByBaseModule

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Restriction along chart base change along a thickening is additive. -/
instance thickeningHomModuleEquivalence_functor_additive {X X' : AlgebraicSpaces B S hS}
    {i : X ⟶ X'} (hi : IsThickeningHom B S hS i)
    (R : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u}) :
    (thickeningHomModuleEquivalence B S hS hi R).functor.Additive :=
  ⟨rfl⟩

namespace CoherentSituation

variable (D : CoherentSituation B S hS) {T₀ T : SchemesOver D.Y}

/-- `X_{T₀} ⟶ X_T ⟶ X_{T₀}` is the identity when `T₀ ⟶ T ⟶ T₀` is. -/
theorem relativeMap_section_comp_retraction {b : T₀ ⟶ T} {t : T ⟶ T₀} (hbt : b ≫ t = 𝟙 T₀) :
    D.relativeMap b ≫ D.relativeMap t = 𝟙 (D.space T₀) := by
  rw [← baseChangeMap_comp, hbt, baseChangeMap_id]

/-- The square of `X_t : X_T ⟶ X_{T₀}` over `t : T ⟶ T₀` is cartesian on presheaves. -/
theorem isPullback_relativeMap_hom (t : T ⟶ T₀) :
    IsPullback (D.relativeMap t).hom (D.projection T).hom (D.projection T₀).hom
      (yoneda.map t.left) :=
  AlgebraicSpaces.isPullback_hom B S hS (isPullback_baseChangeMap D.f t)

/-- `X_b : X_{T₀} ⟶ X_T` lies over `b : T₀ ⟶ T`. -/
theorem relativeMap_hom_comp_projection (b : T₀ ⟶ T) :
    (D.relativeMap b).hom ≫ (D.projection T).hom =
      (D.projection T₀).hom ≫ yoneda.map b.left :=
  (isPullback_relativeMap_hom D b).w

section SquareZero

/-- Transport of a commutative square over `yoneda.map g` along equalities of the corners. -/
theorem comp_yoneda_map_eqToHom {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {A A' B₀ B₀' : BigFppfOver B S hS} (hA : A = A') (hB : B₀ = B₀') (i : P ⟶ Q)
    (y : Q ⟶ yoneda.obj A) (x : P ⟶ yoneda.obj B₀) (g : B₀ ⟶ A) (g' : B₀' ⟶ A')
    (hg : eqToHom hB.symm ≫ g ≫ eqToHom hA = g') (h : i ≫ y = x ≫ yoneda.map g) :
    i ≫ y ≫ yoneda.map (eqToHom hA) = (x ≫ yoneda.map (eqToHom hB)) ≫ yoneda.map g' := by
  subst hA hB hg
  simpa using h

/-- Transport of a cartesian square over `yoneda.map g` along equalities of the corners. -/
theorem isPullback_yoneda_map_eqToHom {P R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {A A' B₀ B₀' : BigFppfOver B S hS} (hA : A = A') (hB : B₀ = B₀') (f : P ⟶ R)
    (y : P ⟶ yoneda.obj A) (x : R ⟶ yoneda.obj B₀) (g : A ⟶ B₀)
    (h : IsPullback f y x (yoneda.map g)) :
    IsPullback f (y ≫ yoneda.map (eqToHom hA)) (x ≫ yoneda.map (eqToHom hB))
      (yoneda.map (eqToHom hA.symm ≫ g ≫ eqToHom hB)) := by
  subst hA hB
  simpa using h

/-- Conjugating a section and a retraction by equalities keeps them a section and a retraction. -/
theorem eqToHom_conj_comp_eqToHom_conj {C : Type*} [Category* C] {A A' B₀ B₀' : C}
    (hA : A = A') (hB : B₀ = B₀') (b : A ⟶ B₀) (t : B₀ ⟶ A) (h : b ≫ t = 𝟙 A) (g' : A' ⟶ B₀')
    (hg : eqToHom hA.symm ≫ b ≫ eqToHom hB = g') :
    g' ≫ (eqToHom hB.symm ≫ t ≫ eqToHom hA) = 𝟙 A' := by
  subst hA hB hg
  simpa using h

variable {k : Type u} [CommRing k] {toS : Spec (.of k) ⟶ S} {hk : B.Contains (Spec (.of k))}
  {V : SiteModule k B} {b : T₀ ⟶ T} {t : T ⟶ T₀}

/-- **The structure sheaf of `X_T` on the small étale site of `X_{T₀}` is
`𝒪_{X_{T₀}}[𝒪_{X_{T₀}} ⊗_k V]`**, for test schemes `T₀ = Spec k`, `T = Spec k[V]` over `Y` with a
section `b` (the closed immersion) and a retraction `t`. -/
def testSchemeRetractionRingIso (hbt : b ≫ t = 𝟙 T₀)
    (hb : IsSquareZeroClosedImmersion B S hS b.left)
    (hT₀ : T₀.left = algebraOver k B S hS toS hk) (hT : T.left = squareZeroOver k B S hS toS V)
    (hβ : eqToHom hT₀.symm ≫ b.left ≫ eqToHom hT = squareZeroArrow k B S hS toS hk V) :
    thickeningRetractionRing B S hS (relativelyRepresentable_baseChangeMap B S hS D.f t) ≅
      sqZeroExtSheafAnySite (structureSheaf B S hS (D.space T₀).1 (D.space T₀).2)
        ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS (D.space T₀).1)
          (structureSheaf B S hS (D.space T₀).1 (D.space T₀).2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk
            ((D.projection T₀).hom ≫ yoneda.map (eqToHom hT₀)))).obj V.obj) :=
  squareZeroRetractionRingIso
    (IsFirstOrderThickeningHom.isThickeningHom B S hS
      (isFirstOrderThickeningHom_relativeMap D b hb))
    (relativeMap_section_comp_retraction D hbt)
    (comp_yoneda_map_eqToHom hT hT₀ _ _ _ _ _ hβ (relativeMap_hom_comp_projection D b))
    (isPullback_yoneda_map_eqToHom hT hT₀ _ _ _ _ (isPullback_relativeMap_hom D t))
    (eqToHom_conj_comp_eqToHom_conj hT₀ hT _ _ (congrArg CommaMorphism.left hbt) _ hβ)

/-- **The `𝒪_{X_{T₀}}[𝒪_{X_{T₀}} ⊗_k V]`-modules on the site of `X_{T₀}` are the
`𝒪_{X_T}`-modules**, for test schemes `T₀ = Spec k`, `T = Spec k[V]` over `Y` with a section `b`
and a retraction `t`: `AlgebraicGeometry.Space.squareZeroModuleEquivalence` for `X_b`, `X_t`. -/
def testSchemeModuleEquivalence (hbt : b ≫ t = 𝟙 T₀)
    (hb : IsSquareZeroClosedImmersion B S hS b.left)
    (hT₀ : T₀.left = algebraOver k B S hS toS hk) (hT : T.left = squareZeroOver k B S hS toS V)
    (hβ : eqToHom hT₀.symm ≫ b.left ≫ eqToHom hT = squareZeroArrow k B S hS toS hk V) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (sqZeroExtSheafAnySite (structureSheaf B S hS (D.space T₀).1 (D.space T₀).2)
          ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS (D.space T₀).1)
            (structureSheaf B S hS (D.space T₀).1 (D.space T₀).2) (SheafOfModules.unit _)
            (squareZeroCoefficientMap k B S hS toS hk
              ((D.projection T₀).hom ≫ yoneda.map (eqToHom hT₀)))).obj V.obj))) ≌
      SheafOfModules.{u} (smallEtaleRingSheaf B S hS (D.space T).1 (D.space T).2) :=
  squareZeroModuleEquivalence (hq := relativelyRepresentable_baseChangeMap B S hS D.f t)
    (IsFirstOrderThickeningHom.isThickeningHom B S hS
      (isFirstOrderThickeningHom_relativeMap D b hb))
    (relativeMap_section_comp_retraction D hbt)
    (comp_yoneda_map_eqToHom hT hT₀ _ _ _ _ _ hβ (relativeMap_hom_comp_projection D b))
    (isPullback_yoneda_map_eqToHom hT hT₀ _ _ _ _ (isPullback_relativeMap_hom D t))
    (eqToHom_conj_comp_eqToHom_conj hT₀ hT _ _ (congrArg CommaMorphism.left hbt) _ hβ)

/-- The equivalence of
`AlgebraicGeometry.Space.CoherentSituation.testSchemeModuleEquivalence` is additive. -/
instance testSchemeModuleEquivalence_functor_additive (hbt : b ≫ t = 𝟙 T₀)
    (hb : IsSquareZeroClosedImmersion B S hS b.left)
    (hT₀ : T₀.left = algebraOver k B S hS toS hk) (hT : T.left = squareZeroOver k B S hS toS V)
    (hβ : eqToHom hT₀.symm ≫ b.left ≫ eqToHom hT = squareZeroArrow k B S hS toS hk V) :
    (testSchemeModuleEquivalence D hbt hb hT₀ hT hβ).functor.Additive := by
  change (_ ⋙ SheafOfModules.restrictScalars _).Additive
  infer_instance

end SquareZero

end CoherentSituation

end AlgebraicGeometry.Space

end
