module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor

/-!
# Base change maps between unbounded right derived functors

Consider a square of additive functors between abelian categories
```
A --G'--> A'
|F        |F'
v         v
B --G---> B'
```
with `G` and `G'` exact, and a transformation `α : F ⋙ G ⟶ G' ⋙ F'`. Given right derived
functors `RF : D(A) ⥤ D(B)` and `RF' : D(A') ⥤ D(B')` of `F` and `F'` along the localizations
`DerivedCategory.Q` of unbounded cochain complexes, and assuming that `G` acts on derived
categories as a left adjoint, this file constructs the induced *base change map*
$$
G \circ RF \longrightarrow RF' \circ G'
$$
of functors `D(A) ⥤ D(B')`. The exact functors act on derived categories degreewise
(`CategoryTheory.Functor.mapDerivedCategory`), `RF ⋙ G` is a right derived functor of degreewise
`F` followed by `G` because `G` is a left adjoint, and the degreewise transformation `α`, followed
by the derived-functor unit of `RF'`, descends along that universal property.

This is the shape of the base change map `g^{-1} Rf_* ⟶ Rf'_* (g')^{-1}` of [Stacks, Tag 0A2A]
on unbounded complexes, where `F = f_*`, `F' = f'_*`, `G = g^{-1}`, `G' = (g')^{-1}` and `α` is
the underived base change comparison. It is the unbounded counterpart of
`Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlus`.

## Main definitions

* `Stacks.Cohomology.DerivedBaseChangeUnbounded.complexMap`: `α` applied degreewise to
  unbounded complexes.
* `Stacks.Cohomology.DerivedBaseChangeUnbounded.derivedBaseChange`: the base change map
  `RF ⋙ G ⟶ G' ⋙ RF'`.

## Main results

* `Stacks.Cohomology.DerivedBaseChangeUnbounded.derivedBaseChange_fac`: precomposed with `G` of
  the derived-functor unit of `RF` at a complex `K`, the base change map is the exactness
  comparison of `G`, the localized degreewise `α`, the derived-functor unit of `RF'` and the
  exactness comparison of `G'`.
* `Stacks.Cohomology.DerivedBaseChangeUnbounded.isIso_derivedBaseChange_of_injective`: over a
  Grothendieck abelian `A`, the base change map is an isomorphism as soon as `α` is invertible at
  every injective object and `G'(I)` computes `RF'` for every complex `I` of injectives.

## Implementation notes

Everything is stated for abstract categories, so that the instances at concrete categories of
sheaves never have to be reduced: the components of the composite transformations are read off
with `CategoryTheory.NatTrans.comp_app`, and a consumer instantiates the equations.

## References

* [Stacks Project, Tag 0A2A](https://stacks.math.columbia.edu/tag/0A2A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.DerivedBaseChangeUnbounded

universe w vA uA vA' uA' vB uB vB' uB' dA dA' dB dB'

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{dA} A]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A'] [HasDerivedCategory.{dA'} A']
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{dB} B]
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B'] [HasDerivedCategory.{dB'} B']
  (F : A ⥤ B) [F.Additive] (F' : A' ⥤ B') [F'.Additive]
  (G : B ⥤ B') [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (G' : A ⥤ A') [G'.Additive] [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  (α : F ⋙ G ⟶ G' ⋙ F')
  (RF : DerivedCategory A ⥤ DerivedCategory B)
  (αF : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ RF)
  (RF' : DerivedCategory A' ⥤ DerivedCategory B')
  (αF' : F'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ RF')

/-- The transformation `α` applied degreewise to unbounded cochain complexes. -/
def complexMap :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ G.mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      G'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        F'.mapHomologicalComplex (ComplexShape.up ℤ) :=
  (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).hom ≫
    NatTrans.mapHomologicalComplex α _ ≫ (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).inv

omit [HasDerivedCategory A] [HasDerivedCategory A'] [HasDerivedCategory B] [HasDerivedCategory B']
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] [PreservesFiniteLimits G']
  [PreservesFiniteColimits G'] in
/-- In each degree, the degreewise transformation is `α`. -/
@[simp]
theorem complexMap_app_f (K : CochainComplex A ℤ) (i : ℤ) :
    ((complexMap F F' G G' α).app K).f i = α.app (K.X i) := by
  simp [complexMap]

/-- The derived-functor unit exhibiting `RF ⋙ G` as a right derived functor of degreewise `F`
followed by `G`: the unit of `RF` whiskered with `G`. -/
abbrev unit :
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙ G.mapDerivedCategory ⟶
      DerivedCategory.Q ⋙ (RF ⋙ G.mapDerivedCategory) :=
  Functor.whiskerRight αF G.mapDerivedCategory ≫ (Functor.associator _ _ _).hom

/-- The transformation that the universal property of `RF ⋙ G` descends: the exactness
comparison of `G`, the localized degreewise `α`, the derived-functor unit of `RF'`, and the
exactness comparison of `G'`. -/
def beta :
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙ G.mapDerivedCategory ⟶
      DerivedCategory.Q ⋙ (G'.mapDerivedCategory ⋙ RF') :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (F.mapHomologicalComplex _) G.mapDerivedCategoryFactors.hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (complexMap F F' G G' α) DerivedCategory.Q ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (G'.mapHomologicalComplex _) αF' ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight G'.mapDerivedCategoryFactors.inv RF' ≫
    (Functor.associator _ _ _).hom

/-- The component of `unit` at a complex is `G` applied to the component of `αF`. -/
theorem unit_app (K : CochainComplex A ℤ) :
    (unit F G RF αF).app K = G.mapDerivedCategory.map (αF.app K) := by
  simp [unit]

/-- The component of `beta` at a complex, written out. -/
theorem beta_app (K : CochainComplex A ℤ) :
    (beta F F' G G' α RF' αF').app K =
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex _).obj K) ≫
        DerivedCategory.Q.map ((complexMap F F' G G' α).app K) ≫
        αF'.app ((G'.mapHomologicalComplex _).obj K) ≫
        RF'.map (G'.mapDerivedCategoryFactors.inv.app K) := by
  simp [beta]

variable [G.mapDerivedCategory.IsLeftAdjoint]
  [RF.IsRightDerivedFunctor αF (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]

/-- **The base change map `RF ⋙ G ⟶ G' ⋙ RF'`** induced by `α : F ⋙ G ⟶ G' ⋙ F'` on unbounded
derived categories. -/
def derivedBaseChange : RF ⋙ G.mapDerivedCategory ⟶ G'.mapDerivedCategory ⋙ RF' :=
  (RF ⋙ G.mapDerivedCategory).rightDerivedDesc (unit F G RF αF)
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) (G'.mapDerivedCategory ⋙ RF')
    (beta F F' G G' α RF' αF')

/-- **The characterization of the base change map on unbounded complexes.** At the object
represented by a complex `K`, the base change map precomposed with `G` of the derived-functor
unit of `RF` is the exactness comparison of `G`, the localized degreewise `α`, the
derived-functor unit of `RF'` and the exactness comparison of `G'`. -/
theorem derivedBaseChange_fac (K : CochainComplex A ℤ) :
    G.mapDerivedCategory.map (αF.app K) ≫
      (derivedBaseChange F F' G G' α RF αF RF' αF').app (DerivedCategory.Q.obj K) =
    G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex _).obj K) ≫
      DerivedCategory.Q.map ((complexMap F F' G G' α).app K) ≫
      αF'.app ((G'.mapHomologicalComplex _).obj K) ≫
      RF'.map (G'.mapDerivedCategoryFactors.inv.app K) := by
  have hfac : (unit F G RF αF).app K ≫
      (derivedBaseChange F F' G G' α RF αF RF' αF').app (DerivedCategory.Q.obj K) =
        (beta F F' G G' α RF' αF').app K :=
    (RF ⋙ G.mapDerivedCategory).rightDerived_fac_app (unit F G RF αF)
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) (G'.mapDerivedCategory ⋙ RF')
      (beta F F' G G' α RF' αF') K
  rw [unit_app, beta_app] at hfac
  exact hfac

/-- **The base change map is invertible at a complex `K`** as soon as `K` computes `RF`, the
degreewise transformation is invertible at `K`, and `G'(K)` computes `RF'`: in the equation
`derivedBaseChange_fac` every other factor is an isomorphism. -/
theorem isIso_derivedBaseChange_app (K : CochainComplex A ℤ) (h₁ : IsIso (αF.app K))
    (h₂ : IsIso ((complexMap F F' G G' α).app K))
    (h₃ : IsIso (αF'.app ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) :
    IsIso ((derivedBaseChange F F' G G' α RF αF RF' αF').app (DerivedCategory.Q.obj K)) := by
  have hfac := derivedBaseChange_fac F F' G G' α RF αF RF' αF' K
  exact IsIso.of_isIso_fac_left hfac

/-- **The base change map is invertible at a complex `K`** as soon as `K` computes `RF`, `α` is
invertible at every term of `K`, and `G'(K)` computes `RF'`. -/
theorem isIso_derivedBaseChange_app_of_forall (K : CochainComplex A ℤ) (h₁ : IsIso (αF.app K))
    (h₂ : ∀ i : ℤ, IsIso (α.app (K.X i)))
    (h₃ : IsIso (αF'.app ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) :
    IsIso ((derivedBaseChange F F' G G' α RF αF RF' αF').app (DerivedCategory.Q.obj K)) := by
  refine isIso_derivedBaseChange_app F F' G G' α RF αF RF' αF' K h₁ ?_ h₃
  have (i : ℤ) : IsIso (((complexMap F F' G G' α).app K).f i) := by
    rw [complexMap_app_f]
    exact h₂ i
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **The base change map is an isomorphism** as soon as `α` is invertible at every injective
object of `A` and `G'(I)` computes `RF'` for every complex `I` of injective objects. Every
object of `D(A)` is represented by a K-injective complex of injectives ([Stacks, Tag 079P]),
which computes `RF`. -/
theorem isIso_derivedBaseChange_of_injective [IsGrothendieckAbelian.{w} A]
    (hα : ∀ I : A, Injective I → IsIso (α.app I))
    (hunit : ∀ J : CochainComplex A ℤ, (∀ i : ℤ, Injective (J.X i)) →
      IsIso (αF'.app ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj J))) :
    IsIso (derivedBaseChange F F' G G' α RF αF RF' αF') := by
  have hE : ∀ E : DerivedCategory A,
      IsIso ((derivedBaseChange F F' G G' α RF αF RF' αF').app E) := by
    intro E
    have := Localization.essSurj DerivedCategory.Q
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    obtain ⟨K, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := DerivedCategory.Q) (Y := E)
      (self := inferInstance)
    let I := (Stacks.Injectives.kInjectiveResolutionFunctor A).obj K
    have : IsIso (DerivedCategory.Q.map
        ((Stacks.Injectives.kInjectiveResolutionInclusion A).app K)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
    let e' : DerivedCategory.Q.obj I ≅ E :=
      (asIso (DerivedCategory.Q.map
        ((Stacks.Injectives.kInjectiveResolutionInclusion A).app K))).symm ≪≫ e
    refine (NatTrans.isIso_app_iff_of_iso _ e').1 ?_
    exact isIso_derivedBaseChange_app_of_forall F F' G G' α RF αF RF' αF' I
      (Stacks.Injectives.KInjectiveResolution.isIso_app_of_isKInjective.{w} DerivedCategory.Q RF
        αF (Stacks.Injectives.KInjectiveResolution.invertsQuasiIso_mapHomologicalComplex_comp_Q F)
        I inferInstance)
      (fun i ↦ hα _ inferInstance) (hunit I fun i ↦ inferInstance)
  exact NatIso.isIso_of_isIso_app _

/-- **The base change map is an isomorphism**, with the two hypotheses of
`isIso_derivedBaseChange_of_injective` stated as the invertibility of natural transformations:
`α` restricted to the injective objects of `A`, and the unit of `RF'` restricted to the images
under `G'` of the complexes of injectives. -/
theorem isIso_derivedBaseChange_of_isIso_whiskerLeft [IsGrothendieckAbelian.{w} A]
    (hα : IsIso (Functor.whiskerLeft (ObjectProperty.ι fun I : A ↦ Injective I) α))
    (hunit : IsIso (Functor.whiskerLeft
      (ObjectProperty.ι (fun J : CochainComplex A ℤ ↦ ∀ i : ℤ, Injective (J.X i)) ⋙
        G'.mapHomologicalComplex (ComplexShape.up ℤ)) αF')) :
    IsIso (derivedBaseChange F F' G G' α RF αF RF' αF') :=
  isIso_derivedBaseChange_of_injective.{w} F F' G G' α RF αF RF' αF'
    (fun I hI ↦ (NatIso.isIso_app_of_isIso
      (Functor.whiskerLeft (ObjectProperty.ι fun I : A ↦ Injective I) α) ⟨I, hI⟩ :))
    (fun J hJ ↦ (NatIso.isIso_app_of_isIso (Functor.whiskerLeft
      (ObjectProperty.ι (fun J : CochainComplex A ℤ ↦ ∀ i : ℤ, Injective (J.X i)) ⋙
        G'.mapHomologicalComplex (ComplexShape.up ℤ)) αF') ⟨J, hJ⟩ :))

end Stacks.Cohomology.DerivedBaseChangeUnbounded

end
