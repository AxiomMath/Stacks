module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObjectDerivedDescentUnconditional
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CohomologySpectralSequenceTagSheaf
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationComponentInverseImageAb
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject

/-!
# The cohomology spectral sequence of a hypercovering by a simplicial object

Let `C` be a site with fibre products, let `X` be an object of `C` and let `a : U ⟶ X` be a
hypercovering of `X` by a simplicial object `U` of `C`, in the sense of Stacks 09X8. For an
abelian sheaf `𝓕` on `C/X` the spectral sequence of Stacks 09WJ of the total site
`(C/U)_total`, applied to the inverse image `a⁻¹𝓕`, has first page

`E₁^{p,q} = H^q(C/U_p, a_p⁻¹𝓕)`

and abuts to `H^{p+q}(C/X, 𝓕)`. This is descent for the cohomology of `C/X` along the
hypercovering, in the form in which it is used for the étale cohomology spectral sequences of
the hypercoverings of algebraic spaces in Chapter 85: Stacks 09X9 identifies the abutment
`H^{p+q}((C/U)_total, a⁻¹𝓕)` of Stacks 09WJ with `H^{p+q}(C/X, 𝓕)`, and Stacks 0D70 (b)
identifies the restriction of `a⁻¹𝓕` to the component `C/U_p` with `a_p⁻¹𝓕`.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.hypercoveringInverseImage`: the inverse image
  `a⁻¹ : Ab(C/X) ⥤ Ab((C/U)_total)` along the augmentation of the hypercovering.
* `CategoryTheory.SimplicialSemiRepresentable.hypercoveringSpectralSequence`: the spectral
  sequence, as a functor of the abelian sheaf `𝓕` on `C/X`.
* `CategoryTheory.SimplicialSemiRepresentable.baseCohomology`: the integer-graded cohomology
  `H^n(C/X, 𝓕)`, the cohomology of `RΓ(C/X, 𝓕)`.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.hypercoveringSpectralSequence_pageOneIso`:
  `E₁^{p,q} = H^q(C/U_p, a_p⁻¹𝓕)`, naturally in `𝓕`.
* `CategoryTheory.SimplicialSemiRepresentable.hypercoveringSpectralSequence_abutsTo`: the
  spectral sequence abuts to `H^{p+q}(C/X, 𝓕)`.
* `CategoryTheory.SimplicialSemiRepresentable.baseCohomologyIsoRightDerived`: in the degrees
  `n ≥ 0` the abutment is the classical right derived functor `R^nΓ(C/X, 𝓕)`.
* `Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIsoResolution`: in every integer degree,
  the cohomology of the unbounded right derived functor at an object placed in degree zero is the
  cohomology of the functor applied to its chosen injective resolution.

## References

* [Stacks Project, Tag 09WJ](https://stacks.math.columbia.edu/tag/09WJ)
* [Stacks Project, Tag 09X8](https://stacks.math.columbia.edu/tag/09X8)
* [Stacks Project, Tag 09X9](https://stacks.math.columbia.edu/tag/09X9)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialSiteSituation

namespace Stacks.DerivedFunctor

universe v u vB uB wG wD wE

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{wG} A]
  [EnoughInjectives A] [HasDerivedCategory.{wD} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wE} B]

/-- For an object `M` placed in degree `0` of the unbounded derived category and every integer
`n`, the degree-`n` cohomology of the unbounded right derived functor of `F` at `M` is the
degree-`n` cohomology of `F` applied to the chosen injective resolution of `M`, extended by zero
to the integers. The chosen resolution is a bounded below complex of injectives, hence
K-injective, and the unit of the derived functor is invertible there. -/
def homologyTotalRightDerivedSingleIsoResolution (F : A ⥤ B) [F.Additive] (M : A) (n : ℤ) :
    (DerivedCategory.homologyFunctor B n).obj
        ((totalRightDerived F).obj ((DerivedCategory.singleFunctor A 0).obj M)) ≅
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (injectiveResolution M).cochainComplex).homology n := by
  let I := injectiveResolution M
  let K := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I.cochainComplex
  haveI : I.cochainComplex.IsKInjective :=
    CochainComplex.isKInjective_of_injective I.cochainComplex 0
  have hunit := isIso_totalRightDerivedUnit_app_of_isKInjective F I.cochainComplex
  let e : (DerivedCategory.singleFunctor A 0).obj M ≅ DerivedCategory.Qh.obj K :=
    (DerivedCategory.singleFunctorIsoCompQ A 0).app M ≪≫
      asIso (DerivedCategory.Q.map I.ι') ≪≫
      ((DerivedCategory.quotientCompQhIso A).app I.cochainComplex).symm
  let e' : (totalRightDerived F).obj ((DerivedCategory.singleFunctor A 0).obj M) ≅
      DerivedCategory.Q.obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex) :=
    (totalRightDerived F).mapIso e ≪≫ (@asIso _ _ _ _ _ hunit).symm ≪≫
      DerivedCategory.Qh.mapIso
        ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app I.cochainComplex) ≪≫
      (DerivedCategory.quotientCompQhIso B).app _
  exact (DerivedCategory.homologyFunctor B n).mapIso e' ≪≫
    (DerivedCategory.homologyFunctorFactors B n).app _

end Stacks.DerivedFunctor

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

open Stacks.CategoryTheory.Hypercovering

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (U : SimplicialObject C) (a : U ⟶ (SimplicialObject.const C).obj X)

/-- The inverse image `a⁻¹ : Ab(C/X) ⥤ Ab((C/U)_total)` along the augmentation of Stacks 09X8
of an augmented simplicial object `a : U ⟶ X` of the site. -/
abbrev hypercoveringInverseImage :
    Sheaf (P.toGrothendieck.over X) AddCommGrpCat.{u} ⥤
      Sheaf (totalSituation P U a).totalTopology AddCommGrpCat.{u} :=
  Augmentation.totalInverseImageAb (totalSituation P U a) (Cat.of (Over X))
    (P.toGrothendieck.over X) (augmentationAugmented P U a)

/-- The inverse image `a_p⁻¹ : Ab(C/X) ⥤ Ab(C/U_p)` along the augmentation in simplicial
degree `p`. -/
abbrev hypercoveringComponentInverseImage (p : ℕ) :
    Sheaf (P.toGrothendieck.over X) AddCommGrpCat.{u} ⥤
      Sheaf ((totalSituation P U a).componentTopology (SimplexCategory.mk p)) AddCommGrpCat.{u} :=
  Augmentation.componentInverseImageAb (totalSituation P U a) (Cat.of (Over X))
    (P.toGrothendieck.over X) (augmentationAugmented P U a) (SimplexCategory.mk p)

/-- **The cohomology spectral sequence of a hypercovering**, as a functor of the abelian sheaf
`𝓕` on `C/X`: the spectral sequence of Stacks 09WJ of the total site `(C/U)_total` at the
inverse image `a⁻¹𝓕`. -/
def hypercoveringSpectralSequence :
    Sheaf (P.toGrothendieck.over X) AddCommGrpCat.{u} ⥤
      CohomologicalSpectralSequence AddCommGrpCat.{u} 1 :=
  hypercoveringInverseImage P U a ⋙ (totalSituation P U a).cohomologySpectralSequence

/-- **`E₁^{p,q} = H^q(C/U_p, a_p⁻¹𝓕)`**, naturally in the abelian sheaf `𝓕` on `C/X`: the first
page of Stacks 09WJ at `a⁻¹𝓕`, with the restriction of `a⁻¹𝓕` to the component `C/U_p`
identified with `a_p⁻¹𝓕` by Stacks 0D70 (b). -/
def hypercoveringSpectralSequence_pageOneIso (p q : ℕ) :
    hypercoveringSpectralSequence P U a ⋙
        CategoryTheory.SpectralSequence.pageFunctor AddCommGrpCat.{u} _ 1 1 le_rfl ⋙
          HomologicalComplex.eval AddCommGrpCat.{u} _ ((p : ℤ), (q : ℤ)) ≅
      hypercoveringComponentInverseImage P U a p ⋙
        (Sheaf.Γ ((totalSituation P U a).componentTopology (SimplexCategory.mk p))
          AddCommGrpCat.{u}).rightDerived q :=
  Functor.isoWhiskerLeft (hypercoveringInverseImage P U a)
      ((totalSituation P U a).cohomologySpectralSequence_pageOneIso p q) ≪≫
    Functor.isoWhiskerRight
      (componentRestrictionAbInverseImageNatIso' (totalSituation P U a) (Cat.of (Over X))
        (P.toGrothendieck.over X) (augmentationAugmented P U a) (SimplexCategory.mk p))
      ((Sheaf.Γ ((totalSituation P U a).componentTopology (SimplexCategory.mk p))
        AddCommGrpCat.{u}).rightDerived q)

/-- The integer-graded cohomology `H^n(C/X, 𝓕)`: the degree-`n` cohomology of the derived global
sections `RΓ(C/X, 𝓕)` of the abelian sheaf `𝓕` placed in degree zero. -/
abbrev baseCohomology (F : Sheaf (P.toGrothendieck.over X) AddCommGrpCat.{u}) (n : ℤ) :
    AddCommGrpCat.{u} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
    ((Augmentation.derivedGlobalSectionsBase (Cat.of (Over X)) (P.toGrothendieck.over X)).obj
      ((DerivedCategory.singleFunctor _ 0).obj F))

/-- Global sections of abelian sheaves on `C/X` are additive, being a right adjoint. -/
instance additive_globalSectionsOver :
    (Sheaf.Γ (P.toGrothendieck.over X) AddCommGrpCat.{u}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- In the degrees `n ≥ 0` the integer-graded cohomology `H^n(C/X, 𝓕)` is the classical right
derived functor `R^nΓ(C/X, 𝓕)`. -/
def baseCohomologyIsoRightDerived (F : Sheaf (P.toGrothendieck.over X) AddCommGrpCat.{u})
    (n : ℕ) :
    baseCohomology P F (n : ℤ) ≅
      ((Sheaf.Γ (P.toGrothendieck.over X) AddCommGrpCat.{u}).rightDerived n).obj F :=
  Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso _
    (Stacks.DerivedFunctor.totalRightDerived
      (Sheaf.Γ (P.toGrothendieck.over X) AddCommGrpCat.{u}))
    ((Stacks.DerivedFunctor.homotopyMap
      (Sheaf.Γ (P.toGrothendieck.over X) AddCommGrpCat.{u})).totalRightDerivedUnit
        DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Sheaf (P.toGrothendieck.over X) AddCommGrpCat.{u})
          (ComplexShape.up ℤ)))
    Stacks.Cohomology.Localization.enoughKInjectives F n

/-- **Descent of cohomology along a hypercovering, degree by degree.** For a hypercovering
`a : U ⟶ X` and an abelian sheaf `𝓕` on `C/X`, the cohomology `H^n((C/U)_total, a⁻¹𝓕)` in
which the spectral sequence of Stacks 09WJ converges is `H^n(C/X, 𝓕)`, by Stacks 09X9. -/
def totalCohomologyZIsoBaseCohomology (h : IsHypercoveringAugmentation P U a)
    (F : Sheaf (P.toGrothendieck.over X) AddCommGrpCat.{u}) (n : ℤ) :
    (totalSituation P U a).totalCohomologyZ ((hypercoveringInverseImage P U a).obj F) n ≅
      baseCohomology P F n :=
  (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIsoResolution
      (Sheaf.Γ (totalSituation P U a).totalTopology AddCommGrpCat.{u})
      ((hypercoveringInverseImage P U a).obj F) n).symm ≪≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).mapIso
      ((Augmentation.derivedGlobalSectionsTotal (totalSituation P U a)).mapIso
        (Augmentation.derivedTotalInverseImageSingleFunctorObjIso (totalSituation P U a)
          (Cat.of (Over X)) (P.toGrothendieck.over X) (augmentationAugmented P U a) F).symm) ≪≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).mapIso
      ((derivedGlobalSectionsInverseImageIsoAugmented' P U a h).app
        ((DerivedCategory.singleFunctor _ 0).obj F)).symm

/-- **The cohomology spectral sequence of a hypercovering abuts to `H^{p+q}(C/X, 𝓕)`.** Its
infinity page at `(p, q)` is the `p`-th graded piece of a finite filtration of `H^{p+q}(C/X, 𝓕)`:
the abutment `H^{p+q}((C/U)_total, a⁻¹𝓕)` of Stacks 09WJ, transported along Stacks 09X9. -/
theorem hypercoveringSpectralSequence_abutsTo (h : IsHypercoveringAugmentation P U a)
    (F : Sheaf (P.toGrothendieck.over X) AddCommGrpCat.{u}) :
    CategoryTheory.SpectralSequence.AbutsTo ((hypercoveringSpectralSequence P U a).obj F)
      (baseCohomology P F) :=
  ((totalSituation P U a).cohomologySpectralSequence_abutsTo
    ((hypercoveringInverseImage P U a).obj F)).of_iso
      (totalCohomologyZIsoBaseCohomology P U a h F)

end CategoryTheory.SimplicialSemiRepresentable

end
