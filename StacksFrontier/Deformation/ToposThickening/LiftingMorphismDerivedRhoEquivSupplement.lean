module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.ChaoticSiteCoveringObject
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentExtZero
public import StacksFrontier.Deformation.ToposThickening.LiftingMorphismDerivedRhoEquiv

/-!
# The identification of Ext groups of Stacks 0GQ8: vanishing and other degrees

Let `f : (Sh(𝒞), 𝒪_𝒞) ⟶ (Sh(ℬ), 𝒪_ℬ)` and `g : (Sh(𝒟), 𝒪_𝒟) ⟶ (Sh(𝒞), 𝒪_𝒞)` be morphisms of
ringed topoi and `𝒢` an `𝒪_𝒟`-module. This file supplements
`StacksFrontier.Deformation.ToposThickening.LiftingMorphismDerivedRhoEquiv`, which identifies
`Ext¹_{𝒪_𝒟}(Lg^*NL_{𝒪_𝒞/𝒪_ℬ}, 𝒢) = Ext¹_{g⁻¹𝒪_𝒞}(NL_{g⁻¹𝒪_𝒞/g⁻¹f⁻¹𝒪_ℬ}, 𝒢)` (Stacks 0GQ8),
with the vanishing of classes under that identification, the same identification in an
arbitrary degree `n`, and its degree `0` case read through differentials. The declarations are
stated in the same context as the base file, with the same derived-category model.

## Main definitions

* `Deformation.ToposThickening.LiftingMorphismDerived.rhoClassShift` and `.rhoShiftAddEquiv`:
  the identification of Stacks 0GQ8 in an arbitrary degree `n`, as an additive equivalence.
* `.extZeroDifferentialsAddEquiv`: its degree `0` case read through
  `Ext⁰(NL_{B/A}, 𝒢) = Hom(Ω_{B/A}, 𝒢)`, which is the second equality of the display of
  Stacks 08UG, clause (2).

## Main results

* `.rhoEquiv_zero` and `.rhoEquiv_symm_eq_zero_iff`: the identification preserves and reflects
  the vanishing of a class.
* `.rhoClassShift_bijective` and `.rhoClassShift_add`: `rhoClassShift` is bijective and additive.

## References

* [Stacks Project, Tag 0GQ8](https://stacks.math.columbia.edu/tag/0GQ8)
* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry (RingedTopos RingedToposHom)

universe u v' u' w'

namespace Deformation.ToposThickening.LiftingMorphismDerived

open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor inverseImageRingSheaf)
open Stacks.Sheaves.RingedToposModules (inverseImageModules extendScalarsFSharp)
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat hasResolutions_isKFlat)
open Deformation.ToposThickening.InverseImageExtension (invImage inverseImageRingedTopos
  toInverseImage)

attribute [local instance 10000] HasDerivedCategory.standard

/-- A composite through a zero morphism vanishes, in the shape of `rhoClass`. -/
private lemma comp_zero_comp_aux {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞]
    {A₁ A₂ A₃ A₄ A₅ A₆ A₇ A₈ : 𝒞} (p₁ : A₁ ⟶ A₂) (p₂ : A₂ ⟶ A₃) (p₃ : A₃ ⟶ A₄)
    (p₄ : A₄ ⟶ A₅) (q₁ : A₆ ⟶ A₇) (q₂ : A₇ ⟶ A₈) :
    p₁ ≫ p₂ ≫ p₃ ≫ p₄ ≫ (0 : A₅ ⟶ A₆) ≫ q₁ ≫ q₂ = 0 := by
  simp

/-- A composite through the image of a sum under an additive functor, in the shape of
`rhoClassShift`, is the sum of the two composites. -/
private lemma comp_map_add_comp_aux {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] [Preadditive 𝒞]
    [Preadditive 𝒟] (F : 𝒞 ⥤ 𝒟) [F.Additive] {A₁ A₂ A₃ A₄ : 𝒟} {B₁ B₂ : 𝒞} {A₆ A₇ : 𝒟}
    (p₁ : A₁ ⟶ A₂) (p₂ : A₂ ⟶ A₃) (p₃ : A₃ ⟶ A₄) (p₄ : A₄ ⟶ F.obj B₁) (e e' : B₁ ⟶ B₂)
    (q₁ : F.obj B₂ ⟶ A₆) (q₂ : A₆ ⟶ A₇) :
    p₁ ≫ p₂ ≫ p₃ ≫ p₄ ≫ F.map (e + e') ≫ q₁ ≫ q₂ =
      p₁ ≫ p₂ ≫ p₃ ≫ p₄ ≫ F.map e ≫ q₁ ≫ q₂ + p₁ ≫ p₂ ≫ p₃ ≫ p₄ ≫ F.map e' ≫ q₁ ≫ q₂ := by
  simp

variable {X Y : RingedTopos.{u, u, u}}
  [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (g : RingedToposHom Y X)

section RhoEquiv

open Deformation.ToposThickening.RingedToposExtensionProblem (ofTrivialBase)
open Deformation.ToposThickening.InverseImageExtension (baseIso restrictedIdeal pushoutSolution
  pullbackSolution)

variable {B : RingedTopos.{v', u', w'}} [B.J.HasSheafCompose (forget RingCat.{w'})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y.J.HasSheafCompose (forget CommRingCat.{u})]
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}]
  {f : RingedToposHom X B}
  {G : SheafOfModules.{u} ((sheafCompose Y.J (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.O)}

/-- The identification of Stacks 0GQ8 carries the zero class to the zero class. -/
theorem rhoEquiv_zero : rhoEquiv (f := f) (G := G) g 0 = 0 := by
  rw [rhoEquiv_apply, rhoClass]
  have : (restrictDerived g).Additive :=
    inferInstanceAs ((restrictAlong g).mapDerivedCategory.Additive)
  erw [Functor.map_zero]
  exact comp_zero_comp_aux _ _ _ _ _ _

/-- A class on `NL_{g⁻¹𝒪_𝒞/(f ∘ g)⁻¹𝒪_ℬ}` read on `Lg^*NL_{𝒪_𝒞/𝒪_ℬ}` through the identification of
Stacks 0GQ8 vanishes exactly when it vanishes. -/
theorem rhoEquiv_symm_eq_zero_iff (x) :
    (rhoEquiv (f := f) (G := G) g).symm x = 0 ↔ x = 0 := by
  rw [Equiv.symm_apply_eq, rhoEquiv_zero]

/-- **`rhoClass` in an arbitrary degree `n`**: for `e : Lg^*NL_{𝒪_𝒞/𝒪_ℬ} ⟶ 𝒢[n]`, the composite
of the change of base ring, the inverse of the identification of Stacks 08TZ, the derived unit and
the restriction of scalars of `e`, with `res(𝒢[n]) = (res 𝒢)[n]`. In degree `1` it is
`rhoClass`. -/
def rhoClassShift (n : ℤ)
    (e : DerivedCategory.Ext ((derivedPullback g).obj (DerivedCategory.Q.obj
        (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} X.J
          ((inverseImageCommRingFunctor f.toToposHom).obj B.O) X.O f.fSharpInverseImage)))
      ((DerivedCategory.singleFunctor _ 0).obj G) n) :
    DerivedCategory.Ext (DerivedCategory.Q.obj
        (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} Y.J
        ((inverseImageCommRingFunctor (f.comp (toInverseImage g)).toToposHom).obj B.O)
        ((invImage g).obj X.O) (f.comp (toInverseImage g)).fSharpInverseImage))
      ((DerivedCategory.singleFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((invImage g).obj X.O))) 0).obj
          (restrictedIdeal g G)) n :=
  DerivedCategory.Q.map (baseIsoChange g) ≫
    DerivedCategory.Q.map
      (Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso.{u, u, u, u, u, u}
      Y.J X.J g.toToposHom (A := (inverseImageCommRingFunctor f.toToposHom).obj B.O) (B := X.O)
      f.fSharpInverseImage).inv ≫
    (inverseImageModules g.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapDerivedCategoryFactors.inv.app _ ≫
    (derivedUnit g).app _ ≫ (restrictDerived g).map e ≫
    ((restrictAlong g).mapDerivedCategory.commShiftIso n).hom.app _ ≫
    (shiftFunctor (DerivedCategory (SheafOfModules.{u}
        (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf g.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) n).map
      (((restrictAlong g).mapDerivedCategorySingleFunctor 0).hom.app G)

/-- `rhoClassShift` is bijective in every degree, for the reason `rhoClass` is
(`rhoClass_bijective`). -/
theorem rhoClassShift_bijective (n : ℤ) :
    Function.Bijective (rhoClassShift (f := f) (G := G) g n) := by
  have pre : ∀ {𝒞 : Type (u + 1)} [Category.{u + 1} 𝒞] {P Q Z : 𝒞} (a : P ≅ Q),
      Function.Bijective (fun x : Q ⟶ Z => a.hom ≫ x) :=
    fun a => (Iso.homFromEquiv a.symm).bijective
  let a₁ := asIso (baseIsoChange (f := f) g)
  exact (pre (DerivedCategory.Q.mapIso a₁)).comp
    ((pre (DerivedCategory.Q.mapIso
      (Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso.{u, u, u, u, u, u}
      Y.J X.J g.toToposHom (A := (inverseImageCommRingFunctor f.toToposHom).obj B.O) (B := X.O)
      f.fSharpInverseImage).symm)).comp
    ((pre ((inverseImageModules g.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapDerivedCategoryFactors.app _).symm).comp
    ((isUniversal_derivedUnit_app g _).bijective_comp_iso (derivedExtendAdjunction g)
      (((restrictAlong g).mapDerivedCategory.commShiftIso n).app _ ≪≫
        (shiftFunctor (DerivedCategory (SheafOfModules.{u}
          (inverseImageRingSheaf g.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) n).mapIso
          (((restrictAlong g).mapDerivedCategorySingleFunctor 0).app G)))))

/-- `rhoClassShift` is additive. -/
theorem rhoClassShift_add (n : ℤ) (e e') :
    rhoClassShift (f := f) (G := G) g n (e + e') =
      rhoClassShift (f := f) (G := G) g n e + rhoClassShift (f := f) (G := G) g n e' := by
  have : (restrictDerived g).Additive :=
    inferInstanceAs ((restrictAlong g).mapDerivedCategory.Additive)
  exact comp_map_add_comp_aux (restrictDerived g) _ _ _ _ e e' _ _

/-- **Stacks 0GQ8 in an arbitrary degree**, as an additive equivalence:
`Ext^n_{𝒪_𝒟}(Lg^*NL_{𝒪_𝒞/𝒪_ℬ}, 𝒢) = Ext^n_{g⁻¹𝒪_𝒞}(NL_{g⁻¹𝒪_𝒞/(f ∘ g)⁻¹𝒪_ℬ}, 𝒢)`. -/
def rhoShiftAddEquiv (n : ℤ) :
    DerivedCategory.Ext ((derivedPullback g).obj (DerivedCategory.Q.obj
        (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} X.J
          ((inverseImageCommRingFunctor f.toToposHom).obj B.O) X.O f.fSharpInverseImage)))
      ((DerivedCategory.singleFunctor _ 0).obj G) n ≃+
    DerivedCategory.Ext (DerivedCategory.Q.obj
        (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} Y.J
        ((inverseImageCommRingFunctor (f.comp (toInverseImage g)).toToposHom).obj B.O)
        ((invImage g).obj X.O) (f.comp (toInverseImage g)).fSharpInverseImage))
      ((DerivedCategory.singleFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((invImage g).obj X.O))) 0).obj
          (restrictedIdeal g G)) n :=
  { Equiv.ofBijective _ (rhoClassShift_bijective (f := f) (G := G) g n) with
    map_add' := rhoClassShift_add g n }

/-- **The `Ext⁰` group of `Lg^*NL_{𝒪_𝒞/𝒪_ℬ}`**: `Ext⁰_{𝒪_𝒟}(Lg^*NL_{𝒪_𝒞/𝒪_ℬ}, 𝒢)` is
`Hom_{g⁻¹𝒪_𝒞}(Ω_{g⁻¹𝒪_𝒞/g⁻¹f⁻¹𝒪_ℬ}, 𝒢)`, by Stacks 0GQ8 in degree `0`, the change of base ring
`(f ∘ g)⁻¹𝒪_ℬ ≅ g⁻¹f⁻¹𝒪_ℬ`, and `Ext⁰(NL_{B/A}, 𝒢) = Hom(Ω_{B/A}, 𝒢)` (the naive cotangent
complex lives in degrees `≤ 0` and its `H⁰` is `Ω_{B/A}`, Stacks 08TY). -/
def extZeroDifferentialsAddEquiv :
    DerivedCategory.Ext ((derivedPullback g).obj (DerivedCategory.Q.obj
        (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} X.J
          ((inverseImageCommRingFunctor f.toToposHom).obj B.O) X.O f.fSharpInverseImage)))
      ((DerivedCategory.singleFunctor _ 0).obj G) 0 ≃+
    (AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSite.{u, u, u, u}
        ((invImage g).obj ((inverseImageCommRingFunctor f.toToposHom).obj B.O))
        ((invImage g).obj X.O) ((invImage g).map f.fSharpInverseImage) ⟶
      (show SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf ((invImage g).obj X.O)) from
        restrictedIdeal g G)) :=
  haveI : Presheaf.IsLocallySurjective Y.J (Stacks.SheafOfModules.presentation Y.J
      ((invImage g).obj ((inverseImageCommRingFunctor f.toToposHom).obj B.O))
      ((invImage g).obj X.O) ((invImage g).map f.fSharpInverseImage)
      (Stacks.Sites.FreeAlgebra.underlyingPresheaf Y.J ((invImage g).obj X.O)) (𝟙 _)).hom :=
    (Presheaf.isLocallySurjective_iff_whisker_forget Y.J _).mpr
      (Stacks.Sites.FreeAlgebra.canonicalPresentation_isLocallySurjective Y.J _ _ _)
  (rhoShiftAddEquiv (f := f) (G := G) g 0).trans
    ((Stacks.Cohomology.precompAddEquiv
      (DerivedCategory.Q.mapIso (asIso (baseIsoChange (f := f) g)))).trans
      (Stacks.SheafOfModules.presentationNaiveCotangentExtZeroAddEquiv.{u, u, u, u, u + 1} Y.J
        ((invImage g).obj ((inverseImageCommRingFunctor f.toToposHom).obj B.O))
        ((invImage g).obj X.O) ((invImage g).map f.fSharpInverseImage)
        (Stacks.Sites.FreeAlgebra.underlyingPresheaf Y.J ((invImage g).obj X.O)) (𝟙 _)
        (restrictedIdeal g G)))

end RhoEquiv

end Deformation.ToposThickening.LiftingMorphismDerived
