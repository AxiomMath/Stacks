module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor

/-!
# A right derived functor commutes with an exact change of categories

Consider a square of abelian categories
```
A₂ --F--> B₂
|          |
cA         cB
|          |
A₁ --F'--> B₁
```
in which the horizontal functors are merely additive -- so that they have to be *derived* -- and
the vertical ones are exact, hence applied degreewise.  If the square commutes, `A₂` is
Grothendieck abelian, and the unit of `RF'` is invertible at `cA` of every K-injective complex,
then the square of derived functors
```
D(A₂) --RF--> D(B₂)
|              |
cA             cB
|              |
D(A₁) --RF'--> D(B₁)
```
commutes as well.

## Main definitions

* `Stacks.DerivedSquare.exactChangeSource`: the underived functor both derived composites are
  right derived functors of -- apply `F` degreewise, change by `cB`, localize.
* `Stacks.DerivedSquare.exactChangeUnitDerivedFirst` and
  `Stacks.DerivedSquare.exactChangeUnitChangeFirst`: the two units.

## Main results

* `Stacks.DerivedSquare.rightDerivedExactChangeIso`: **the square of derived functors
  commutes**, `RF ⋙ cB ≅ cA ⋙ RF'`.
* `Stacks.DerivedSquare.isIso_rightDerivedUnit_app_of_exact`: the hypothesis on the unit of
  `RF'` is automatic when `F'` is itself exact, in which case it holds at every complex and not
  only at the complexes coming from `A₂`.

## Implementation notes

Both composites are right derived functors of one underived functor, so they are isomorphic by
the uniqueness `CategoryTheory.Functor.rightDerivedUnique` of right derived functors; no
comparison map has to be constructed by hand and no naturality has to be checked.  Recognising
each composite as a right derived functor is
`Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_iff_isIso_app_of_isKInjective`,
and the only input that is not formal is the invertibility of the unit of `RF'` at the complexes
`cA(I)` for `I` K-injective: those are *not* K-injective in general, which is the whole
mathematical content of a statement of this shape.

`CategoryTheory.Functor.mapDerivedCategorySquareIso` is the companion statement in which all
four functors are exact.  That case is strictly easier -- every functor there is applied
degreewise and nothing is derived -- and it does not apply here, the direct image of sheaves
being the motivating `F`.

Everything is stated for the localization `DerivedCategory.Q` out of cochain complexes rather
than for `DerivedCategory.Qh` out of the homotopy category, because that is the shape in which
the unbounded derived functors built by Spaltenstein's theorem
(`Stacks.Injectives.KInjectiveResolution.hasRightDerivedFunctor_mapHomologicalComplex_comp_Q`)
come.

## References

* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category
open Stacks.Injectives.KInjectiveResolution

universe w w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace Stacks.DerivedSquare

section Exact

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  [IsGrothendieckAbelian.{w} A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₂} B]

/-- **The unit of the right derived functor of an exact functor is invertible everywhere.**  An
exact functor preserves homology, hence sends a quasi-isomorphism of complexes to a
quasi-isomorphism, so the hypothesis of
`Stacks.Injectives.KInjectiveResolution.isIso_app_of_quasiIso_resolution` holds at a K-injective
resolution of any complex at all. -/
theorem isIso_rightDerivedUnit_app_of_exact (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] (RG : DerivedCategory A ⥤ DerivedCategory B)
    (α : G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RG)
    [RG.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]
    (Z : CochainComplex A ℤ) : IsIso (α.app Z) := by
  obtain ⟨NR⟩ :=
    Stacks.Injectives.FunctorialEnlargement.exists_functorial_quasiIso_isKInjective A
  have hq : QuasiIso (NR.inclusion.app Z) := NR.quasiIso Z
  refine isIso_app_of_quasiIso_resolution DerivedCategory.Q RG α
    (invertsQuasiIso_mapHomologicalComplex_comp_Q G) (NR.inclusion.app Z) (NR.isKInjective Z)
    hq ?_
  change IsIso (DerivedCategory.Q.map
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map (NR.inclusion.app Z)))
  rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
  infer_instance

end Exact

section Square

variable {A₂ : Type u₁} [Category.{v₁} A₂] [Abelian A₂] [HasDerivedCategory.{w₁} A₂]
  [IsGrothendieckAbelian.{w} A₂] {B₂ : Type u₂} [Category.{v₂} B₂] [Abelian B₂]
  [HasDerivedCategory.{w₂} B₂] {A₁ : Type u₃} [Category.{v₃} A₁] [Abelian A₁]
  [HasDerivedCategory.{w₃} A₁] {B₁ : Type u₄} [Category.{v₄} B₁] [Abelian B₁]
  [HasDerivedCategory.{w₄} B₁]
  (F : A₂ ⥤ B₂) [F.Additive] (F' : A₁ ⥤ B₁) [F'.Additive]
  (cA : A₂ ⥤ A₁) [cA.Additive] [PreservesFiniteLimits cA] [PreservesFiniteColimits cA]
  (cB : B₂ ⥤ B₁) [cB.Additive] [PreservesFiniteLimits cB] [PreservesFiniteColimits cB]

/-- The underived functor of which both composites around the square are right derived
functors: apply `F` degreewise, change categories by `cB`, and localize. -/
abbrev exactChangeSource : CochainComplex A₂ ℤ ⥤ DerivedCategory B₁ :=
  (F ⋙ cB).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q

variable (RF : DerivedCategory A₂ ⥤ DerivedCategory B₂)
  (α : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ RF)
  (RF' : DerivedCategory A₁ ⥤ DerivedCategory B₁)
  (α' : F'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ RF')

/-- The unit exhibiting "derive, then change categories" as a right derived functor of
`Stacks.DerivedSquare.exactChangeSource`. -/
def exactChangeUnitDerivedFirst :
    exactChangeSource F cB ⟶ DerivedCategory.Q ⋙ (RF ⋙ cB.mapDerivedCategory) :=
  Functor.whiskerRight
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ cB)) (ComplexShape.up ℤ)).inv
      DerivedCategory.Q ≫
    Functor.whiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
      cB.mapDerivedCategoryFactors.inv ≫
    Functor.whiskerRight α cB.mapDerivedCategory

/-- The unit exhibiting "change categories, then derive" as a right derived functor of
`Stacks.DerivedSquare.exactChangeSource`. -/
def exactChangeUnitChangeFirst (e : F ⋙ cB ≅ cA ⋙ F') :
    exactChangeSource F cB ⟶ DerivedCategory.Q ⋙ (cA.mapDerivedCategory ⋙ RF') :=
  Functor.whiskerRight (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom
      DerivedCategory.Q ≫
    Functor.whiskerRight
      (Functor.mapHomologicalComplexCompIso (Iso.refl (cA ⋙ F')) (ComplexShape.up ℤ)).inv
      DerivedCategory.Q ≫
    Functor.whiskerLeft (cA.mapHomologicalComplex (ComplexShape.up ℤ)) α' ≫
    Functor.whiskerRight cA.mapDerivedCategoryFactors.inv RF'

/-- A functor with a unit from `G.mapHomologicalComplex ⋙ Q` is right derived as soon as the unit
is invertible at every K-injective complex. -/
private theorem isRightDerivedFunctor_of_isIso_app_isKInjective (G : A₂ ⥤ B₁) [G.Additive]
    (R : DerivedCategory A₂ ⥤ DerivedCategory B₁)
    (β : G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
    (h : ∀ I : CochainComplex A₂ ℤ, I.IsKInjective → IsIso (β.app I)) :
    R.IsRightDerivedFunctor β (HomologicalComplex.quasiIso A₂ (ComplexShape.up ℤ)) :=
  (isRightDerivedFunctor_iff_isIso_app_of_isKInjective DerivedCategory.Q _ _
    (invertsQuasiIso_mapHomologicalComplex_comp_Q G)).2 h

/-- **Deriving and then changing categories is a right derived functor** of the composite of
the degreewise functors.  This is the absoluteness of right derived functors: the change of
categories is exact, so it does not interfere with the K-injective complexes that compute
`RF`. -/
theorem isRightDerivedFunctor_exactChangeUnitDerivedFirst
    [RF.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A₂ (ComplexShape.up ℤ))] :
    (RF ⋙ cB.mapDerivedCategory).IsRightDerivedFunctor
      (exactChangeUnitDerivedFirst F cB RF α)
      (HomologicalComplex.quasiIso A₂ (ComplexShape.up ℤ)) := by
  refine isRightDerivedFunctor_of_isIso_app_isKInjective _ _ _ fun I hI => ?_
  have h := isIso_app_of_isKInjective DerivedCategory.Q RF α
    (invertsQuasiIso_mapHomologicalComplex_comp_Q F) I hI
  dsimp [exactChangeUnitDerivedFirst]
  infer_instance

omit [HasDerivedCategory B₂] [PreservesFiniteLimits cB] [PreservesFiniteColimits cB] in
/-- **Changing categories and then deriving is a right derived functor** of the composite of
the degreewise functors, as soon as the unit of `RF'` is invertible at the image of every
K-injective complex.  That hypothesis is the mathematical content: those images are not
K-injective. -/
theorem isRightDerivedFunctor_exactChangeUnitChangeFirst (e : F ⋙ cB ≅ cA ⋙ F')
    [RF'.IsRightDerivedFunctor α' (HomologicalComplex.quasiIso A₁ (ComplexShape.up ℤ))]
    (hα' : ∀ I : CochainComplex A₂ ℤ, I.IsKInjective →
      IsIso (α'.app ((cA.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) :
    (cA.mapDerivedCategory ⋙ RF').IsRightDerivedFunctor
      (exactChangeUnitChangeFirst F F' cA cB RF' α' e)
      (HomologicalComplex.quasiIso A₂ (ComplexShape.up ℤ)) := by
  refine isRightDerivedFunctor_of_isIso_app_isKInjective _ _ _ fun I hI => ?_
  have h := hα' I hI
  dsimp [exactChangeUnitChangeFirst]
  infer_instance

/-- **A right derived functor commutes with an exact change of categories.**  Given a
commuting square of additive functors whose vertical maps are exact, the square of unbounded
right derived functors commutes, provided the unit of the lower derived functor is invertible
at the image of every K-injective complex of the upper left corner. -/
def rightDerivedExactChangeIso (e : F ⋙ cB ≅ cA ⋙ F')
    [RF.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A₂ (ComplexShape.up ℤ))]
    [RF'.IsRightDerivedFunctor α' (HomologicalComplex.quasiIso A₁ (ComplexShape.up ℤ))]
    (hα' : ∀ I : CochainComplex A₂ ℤ, I.IsKInjective →
      IsIso (α'.app ((cA.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) :
    RF ⋙ cB.mapDerivedCategory ≅ cA.mapDerivedCategory ⋙ RF' :=
  haveI := isRightDerivedFunctor_exactChangeUnitDerivedFirst.{w} F cB RF α
  haveI := isRightDerivedFunctor_exactChangeUnitChangeFirst.{w} F F' cA cB RF' α' e hα'
  Functor.rightDerivedUnique _ _ (exactChangeUnitDerivedFirst F cB RF α)
    (exactChangeUnitChangeFirst F F' cA cB RF' α' e)
    (HomologicalComplex.quasiIso A₂ (ComplexShape.up ℤ))

/-- **The comparison of `rightDerivedExactChangeIso` on complexes**: precomposed with the unit
of "derive, then change categories", it is the unit of "change categories, then derive". -/
@[reassoc]
theorem rightDerivedExactChangeIso_hom_fac (e : F ⋙ cB ≅ cA ⋙ F')
    [RF.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A₂ (ComplexShape.up ℤ))]
    [RF'.IsRightDerivedFunctor α' (HomologicalComplex.quasiIso A₁ (ComplexShape.up ℤ))]
    (hα' : ∀ I : CochainComplex A₂ ℤ, I.IsKInjective →
      IsIso (α'.app ((cA.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))
    (K : CochainComplex A₂ ℤ) :
    (exactChangeUnitDerivedFirst F cB RF α).app K ≫
        (rightDerivedExactChangeIso.{w} F F' cA cB RF α RF' α' e hα').hom.app
          (DerivedCategory.Q.obj K) =
      (exactChangeUnitChangeFirst F F' cA cB RF' α' e).app K := by
  have := isRightDerivedFunctor_exactChangeUnitDerivedFirst.{w} F cB RF α
  have := isRightDerivedFunctor_exactChangeUnitChangeFirst.{w} F F' cA cB RF' α' e hα'
  have h := Functor.rightDerivedNatTrans_app (RF ⋙ cB.mapDerivedCategory)
    (cA.mapDerivedCategory ⋙ RF') (exactChangeUnitDerivedFirst F cB RF α)
    (exactChangeUnitChangeFirst F F' cA cB RF' α' e)
    (HomologicalComplex.quasiIso A₂ (ComplexShape.up ℤ)) (𝟙 _) K
  rwa [NatTrans.id_app, Category.id_comp] at h

end Square

end Stacks.DerivedSquare

end
