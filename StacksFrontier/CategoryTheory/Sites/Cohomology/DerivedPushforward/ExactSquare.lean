module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.CompositionOfToposHomUnconditional
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Derived direct images across a square with two exact sides

Let `b ∘ a = d ∘ c` be a square of morphisms of ringed topoi, read on the direct images of
sheaves of modules, in which the direct images `b_*` and `c_*` are exact. Then
`b_* ∘ Ra_* ≅ Rd_* ∘ c_*` as functors between unbounded derived categories of modules.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.derivedPushforwardExactSquareIsoOfIsIso`: the comparison for
  arbitrary exact functors `Fb` and `Fc`, `Fc` carrying K-injective complexes to complexes
  computing `Rd_*`.
* `AlgebraicGeometry.RingedToposHom.derivedPushforwardExactSquareIso`: the case where `Fb` and
  `Fc` are direct images along morphisms of ringed topoi, by Tag 0D6E.

## Implementation notes

Both composites are right derived functors of the degreewise direct image along the square.
For `b_* ∘ Ra_*` this is absoluteness of right derived functors over a Grothendieck abelian
category (`Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_comp`), `b_*` being its
own derived functor. For `Rd_* ∘ c_*` it is the composition formula of Tag 0D6E: the
degreewise direct image along `c` of a K-injective complex computes `Rd_*`
(`isIso_app_pushforwardMapHomotopy_of_isKInjective` in the namespace
`Stacks.Cohomology.DerivedPushforwardCompositionOfToposHom`). Note that `c_*` need not preserve
K-injective complexes; for sheaves of modules it usually does not.

## References

* [Stacks Project, Tag 0D6E](https://stacks.math.columbia.edu/tag/0D6E)
* [Stacks Project, Tag 075A](https://stacks.math.columbia.edu/tag/075A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward

namespace AlgebraicGeometry.RingedToposHom

attribute [local instance 10000] HasDerivedCategory.standard

universe v w uu

variable {X X' Y Y' : RingedTopos.{v, uu, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})] [Y'.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})] [Y'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y'.J AddCommGrpCat.{w}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w)] [HasSheafify Y'.J (Type w)]
  [IsGrothendieckAbelian.{w} X.Modules] [IsGrothendieckAbelian.{w} Y.Modules]

section General

variable (a : RingedToposHom X X') (d : RingedToposHom Y Y')
  (Fb : X'.Modules ⥤ Y'.Modules) (Fc : X.Modules ⥤ Y.Modules)
  [Fb.Additive] [PreservesFiniteLimits Fb] [PreservesFiniteColimits Fb]
  [Fc.Additive] [PreservesFiniteLimits Fc] [PreservesFiniteColimits Fc]

/-- The comparison transformation exhibiting `Fc ⋙ Rd_*` as a right derived functor of `Fc`
followed by degreewise `d_*`. -/
abbrev exactThenDerivedUnit :
    Fc.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ pushforwardToDerivedCategory d ⟶
      DerivedCategory.Qh ⋙ Fc.mapDerivedCategory ⋙ derivedPushforward d :=
  Functor.whiskerLeft _
      (Stacks.Cohomology.DerivedPushforwardCompositionOfToposHom.derivedPushforwardUnit d) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight Fc.mapDerivedCategoryFactorsh.inv _ ≫
    (Functor.associator _ _ _).hom

omit [Fb.Additive] [PreservesFiniteLimits Fb] [PreservesFiniteColimits Fb]
  [X.J.HasSheafCompose (forget RingCat)] [X.J.HasSheafCompose (forget AddCommGrpCat)]
  [Y'.J.HasSheafCompose (forget AddCommGrpCat)] [HasSheafify X.J (Type w)]
  [HasSheafify Y.J (Type w)] [HasSheafify Y'.J (Type w)] in
/-- `Fc ⋙ Rd_*` is a right derived functor of `Fc` followed by degreewise `d_*` as soon as `Fc`
carries K-injective complexes to complexes computing `Rd_*`. -/
theorem exactThenDerived_isRightDerivedFunctor
    (hc : ∀ I : CochainComplex X.Modules ℤ, I.IsKInjective →
      IsIso
        ((Stacks.Cohomology.DerivedPushforwardCompositionOfToposHom.derivedPushforwardUnit d).app
          ((Fc.mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I)))) :
    (Fc.mapDerivedCategory ⋙ derivedPushforward d).IsRightDerivedFunctor
      (exactThenDerivedUnit d Fc) (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) := by
  refine Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_of_isIso_app_isKInjective
    _ _ _ _ fun I hI => ?_
  have h₁ := hc I hI
  simp only [exactThenDerivedUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Category.id_comp, Category.comp_id]
  exact IsIso.comp_isIso' h₁ (Functor.map_isIso _ _)

/-- **Derived direct images across a square with two exact sides.** If `Fb ∘ a_* = d_* ∘ Fc`
through `e`, for exact functors `Fb` and `Fc` of which `Fc` carries K-injective complexes to
complexes computing `Rd_*`, then `Fb ∘ Ra_* ≅ Rd_* ∘ Fc` on unbounded derived categories. -/
def derivedPushforwardExactSquareIsoOfIsIso
    (hc : ∀ I : CochainComplex X.Modules ℤ, I.IsKInjective →
      IsIso
        ((Stacks.Cohomology.DerivedPushforwardCompositionOfToposHom.derivedPushforwardUnit d).app
          ((Fc.mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I))))
    (e : pushforwardModules a ⋙ Fb ≅ Fc ⋙ pushforwardModules d) :
    derivedPushforward a ⋙ Fb.mapDerivedCategory ≅ Fc.mapDerivedCategory ⋙ derivedPushforward d :=
  letI : Fb.mapDerivedCategory.IsRightDerivedFunctor Fb.mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso X'.Modules (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ _ Fb.mapDerivedCategoryFactorsh
  letI := Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_comp
    (pushforwardToDerivedCategory a) DerivedCategory.Qh (derivedPushforward a)
    (Stacks.Cohomology.DerivedPushforwardCompositionOfToposHom.derivedPushforwardUnit a)
    Fb.mapDerivedCategory
  letI := exactThenDerived_isRightDerivedFunctor d Fc hc
  let eH : (pushforwardModules a).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        Fb.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      Fc.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (pushforwardModules d).mapHomotopyCategory (ComplexShape.up ℤ) :=
    Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (ComplexShape.up ℤ)).symm
  Functor.rightDerivedNatIso _ _
    (Functor.whiskerRight
      (Stacks.Cohomology.DerivedPushforwardCompositionOfToposHom.derivedPushforwardUnit a)
      Fb.mapDerivedCategory ≫ (Functor.associator _ _ _).hom)
    (exactThenDerivedUnit d Fc)
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ Fb.mapDerivedCategoryFactorsh ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eH DerivedCategory.Qh ≪≫
      Functor.associator _ _ _)

omit [IsGrothendieckAbelian.{w} X.Modules] [Fb.Additive] [PreservesFiniteLimits Fb]
  [PreservesFiniteColimits Fb] [PreservesFiniteLimits Fc] [PreservesFiniteColimits Fc]
  [X.J.HasSheafCompose (forget RingCat)] [X.J.HasSheafCompose (forget AddCommGrpCat)]
  [Y'.J.HasSheafCompose (forget AddCommGrpCat)] [HasSheafify X.J (Type w)]
  [HasSheafify Y.J (Type w)] [HasSheafify Y'.J (Type w)] in
/-- If `Fc` carries K-injective complexes to K-injective complexes, it carries them to complexes
computing `Rd_*`. -/
theorem isIso_derivedPushforwardUnit_app_of_preservesKInjective
    (hc : ∀ I : CochainComplex X.Modules ℤ, I.IsKInjective →
      CochainComplex.IsKInjective ((Fc.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
    (I : CochainComplex X.Modules ℤ) (hI : I.IsKInjective) :
    IsIso ((Stacks.Cohomology.DerivedPushforwardCompositionOfToposHom.derivedPushforwardUnit d).app
      ((Fc.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I))) :=
  Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective
    (pushforwardToDerivedCategory d) DerivedCategory.Qh (derivedPushforward d)
    (Stacks.Cohomology.DerivedPushforwardCompositionOfToposHom.derivedPushforwardUnit d) _ (hc I hI)

/-- `derivedPushforwardExactSquareIsoOfIsIso` when `Fc` preserves K-injective complexes. -/
def derivedPushforwardExactSquareIsoOfKInjective
    (hc : ∀ I : CochainComplex X.Modules ℤ, I.IsKInjective →
      CochainComplex.IsKInjective ((Fc.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
    (e : pushforwardModules a ⋙ Fb ≅ Fc ⋙ pushforwardModules d) :
    derivedPushforward a ⋙ Fb.mapDerivedCategory ≅ Fc.mapDerivedCategory ⋙ derivedPushforward d :=
  derivedPushforwardExactSquareIsoOfIsIso a d Fb Fc
    (isIso_derivedPushforwardUnit_app_of_preservesKInjective d Fc hc) e

end General

variable (a : RingedToposHom X X') (b : RingedToposHom X' Y') (c : RingedToposHom X Y)
  (d : RingedToposHom Y Y')
  [PreservesFiniteLimits (pushforwardModules b)] [PreservesFiniteColimits (pushforwardModules b)]
  [PreservesFiniteLimits (pushforwardModules c)] [PreservesFiniteColimits (pushforwardModules c)]

open Stacks.Cohomology.DerivedPushforwardCompositionOfToposHom
  (isIso_app_pushforwardMapHomotopy_of_isKInjective) in
/-- **Derived direct images across a square of ringed topoi with two exact sides.** If
`b ∘ a = d ∘ c` on direct images of sheaves of modules, through `e`, and `b_*` and `c_*` are
exact, then `b_* ∘ Ra_* ≅ Rd_* ∘ c_*` on unbounded derived categories. The degreewise direct
image along `c` of a K-injective complex computes `Rd_*` by Tag 0D6E. -/
def derivedPushforwardExactSquareIso
    (e : pushforwardModules a ⋙ pushforwardModules b ≅
      pushforwardModules c ⋙ pushforwardModules d) :
    derivedPushforward a ⋙ (pushforwardModules b).mapDerivedCategory ≅
      (pushforwardModules c).mapDerivedCategory ⋙ derivedPushforward d :=
  derivedPushforwardExactSquareIsoOfIsIso a d _ _
    (isIso_app_pushforwardMapHomotopy_of_isKInjective
      c d (derivedPushforward d)
      (Stacks.Cohomology.DerivedPushforwardCompositionOfToposHom.derivedPushforwardUnit d)) e

end AlgebraicGeometry.RingedToposHom

end
