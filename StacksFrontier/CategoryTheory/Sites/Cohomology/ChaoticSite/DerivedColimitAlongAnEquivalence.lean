module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedChangeOfCoefficients
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek is invariant under an equivalence of chaotic sites

Let `e : C ≌ C'` be an equivalence of categories, both carrying the chaotic topology, and let `A`
be an abelian category of coefficients. Precomposition with `e` is an equivalence
`(C'ᵒᵖ ⥤ A) ≌ (Cᵒᵖ ⥤ A)` between the categories of abelian presheaves -- their sheaves, the
topology being chaotic -- and this file proves that it carries `Lπ_!` on `C` to `Lπ_!` on `C'`:

`e^* ⋙ Lπ_!^C ≅ Lπ_!^{C'}`.

The point of the statement is a size mismatch, not a change of site. The criterion of
[Stacks, Tag 08Q9] computes `Lπ_!` from a point resolution, and -- being proved through the
projective generators of the category of abelian presheaves -- it is stated for a *small* site.
A site may fail to be small while being equivalent to a small category at a higher coefficient
universe, and then the criterion applies to the small category and this file carries its
conclusion back to the site one started from. That is how [Stacks, Tag 08PS] is proved for
`CommAlgCat.polynomialSite`, whose objects live one universe above its morphisms.

## Main definitions

* `Stacks.CategoryHomology.mapDerivedCategoryIdIso`: the degreewise derived functor of the
  identity is the identity.
* `Stacks.CategoryHomology.mapDerivedCategoryCompIso`: the degreewise derived functor of a
  composite of exact functors is the composite of their degreewise derived functors, read through
  a natural isomorphism identifying the composite.
* `Stacks.CategoryHomology.mapDerivedCategoryEquivalence`: an exact equivalence of abelian
  categories induces an equivalence of their derived categories, with the degreewise derived
  functors of its two legs.
* `Stacks.ChaoticSite.presheafEquivalenceOfEquivalence`: precomposition with an equivalence of
  sites, as an equivalence of the categories of abelian presheaves.

## Main results

* `Stacks.ChaoticSite.totalDerivedColimitEquivalenceIso`: **`Lπ_!` is invariant under an
  equivalence of sites.** Both sides are left adjoint to the degreewise derived functor of the
  constant diagram, so they agree by uniqueness of left adjoints -- the same argument by which
  `Stacks.ChaoticSite.derivedColimitExtendScalarsIso` compares `Lπ_!` across a change of
  coefficients.

## Implementation notes

**Why uniqueness of left adjoints and not uniqueness of derived functors.** `Lπ_!` is a total
left derived functor, and the transport of such a functor along an equivalence of the source is
`CategoryTheory.LocalizerMorphism.isLeftDerivedFunctor_iff_precomp`. That route needs the
localizer morphism of the equivalence and a comparison of the two counits. It is not taken: on a
chaotic site `Lπ_!` is a left adjoint unconditionally
(`Stacks.CategoryHomology.totalDerivedColimitAdjunction'`, [Stacks, Tag 09T5]), and the constant
diagram is insensitive to precomposition -- `K ⋙ (const J).obj X` *is* `(const J').obj X`, by
definition -- so the two right adjoints are isomorphic for formal reasons and
`CategoryTheory.Adjunction.leftAdjointUniq` finishes. No counit has to be compared.

**The identity's derived functor.** `Stacks.CategoryHomology.mapDerivedCategoryCompIsoOfNatIso`
compares two *composites* of degreewise derived functors, so it cannot by itself identify a
composite with a single functor. `mapDerivedCategoryIdIso` supplies the missing unit: both
`(𝟭 A).mapDerivedCategory` and `𝟭` lift `DerivedCategory.Q` through the localization, and a lift
is determined up to isomorphism by what it lifts.

## References

* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.CategoryHomology

attribute [local instance] HasDerivedCategory.standard

/-! ### The degreewise derived functor of an equivalence -/

section MapDerivedCategory

variable {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Abelian C₁] [Abelian C₂] [Abelian C₃]

/-- **The degreewise derived functor of the identity is the identity.** Both functors lift
`DerivedCategory.Q` through the localization of the quasi-isomorphisms, and a lift is determined
up to isomorphism by what it lifts. -/
def mapDerivedCategoryIdIso : (𝟭 C₁).mapDerivedCategory ≅ 𝟭 (DerivedCategory C₁) :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    ((𝟭 C₁).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (DerivedCategory.Q ⋙ 𝟭 (DerivedCategory C₁)) _ _ (Iso.refl _)

/-- **The degreewise derived functors of two exact functors compose to the degreewise derived
functor of any exact functor isomorphic to their composite.** -/
def mapDerivedCategoryCompIso (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (H : C₁ ⥤ C₃)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory :=
  mapDerivedCategoryCompIsoOfNatIso F G (𝟭 C₁) H
      (e ≪≫ (Functor.leftUnitor H).symm) ≪≫
    Functor.isoWhiskerRight mapDerivedCategoryIdIso H.mapDerivedCategory ≪≫
      Functor.leftUnitor _

/-- **An exact equivalence of abelian categories induces an equivalence of derived
categories**, with the degreewise derived functors of its two legs. -/
def mapDerivedCategoryEquivalence (e : C₁ ≌ C₂)
    [e.functor.Additive] [PreservesFiniteLimits e.functor] [PreservesFiniteColimits e.functor]
    [e.inverse.Additive] [PreservesFiniteLimits e.inverse] [PreservesFiniteColimits e.inverse] :
    DerivedCategory C₁ ≌ DerivedCategory C₂ :=
  CategoryTheory.Equivalence.mk e.functor.mapDerivedCategory e.inverse.mapDerivedCategory
    (mapDerivedCategoryIdIso.symm ≪≫
      (mapDerivedCategoryCompIso e.functor e.inverse (𝟭 C₁) e.unitIso.symm).symm)
    (mapDerivedCategoryCompIso e.inverse e.functor (𝟭 C₂) e.counitIso ≪≫
      mapDerivedCategoryIdIso)

end MapDerivedCategory

end Stacks.CategoryHomology

namespace Stacks.ChaoticSite

open Stacks.CategoryHomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Precomposition with an equivalence of sites -/

section Equiv

variable {C : Type*} [Category* C] {C' : Type*} [Category* C'] (e : C ≌ C')
  (A : Type*) [Category* A] [Abelian A]

/-- **Precomposition with an equivalence of sites, as an equivalence of the categories of
abelian presheaves.** Its functor sends a presheaf on `C'` to its restriction along `e`, and so
goes from presheaves on `C'` to presheaves on `C`. -/
@[sga "1 VI 4.5" "special case"]
abbrev presheafEquivalenceOfEquivalence : (C'ᵒᵖ ⥤ A) ≌ (Cᵒᵖ ⥤ A) :=
  (CategoryTheory.Equivalence.congrLeft (E := A) e.op).symm

/-- Restriction of coefficients along a functor of sites is additive: it acts on a morphism of
presheaves by whiskering, hence objectwise. -/
instance presheafEquivalenceOfEquivalence_functor_additive :
    (presheafEquivalenceOfEquivalence e A).functor.Additive where
  map_add := by intros; ext; rfl

/-- The quasi-inverse of restriction along an equivalence of sites is again a restriction, hence
additive. -/
instance presheafEquivalenceOfEquivalence_inverse_additive :
    (presheafEquivalenceOfEquivalence e A).inverse.Additive where
  map_add := by intros; ext; rfl

/-- The constant diagram is insensitive to precomposition: restricting the constant presheaf with
value `X` along `e` is the constant presheaf with value `X`. -/
def constPresheafEquivalenceIso :
    (Functor.const Cᵒᵖ : A ⥤ _) ⋙ (presheafEquivalenceOfEquivalence e A).inverse ≅
      (Functor.const C'ᵒᵖ : A ⥤ _) :=
  Iso.refl _

variable [EnoughProjectives (Cᵒᵖ ⥤ A)] [EnoughProjectives (C'ᵒᵖ ⥤ A)]
  [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A]
  [HasColimitsOfShape Cᵒᵖ A] [HasColimitsOfShape C'ᵒᵖ A]

/-- **Derived lower shriek is invariant under an equivalence of sites**: for `e : C ≌ C'` an
equivalence of categories with the chaotic topology, restriction of coefficients along `e`
carries `Lπ_!` on `C` to `Lπ_!` on `C'`.

Both sides are left adjoint to the degreewise derived functor of the constant diagram -- on the
left because restriction along an equivalence and `Lπ_!` are both left adjoints
([Stacks, Tag 09T5]) and the constant diagram is unchanged by precomposition, on the right by
`Stacks.CategoryHomology.totalDerivedColimitAdjunction'` -- so they agree by uniqueness of left
adjoints. This is what lets the criterion of [Stacks, Tag 08Q9], which asks for a small site, be
applied at a small category equivalent to a large site and its conclusion be read back at the
site. -/
def totalDerivedColimitEquivalenceIso :
    (presheafEquivalenceOfEquivalence e A).functor.mapDerivedCategory ⋙
        totalDerivedColimit' C A ≅
      totalDerivedColimit' C' A :=
  Adjunction.leftAdjointUniq
    ((mapDerivedCategoryEquivalence (presheafEquivalenceOfEquivalence e A)).toAdjunction.comp
      (totalDerivedColimitAdjunction' C A))
    ((totalDerivedColimitAdjunction' C' A).ofNatIsoRight
      (mapDerivedCategoryCompIso (Functor.const Cᵒᵖ : A ⥤ _)
          (presheafEquivalenceOfEquivalence e A).inverse (Functor.const C'ᵒᵖ : A ⥤ _)
          (constPresheafEquivalenceIso e A)).symm)

/-- **The right-hand side of the criterion of [Stacks, Tag 08Q9] is carried along an equivalence
of sites.** The functor sending an abelian presheaf to `Lπ_!` of the complex concentrated on it in
degree zero is, read on `C'`, the restriction along `e` of the same functor read on `C`.

This is `Stacks.ChaoticSite.totalDerivedColimitEquivalenceIso` composed with the two formal
comparisons that move restriction of coefficients past the single-complex functor
(`HomologicalComplex.singleMapHomologicalComplex`, restriction being additive) and past the
localization (`CategoryTheory.Functor.mapDerivedCategoryFactors`, restriction being exact). -/
def derivedColimitSingleEquivalenceIso :
    HomologicalComplex.single (C'ᵒᵖ ⥤ A) (ComplexShape.up ℤ) 0 ⋙
        DerivedCategory.Q ⋙ totalDerivedColimit' C' A ≅
      (presheafEquivalenceOfEquivalence e A).functor ⋙
        HomologicalComplex.single (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) 0 ⋙
          DerivedCategory.Q ⋙ totalDerivedColimit' C A :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (totalDerivedColimitEquivalenceIso e A).symm) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (presheafEquivalenceOfEquivalence e A).functor.mapDerivedCategoryFactors _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (HomologicalComplex.singleMapHomologicalComplex
      (presheafEquivalenceOfEquivalence e A).functor (ComplexShape.up ℤ) 0) _ ≪≫
    Functor.associator _ _ _

end Equiv

/-- A natural isomorphism of functors out of a category is determined by its restriction along an
equivalence into that category. -/
def cancelLeftNatIsoOfEquivalence {X Y Z : Type*} [Category* X] [Category* Y] [Category* Z]
    (e : X ≌ Y) (P Q : Y ⥤ Z) (h : e.functor ⋙ P ≅ e.functor ⋙ Q) : P ≅ Q :=
  (e.invFunIdAssoc P).symm ≪≫ Functor.isoWhiskerLeft e.inverse h ≪≫ e.invFunIdAssoc Q

end Stacks.ChaoticSite

end
