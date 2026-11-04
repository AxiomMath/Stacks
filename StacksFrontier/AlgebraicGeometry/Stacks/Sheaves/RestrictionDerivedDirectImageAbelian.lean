module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RestrictionDerivedDirectImage
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianPushforwardExact

/-!
# The restricted derived direct image for abelian sheaves

Let `S` be a scheme in a big fppf site and let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred
in groupoids over `(Sch/S)_{fppf}`, with `𝒳` representable by an algebraic space `F` and `𝒴` by
an algebraic space `G`, and write `f : F ⟶ G` for the induced morphism of algebraic spaces.
Stacks 075N asserts, in its clause **(1)**, for an abelian sheaf `ℱ` on `𝒳_étale`, the identity

`(Rf_*ℱ)|_{G_étale} = Rf_{small,*}(ℱ|_{F_étale})`

in `D(G_étale)`, where `(-)|_{F_étale}` and `(-)|_{G_étale}` are the restrictions to the small
étale sites of Stacks 073M. This file states and proves it. Clause (2), the same identity for
sheaves of modules in `D(𝒪_G)`, is
`AlgebraicGeometry.Space.restrictedDerivedDirectImageIso` of
`StacksFrontier/AlgebraicGeometry/Stacks/Sheaves/RestrictionDerivedDirectImage.lean`.

The argument is the source's, and at abelian coefficients it is the *easy* clause. The square of
Stacks 073N says that `π_G ∘ f` and `f_small ∘ π_F` are 2-isomorphic morphisms of ringed topoi;
each of the two derived composites `Rf_* ⋙ Rπ_{G,*}` and `Rπ_{F,*} ⋙ Rf_{small,*}` is a right
derived functor of degreewise direct image along its own leg; the 2-isomorphism identifies the
two degreewise legs; so the two composites are right derived functors of one and the same
functor and the canonical comparison between them is invertible. The restrictions `π_{F,*}` and
`π_{G,*}` are exact, so they are their own total right derived functors and the display above is
what the comparison says.

What makes clause (1) easier than clause (2) is the step that identifies each composite as a
right derived functor of its leg. It needs, of the *first* morphism of the leg, that degreewise
direct image preserve K-injectivity — Stacks 093Y. For the leg `π_G ∘ f` that is not needed at
all: the second morphism `π_G` is exact, so the unit of its derived functor is invertible
everywhere. For the leg `f_small ∘ π_F` it is needed of `π_{F,*}`, and this is Stacks 075L
part (2), which at abelian coefficients is **true and proved here** —
`Stacks.Topos.AbelianPushforward.isKInjective_mapHomologicalComplex_abelianPushforward` — while
at module coefficients the source records it as *false*, by Stacks 0758. That single asymmetry
is the whole difference between the two clauses: clause (2) has to reach the condition the
composition criterion consumes at that leg by another route, the unconditional Stacks 0D6E for a
morphism of ringed topoi, and clause (1) needs nothing in its place.

## Main definitions

* `Stacks.Cohomology.UnboundedComplexes.mapToDerivedCategory`: degreewise image of complexes
  under an additive functor of abelian categories, read into the derived category of the target
  — the functor of which a total right derived functor is taken.
* `Stacks.Cohomology.UnboundedComplexes.compDerivedUnit`: the canonical transformation from
  degreewise `F ⋙ G` to the composite `RF ⋙ RG` of two right derived functors.
* `Stacks.Cohomology.UnboundedComplexes.ComputesDerivedComp`: the condition the composition
  criterion consumes — the unit of `RG` is invertible at the degreewise image under `F` of every
  K-injective complex.
* `Stacks.Cohomology.UnboundedComplexes.twoLegsDerivedComparison` and
  `Stacks.Cohomology.UnboundedComplexes.twoLegsDerivedIso`: the canonical comparison of the two
  derived composites around a square of additive functors whose two legs are isomorphic, and the
  isomorphism it is.
* `Stacks.Topos.AbelianPushforward.commGrpPushforwardPairIso` and
  `Stacks.Topos.AbelianPushforward.abelianPushforwardPairIso`: an isomorphism of the two
  composite direct images of *sheaves of sets* around such a square of morphisms of topoi
  induces one of the composite direct images of commutative group objects, and hence of abelian
  sheaves.
* `AlgebraicGeometry.Space.abelianRestrictionFunctor`: the restriction `ℱ ↦ ℱ|_{F_étale}` of
  abelian sheaves, that is, the direct image of abelian sheaves along the morphism of topoi
  `π_F` of Stacks 073M.
* `AlgebraicGeometry.Space.abelianDirectImageFibred` and
  `AlgebraicGeometry.Space.abelianDirectImageSpace`: the direct images of abelian sheaves along
  the 1-morphism `f : 𝒳 ⥤ 𝒴` and along the induced morphism of algebraic spaces `F ⟶ G`.
* `AlgebraicGeometry.Space.restrictedAbelianDerivedDirectImageIso`: **Stacks 075N, clause (1)**,
  the display above as an isomorphism of functors `D(𝒳_étale) ⥤ D(G_étale)`.
* `AlgebraicGeometry.Space.restrictedDerivedDirectImageIsoClauses`: **Stacks 075N**, both
  clauses — clause (1) above paired with clause (2) for sheaves of modules. This is where the
  tag sits, a tag belonging on a declaration that states the whole of it.

## Main results

* `Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_compDerivedUnit`: Stacks 0D6E's
  criterion at the level of additive functors of Grothendieck abelian categories.
* `Stacks.Cohomology.UnboundedComplexes.isIso_twoLegsDerivedComparison`: the comparison of the
  two derived composites around a square with isomorphic legs is invertible.
* `Stacks.Topos.AbelianPushforward.isKInjective_mapHomologicalComplex_abelianPushforward`:
  **Stacks 075L, part (2) at abelian coefficients**, for an arbitrary morphism of topoi:
  degreewise direct image of abelian sheaves preserves K-injectivity.
* `AlgebraicGeometry.Space.preservesFiniteColimits_abelianRestrictionFunctor` and
  `AlgebraicGeometry.Space.exactFunctor_abelianRestrictionFunctor`: the restriction of abelian
  sheaves to the small étale site of `F` is exact. This is the source's closing step.
* `AlgebraicGeometry.Space.isIso_restrictedAbelianDerivedDirectImageComparison`: the comparison
  of the two derived composites around the square of Stacks 073N is invertible, for arbitrary
  right derived functors of the two restrictions. This is *not* clause (1) — the source's
  restrictions are underived — and so carries no tag;
  `restrictedAbelianDerivedDirectImageIso` is the statement of the clause.

## Implementation notes

**What is proved.** Nothing beyond the source's own data is a hypothesis. The 2-isomorphism of
the two legs of the square, Stacks 073N itself, is
`AlgebraicGeometry.Space.restrictionRingedSquareInducedAlgebraicSpaces`, built from
invertibility of the comparison map of equation 075M and its structure-sheaf compatibility; the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Stacks/Sheaves/RestrictionDerivedDirectImage.lean` say how. It is
the *same term* that clause (2) uses, not an abelian shadow of it: it is an
`AlgebraicGeometry.RingedToposHom.TwoIso` of the two legs, and
`Stacks.Topos.AbelianPushforward.abelianPushforwardPairIso` carries its underlying isomorphism
of direct images of sheaves of sets over to abelian sheaves. So the one construction serves
clause (1) and clause (2) at once.

In particular the other input of clause (2), Stacks 093Y for
degreewise `π_{F,*}`, is **proved** here, at abelian coefficients and for an arbitrary morphism
of topoi: `π_{F,*}` on abelian sheaves is right adjoint to `π_F^{-1}` on abelian sheaves, which
is exact by Stacks 04JC (`CategoryTheory.Sites.abelianInverseImage_exact`, with no hypothesis on
the morphism), so Stacks 08BJ applies. This is the formal counterpart of the source's own
reason, which reads the restriction simultaneously as the direct image `π_{F,*}` and as the
inverse image `i_F^{-1}` of the other morphism of Stacks 073M and uses that `i_{F,!}` is exact;
and it is exactly the step that fails for modules, where an inverse image of modules is not
exact without flatness.

**The spelling of the restriction.** The restriction of abelian sheaves is taken here as
`Stacks.Topos.AbelianPushforward.abelianPushforward` of the morphism of topoi underlying `π_F`,
i.e. the direct image of abelian sheaves along `π_F`, which is the repository's canonical
spelling for a direct image of abelian sheaves attached to a morphism of topoi (it is the one
`AlgebraicGeometry.Space.smallEtaleAbelianPushforwardBaseChangeIso` uses). That this is
restriction along the functor `u_F : F_étale ⥤ 𝒳` of Stacks 073M is
`AlgebraicGeometry.Space.abelianRestrictionFunctor_forgetIso`, which is
`Stacks.Topos.AbelianPushforward.abelianPushforward_forgetIso` — the identity isomorphism — read
through `AlgebraicGeometry.Space.projectionRingedToposHom_pushforward`.

There is a second spelling in the tree,
`AlgebraicGeometry.Space.restrictionAbSheafFunctor` of
`StacksFrontier/AlgebraicGeometry/Stacks/RestrictionToAlgebraicSpaceInjectives.lean`, namely
`CategoryTheory.Functor.sheafPushforwardContinuous` of `u_F` at `Ab` coefficients, and Stacks
075L is proved there for it
(`AlgebraicGeometry.Space.injective_restrictionAbSheafFunctor_obj` and
`isKInjective_restrictionAbSheafFunctor_obj`). It is *not* the spelling used here, because the
2-isomorphism of Stacks 073N relates the direct images of the morphisms of topoi and so meets
the `abelianPushforward` spelling and not the `sheafPushforwardContinuous` one; an
identification of the two is not in the tree. The two Stacks 075L statements proved there and
the two proved here therefore say the same thing about two spellings of one functor, by the same
argument — a right adjoint of an exact functor preserves injectives and K-injectivity — and
neither is derived from the other.

**Exactness of the restrictions.** Only right exactness has content; left exactness is adjointness.
`AlgebraicGeometry.Space.preservesEpimorphisms_projectionRingedToposHom_pushforward` — the
restriction of sheaves of *sets* preserves epimorphisms, because `u_F` is continuous *and*
cocontinuous (Stacks 073M) — is already in the tree, and Stacks 04DB
(`Stacks.Topos.AbelianPushforward.abelianPushforward_exact_of_preservesEpimorphisms` through
`preservesEpimorphisms_abelianPushforward`) carries it to abelian sheaves. The resulting
`PreservesFiniteColimits` is registered as an instance, so that the hypotheses which
`CategoryTheory.Functor.mapDerivedCategory` carries are discharged wherever the morphism is one
of these restrictions.

**The morphism of algebraic spaces is induced, not given.** As in clause (2) and in the source,
`fSpace` is not a parameter: every binder that mentions it — the derived direct image `RfSpace`
and its unit `αfSpace` — is stated at
`AlgebraicGeometry.Space.inducedAlgebraicSpacesHom`, the morphism
`AlgebraicGeometry.Space.inducedSpacesHom` builds from the two presentations and the verticality
of the 1-morphism. So the data of the statement is the source's: `S`, the 1-morphism, the two
presentations, and the sheaf.

**The size and derived-category instances.** They are the abelian-coefficient analogues of the
ones clause (2) carries, and each is satisfiable from the data: `HasSheafify` and
`WEqualsLocallyBijective` for `AddCommGrpCat.{u}` and `IsGrothendieckAbelian.{u}` of the four
categories of abelian sheaves all follow from essential smallness of the four sites — for the
small étale sites it is an instance, for `𝒳` and `𝒴` it is
`AlgebraicGeometry.Space.essentiallySmall_of_equivalenceOver` applied to `eF`, `eG` — through
`CategoryTheory.hasSheafifyEssentiallySmallSite`,
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall` and
`CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall`. They are carried rather than
discharged because the presentations `eF`, `eG` are data and so cannot take part in instance
search. The four `HasDerivedCategory` universes are left free, as in clause (2).

## References

* [Stacks Project, Tag 075N](https://stacks.math.columbia.edu/tag/075N)
* [Stacks Project, Tag 075L](https://stacks.math.columbia.edu/tag/075L)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 073N](https://stacks.math.columbia.edu/tag/073N)
* [Stacks Project, Tag 0D6E](https://stacks.math.columbia.edu/tag/0D6E)
* [Stacks Project, Tag 04DB](https://stacks.math.columbia.edu/tag/04DB)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/-! ### Right derived functors of a composite of additive functors -/

namespace Stacks.Cohomology.UnboundedComplexes

universe wA wB wB₂ vA uA vB uB vB₂ uB₂ vC uC dA dB dB₂ dC

section Composite

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  {E : Type uC} [Category.{vC} E] [Abelian E]
  [HasDerivedCategory.{dA} A] [HasDerivedCategory.{dB} B] [HasDerivedCategory.{dC} E]

/-- Degreewise image of complexes under an additive functor, read as a functor from the
unbounded homotopy category of the source to the unbounded derived category of the target. A
right derived functor of this is the total right derived functor of `F`.

This is `AlgebraicGeometry.RingedToposHom.pushforwardToDerivedCategory` with the morphism of
ringed topoi and its direct image of modules replaced by an arbitrary additive functor. -/
abbrev mapToDerivedCategory (F : A ⥤ B) [F.Additive] :
    HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory B :=
  F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

variable (F : A ⥤ B) (G : B ⥤ E) [F.Additive] [G.Additive]
  (RF : DerivedCategory A ⥤ DerivedCategory B)
  (RG : DerivedCategory B ⥤ DerivedCategory E)
  (αF : mapToDerivedCategory F ⟶ DerivedCategory.Qh ⋙ RF)
  (αG : mapToDerivedCategory G ⟶ DerivedCategory.Qh ⋙ RG)

/-- The transformation from degreewise `F ⋙ G` to the composite `RF ⋙ RG` of two right derived
functors: the comparison of the degreewise composite with the composite of the degreewise
functors, then the unit of `RG` at the image under `F`, then `RG` applied to the unit of `RF`.

This is the unit with respect to which `RF ⋙ RG` is a right derived functor of degreewise
`F ⋙ G`, and hence the one the comparison of Stacks 0D6E is induced by. -/
def compDerivedUnit : mapToDerivedCategory (F ⋙ G) ⟶ DerivedCategory.Qh ⋙ (RF ⋙ RG) :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).inv
      DerivedCategory.Qh ≫
    Functor.whiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ)) αG ≫
    Functor.whiskerRight αF RG

/-- **The condition the composition criterion actually uses**: the unit of `RG` is invertible at
the degreewise image under `F` of every K-injective complex.

`isRightDerivedFunctor_compDerivedUnit` consumes nothing else of its K-injectivity input, and
there are two ways to supply it: `computesDerivedComp_of_preservesKInjective`, which is
Stacks 093Y for `F`, and `computesDerivedComp_of_isIso`, which asks nothing of `F` at all and
applies whenever the unit of `RG` is an isomorphism — in particular when `G` is exact and `RG`
is `CategoryTheory.Functor.mapDerivedCategory`. Splitting the two off from the criterion is what
lets the leg of a square with an exact second functor carry no hypothesis on its first.

This is `AlgebraicGeometry.RingedToposHom.PushforwardComputesDerived` with the two morphisms of
ringed topoi and their direct images of modules replaced by arbitrary additive functors. -/
def ComputesDerivedComp : Prop :=
  ∀ I : CochainComplex A ℤ, I.IsKInjective →
    IsIso (αG.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))

omit [HasDerivedCategory.{dA} A] in
/-- **Stacks 093Y for `F` supplies the condition.** If degreewise `F` preserves K-injectivity,
then the unit of any right derived functor `RG` is invertible at the image of a K-injective
complex, by `Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective`. -/
theorem computesDerivedComp_of_preservesKInjective [IsGrothendieckAbelian.{wB} B]
    [RG.IsRightDerivedFunctor αG (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))]
    (hF : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      CochainComplex.IsKInjective
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    ComputesDerivedComp F G RG αG := fun I hI ↦
  isIso_app_of_isKInjective (mapToDerivedCategory G) DerivedCategory.Qh RG αG _ (hF I hI)

omit [HasDerivedCategory.{dA} A] in
/-- **An invertible unit supplies the condition, with no hypothesis on `F`.** This is the case
of an exact `G`, where the unit of `CategoryTheory.Functor.mapDerivedCategory` is the inverse of
the isomorphism `CategoryTheory.Functor.mapDerivedCategoryFactorsh`, hence an isomorphism
everywhere by `CategoryTheory.Iso.isIso_inv`, so in particular at the images of K-injective
complexes. -/
theorem computesDerivedComp_of_isIso [IsIso αG] : ComputesDerivedComp F G RG αG :=
  fun _ _ ↦ inferInstance

/-- **Stacks 0D6E's criterion for `RF ⋙ RG`**, at the level of additive functors of Grothendieck
abelian categories: if the unit of `RG` is invertible at the images of K-injective complexes,
then `RF ⋙ RG`, with the unit `compDerivedUnit`, is a right derived functor of degreewise
`F ⋙ G`.

By `isRightDerivedFunctor_of_isIso_app_isKInjective` it suffices that the unit be invertible at
each K-injective `I`, where it is the composite of the degreewise comparison isomorphism, the
unit of `RG` at `F I`, and `RG` applied to the unit of `RF` at `I`.

This is `AlgebraicGeometry.RingedToposHom.isRightDerivedFunctor_comp_of_isGrothendieckAbelian`
with the two morphisms of ringed topoi and their direct images of modules replaced by arbitrary
additive functors. -/
theorem isRightDerivedFunctor_compDerivedUnit [IsGrothendieckAbelian.{wA} A]
    [IsGrothendieckAbelian.{wB} B]
    [RF.IsRightDerivedFunctor αF (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    [RG.IsRightDerivedFunctor αG (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))]
    (hF : ComputesDerivedComp F G RG αG) :
    (RF ⋙ RG).IsRightDerivedFunctor (compDerivedUnit F G RF RG αF αG)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  refine isRightDerivedFunctor_of_isIso_app_isKInjective _ _ _ _ fun I hI ↦ ?_
  have h₂ : IsIso (αG.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))) := hF I hI
  have h₃ : IsIso (αF.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) :=
    isIso_app_of_isKInjective (mapToDerivedCategory F) DerivedCategory.Qh RF αF I hI
  simp only [compDerivedUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

end Composite

section Exact

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  [HasDerivedCategory.{dA} A] [HasDerivedCategory.{dB} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **An exact functor is its own total right derived functor.** If `F` is additive and exact,
then the functor it induces on unbounded derived categories is a right derived functor of
degreewise `F`, with the canonical factorization isomorphism for unit.

The unit is an isomorphism outright, hence an isomorphism at every K-injective complex, which by
`isRightDerivedFunctor_of_isIso_app_isKInjective` is all that has to be checked. It is what lets
a right derived functor of an exact functor be read as the degreewise one. -/
theorem isRightDerivedFunctor_mapDerivedCategoryFactorsh_inv [IsGrothendieckAbelian.{wA} A] :
    F.mapDerivedCategory.IsRightDerivedFunctor F.mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_of_isIso_app_isKInjective _ _ _ _ fun _ _ ↦ inferInstance

end Exact

/-! ### Two factorizations of isomorphic composites -/

section TwoLegs

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  {B₂ : Type uB₂} [Category.{vB₂} B₂] [Abelian B₂]
  {E : Type uC} [Category.{vC} E] [Abelian E]
  [HasDerivedCategory.{dA} A] [HasDerivedCategory.{dB} B]
  [HasDerivedCategory.{dB₂} B₂] [HasDerivedCategory.{dC} E]

/-- An isomorphism of additive functors induces an isomorphism of the degreewise functors on
unbounded homotopy categories. -/
def mapHomotopyCategoryIso {H H' : A ⥤ E} [H.Additive] [H'.Additive] (e : H ≅ H') :
    H.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      H'.mapHomotopyCategory (ComplexShape.up ℤ) where
  hom := NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)
  inv := NatTrans.mapHomotopyCategory e.inv (ComplexShape.up ℤ)
  hom_inv_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id, NatTrans.mapHomotopyCategory_id]
  inv_hom_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id, NatTrans.mapHomotopyCategory_id]

/-- An isomorphism of additive functors induces an isomorphism of the degreewise functors read
into the derived category of the target.

This is `AlgebraicGeometry.RingedToposHom.TwoIso.pushforwardToDerivedCategoryIso` with the
2-isomorphism of morphisms of ringed topoi and its isomorphism of direct images of modules
replaced by an arbitrary isomorphism of additive functors. -/
def mapToDerivedCategoryIso {H H' : A ⥤ E} [H.Additive] [H'.Additive] (e : H ≅ H') :
    mapToDerivedCategory H ≅ mapToDerivedCategory H' :=
  Functor.isoWhiskerRight (mapHomotopyCategoryIso e) DerivedCategory.Qh

variable (F : A ⥤ B) (G : B ⥤ E) (F' : A ⥤ B₂) (G' : B₂ ⥤ E)
  [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
  (RF : DerivedCategory A ⥤ DerivedCategory B)
  (RG : DerivedCategory B ⥤ DerivedCategory E)
  (RF' : DerivedCategory A ⥤ DerivedCategory B₂)
  (RG' : DerivedCategory B₂ ⥤ DerivedCategory E)
  (αF : mapToDerivedCategory F ⟶ DerivedCategory.Qh ⋙ RF)
  (αG : mapToDerivedCategory G ⟶ DerivedCategory.Qh ⋙ RG)
  (αF' : mapToDerivedCategory F' ⟶ DerivedCategory.Qh ⋙ RF')
  (αG' : mapToDerivedCategory G' ⟶ DerivedCategory.Qh ⋙ RG')
  (t : F ⋙ G ≅ F' ⋙ G')

/-- The unit of the second composite `RF' ⋙ RG'`, read as a transformation out of the degreewise
*first* composite through the isomorphism of the two composites. -/
def twoLegsDerivedUnit :
    mapToDerivedCategory (F ⋙ G) ⟶ DerivedCategory.Qh ⋙ (RF' ⋙ RG') :=
  (mapToDerivedCategoryIso t).hom ≫ compDerivedUnit F' G' RF' RG' αF' αG'

variable [IsGrothendieckAbelian.{wA} A] [IsGrothendieckAbelian.{wB} B]
  [IsGrothendieckAbelian.{wB₂} B₂]
  [RF.IsRightDerivedFunctor αF (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  [RG.IsRightDerivedFunctor αG (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))]
  [RF'.IsRightDerivedFunctor αF' (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  [RG'.IsRightDerivedFunctor αG' (HomotopyCategory.quasiIso B₂ (ComplexShape.up ℤ))]

/-- The canonical comparison `RF ⋙ RG ⟶ RF' ⋙ RG'` of the two derived composites around a
square-shaped diagram of additive functors with isomorphic legs, induced by the universal
property of the first as a right derived functor of degreewise `F ⋙ G`. The hypothesis is the
one of `isRightDerivedFunctor_compDerivedUnit`, namely `ComputesDerivedComp`. -/
def twoLegsDerivedComparison (hF : ComputesDerivedComp F G RG αG) :
    (RF ⋙ RG) ⟶ (RF' ⋙ RG') :=
  haveI := isRightDerivedFunctor_compDerivedUnit F G RF RG αF αG hF
  (RF ⋙ RG).rightDerivedDesc (compDerivedUnit F G RF RG αF αG)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) (RF' ⋙ RG')
    (twoLegsDerivedUnit F G F' G' RF' RG' αF' αG' t)

/-- **The two derived composites around a square of additive functors with isomorphic legs
agree.** If `F ⋙ G` and `F' ⋙ G'` are isomorphic, and if the units of `RG` and `RG'` are
invertible at the images of K-injective complexes, then the canonical comparison
`RF ⋙ RG ⟶ RF' ⋙ RG'` is invertible. Either leg's hypothesis is supplied by Stacks 093Y for its
first functor, through `computesDerivedComp_of_preservesKInjective`, or for free by
`computesDerivedComp_of_isIso` when its second functor is exact.

Both composites are right derived functors of degreewise composition along their own leg, by
`isRightDerivedFunctor_compDerivedUnit`; the isomorphism identifies the two degreewise legs, so
by `isRightDerivedFunctor_comp_of_isIso` they are right derived functors of one and the same
functor, and the comparison between two right derived functors of one functor is invertible. -/
theorem isIso_twoLegsDerivedComparison (hF : ComputesDerivedComp F G RG αG)
    (hF' : ComputesDerivedComp F' G' RG' αG') :
    IsIso (twoLegsDerivedComparison F G F' G' RF RG RF' RG' αF αG αF' αG' t hF) := by
  have := isRightDerivedFunctor_compDerivedUnit F G RF RG αF αG hF
  have := isRightDerivedFunctor_compDerivedUnit F' G' RF' RG' αF' αG' hF'
  have := isRightDerivedFunctor_comp_of_isIso
    (mapToDerivedCategoryIso t).hom DerivedCategory.Qh (RF' ⋙ RG')
    (compDerivedUnit F' G' RF' RG' αF' αG')
  exact (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc (RF ⋙ RG)
    (compDerivedUnit F G RF RG αF αG)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) (RF' ⋙ RG')
    (twoLegsDerivedUnit F G F' G' RF' RG' αF' αG' t)).mp this

/-- **The two derived composites around a square of additive functors with isomorphic legs are
isomorphic**, by the invertible comparison `twoLegsDerivedComparison`. -/
def twoLegsDerivedIso (hF : ComputesDerivedComp F G RG αG)
    (hF' : ComputesDerivedComp F' G' RG' αG') : (RF ⋙ RG) ≅ (RF' ⋙ RG') :=
  have := isIso_twoLegsDerivedComparison F G F' G' RF RG RF' RG' αF αG αF' αG' t hF hF'
  asIso (twoLegsDerivedComparison F G F' G' RF RG RF' RG' αF αG αF' αG' t hF)

end TwoLegs

end Stacks.Cohomology.UnboundedComplexes

/-! ### The direct image of abelian sheaves along a morphism of topoi -/

attribute [local instance 5000] CategoryTheory.SemiCartesianMonoidalCategory.toMonoidalCategory

attribute [local instance 5000]
  CategoryTheory.CartesianMonoidalCategory.toSemiCartesianMonoidalCategory

attribute [local instance 3000]
  Stacks.Topos.AbelianInverseImage.instCartesianMonoidalCategorySheafType_stacksFrontier

attribute [local instance 3000]
  Stacks.Topos.AbelianInverseImage.instBraidedCategorySheafType_stacksFrontier

namespace Stacks.Topos.AbelianPushforward

open Stacks.Topos.AbelianInverseImage

section Pair

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ w

variable {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁}
  {C₂ : Type u₂} [Category.{v₂} C₂] {J₂ : GrothendieckTopology C₂}
  {C₃ : Type u₃} [Category.{v₃} C₃] {J₃ : GrothendieckTopology C₃}
  {C₄ : Type u₄} [Category.{v₄} C₄] {J₄ : GrothendieckTopology C₄}
  (f : MorphismOfTopoi (Sheaf J₁ (Type w)) (Sheaf J₂ (Type w)))
  (g : MorphismOfTopoi (Sheaf J₂ (Type w)) (Sheaf J₄ (Type w)))
  (f' : MorphismOfTopoi (Sheaf J₁ (Type w)) (Sheaf J₃ (Type w)))
  (g' : MorphismOfTopoi (Sheaf J₃ (Type w)) (Sheaf J₄ (Type w)))

/-- **The two composite direct images around a square of morphisms of topoi, on commutative
group objects.** An isomorphism `f_* ⋙ g_* ≅ f'_* ⋙ g'_*` of the composite direct images of
sheaves of sets induces the corresponding isomorphism of functors on commutative group objects.
Nothing here assumes the four morphisms form a commutative, let alone cartesian, square: the
natural isomorphism is the only link between them.

All four functors on group objects are `CategoryTheory.Functor.mapCommGrp` of a
finite-product-preserving functor of topoi, so this is the pseudofunctoriality of `mapCommGrp`:
`CategoryTheory.Functor.mapCommGrpCompIso` twice and
`CategoryTheory.Functor.mapCommGrpNatIso` once. It is the direct-image/direct-image analogue of
`StacksTag03LR.commGrpBaseChangeIso`. -/
def commGrpPushforwardPairIso
    (α : f.pushforward ⋙ g.pushforward ≅ f'.pushforward ⋙ g'.pushforward) :
    commGrpPushforward J₁ f ⋙ commGrpPushforward J₂ g ≅
      commGrpPushforward J₁ f' ⋙ commGrpPushforward J₃ g' := by
  letI : PreservesLimitsOfSize.{0, 0} f.pushforward := f.adj.rightAdjoint_preservesLimits
  letI : PreservesFiniteLimits f.pushforward := inferInstance
  letI : f.pushforward.Braided := .ofChosenFiniteProducts _
  letI : PreservesLimitsOfSize.{0, 0} g.pushforward := g.adj.rightAdjoint_preservesLimits
  letI : PreservesFiniteLimits g.pushforward := inferInstance
  letI : g.pushforward.Braided := .ofChosenFiniteProducts _
  letI : PreservesLimitsOfSize.{0, 0} f'.pushforward := f'.adj.rightAdjoint_preservesLimits
  letI : PreservesFiniteLimits f'.pushforward := inferInstance
  letI : f'.pushforward.Braided := .ofChosenFiniteProducts _
  letI : PreservesLimitsOfSize.{0, 0} g'.pushforward := g'.adj.rightAdjoint_preservesLimits
  letI : PreservesFiniteLimits g'.pushforward := inferInstance
  letI : g'.pushforward.Braided := .ofChosenFiniteProducts _
  exact Functor.mapCommGrpCompIso.symm ≪≫ Functor.mapCommGrpNatIso α ≪≫
    Functor.mapCommGrpCompIso

/-- **The two composite direct images around a square of morphisms of topoi, on abelian
sheaves.** An isomorphism `f_* ⋙ g_* ≅ f'_* ⋙ g'_*` of the composite direct images of sheaves
of sets induces the corresponding isomorphism of the composite direct images of abelian sheaves.

Each of the four functors on abelian sheaves is the conjugate, by the identification
`CategoryTheory.Sites.AbelianSheaf.equivalence` of abelian sheaves with commutative group
objects, of the corresponding functor on group objects, where the statement is
`commGrpPushforwardPairIso`; `CategoryTheory.Equivalence.conjugateCompIso` collapses the
composites of conjugates to the conjugates of the composites. It is the
direct-image/direct-image analogue of `StacksTag03LR.abelianBaseChangeIso`. -/
def abelianPushforwardPairIso
    (α : f.pushforward ⋙ g.pushforward ≅ f'.pushforward ⋙ g'.pushforward) :
    abelianPushforward J₁ f ⋙ abelianPushforward J₂ g ≅
      abelianPushforward J₁ f' ⋙ abelianPushforward J₃ g' :=
  let E₁ : CommGrp (Sheaf J₁ (Type w)) ≌ Sheaf J₁ AddCommGrpCat.{w} :=
    (CategoryTheory.Sites.AbelianSheaf.equivalence J₁).symm
  let E₂ : CommGrp (Sheaf J₂ (Type w)) ≌ Sheaf J₂ AddCommGrpCat.{w} :=
    (CategoryTheory.Sites.AbelianSheaf.equivalence J₂).symm
  let E₃ : CommGrp (Sheaf J₃ (Type w)) ≌ Sheaf J₃ AddCommGrpCat.{w} :=
    (CategoryTheory.Sites.AbelianSheaf.equivalence J₃).symm
  let E₄ : CommGrp (Sheaf J₄ (Type w)) ≌ Sheaf J₄ AddCommGrpCat.{w} :=
    (CategoryTheory.Sites.AbelianSheaf.equivalence J₄).symm
  Equivalence.conjugateCompIso E₁ E₂ E₄ (commGrpPushforward J₁ f)
      (commGrpPushforward J₂ g) ≪≫
    Functor.isoWhiskerLeft E₁.inverse
      (Functor.isoWhiskerRight (commGrpPushforwardPairIso f g f' g' α) E₄.functor) ≪≫
    (Equivalence.conjugateCompIso E₁ E₃ E₄ (commGrpPushforward J₁ f')
      (commGrpPushforward J₃ g')).symm

end Pair

section KInjective

universe v u v' u' w w'

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w'}]

/-- The inverse image of abelian sheaves along a morphism of topoi is additive, with no
hypothesis on the morphism, because it is left exact (Stacks 04JC). -/
theorem additive_abelianInverseImage :
    (CategoryTheory.Sites.abelianInverseImage f).Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [instance] additive_abelianInverseImage

/-- **Stacks 075L, part (2) at abelian coefficients, for an arbitrary morphism of topoi.** The
degreewise direct image of abelian sheaves along a morphism of topoi carries K-injective
complexes to K-injective complexes.

This is Stacks 08BJ, `CochainComplex.isKInjective_mapHomologicalComplex_of_exact`: the direct
image of abelian sheaves is right adjoint to the inverse image
(`abelianInverseImageAdjPushforward`), and the inverse image of abelian sheaves is exact by
Stacks 04JC (`CategoryTheory.Sites.abelianInverseImage_exact`), with no hypothesis on the
morphism of topoi.

It is the formal counterpart of the source's reason for Stacks 075L at the restriction `π_F`:
the restriction is simultaneously the direct image `π_{F,*}` and the inverse image `i_F^{-1}`,
and an inverse image is exact. It is exactly the step that fails for sheaves of modules, where
Stacks 0758 gives a counterexample; for abelian sheaves no flatness is needed, which is why
Stacks 075N's clause (1) carries no hypothesis in the place where its clause (2) carries one. -/
theorem isKInjective_mapHomologicalComplex_abelianPushforward
    (I : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((abelianPushforward J f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact _
    (CategoryTheory.Sites.abelianInverseImage f)
    (abelianInverseImageAdjPushforward J f) I

/-- **Stacks 075L, part (2) at abelian coefficients**, in the form the composition criterion
`Stacks.Cohomology.UnboundedComplexes.computesDerivedComp_of_preservesKInjective` consumes:
K-injectivity of the complex as an explicit hypothesis rather than an instance. -/
theorem preservesKInjective_abelianPushforward :
    ∀ I : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ, I.IsKInjective →
      CochainComplex.IsKInjective
        (((abelianPushforward J f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  fun I hI ↦
    let := hI
    isKInjective_mapHomologicalComplex_abelianPushforward J f I

end KInjective

end Stacks.Topos.AbelianPushforward

/-! ### Stacks 075N for abelian sheaves -/

namespace AlgebraicGeometry.Space

universe u v w v' w' dX dY dF dG

open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Cohomology.UnboundedComplexes Stacks.Topos.AbelianPushforward

attribute [local instance] hasSheafCompose_forget_ringCat
  Stacks.hasSheafCompose_forget₂_commRingCat

/-! #### The restriction of abelian sheaves and its exactness -/

section Restriction

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hF : IsAlgebraicSpace B S hS F)
  (e : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (F ⋙ typeToCat)).p)

/-- **Stacks 073M, equation 075K, at abelian coefficients.** The restriction
`ℱ|_{F_étale} = i_F^{-1}ℱ = π_{F,*}ℱ` of an abelian sheaf on the inherited étale site of `𝒳` to
the small étale site of the algebraic space `F`: the direct image of abelian sheaves along the
morphism of topoi underlying `π_F`. -/
abbrev abelianRestrictionFunctor :
    Sheaf (FibredSite.associatedRingedTopos B S hS p hp .etale).J AddCommGrpCat.{u} ⥤
      Sheaf (smallEtaleRingedTopos B S hS ⟨F, hF⟩).J AddCommGrpCat.{u} :=
  abelianPushforward (FibredSite.associatedRingedTopos B S hS p hp .etale).J
    (projectionRingedToposHom B S hS F p hp hF e).toToposHom

/-- **Stacks 073M, equation 075K.** On underlying sheaves of sets the restriction of abelian
sheaves is restriction along the functor `u_F : F_étale ⥤ 𝒳`, that is,
`(ℱ|_{F_étale})(U) = ℱ(u_F(U))` with the group operations of `ℱ(u_F(U))`.

This identifies `abelianRestrictionFunctor` with the source's `(-)|_{F_étale}`. It is
`Stacks.Topos.AbelianPushforward.abelianPushforward_forgetIso` — the identity isomorphism — read
through `AlgebraicGeometry.Space.projectionRingedToposHom_pushforward`. -/
def abelianRestrictionFunctor_forgetIso :
    letI := restrictionFunctor_isContinuous B S hS F p hp e
    abelianRestrictionFunctor B S hS F p hp hF e ⋙
        sheafCompose (SmallEtale.topology B S hS F) (forget AddCommGrpCat.{u}) ≅
      sheafCompose (BigFppfOver.associatedTopology B S hS p .etale)
          (forget AddCommGrpCat.{u}) ⋙
        (restrictionFunctor B S hS F p e).sheafPushforwardContinuous (Type u)
          (SmallEtale.topology B S hS F)
          (BigFppfOver.associatedTopology B S hS p .etale) :=
  abelianPushforward_forgetIso _ _

variable
  [HasSheafify (FibredSite.associatedRingedTopos B S hS p hp .etale).J AddCommGrpCat.{u}]
  [HasSheafify (smallEtaleRingedTopos B S hS ⟨F, hF⟩).J AddCommGrpCat.{u}]
  [(FibredSite.associatedRingedTopos B S hS p hp .etale).J.WEqualsLocallyBijective
    AddCommGrpCat.{u}]

omit [HasSheafify (smallEtaleRingedTopos B S hS ⟨F, hF⟩).J AddCommGrpCat.{u}] in
/-- **The restriction of abelian sheaves to the small étale site of `F` preserves
epimorphisms.** This is Stacks 04DB's alternative (1) for `π_F`, carried from sheaves of sets to
abelian sheaves: the restriction of sheaves of sets preserves epimorphisms because the functor
`u_F : F_étale ⥤ 𝒳` of Stacks 073M is continuous *and* cocontinuous, which is
`AlgebraicGeometry.Space.preservesEpimorphisms_projectionRingedToposHom_pushforward`. -/
theorem preservesEpimorphisms_abelianRestrictionFunctor :
    (abelianRestrictionFunctor B S hS F p hp hF e).PreservesEpimorphisms :=
  preservesEpimorphisms_abelianPushforward _ _
    (preservesEpimorphisms_projectionRingedToposHom_pushforward B S hS F p hp hF e)

/-- **The restriction of abelian sheaves to the small étale site of `F` is right exact.** This
is the half of exactness of `π_{F,*}` that has content; left exactness is adjointness. -/
theorem preservesFiniteColimits_abelianRestrictionFunctor :
    PreservesFiniteColimits (abelianRestrictionFunctor B S hS F p hp hF e) :=
  (abelianPushforward_exact_of_preservesEpimorphisms _ _
    (preservesEpimorphisms_abelianRestrictionFunctor B S hS F p hp hF e)).2

attribute [instance] preservesFiniteColimits_abelianRestrictionFunctor

/-- **The restriction of abelian sheaves to the small étale site of `F` is exact.** This is the
source's closing step in the proof of Stacks 075N, "because the restriction functors `π_{F,*}`
and `π_{G,*}` are exact". -/
theorem exactFunctor_abelianRestrictionFunctor :
    exactFunctor (Sheaf (FibredSite.associatedRingedTopos B S hS p hp .etale).J
        AddCommGrpCat.{u})
      (Sheaf (smallEtaleRingedTopos B S hS ⟨F, hF⟩).J AddCommGrpCat.{u})
      (abelianRestrictionFunctor B S hS F p hp hF e) :=
  abelianPushforward_exact_of_preservesEpimorphisms _ _
    (preservesEpimorphisms_abelianRestrictionFunctor B S hS F p hp hF e)

end Restriction

/-! #### Clause (1) of Stacks 075N -/

section Clause

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
  (eF : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (F ⋙ typeToCat)).p)
  (eG : StacksRepresentableCFG.EquivalenceOver q
    (presheafOfCategories (G ⋙ typeToCat)).p)
  (fStack : 𝒳 ⥤ 𝒴) (hfStack : p.IsFibredOneMorphism q fStack)
  [∀ P : 𝒳ᵒᵖ ⥤ Type u, fStack.op.HasPointwiseRightKanExtension P]

/-- **The direct image of abelian sheaves along the 1-morphism** `f : 𝒳 ⥤ 𝒴`, that is `f_*` of
Stacks 06TW at abelian coefficients: the direct image of abelian sheaves along the morphism of
topoi underlying `AlgebraicGeometry.FibredSite.ringedToposMorphism`. -/
abbrev abelianDirectImageFibred :
    Sheaf (FibredSite.associatedRingedTopos B S hS p hp .etale).J AddCommGrpCat.{u} ⥤
      Sheaf (FibredSite.associatedRingedTopos B S hS q hq .etale).J AddCommGrpCat.{u} :=
  abelianPushforward (FibredSite.associatedRingedTopos B S hS p hp .etale).J
    (FibredSite.ringedToposMorphism B S hS p q hp hq fStack hfStack .etale).toToposHom

/-- **The direct image of abelian sheaves along the induced morphism of algebraic spaces**
`f : F ⟶ G`, that is `f_{small,*}` of Stacks 03G2 at abelian coefficients, taken at
`AlgebraicGeometry.Space.inducedAlgebraicSpacesHom` — the source's "induced morphism of
algebraic spaces", which is derived from the 1-morphism and the two presentations and is
therefore not a parameter of clause (1). -/
abbrev abelianDirectImageSpace :
    Sheaf (smallEtaleRingedTopos B S hS ⟨F, hF⟩).J AddCommGrpCat.{u} ⥤
      Sheaf (smallEtaleRingedTopos B S hS ⟨G, hG⟩).J AddCommGrpCat.{u} :=
  abelianPushforward (smallEtaleRingedTopos B S hS ⟨F, hF⟩).J
    (smallEtaleRingedToposHom B S hS
      (inducedAlgebraicSpacesHom B S hS F G p q hF hG eF eG fStack hfStack)).toToposHom

variable
  [HasSheafify (FibredSite.associatedRingedTopos B S hS p hp .etale).J AddCommGrpCat.{u}]
  [HasSheafify (FibredSite.associatedRingedTopos B S hS q hq .etale).J AddCommGrpCat.{u}]
  [HasSheafify (smallEtaleRingedTopos B S hS ⟨F, hF⟩).J AddCommGrpCat.{u}]
  [HasSheafify (smallEtaleRingedTopos B S hS ⟨G, hG⟩).J AddCommGrpCat.{u}]
  [(FibredSite.associatedRingedTopos B S hS p hp .etale).J.WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [(FibredSite.associatedRingedTopos B S hS q hq .etale).J.WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [HasDerivedCategory.{dX}
    (Sheaf (FibredSite.associatedRingedTopos B S hS p hp .etale).J AddCommGrpCat.{u})]
  [HasDerivedCategory.{dY}
    (Sheaf (FibredSite.associatedRingedTopos B S hS q hq .etale).J AddCommGrpCat.{u})]
  [HasDerivedCategory.{dF}
    (Sheaf (smallEtaleRingedTopos B S hS ⟨F, hF⟩).J AddCommGrpCat.{u})]
  [HasDerivedCategory.{dG}
    (Sheaf (smallEtaleRingedTopos B S hS ⟨G, hG⟩).J AddCommGrpCat.{u})]
  [IsGrothendieckAbelian.{u}
    (Sheaf (FibredSite.associatedRingedTopos B S hS p hp .etale).J AddCommGrpCat.{u})]
  [IsGrothendieckAbelian.{u}
    (Sheaf (FibredSite.associatedRingedTopos B S hS q hq .etale).J AddCommGrpCat.{u})]
  [IsGrothendieckAbelian.{u}
    (Sheaf (smallEtaleRingedTopos B S hS ⟨F, hF⟩).J AddCommGrpCat.{u})]
  (Rf : DerivedCategory
      (Sheaf (FibredSite.associatedRingedTopos B S hS p hp .etale).J AddCommGrpCat.{u}) ⥤
    DerivedCategory
      (Sheaf (FibredSite.associatedRingedTopos B S hS q hq .etale).J AddCommGrpCat.{u}))
  (RprojG : DerivedCategory
      (Sheaf (FibredSite.associatedRingedTopos B S hS q hq .etale).J AddCommGrpCat.{u}) ⥤
    DerivedCategory (Sheaf (smallEtaleRingedTopos B S hS ⟨G, hG⟩).J AddCommGrpCat.{u}))
  (RprojF : DerivedCategory
      (Sheaf (FibredSite.associatedRingedTopos B S hS p hp .etale).J AddCommGrpCat.{u}) ⥤
    DerivedCategory (Sheaf (smallEtaleRingedTopos B S hS ⟨F, hF⟩).J AddCommGrpCat.{u}))
  (RfSpace : DerivedCategory
      (Sheaf (smallEtaleRingedTopos B S hS ⟨F, hF⟩).J AddCommGrpCat.{u}) ⥤
    DerivedCategory (Sheaf (smallEtaleRingedTopos B S hS ⟨G, hG⟩).J AddCommGrpCat.{u}))
  (αf : mapToDerivedCategory
      (abelianDirectImageFibred B S hS p q hp hq fStack hfStack) ⟶
    DerivedCategory.Qh ⋙ Rf)
  (αprojG : mapToDerivedCategory (abelianRestrictionFunctor B S hS G q hq hG eG) ⟶
    DerivedCategory.Qh ⋙ RprojG)
  (αprojF : mapToDerivedCategory (abelianRestrictionFunctor B S hS F p hp hF eF) ⟶
    DerivedCategory.Qh ⋙ RprojF)
  (αfSpace : mapToDerivedCategory
      (abelianDirectImageSpace B S hS F G p q hF hG eF eG fStack hfStack) ⟶
    DerivedCategory.Qh ⋙ RfSpace)
  [Rf.IsRightDerivedFunctor αf (HomotopyCategory.quasiIso
    (Sheaf (FibredSite.associatedRingedTopos B S hS p hp .etale).J AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]
  [RprojG.IsRightDerivedFunctor αprojG (HomotopyCategory.quasiIso
    (Sheaf (FibredSite.associatedRingedTopos B S hS q hq .etale).J AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]
  [RprojF.IsRightDerivedFunctor αprojF (HomotopyCategory.quasiIso
    (Sheaf (FibredSite.associatedRingedTopos B S hS p hp .etale).J AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]
  [RfSpace.IsRightDerivedFunctor αfSpace (HomotopyCategory.quasiIso
    (Sheaf (smallEtaleRingedTopos B S hS ⟨F, hF⟩).J AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]

omit [(FibredSite.associatedRingedTopos B S hS p hp .etale).J.WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [(FibredSite.associatedRingedTopos B S hS q hq .etale).J.WEqualsLocallyBijective
    AddCommGrpCat.{u}] in
/-- The comparison `Rf_* ⋙ Rπ_{G,*} ⟶ Rπ_{F,*} ⋙ Rf_{small,*}` of the two derived composites of
abelian sheaves around the square of Stacks 073N is an isomorphism.

This is `Stacks.Cohomology.UnboundedComplexes.isIso_twoLegsDerivedComparison` at the two legs
`AlgebraicGeometry.Space.restrictionSquareFibredLeg` and
`AlgebraicGeometry.Space.restrictionSquareSpaceLeg`, read on abelian sheaves. It is stated for
*arbitrary* right derived functors `RprojF`, `RprojG` of the two restriction functors, and so is
not itself the statement of Stacks 075N, clause (1), which has the two restrictions appearing
underived; that statement is `restrictedAbelianDerivedDirectImageIso` below.

There is no hypothesis. The 2-isomorphism of the two legs, Stacks 073N, is
`AlgebraicGeometry.Space.restrictionRingedSquareInducedAlgebraicSpaces` — the same term clause
(2) uses. Stacks 093Y for the first morphism of each leg — degreewise `f_*` and degreewise
`π_{F,*}` — is *not* a hypothesis either: at abelian coefficients it is
`Stacks.Topos.AbelianPushforward.isKInjective_mapHomologicalComplex_abelianPushforward`, proved
for every morphism of topoi. -/
theorem isIso_restrictedAbelianDerivedDirectImageComparison :
    IsIso (twoLegsDerivedComparison
      (abelianDirectImageFibred B S hS p q hp hq fStack hfStack)
      (abelianRestrictionFunctor B S hS G q hq hG eG)
      (abelianRestrictionFunctor B S hS F p hp hF eF)
      (abelianDirectImageSpace B S hS F G p q hF hG eF eG fStack hfStack)
      Rf RprojG RprojF RfSpace αf αprojG αprojF αfSpace
      (abelianPushforwardPairIso
        (FibredSite.ringedToposMorphism B S hS p q hp hq fStack hfStack .etale).toToposHom
        (projectionRingedToposHom B S hS G q hq hG eG).toToposHom
        (projectionRingedToposHom B S hS F p hp hF eF).toToposHom
        (smallEtaleRingedToposHom B S hS
          (inducedAlgebraicSpacesHom B S hS F G p q hF hG eF eG fStack hfStack)).toToposHom
        (restrictionRingedSquareInducedAlgebraicSpaces B S hS F G p q hp hq hF hG eF eG
          fStack hfStack).e)
      (computesDerivedComp_of_preservesKInjective _ _ _ _
        (preservesKInjective_abelianPushforward _ _))) :=
  isIso_twoLegsDerivedComparison _ _ _ _ Rf RprojG RprojF RfSpace αf αprojG αprojF αfSpace _ _
    (computesDerivedComp_of_preservesKInjective _ _ _ _
      (preservesKInjective_abelianPushforward _ _))

/-- **Stacks 075N, clause (1).** For an abelian sheaf `ℱ` on `𝒳_étale`, the restriction of
`Rf_*ℱ` to the small étale site of `G` is `Rf_{small,*}` of the restriction of `ℱ` to the small
étale site of `F`, as an identity in `D(G_étale)`.

The two restriction functors appear **underived**, as they do in the source: they are the
functors `CategoryTheory.Functor.mapDerivedCategory` induced on derived categories by the
degreewise restrictions `π_{G,*}` and `π_{F,*}` of abelian sheaves, which are their own right
derived functors because they are exact
(`AlgebraicGeometry.Space.exactFunctor_abelianRestrictionFunctor` and
`Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_mapDerivedCategoryFactorsh_inv`).
This is the source's closing step.

The isomorphism is the canonical comparison
`Stacks.Cohomology.UnboundedComplexes.twoLegsDerivedComparison` of the two derived composites
around the square of Stacks 073N, which
`isIso_restrictedAbelianDerivedDirectImageComparison` shows invertible; it is not a chosen
isomorphism of abstractly isomorphic functors.

Nothing beyond the source's data is a hypothesis. The 2-isomorphism of the two legs of the
square, Stacks 073N itself, is
`AlgebraicGeometry.Space.restrictionRingedSquareInducedAlgebraicSpaces` — the *same* term clause
(2) uses. Exactness of the two restrictions of abelian sheaves, which is the source's own stated
reason for the closing step, is proved; and so is Stacks 075L part (2) for degreewise `π_{F,*}`
and degreewise `f_*`, which at abelian coefficients holds for every morphism of topoi because an
inverse image of abelian sheaves is exact (Stacks 04JC), and which is the one place where
clause (2) needs a different argument, the module statement being false by Stacks 0758. -/
def restrictedAbelianDerivedDirectImageIso :
    Rf ⋙ (abelianRestrictionFunctor B S hS G q hq hG eG).mapDerivedCategory ≅
      (abelianRestrictionFunctor B S hS F p hp hF eF).mapDerivedCategory ⋙ RfSpace :=
  have := isRightDerivedFunctor_mapDerivedCategoryFactorsh_inv.{u}
    (abelianRestrictionFunctor B S hS G q hq hG eG)
  have := isRightDerivedFunctor_mapDerivedCategoryFactorsh_inv.{u}
    (abelianRestrictionFunctor B S hS F p hp hF eF)
  twoLegsDerivedIso
    (abelianDirectImageFibred B S hS p q hp hq fStack hfStack)
    (abelianRestrictionFunctor B S hS G q hq hG eG)
    (abelianRestrictionFunctor B S hS F p hp hF eF)
    (abelianDirectImageSpace B S hS F G p q hF hG eF eG fStack hfStack)
    Rf
    (abelianRestrictionFunctor B S hS G q hq hG eG).mapDerivedCategory
    (abelianRestrictionFunctor B S hS F p hp hF eF).mapDerivedCategory
    RfSpace αf
    (abelianRestrictionFunctor B S hS G q hq hG eG).mapDerivedCategoryFactorsh.inv
    (abelianRestrictionFunctor B S hS F p hp hF eF).mapDerivedCategoryFactorsh.inv
    αfSpace
    (abelianPushforwardPairIso
      (FibredSite.ringedToposMorphism B S hS p q hp hq fStack hfStack .etale).toToposHom
      (projectionRingedToposHom B S hS G q hq hG eG).toToposHom
      (projectionRingedToposHom B S hS F p hp hF eF).toToposHom
      (smallEtaleRingedToposHom B S hS
        (inducedAlgebraicSpacesHom B S hS F G p q hF hG eF eG fStack hfStack)).toToposHom
      (restrictionRingedSquareInducedAlgebraicSpaces B S hS F G p q hp hq hF hG eF eG
        fStack hfStack).e)
    (computesDerivedComp_of_isIso _ _ _ _)
    (computesDerivedComp_of_preservesKInjective _ _ _ _
      (preservesKInjective_abelianPushforward _ _))

end Clause

/-! #### Stacks 075N: both clauses -/

section WholeTag

universe mX mY mF mG

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
  (eF : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (F ⋙ typeToCat)).p)
  (eG : StacksRepresentableCFG.EquivalenceOver q
    (presheafOfCategories (G ⋙ typeToCat)).p)
  (fStack : 𝒳 ⥤ 𝒴) (hfStack : p.IsFibredOneMorphism q fStack)
  [∀ P : 𝒳ᵒᵖ ⥤ Type u, fStack.op.HasPointwiseRightKanExtension P]
  [(FibredSite.associatedRingedTopos B S hS p hp .etale).J.HasSheafCompose
    (forget AddCommGrpCat.{u})]
  [(FibredSite.associatedRingedTopos B S hS q hq .etale).J.HasSheafCompose
    (forget AddCommGrpCat.{u})]
  [(smallEtaleRingedTopos B S hS ⟨F, hF⟩).J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [(smallEtaleRingedTopos B S hS ⟨G, hG⟩).J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify (FibredSite.associatedRingedTopos B S hS p hp .etale).J AddCommGrpCat.{u}]
  [HasSheafify (FibredSite.associatedRingedTopos B S hS q hq .etale).J AddCommGrpCat.{u}]
  [HasSheafify (smallEtaleRingedTopos B S hS ⟨F, hF⟩).J AddCommGrpCat.{u}]
  [HasSheafify (smallEtaleRingedTopos B S hS ⟨G, hG⟩).J AddCommGrpCat.{u}]
  [(FibredSite.associatedRingedTopos B S hS p hp .etale).J.WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [(FibredSite.associatedRingedTopos B S hS q hq .etale).J.WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [(smallEtaleRingedTopos B S hS ⟨F, hF⟩).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(smallEtaleRingedTopos B S hS ⟨G, hG⟩).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{dX}
    (Sheaf (FibredSite.associatedRingedTopos B S hS p hp .etale).J AddCommGrpCat.{u})]
  [HasDerivedCategory.{dY}
    (Sheaf (FibredSite.associatedRingedTopos B S hS q hq .etale).J AddCommGrpCat.{u})]
  [HasDerivedCategory.{dF}
    (Sheaf (smallEtaleRingedTopos B S hS ⟨F, hF⟩).J AddCommGrpCat.{u})]
  [HasDerivedCategory.{dG}
    (Sheaf (smallEtaleRingedTopos B S hS ⟨G, hG⟩).J AddCommGrpCat.{u})]
  [IsGrothendieckAbelian.{u}
    (Sheaf (FibredSite.associatedRingedTopos B S hS p hp .etale).J AddCommGrpCat.{u})]
  [IsGrothendieckAbelian.{u}
    (Sheaf (FibredSite.associatedRingedTopos B S hS q hq .etale).J AddCommGrpCat.{u})]
  [IsGrothendieckAbelian.{u}
    (Sheaf (smallEtaleRingedTopos B S hS ⟨F, hF⟩).J AddCommGrpCat.{u})]
  [HasDerivedCategory.{mX} (FibredSite.associatedRingedTopos B S hS p hp .etale).Modules]
  [HasDerivedCategory.{mY} (FibredSite.associatedRingedTopos B S hS q hq .etale).Modules]
  [HasDerivedCategory.{mF} (smallEtaleRingedTopos B S hS ⟨F, hF⟩).Modules]
  [HasDerivedCategory.{mG} (smallEtaleRingedTopos B S hS ⟨G, hG⟩).Modules]
  [IsGrothendieckAbelian.{u} (FibredSite.associatedRingedTopos B S hS p hp .etale).Modules]
  [IsGrothendieckAbelian.{u} (FibredSite.associatedRingedTopos B S hS q hq .etale).Modules]
  [IsGrothendieckAbelian.{u} (smallEtaleRingedTopos B S hS ⟨F, hF⟩).Modules]
  (Rab : DerivedCategory
      (Sheaf (FibredSite.associatedRingedTopos B S hS p hp .etale).J AddCommGrpCat.{u}) ⥤
    DerivedCategory
      (Sheaf (FibredSite.associatedRingedTopos B S hS q hq .etale).J AddCommGrpCat.{u}))
  (RabSpace : DerivedCategory
      (Sheaf (smallEtaleRingedTopos B S hS ⟨F, hF⟩).J AddCommGrpCat.{u}) ⥤
    DerivedCategory (Sheaf (smallEtaleRingedTopos B S hS ⟨G, hG⟩).J AddCommGrpCat.{u}))
  (αab : mapToDerivedCategory
      (abelianDirectImageFibred B S hS p q hp hq fStack hfStack) ⟶
    DerivedCategory.Qh ⋙ Rab)
  (αabSpace : mapToDerivedCategory
      (abelianDirectImageSpace B S hS F G p q hF hG eF eG fStack hfStack) ⟶
    DerivedCategory.Qh ⋙ RabSpace)
  [Rab.IsRightDerivedFunctor αab (HomotopyCategory.quasiIso
    (Sheaf (FibredSite.associatedRingedTopos B S hS p hp .etale).J AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]
  [RabSpace.IsRightDerivedFunctor αabSpace (HomotopyCategory.quasiIso
    (Sheaf (smallEtaleRingedTopos B S hS ⟨F, hF⟩).J AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]
  (Rmod : DerivedCategory (FibredSite.associatedRingedTopos B S hS p hp .etale).Modules ⥤
    DerivedCategory (FibredSite.associatedRingedTopos B S hS q hq .etale).Modules)
  (RmodSpace : DerivedCategory (smallEtaleRingedTopos B S hS ⟨F, hF⟩).Modules ⥤
    DerivedCategory (smallEtaleRingedTopos B S hS ⟨G, hG⟩).Modules)
  (αmod : RingedToposHom.pushforwardToDerivedCategory
      (FibredSite.ringedToposMorphism B S hS p q hp hq fStack hfStack .etale) ⟶
    DerivedCategory.Qh ⋙ Rmod)
  (αmodSpace : RingedToposHom.pushforwardToDerivedCategory
      (smallEtaleRingedToposHom B S hS
        (inducedAlgebraicSpacesHom B S hS F G p q hF hG eF eG fStack hfStack)) ⟶
    DerivedCategory.Qh ⋙ RmodSpace)
  [Rmod.IsRightDerivedFunctor αmod (HomotopyCategory.quasiIso
    (FibredSite.associatedRingedTopos B S hS p hp .etale).Modules (ComplexShape.up ℤ))]
  [RmodSpace.IsRightDerivedFunctor αmodSpace (HomotopyCategory.quasiIso
    (smallEtaleRingedTopos B S hS ⟨F, hF⟩).Modules (ComplexShape.up ℤ))]

/-- **Stacks 075N.** Let `S` be a scheme in a big fppf site, let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of
categories fibred in groupoids over `(Sch/S)_{fppf}` with `𝒳` presented by an algebraic space
`F` and `𝒴` by an algebraic space `G`, and let `f : F ⟶ G` be the induced morphism of algebraic
spaces. Then **both** clauses of Stacks 075N hold:

1. for an abelian sheaf `ℱ` on `𝒳_étale`,
   `(Rf_*ℱ)|_{G_étale} = Rf_{small,*}(ℱ|_{F_étale})` in `D(G_étale)`;
2. for a complex `ℱ` of `𝒪_𝒳`-modules, the same identity in `D(𝒪_G)`.

The two components are `AlgebraicGeometry.Space.restrictedAbelianDerivedDirectImageIso` and
`AlgebraicGeometry.Space.restrictedDerivedDirectImageIso`, and each is the *canonical*
comparison of the two derived composites around the square of Stacks 073N, shown invertible —
not a chosen isomorphism of abstractly isomorphic functors. In both clauses the two restriction
functors appear **underived**, as they do in the source, being their own right derived functors
because they are exact; that is the source's closing step.

The two clauses are collected as a pair rather than as a new structure because each component is
already a single isomorphism of functors and nothing is shared between their types: the derived
categories of `D(𝒳_étale)` and of `D(𝒪_𝒳)` are different categories, so the two clauses need
their own derived direct images `Rab`, `Rmod` and their own units. A pair asserts exactly the
conjunction of the two displays while keeping each one a term one can use on its own, which a
`Nonempty`-style conjunction in `Prop` would not: it would assert that the two sides are
abstractly isomorphic and forget that the comparison map realizing it is the canonical one.

The hypotheses are the source's — `S`, the 1-morphism, the two presentations `eF`, `eG` — along
with the right derived direct images whose existence each display presupposes. -/
@[stacks 075N "BOTH clauses. (1) for ABELIAN sheaves, (Rf_*F)|_{G_etale} =
  Rf_{small,*}(F|_{F_etale}) in D(G_etale), which is
  `AlgebraicGeometry.Space.restrictedAbelianDerivedDirectImageIso`; (2) for sheaves of MODULES,
  the same identity in D(O_G), which is
  `AlgebraicGeometry.Space.restrictedDerivedDirectImageIso`. In both, the two restriction
  functors appear UNDERIVED as in the source, being their own right derived functors because
  they are exact, and the isomorphism is the canonical comparison of the two derived composites
  around the square of Tag 073N. The morphism f : F -> G of algebraic spaces is INDUCED, as the
  source has it -- it says: denote f : F -> G the induced morphism of algebraic spaces -- and is
  therefore no parameter of this statement: the derived direct images of the small sites, their
  units and the square of Tag 073N are all stated at
  `AlgebraicGeometry.Space.inducedAlgebraicSpacesHom`, which Tag 04SW characterises
  (`eq_inducedSpacesHom_iff_forall_sectionOfObj`, `morphismSpaceEquiv_eq_inducedSpaceMap`). So
  the hypotheses here are the source's: S, the 1-morphism, the two presentations, and the
  complex, together with the right derived direct images whose existence each display
  presupposes. Every mathematical input is a theorem of this development. Tag 073N, the
  2-isomorphism of the two legs of the square, is
  `AlgebraicGeometry.Space.restrictionRingedSquareInducedAlgebraicSpaces`, assembled from
  invertibility of the comparison map of equation 075M
  (`AlgebraicGeometry.Space.isIso_restrictedDirectImageComparison`, settled chartwise: the
  pushforward formula of Tag 06W6 and the chart correspondence of Tag 03G8 give injectivity, and
  gluing a compatible family over the chart diagrams against Properties of Spaces 03H7 gives
  surjectivity) together with its structure-sheaf compatibility
  (`AlgebraicGeometry.Space.restrictedDirectImageComparison_structureSheafCompatible`, whose
  verticality input is
  `AlgebraicGeometry.Space.isHomLift_schemeChartPostcompIso_hom_app`). Exactness of the two
  restriction functors, the source's own stated reason for the closing step, is
  `AlgebraicGeometry.Space.exactFunctor_pushforwardModules_projectionRingedToposHom` for modules
  and `AlgebraicGeometry.Space.exactFunctor_abelianRestrictionFunctor` for abelian sheaves. Tag
  093Y for degreewise f_* is unnecessary, the unit of the exact pi_{G,*} being invertible
  everywhere. The condition the composition criterion consumes at the leg f_small . pi_F is
  `AlgebraicGeometry.Space.pushforwardComputesDerived_smallEtaleRingedToposHom` for modules, out
  of the unconditional Tag 0D6E for a morphism of ringed topoi, and
  `Stacks.Topos.AbelianPushforward.isKInjective_mapHomologicalComplex_abelianPushforward`,
  Tag 075L part (2) at abelian coefficients, for abelian sheaves"]
noncomputable def restrictedDerivedDirectImageIsoClauses :
    (Rab ⋙ (abelianRestrictionFunctor B S hS G q hq hG eG).mapDerivedCategory ≅
        (abelianRestrictionFunctor B S hS F p hp hF eF).mapDerivedCategory ⋙ RabSpace) ×
      (Rmod ⋙ RingedToposHom.derivedPushforwardOfExact
            (projectionRingedToposHom B S hS G q hq hG eG) ≅
        RingedToposHom.derivedPushforwardOfExact
            (projectionRingedToposHom B S hS F p hp hF eF) ⋙ RmodSpace) :=
  ⟨restrictedAbelianDerivedDirectImageIso B S hS F G p q hp hq hF hG eF eG fStack hfStack
      Rab RabSpace αab αabSpace,
    restrictedDerivedDirectImageIso B S hS F G p q hp hq hF hG eF eG fStack hfStack
      Rmod RmodSpace αmod αmodSpace⟩

end WholeTag

end AlgebraicGeometry.Space

end
