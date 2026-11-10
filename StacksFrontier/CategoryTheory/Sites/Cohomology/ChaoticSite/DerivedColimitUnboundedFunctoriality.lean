module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.CategoryTheory.Shift.Mates
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.EvaluationToDerivedColimit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.Functoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekAlongAFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# The comparison of the two derived lower shrieks on the unbounded derived category

Let `f : C' ⥤ C` be a functor between small categories carrying their chaotic topologies, let the
coefficients be an abelian category `D` in which countable filtered colimits are exact and whose
diagram categories have enough projectives, and let `g^{-1}` be the inverse image of the induced
morphism of ringed topoi — restriction of diagrams along `f`. This file constructs the canonical
comparison

`Lπ'_! ∘ g^{-1} ⟶ Lπ_!`

as a natural transformation of functors on the **unbounded** derived category `D(Cᵒᵖ ⥤ D)`, with
no hypothesis on `f` whatsoever.

## Main definitions

* `Stacks.ChaoticSite.derivedConstRestrictionIso`: the identification `g^{-1} ∘ π^{-1} = π'^{-1}`
  of the derived inverse images of the constant diagram — the datum of [Stacks, Tag 08PH] read in
  the derived categories.
* `Stacks.ChaoticSite.unboundedComparison`: the comparison `Lπ'_!(g^{-1}K) ⟶ Lπ_!(K)`, natural in
  `K ∈ D(Cᵒᵖ ⥤ D)`.
* `Stacks.ChaoticSite.AbelianValued.derivedColimitPresheafRestrictionUnboundedComparison` and
  `Stacks.ChaoticSite.ModuleValued.derivedColimitInverseImageUnboundedComparison`: the comparison
  at the two coefficient settings of the source, `D(C) ⥤ D(Ab)` and `D(C, B̲) ⥤ D(B)`.

## Main results

* `Stacks.ChaoticSite.commShift_unboundedComparison`: the comparison is compatible with the
  shift, which is the first of the inputs a dévissage along compact generators needs.
* `Stacks.ChaoticSite.unit_comp_unboundedComparison_comp_counit`: the transpose of the comparison
  composed with the derived-functor comparison, computed outright in terms of the *underived* unit
  of `colim ⊣ const`.
* `Stacks.ChaoticSite.unit_comp_derivedConstRestrictionIso`: the identity that pins the comparison
  down. It is the mate of `derivedConstRestrictionIso` across the two derived adjunctions
  `Lπ_! ⊣ π^{-1}` of `Stacks.CategoryHomology.totalDerivedColimitAdjunction`, so it is the unique
  morphism whose `π^{-1}`-transpose is `g^{-1}` applied to the unit of `Lπ_! ⊣ π^{-1}` followed by
  that identification. There is no choice in it.

## How it is built, and what it is for

`g^{-1}` is precomposition with `f.op`, so it carries the constant diagram on `C` to the constant
diagram on `C'` **on the nose** — `Stacks.ChaoticSite.const_comp_whiskeringLeft_obj_op` is `rfl`.
Both derived lower shrieks are left adjoints, by
`Stacks.CategoryHomology.totalDerivedColimitAdjunction`, and their right adjoints are the derived
constant-diagram functors; so the identification of the right adjoints has a mate between the left
adjoints, and that mate is the comparison. The mates correspondence is
`CategoryTheory.mateEquiv`, which supplies naturality in `K` as part of the package.

Pointwise this is `CategoryTheory.Adjunction.restrictionMate` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/ChaoticSite/EilenbergZilber.lean`, which is the
shape in which the hypotheses `_h08QA`, `_h08QA₁`, `_h08QA₂` of
`Stacks.ChaoticSite.isIso_totalDerivedColimitTensorComparison` state [Stacks, Tag 08QA] at the
derived level: those hypotheses also take the identification `α` of the derived constant diagrams
as an input, and `derivedConstRestrictionIso` is that input.

## [Stacks, Tag 08QA] on the unbounded derived category

The source asserts that the comparison is an **isomorphism** when there is a cosimplicial object
`U'_•` of `C'` such that [Stacks, Tag 08Q9] applies to both `U'_•` in `C'` and `f(U'_•)` in `C`.
That is now proved, in
`StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitUnboundedIsIso`:
`Stacks.ChaoticSite.isIso_unboundedComparison_of_isPointResolutions`, at coefficients which are
Grothendieck abelian relative to the universe of `C` and `C'` and carry a separating family of
projective compact objects, with the source's module coefficients spelled out as
`Stacks.ChaoticSite.ModuleValued.isIso_derivedColimitInverseImageUnboundedComparison`. The
repository also proves the identification

* degreewise, `Stacks.ChaoticSite.leftDerivedColimitPresheafRestrictionNatIso`;
* on the heart, `Stacks.ChaoticSite.AbelianValued.derivedColimitPresheafRestrictionNatIso` and
  `Stacks.ChaoticSite.ModuleValued.derivedColimitInverseImageNatIso`;
* on complexes strictly bounded above by `0`,
  `Stacks.ChaoticSite.AbelianValued.derivedColimitPresheafRestrictionComplexNatIso` and
  `Stacks.ChaoticSite.ModuleValued.derivedColimitInverseImageComplexNatIso`.

The unbounded statement goes through the dévissage
`StacksDraft.CompactDevissage.isIso_of_isIso_app_freeYoneda_anyModel` along compact generators of
`D(Cᵒᵖ ⥤ D)`. Its three inputs:

* `NatTrans.CommShift (unboundedComparison f D) ℤ` — **proved**, as
  `Stacks.ChaoticSite.commShift_unboundedComparison`. Each factor of the mate is shift-compatible:
  `CategoryTheory.Adjunction.CommShift` carries `NatTrans.CommShift` for the unit and the counit
  (and `CategoryTheory.Adjunction.commShift_of_rightAdjoint` supplies it for both derived
  adjunctions), whiskerings, associators and unitors have the instance, and the identification of
  the derived constant diagrams has it by
  `Stacks.ChaoticSite.commShift_derivedConstRestrictionIso`. Two things had to be built for that
  chain. `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` used to hide its
  `CategoryTheory.Localization.Lifting` datum in a `letI`, where no later declaration could reach
  it; it is now the named `Stacks.DerivedCategoryComparisons.liftingMapDerivedCategoryComp`, whose
  comparison is shift-compatible
  (`Stacks.DerivedCategoryComparisons.commShift_mapDerivedCategoryCompLiftingIso_hom`), so
  `Stacks.DerivedCategoryComparisons.localization_liftNatTrans_commShift` applies. And a mate is
  an application of an `Equiv` literal, which instance search cannot unfold, so the general fact
  that mates of shift-compatible squares are shift-compatible is stated for abstract functors as
  `CategoryTheory.NatTrans.commShift_mateEquiv_symm`.
* Compact generation of `D(Cᵒᵖ ⥤ D)` — **proved**, as
  `StacksDraft.CompactDevissage.isCompactlyGenerated_derivedCategory_diagrams`: the free diagrams
  `CategoryTheory.Presheaf.freeYoneda X (S i)`, placed in degree zero, generate, for any
  separating family `S` of projective compact objects of the coefficients. Three things had to be
  built or opened for it. The generating family needed two statements, and both are now there: the
  projectivity of `CategoryTheory.Presheaf.freeYoneda X P` for a projective `P`, which
  `Stacks.CategoryHomology.freeYonedaProjective` used to assert only for `D = AddCommGrpCat` and
  now asserts over any target where the free diagrams exist and epimorphisms of diagrams are
  epimorphisms componentwise; and its compactness,
  `CategoryTheory.Presheaf.isCompactObject_freeYoneda`, which was nowhere stated and comes from
  `CategoryTheory.Presheaf.freeYonedaHomEquiv` once that bijection is read additively
  (`CategoryTheory.Presheaf.freeYonedaHomAddEquiv`) and the evaluation at `X` is let through the
  direct sum. The third was the criterion
  `Stacks.Cohomology.isWeakTriangulatedGenerator_single_of_projective_separating`, which was
  `private` to the site file that happened to prove it and is now public, being a statement about
  an arbitrary abelian category. The other prerequisites were already available: `Cᵒᵖ ⥤ D` is
  Grothendieck abelian relative to the universe of the objects of `C`
  (`CategoryTheory.isGrothendieckAbelian_presheafCategory`), so `D(Cᵒᵖ ⥤ D)` has the direct sums
  the dévissage needs (`Stacks.Injectives.hasCoproducts_derivedCategory_diagrams`), has enough
  injectives (Mathlib's instance `CategoryTheory.IsGrothendieckAbelian.enoughInjectives`), and has
  a model whose morphisms live in that universe (`Stacks.Injectives.hasDerivedCategory_diagrams`,
  [Stacks, Tag 079Q]).

  The dévissage *at the model this file works in* is
  `StacksDraft.CompactDevissage.isIso_of_isIso_app_freeYoneda_anyModel`: the compact generation
  asserts compactness at the morphism universe of `Cᵒᵖ ⥤ D`, which agrees with the model's hom
  universe at the [Stacks, Tag 079Q] model and not at `CategoryTheory.HasDerivedCategory.standard`,
  where the morphisms of `D(Cᵒᵖ ⥤ D)` are one level higher; but the *conclusion* transports,
  because a morphism is invertible exactly when its whiskering by the comparison equivalence
  `StacksDraft.DerivedModel.modelEquiv` of the two models is. That transport was already
  model-generic, as `StacksDraft.DerivedModel.modelEquiv` takes both `HasDerivedCategory` instances
  as explicit arguments; nothing about two `HasDerivedCategory` instances for one category had to
  be built. The resulting reduction of the whole statement to the generators is
  `Stacks.ChaoticSite.isIso_unboundedComparison_of_isIso_app_freeYoneda`.
* The identification of `(unboundedComparison f D).app` at a generator — **proved**. It is *not*
  the comparison on the heart: that is a composite of two [Stacks, Tag 08Q9] isomorphisms through
  the double complex of a *chosen* projective resolution, nothing characterizes it by a universal
  property, and so it cannot be recognized in the pinning — that route is closed. What the pinning
  needs instead is the *underived* unit of `colim ⊣ const`, and reading it against
  `CategoryTheory.Limits.colimit.ι_pre` turns the invertibility at a generator into two statements:
  the vanishing `L_nπ'_!(g^{-1}E) = 0` for `n > 0`, which is
  `Stacks.ChaoticSite.isIso_totalDerivedColimitCounit_single_of_projective_restrict` (whose two
  projectivity inputs are `Stacks.ChaoticSite.projective_restrict_freeYoneda` and
  `Stacks.ChaoticSite.preservesProjectiveObjects_restrictAlongPointResolution`), and the
  invertibility of the underived comparison `colimit.pre E f.op`, which is
  `Stacks.ChaoticSite.isIso_colimitPre_op_of_isPointResolutions`. The reading itself — that the
  pinned map *is* `colimit.pre E f.op` through the two counits — is
  `Stacks.ChaoticSite.unboundedComparison_app_comp_counit`, whose underived input is
  `Stacks.ChaoticSite.restrict_colimConstAdj_unit`.

## References

* [Stacks Project, Tag 08QA](https://stacks.math.columbia.edu/tag/08QA)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08PH](https://stacks.math.columbia.edu/tag/08PH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CategoryHomology

namespace Stacks.ChaoticSite

universe uD vD u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

section Comparison

variable {C C' : Type u} [SmallCategory C] [SmallCategory C'] (f : C' ⥤ C)
  (D : Type uD) [Category.{vD} D] [Abelian D]
  [EnoughProjectives (Cᵒᵖ ⥤ D)] [EnoughProjectives (C'ᵒᵖ ⥤ D)]
  [HasColimitsOfShape ℕ D] [HasExactColimitsOfShape ℕ D]
  [HasColimitsOfShape Cᵒᵖ D] [HasColimitsOfShape C'ᵒᵖ D]

omit [Abelian D] [EnoughProjectives (Cᵒᵖ ⥤ D)] [EnoughProjectives (C'ᵒᵖ ⥤ D)]
  [HasColimitsOfShape ℕ D] [HasExactColimitsOfShape ℕ D]
  [HasColimitsOfShape Cᵒᵖ D] [HasColimitsOfShape C'ᵒᵖ D] in
/-- **Restriction along `f` carries the constant diagram on `C` to the constant diagram on `C'`**,
on the nose: both are precomposition of a constant functor, and a constant functor precomposed
with anything is the constant functor with the same value, with the same identity morphisms. This
is the datum of [Stacks, Tag 08PH] saying that `g^{-1} ∘ π^{-1} = π'^{-1}`. -/
lemma const_comp_whiskeringLeft_obj_op :
    (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)) ⋙ (Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op =
      (Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)) :=
  rfl

/-- **The identification `g^{-1} ∘ π^{-1} = π'^{-1}` of the derived inverse images of the constant
diagram.** The two underived functors are equal by
`Stacks.ChaoticSite.const_comp_whiskeringLeft_obj_op`, and both are exact, so the only thing to
spend is the comparison of the degreewise action of a composite with the composite of the
degreewise actions. -/
def derivedConstRestrictionIso :
    (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategory ⋙
        ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategory ≅
      (Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)).mapDerivedCategory :=
  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
    (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D))
    ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op)).symm

/-- **The comparison `Lπ'_! ∘ g^{-1} ⟶ Lπ_!` on the unbounded derived category.** Both derived
lower shrieks are left adjoints, with the derived constant diagrams as right adjoints
(`Stacks.CategoryHomology.totalDerivedColimitAdjunction`); this is the mate of the identification
`Stacks.ChaoticSite.derivedConstRestrictionIso` of those right adjoints. No hypothesis on `f` is
used: the comparison exists always, and it is its invertibility that [Stacks, Tag 08QA] asserts
under the hypothesis of a common cosimplicial resolution. -/
def unboundedComparison :
    ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategory ⋙
        totalDerivedColimit C' D ⟶
      totalDerivedColimit C D :=
  ((mateEquiv (totalDerivedColimitAdjunction C D)
      (totalDerivedColimitAdjunction C' D)).symm
        (TwoSquare.mk _ _ _ _ (derivedConstRestrictionIso f D).hom) :
      ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategory ⋙
        totalDerivedColimit C' D ⟶ totalDerivedColimit C D ⋙ 𝟭 _) ≫
    (Functor.rightUnitor (totalDerivedColimit C D)).hom

/-- **The identity that pins `Stacks.ChaoticSite.unboundedComparison` down.** Its transpose along
`Lπ'_! ⊣ π'^{-1}` is `g^{-1}` applied to the unit of `Lπ_! ⊣ π^{-1}`, followed by the
identification of the derived constant diagrams. Being a mate, it is the unique morphism with that
property. -/
lemma unit_comp_derivedConstRestrictionIso (K : DerivedCategory (Cᵒᵖ ⥤ D)) :
    ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategory.map
          ((totalDerivedColimitAdjunction C D).unit.app K) ≫
        (derivedConstRestrictionIso f D).hom.app ((totalDerivedColimit C D).obj K) =
      (totalDerivedColimitAdjunction C' D).unit.app
          (((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategory.obj K) ≫
        (Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)).mapDerivedCategory.map
          ((unboundedComparison f D).app K) := by
  simp [unboundedComparison]

/-- **The comparison composed with the derived-functor comparison, transposed.** This computes the
transpose of `Stacks.ChaoticSite.unboundedComparison` outright, at every object coming from the
homotopy category: it is `g^{-1}` applied to the *underived* unit of `colim ⊣ const`, read through
the degreewise comparison of the derived constant diagram and then through the identification
`Stacks.ChaoticSite.derivedConstRestrictionIso`.

Since the transpose along `Lπ'_! ⊣ π'^{-1}` is a bijection, this pins
`(unboundedComparison f D).app (Q_h K) ≫ (totalDerivedColimitCounit C D).app K` completely; and
`Stacks.CategoryHomology.totalDerivedColimitCounit` is invertible at a K-projective complex, so
there it pins the comparison itself. Together with
`Stacks.CategoryHomology.totalDerivedColimitObjSingleIso` this is the statement at a projective
diagram placed in degree zero, which is the shape the generators of the dévissage have. -/
theorem unit_comp_unboundedComparison_comp_counit
    (X : HomotopyCategory (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)) :
    (totalDerivedColimitAdjunction C' D).unit.app
          (((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategory.obj
            (DerivedCategory.Qh.obj X)) ≫
        (Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)).mapDerivedCategory.map
          ((unboundedComparison f D).app (DerivedCategory.Qh.obj X) ≫
            (totalDerivedColimitCounit C D).app X) =
      ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategory.map
          (DerivedCategory.Qh.map
              (((colimConstAdj : (colim : (Cᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const Cᵒᵖ).mapHomotopyCategory
                (ComplexShape.up ℤ)).unit.app X) ≫
            (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategoryFactorsh.inv.app
              (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) ≫
        (derivedConstRestrictionIso f D).hom.app
          (DerivedCategory.Qh.obj
            (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) := by
  -- the naturality square of the identification, written at the applied spelling of its ends:
  -- as a *term* the composite functor's action is the composite of the actions, while `rw` on the
  -- naturality lemma would be looking for `(Q_h ⋙ Lπ_!).obj X`
  have hnat : (derivedConstRestrictionIso f D).hom.app
          ((totalDerivedColimit C D).obj (DerivedCategory.Qh.obj X)) ≫
        (Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)).mapDerivedCategory.map
          ((totalDerivedColimitCounit C D).app X) =
      ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategory.map
          ((Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategory.map
            ((totalDerivedColimitCounit C D).app X)) ≫
        (derivedConstRestrictionIso f D).hom.app
          (DerivedCategory.Qh.obj
            (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) :=
    ((derivedConstRestrictionIso f D).hom.naturality
      ((totalDerivedColimitCounit C D).app X)).symm
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc,
    ← unit_comp_derivedConstRestrictionIso f D (DerivedCategory.Qh.obj X), Category.assoc, hnat,
    ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    totalDerivedColimitAdjunction_unit_app_comp_counit C D X]

/-- **The identification of the derived constant diagrams is compatible with the shift.** It is
the inverse of `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso`, whose compatibility
is `Stacks.DerivedCategoryComparisons.commShift_mapDerivedCategoryCompIso_hom`. -/
instance commShift_derivedConstRestrictionIso :
    NatTrans.CommShift (derivedConstRestrictionIso f D).hom ℤ :=
  inferInstanceAs (NatTrans.CommShift
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
      (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D))
      ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op)).inv ℤ)

/-- **The comparison on the unbounded derived category is compatible with the shift.** Both
derived adjunctions are, being adjunctions whose right adjoint commutes with the shift
(`CategoryTheory.Adjunction.commShift_of_rightAdjoint`), and the identification of the derived
constant diagrams is by
`Stacks.ChaoticSite.commShift_derivedConstRestrictionIso`; so
`CategoryTheory.NatTrans.commShift_mateEquiv_symm` applies to the mate. This is the first of the
three inputs that a dévissage of the comparison along compact generators needs. -/
instance commShift_unboundedComparison :
    NatTrans.CommShift (unboundedComparison f D) ℤ := by
  let : (totalDerivedColimitAdjunction C D).CommShift ℤ :=
    (totalDerivedColimitAdjunction C D).commShift_of_rightAdjoint ℤ
  let : (totalDerivedColimitAdjunction C' D).CommShift ℤ :=
    (totalDerivedColimitAdjunction C' D).commShift_of_rightAdjoint ℤ
  rw [unboundedComparison]
  infer_instance

end Comparison

/-! ### The two coefficient settings of the source -/

namespace AbelianValued

variable {C C' : Type u} [SmallCategory C] [SmallCategory C']

/-- **The comparison `Lπ'_! ∘ g^{-1} ⟶ Lπ_!` as a morphism of functors `D(C) ⥤ D(Ab)`**, on the
unbounded derived category of abelian presheaves on `C`. This is
`Stacks.ChaoticSite.unboundedComparison` at abelian coefficients, stated at the spelling of
`Stacks.CategoryHomology.presheafRestriction`. -/
def derivedColimitPresheafRestrictionUnboundedComparison (f : C' ⥤ C) :
    (Stacks.CategoryHomology.presheafRestriction.{u, u, u} f).mapDerivedCategory ⋙
        totalDerivedColimit C' AddCommGrpCat.{u} ⟶
      totalDerivedColimit C AddCommGrpCat.{u} :=
  unboundedComparison f AddCommGrpCat.{u}

end AbelianValued

namespace ModuleValued

variable {C C' : Type u} [SmallCategory C] [SmallCategory C'] {B : Type u} [Ring B]

/-- **The comparison `Lπ'_! ∘ g^{-1} ⟶ Lπ_!` as a morphism of functors `D(C, B̲) ⥤ D(B)`**, on the
unbounded derived category of diagrams of `B`-modules on `C`. This is
`Stacks.ChaoticSite.unboundedComparison` at module coefficients, stated at the spelling of
`Stacks.ChaoticSite.inverseImageAlongAFunctor`. -/
def derivedColimitInverseImageUnboundedComparison (f : C' ⥤ C) :
    (inverseImageAlongAFunctor C C' f B).mapDerivedCategory ⋙
        totalDerivedColimit C' (ModuleCat.{u} B) ⟶
      totalDerivedColimit C (ModuleCat.{u} B) :=
  unboundedComparison f (ModuleCat.{u} B)

end ModuleValued

end Stacks.ChaoticSite

end
