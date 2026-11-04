module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitUnboundedDevissage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitUnboundedPinning
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.PointResolutionVanishing
public import StacksFrontier.Homology.Perfect.Characterizing
import StacksCore.Tactic.StacksAttribute

/-!
# Derived colimits and restriction along a functor on the unbounded derived category

Let `f : C' ⥤ C` be a functor between small categories with their chaotic topologies, let `g^{-1}`
be restriction of diagrams along `f`, and let `U_•` be a cosimplicial object of `C'` such that both
`U_•` and `f(U_•)` are point resolutions — the hypothesis of [Stacks, Tag 08QA]. Then the
comparison `Lπ'_! ∘ g^{-1} ⟶ Lπ_!` of `Stacks.ChaoticSite.unboundedComparison` is an isomorphism on
the **unbounded** derived category `D(Cᵒᵖ ⥤ D)`, for coefficients `D` which are Grothendieck
abelian relative to the universe of `C` and `C'` and carry a separating family of projective
compact objects. For module coefficients `D = ModuleCat B` that family is the regular module.

## Main results

* `Stacks.ChaoticSite.isIso_unboundedComparison_app_single_freeYoneda`: the comparison is
  invertible at a free diagram placed in degree zero.
* `Stacks.ChaoticSite.isIso_unboundedComparison_of_isPointResolutions` and
  `Stacks.ChaoticSite.unboundedComparisonNatIsoOfIsPointResolutions`: the comparison is invertible
  everywhere, and the resulting identification `Lπ'_! ∘ g^{-1} ≅ Lπ_!`.
* `Stacks.ChaoticSite.ModuleValued.isIso_derivedColimitInverseImageUnboundedComparison` and
  `Stacks.ChaoticSite.ModuleValued.derivedColimitInverseImageUnboundedNatIso`: the same at
  module coefficients, as functors `D(C, B̲) ⥤ D(B)`.

## Implementation notes

`Stacks.ChaoticSite.isIso_unboundedComparison_of_isIso_app_freeYoneda` reduces the statement to the
free diagrams `CategoryTheory.Presheaf.freeYoneda X (S i)` placed in degree zero, and
`Stacks.ChaoticSite.unboundedComparison_app_comp_counit` pins the comparison there: its right-hand
side is a composite of three morphisms, each invertible at such a diagram.

* The comparison of `Lπ'_!` with `π'_!` at the restricted generator, and the comparison of `Lπ_!`
  with `π_!` at the generator, are invertible by
  `Stacks.ChaoticSite.isIso_totalDerivedColimitCounit_single_of_projective_restrict`, read for `C'`
  and for `C`. Both of its projectivity hypotheses are the single statement
  `Stacks.ChaoticSite.projective_restrict_freeYoneda` at the point resolution `U ⋙ f` of `C`:
  `(U ⋙ f).op ⋙ E` is `U.op ⋙ (f.op ⋙ E)`, so the same term discharges the hypothesis about the
  restricted generator.
* The underived comparison is invertible by
  `Stacks.ChaoticSite.isIso_diagramColimitRestrictionPre`, hence so is its degreewise action on
  complexes and the image of that under the two localizations.
* The remaining factor is the degreewise comparison
  `CategoryTheory.Functor.mapDerivedCategoryFactorsh` of `g^{-1}`, a component of an isomorphism.

`CategoryTheory.EnoughProjectives D` and `CategoryTheory.Limits.HasCoproducts D` are not
assumed: the first follows from the separating family of projective objects by
`CategoryTheory.Limits.enoughProjectives_of_isSeparating_projective`, the second from the
coefficients being Grothendieck abelian.

The three invertibility facts entering the composite are passed to
`CategoryTheory.IsIso.comp_isIso'` **by name**. Instance search does not find the one about the
degreewise action of the underived comparison: the object it is stated at is
`(HomotopyCategory.quotient _ _).obj ((single 0).obj E)` in the hypothesis and the projection
`(…).as` of that object in the goal, and the two agree only after unfolding
`CategoryTheory.Quotient.functor`, which instance search does not do.

## References

* [Stacks Project, Tag 08QA](https://stacks.math.columbia.edu/tag/08QA)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CategoryHomology

namespace Stacks.ChaoticSite

universe uD u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {C C' : Type u} [SmallCategory C] [SmallCategory C'] (f : C' ⥤ C)
  (D : Type uD) [Category.{u} D] [Abelian D] [IsGrothendieckAbelian.{u} D]
  [HasProductsOfShape ℕ D] [HasExactLimitsOfShape (Discrete ℕ) D]
  [HasColimitsOfShape ℕ D] [HasExactColimitsOfShape ℕ D]
  [EnoughProjectives (Cᵒᵖ ⥤ D)] [EnoughProjectives (C'ᵒᵖ ⥤ D)]
  [HasColimitsOfShape Cᵒᵖ D] [HasColimitsOfShape C'ᵒᵖ D]

omit [HasProductsOfShape ℕ D] [HasExactLimitsOfShape (Discrete ℕ) D] in
/-- The comparison is invertible at a free diagram placed in degree zero. -/
theorem isIso_unboundedComparison_app_single_freeYoneda
    {U : CosimplicialObject C'} (hU : IsPointResolution U) (hfU : IsPointResolution (U ⋙ f))
    [HasCoproducts.{u} D] [EnoughProjectives D] (W : C) (P : D) [Projective P] :
    IsIso ((unboundedComparison f D).app
      ((DerivedCategory.singleFunctor (Cᵒᵖ ⥤ D) 0).obj (Presheaf.freeYoneda W P))) := by
  set X := (HomotopyCategory.quotient (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)).obj
    ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).obj (Presheaf.freeYoneda W P))
  have hε : IsIso ((totalDerivedColimitCounit C D).app X) :=
    isIso_totalDerivedColimitCounit_single_of_projective_restrict D hfU
      (Presheaf.freeYoneda W P) (projective_restrict_freeYoneda hfU W P)
  have hε'0 : IsIso ((totalDerivedColimitCounit C' D).app
      ((HomotopyCategory.quotient (C'ᵒᵖ ⥤ D) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (C'ᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).obj
          (((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).obj
            (Presheaf.freeYoneda W P))))) :=
    isIso_totalDerivedColimitCounit_single_of_projective_restrict D hU
      (((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).obj (Presheaf.freeYoneda W P))
      (projective_restrict_freeYoneda hfU W P)
  have hε' : IsIso ((totalDerivedColimitCounit C' D).app
      ((((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj X)) :=
    (Stacks.DerivedCategoryComparisons.isIso_app_isClosedUnderIsomorphisms
        (totalDerivedColimitCounit C' D)).of_iso
      ((HomotopyCategory.quotient (C'ᵒᵖ ⥤ D) (ComplexShape.up ℤ)).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex
            ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op) (ComplexShape.up ℤ) 0).app
          (Presheaf.freeYoneda W P)).symm) hε'0
  have : IsIso (Stacks.CategoryHomology.diagramColimitRestrictionPre f D) :=
    isIso_diagramColimitRestrictionPre f D hU hfU
  have : IsIso ((NatTrans.mapHomologicalComplex
      (Stacks.CategoryHomology.diagramColimitRestrictionPre f D) (ComplexShape.up ℤ)).app X.as) :=
    inferInstanceAs (IsIso ((NatIso.mapHomologicalComplex
      (asIso (Stacks.CategoryHomology.diagramColimitRestrictionPre f D))
      (ComplexShape.up ℤ)).hom.app _))
  have : IsIso ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (Stacks.CategoryHomology.diagramColimitRestrictionPre f D)
        (ComplexShape.up ℤ)).app X.as)) :=
    Functor.map_isIso _ _
  have hQ : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (Stacks.CategoryHomology.diagramColimitRestrictionPre f D)
        (ComplexShape.up ℤ)).app X.as))) :=
    Functor.map_isIso _ _
  have hmapphi : IsIso ((totalDerivedColimit C' D).map
      (((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategoryFactorsh.hom.app X)) :=
    Functor.map_isIso _ _
  have hcomp : IsIso ((unboundedComparison f D).app (DerivedCategory.Qh.obj X) ≫
      (totalDerivedColimitCounit C D).app X) := by
    rw [unboundedComparison_app_comp_counit f D]
    exact IsIso.comp_isIso' hmapphi (IsIso.comp_isIso' hε' hQ)
  have hτ : IsIso ((unboundedComparison f D).app (DerivedCategory.Qh.obj X)) :=
    IsIso.of_isIso_comp_right _ ((totalDerivedColimitCounit C D).app X)
  exact (Stacks.DerivedCategoryComparisons.isIso_app_isClosedUnderIsomorphisms
      (unboundedComparison f D)).of_iso
    ((DerivedCategory.singleFunctorIsoCompQh (Cᵒᵖ ⥤ D) 0).app
      (Presheaf.freeYoneda W P)).symm hτ

/-- For a functor `f : C' ⥤ C` between small categories with their chaotic topologies and a
cosimplicial object `U_•` of `C'` such that both `U_•` and `f(U_•)` are point resolutions, the
comparison `Lπ'_! ∘ g^{-1} ⟶ Lπ_!` is an isomorphism on the unbounded derived category, for
coefficients `D` with a separating family `S` of projective compact objects. -/
theorem isIso_unboundedComparison_of_isPointResolutions
    {U : CosimplicialObject C'} (hU : IsPointResolution U) (hfU : IsPointResolution (U ⋙ f))
    {ι : Type u} (S : ι → D) [∀ i, Projective (S i)]
    (hcompact : ∀ i, IsCompactObject.{u} (S i))
    (hS : (ObjectProperty.ofObj S).IsSeparating) :
    IsIso (unboundedComparison f D) := by
  have : HasCoproducts.{u} D := fun K ↦ inferInstance
  have : EnoughProjectives D :=
    CategoryTheory.Limits.enoughProjectives_of_isSeparating_projective S hS
  exact isIso_unboundedComparison_of_isIso_app_freeYoneda f D S hcompact hS fun W i ↦
    isIso_unboundedComparison_app_single_freeYoneda f D hU hfU W (S i)

/-- The isomorphism `Lπ'_! ∘ g^{-1} ≅ Lπ_!` on the unbounded derived category given by the
comparison `Stacks.ChaoticSite.unboundedComparison`, when `U_•` and `f(U_•)` are point
resolutions. -/
def unboundedComparisonNatIsoOfIsPointResolutions
    {U : CosimplicialObject C'} (hU : IsPointResolution U) (hfU : IsPointResolution (U ⋙ f))
    {ι : Type u} (S : ι → D) [∀ i, Projective (S i)]
    (hcompact : ∀ i, IsCompactObject.{u} (S i))
    (hS : (ObjectProperty.ofObj S).IsSeparating) :
    ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategory ⋙
        totalDerivedColimit C' D ≅
      totalDerivedColimit C D :=
  haveI := isIso_unboundedComparison_of_isPointResolutions f D hU hfU S hcompact hS
  asIso (unboundedComparison f D)

/-! ### Module coefficients -/

section ModuleCoefficients

variable {B : Type u} [Ring B]

/-- The regular module `B` is a separating object of `ModuleCat B`. -/
lemma isSeparating_regularModule :
    (ObjectProperty.ofObj (fun _ : PUnit.{u + 1} ↦ ModuleCat.of B B)).IsSeparating := by
  intro X Y a b h
  ext x
  have hx := h (ModuleCat.of B B) ⟨PUnit.unit⟩
    (ModuleCat.ofHom (LinearMap.toSpanSingleton B X x))
  simpa using congrArg (fun (g : ModuleCat.of B B ⟶ Y) ↦ g.hom (1 : B)) hx

/-- For a functor `f : C' ⥤ C` between small categories with their chaotic topologies and a
cosimplicial object `U_•` of `C'` such that both `U_•` and `f(U_•)` are point resolutions, the
comparison `Lπ'_! ∘ g^{-1} ⟶ Lπ_!` of
`Stacks.ChaoticSite.ModuleValued.derivedColimitInverseImageUnboundedComparison` is an
isomorphism of functors `D(C, B̲) ⥤ D(B)` on the unbounded derived category. -/
@[stacks 08QA "the identification `Lπ'_! ∘ g^{-1} = Lπ_!` with values in `D(B)`, at module \
  coefficients, as an isomorphism of functors on the UNBOUNDED derived category `D(C, B̲)`, \
  which is what the source's `resp. D(C, B̲) ⥤ D(B)` says. The other half of the source's \
  `resp.`, the unbounded statement with values in `D(Ab)`, is \
  `Stacks.ChaoticSite.AbelianValued.isIso_derivedColimitPresheafRestrictionUnboundedComparison` \
  in `DerivedColimitUnboundedIsIsoAbelian.lean`: the same mechanism at `AddCommGrpCat`, whose \
  separating family of projective compact objects is `ULift ℤ`."]
theorem ModuleValued.isIso_derivedColimitInverseImageUnboundedComparison
    {U : CosimplicialObject C'} (hU : IsPointResolution U) (hfU : IsPointResolution (U ⋙ f)) :
    IsIso (ModuleValued.derivedColimitInverseImageUnboundedComparison (B := B) f) :=
  isIso_unboundedComparison_of_isPointResolutions f (ModuleCat.{u} B) hU hfU
    (fun _ : PUnit.{u + 1} ↦ ModuleCat.of B B)
    (fun _ ↦ StacksDraft.Perfect.isCompactObject_regularModule) isSeparating_regularModule

/-- The isomorphism of functors `Lπ'_! ∘ g^{-1} ≅ Lπ_!` from `D(C, B̲)` to `D(B)` on the
unbounded derived category, when `U_•` and `f(U_•)` are point resolutions. -/
@[stacks 08QA "the identification `Lπ'_! ∘ g^{-1} = Lπ_!` with values in `D(B)` as an \
  ISOMORPHISM OF FUNCTORS on the unbounded derived category `D(C, B̲)`, packaged from the \
  invertibility of the comparison"]
def ModuleValued.derivedColimitInverseImageUnboundedNatIso
    {U : CosimplicialObject C'} (hU : IsPointResolution U) (hfU : IsPointResolution (U ⋙ f)) :
    (inverseImageAlongAFunctor C C' f B).mapDerivedCategory ⋙
        totalDerivedColimit C' (ModuleCat.{u} B) ≅
      totalDerivedColimit C (ModuleCat.{u} B) :=
  haveI := ModuleValued.isIso_derivedColimitInverseImageUnboundedComparison (B := B) f hU hfU
  asIso (ModuleValued.derivedColimitInverseImageUnboundedComparison (B := B) f)

end ModuleCoefficients

end Stacks.ChaoticSite

end
