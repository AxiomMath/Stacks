module

public import Mathlib.CategoryTheory.Category.ULift
public import StacksFrontier.AlgebraicTopology.SimplicialObject.CopowerHomotopy
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.RepresentableAcyclicity
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitAlongAnEquivalence
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitByPointResolutionAbelian
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitOfComplexesByPointResolution
import StacksCore.Tactic.StacksAttribute

/-!
# The criterion of Tag 08Q9 at a site that is not small

Let `C` be a category with the chaotic topology whose objects and whose morphisms need not live
in the same universe -- the site `C_{B/A}` of [Stacks, Tag 08PR] is such a category, its objects
living one universe above its morphisms -- and let `U_•` be a cosimplicial object of `C` which is
a point resolution. The criterion of [Stacks, Tag 08Q9] computes `Lπ_!` from such a `U_•`, but it
is stated for a *small* site: it is proved through the projective generators of the category of
abelian presheaves, which are the free abelian presheaves on the representables, and those have
their values in the universe of the morphisms of `C`. This file removes the smallness hypothesis.

Nothing of the criterion is reproved. `C` is equivalent to the genuinely small category
`CategoryTheory.AsSmall C`, whose objects and morphisms both live in `max u v`, the criterion
applies there, and the conclusion is carried back along the equivalence by
`Stacks.ChaoticSite.totalDerivedColimitEquivalenceIso`. The coefficients are correspondingly read
at `max u v`, the smallest universe in which a category whose objects live in `u` and whose
morphisms live in `v` has colimits of abelian groups.

## Main results

* `Stacks.ChaoticSite.isPointResolution_asSmall`: the point-resolution hypothesis transfers to
  the small model. The hypothesis speaks only of the simplicial sets of morphisms, and the
  morphisms of `AsSmall C` are the universe lifts of those of `C`.
* `Stacks.ChaoticSite.AbelianValued.mooreCochainNatIsoDerivedColimitOfLarge`: **the derived form
  of [Stacks, Tag 08Q9] at abelian coefficients, with no smallness hypothesis on the site** --
  `Q(ℱ(U_•)) ≅ Lπ_!(ℱ)` in `D(Ab)`, naturally in the abelian presheaf `ℱ`.
* `Stacks.ChaoticSite.ModuleValued.mooreCochainNatIsoDerivedColimitOfLarge`: the same at linear
  coefficients, in `D(B)`, naturally in the diagram of `B`-modules `ℱ`.
* `Stacks.ChaoticSite.AbelianValued.isIso_totalDerivedColimit_single_map_iff_of_large`: the
  criterion read on a single morphism -- `Lπ_!` inverts a map of abelian presheaves placed in
  cohomological degree zero exactly when that map becomes a quasi-isomorphism on the extended
  Moore complexes of its evaluation on `U_•`. This is
  `Stacks.ChaoticSite.AbelianValued.isIso_totalDerivedColimit_single_map_iff` with the smallness
  hypothesis removed.

## Implementation notes

**Where the smallness went.** Two hypotheses of the criterion survive, as instance arguments
rather than as a smallness assumption on `C`: that the category of abelian presheaves, resp. of
diagrams of `B`-modules, on `C` has enough projectives, and that `C` has colimits of the
coefficients. For a small site both are instances; for a large one the first has to be supplied,
and `Stacks.CategoryHomology.diagramsEnoughProjectives'` supplies it from the coproducts of the
free diagrams on the objects, which exist as soon as the coefficient universe is at least that of
the objects and of the morphisms.

**Why `AsSmall` and not the footnote.** A large site can also be cut down to an equivalent small
*full subcategory*, which is what the footnote to the source's section does for `C_{B/A}`. That is
not what happens here: `CategoryTheory.AsSmall.equiv` is an equivalence of categories, so the two
categories of abelian presheaves are equivalent and the two `Lπ_!` agree; restricting to a full
subcategory changes both, and a statement proved there is a statement about different
coefficients.

**The Moore complex needs no comparison.** Restriction of coefficients along the equivalence
composed with the Moore complex of `U_•` *is* the Moore complex of `U_• ⋙ e`, by definition: both
evaluate the presheaf on the same cosimplicial object, the opposite of a composite of functors
being the composite of their opposites. So only the right-hand side of the criterion has to be
transported.

## References

* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Stacks.ChaoticSite

attribute [local instance] HasDerivedCategory.standard

/-! ### The point-resolution hypothesis at the small model -/

/-- Lifting the universe of the sections carries the constant simplicial set on a singleton to
the constant simplicial set on a singleton. -/
def uliftConstPUnitIso.{v₁, u₁} :
    ((SimplicialObject.whiskering (Type v₁) (Type (max v₁ u₁))).obj
        uliftFunctor.{max v₁ u₁, v₁}).obj
        ((Functor.const SimplexCategoryᵒᵖ).obj PUnit.{v₁ + 1}) ≅
      (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{max v₁ u₁ + 1} :=
  NatIso.ofComponents (fun _ => Equiv.toIso ⟨fun _ => PUnit.unit, fun _ => ⟨PUnit.unit⟩,
    fun _ => rfl, fun _ => rfl⟩) (by intro _ _ _; rfl)

variable (C : Type u) [Category.{v} C]

/-- **The simplicial set of morphisms out of a cosimplicial object is unchanged, up to a universe
lift, by passing to the small model.** The morphisms of `CategoryTheory.AsSmall C` are by
definition the universe lifts of those of `C`, so the comparison is an equality of functors. -/
def asSmallYonedaIso (U : CosimplicialObject C) (W : AsSmall.{v, v, u} C) :
    (U ⋙ AsSmall.up.{v, u, v}).op ⋙ yoneda.obj W ≅
      ((SimplicialObject.whiskering (Type v) (Type (max v u))).obj
        uliftFunctor.{max v u, v}).obj (U.op ⋙ yoneda.obj (AsSmall.down.obj W)) :=
  Iso.refl _

/-- **The point-resolution hypothesis of [Stacks, Tag 08Q9] holds at the small model of a
category as soon as it holds at the category.** The condition is that each simplicial set
`Mor_C(U_•, W)` be homotopy equivalent to a singleton; passing to `CategoryTheory.AsSmall C`
replaces those simplicial sets by their universe lifts, and a functor carries a homotopy
equivalence of simplicial objects to one
(`CategoryTheory.SimplicialObject.homotopyEquivalences_whiskering_map`). -/
theorem isPointResolution_asSmall {U : CosimplicialObject C} (hU : IsPointResolution U) :
    IsPointResolution (U ⋙ AsSmall.up.{v, u, v}) := by
  intro W
  obtain ⟨f, hf⟩ := hU (AsSmall.down.obj W)
  exact ⟨(asSmallYonedaIso C U W).hom ≫
    ((SimplicialObject.whiskering (Type v) (Type (max v u))).obj
      uliftFunctor.{max v u, v}).map f ≫ uliftConstPUnitIso.{v, u}.hom,
    SimplicialObject.homotopyEquivalences_iso_comp_iso _ _ _
      (SimplicialObject.homotopyEquivalences_whiskering_map uliftFunctor.{max v u, v} hf)⟩

end Stacks.ChaoticSite

namespace Stacks.ChaoticSite.AbelianValued

attribute [local instance] HasDerivedCategory.standard

open Stacks.CategoryHomology

variable {C : Type u} [Category.{v} C]
  [EnoughProjectives (Cᵒᵖ ⥤ AddCommGrpCat.{max v u})]
  (U : CosimplicialObject C)

/-- **The derived form of [Stacks, Tag 08Q9] at abelian coefficients, for a site that need not be
small.** Let `U_•` be a cosimplicial object of `C` which is a point resolution. Then

`Q(ℱ(U_•)) ≅ Lπ_!(ℱ)` in `D(Ab)`,

**naturally in the abelian presheaf `ℱ`**, where the left side is the extended Moore complex of
the simplicial abelian group `ℱ(U_•)` and `Lπ_!` is the total left derived functor of the colimit
over `Cᵒᵖ`, which is `π_!` on the chaotic site by [Stacks, Tag 08PF].

The objects of `C` and its morphisms may live in different universes; the coefficients are read
at `max v u`, the smallest universe in which `Cᵒᵖ` has colimits of abelian groups. The form
`Stacks.ChaoticSite.AbelianValued.mooreCochainNatIsoDerivedColimit` asks for a small site, and so
does not apply to the site of [Stacks, Tag 08PR]. -/
@[stacks 08Q9 "derived-category form at abelian coefficients, natural in the coefficient \
  presheaf, with the smallness hypothesis on the site removed: the site's objects and its \
  morphisms may live in different universes, the coefficients being read at their maximum. The \
  lemma `Stacks.ChaoticSite.AbelianValued.mooreCochainNatIsoDerivedColimit` is this statement \
  for a small site"]
def mooreCochainNatIsoDerivedColimitOfLarge (hU : IsPointResolution U) :
    GeneralValued.mooreCochainComplex' U AddCommGrpCat.{max v u} ⋙ DerivedCategory.Q ≅
      HomologicalComplex.single (Cᵒᵖ ⥤ AddCommGrpCat.{max v u}) (ComplexShape.up ℤ) 0 ⋙
        DerivedCategory.Q ⋙ totalDerivedColimit' C AddCommGrpCat.{max v u} :=
  cancelLeftNatIsoOfEquivalence
    (presheafEquivalenceOfEquivalence AsSmall.equiv.{v, u, v} AddCommGrpCat.{max v u}) _ _
    (mooreCochainNatIsoDerivedColimit (U ⋙ AsSmall.up.{v, u, v})
        (isPointResolution_asSmall C hU) ≪≫
      Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
        (totalDerivedColimitIsoTotalDerivedColimit' _
          AddCommGrpCat.{max v u})) ≪≫
      derivedColimitSingleEquivalenceIso AsSmall.equiv.{v, u, v} AddCommGrpCat.{max v u})

/-- **`Lπ_!` inverts a map of abelian presheaves placed in cohomological degree zero exactly when
that map becomes a quasi-isomorphism on the extended Moore complexes of its evaluation on a point
resolution**, with no smallness hypothesis on the site.

This is the criterion of [Stacks, Tag 08Q9] read on a single morphism, one application of
`CategoryTheory.NatIso.isIso_map_iff` away from
`Stacks.ChaoticSite.AbelianValued.mooreCochainNatIsoDerivedColimitOfLarge`: a natural isomorphism
of functors makes the invertibility of the two images of a morphism equivalent, and
`DerivedCategory.isIso_Q_map_iff_quasiIso` turns invertibility in the derived category into the
quasi-isomorphism of complexes. The lemma
`Stacks.ChaoticSite.AbelianValued.isIso_totalDerivedColimit_single_map_iff` is this statement for
a small site. -/
theorem isIso_totalDerivedColimit_single_map_iff_of_large (hU : IsPointResolution U)
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{max v u}} (a : F ⟶ G) :
    IsIso ((totalDerivedColimit' C AddCommGrpCat.{max v u}).map (DerivedCategory.Q.map
        ((HomologicalComplex.single (Cᵒᵖ ⥤ AddCommGrpCat.{max v u})
          (ComplexShape.up ℤ) 0).map a))) ↔
      QuasiIso ((GeneralValued.mooreCochainComplex' U AddCommGrpCat.{max v u}).map a) := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact (NatIso.isIso_map_iff (mooreCochainNatIsoDerivedColimitOfLarge U hU) a).symm

end Stacks.ChaoticSite.AbelianValued

namespace Stacks.ChaoticSite.ModuleValued

attribute [local instance] HasDerivedCategory.standard

open Stacks.CategoryHomology

variable {C : Type u} [Category.{v} C] {B : Type max v u} [Ring B]
  [EnoughProjectives (Cᵒᵖ ⥤ ModuleCat.{max v u} B)]
  (U : CosimplicialObject C)

/-- **The derived form of [Stacks, Tag 08Q9] at linear coefficients, for a site that need not be
small.** Let `U_•` be a cosimplicial object of `C` which is a point resolution and let `B` be a
ring. Then

`Q(ℱ(U_•)) ≅ Lπ_!(ℱ)` in `D(B)`,

**naturally in the diagram of `B`-modules `ℱ`** -- equivalently, in the `B̲`-module `ℱ`, the
topology being chaotic. This is the module half beside
`Stacks.ChaoticSite.AbelianValued.mooreCochainNatIsoDerivedColimitOfLarge`, and as there the
objects of `C` and its morphisms may live in different universes. -/
@[stacks 08Q9 "derived-category form at module coefficients, natural in the coefficient module, \
  with the smallness hypothesis on the site removed. The lemma \
  `Stacks.ChaoticSite.ModuleValued.mooreCochainNatIsoDerivedColimit` is this statement for a \
  small site"]
def mooreCochainNatIsoDerivedColimitOfLarge (hU : IsPointResolution U) :
    GeneralValued.mooreCochainComplex' U (ModuleCat.{max v u} B) ⋙ DerivedCategory.Q ≅
      HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{max v u} B) (ComplexShape.up ℤ) 0 ⋙
        DerivedCategory.Q ⋙ totalDerivedColimit' C (ModuleCat.{max v u} B) :=
  cancelLeftNatIsoOfEquivalence
    (presheafEquivalenceOfEquivalence AsSmall.equiv.{v, u, v} (ModuleCat.{max v u} B)) _ _
    (mooreCochainNatIsoDerivedColimit (B := B) (U ⋙ AsSmall.up.{v, u, v})
        (isPointResolution_asSmall C hU) ≪≫
      Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
        (totalDerivedColimitIsoTotalDerivedColimit' _
          (ModuleCat.{max v u} B))) ≪≫
      derivedColimitSingleEquivalenceIso AsSmall.equiv.{v, u, v} (ModuleCat.{max v u} B))

end Stacks.ChaoticSite.ModuleValued

end
