module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.DerivedColimitPreservesColimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitUnboundedFunctoriality
public import StacksFrontier.Homology.Devissage.CompactGenerationOfDiagramsAnyModel

/-!
# The unbounded comparison is an isomorphism as soon as it is one on the free diagrams

Let `f : C' ⥤ C` be a functor between small categories with their chaotic topologies and let the
coefficients `D` be an abelian category, with its morphisms in the universe `u` of the objects and
morphisms of `C` and `C'`, which is Grothendieck abelian relative to `u`, has countable products
and has those products exact, and carries a separating family `S` of projective compact objects.
Then the comparison `Lπ'_! ∘ g^{-1} ⟶ Lπ_!` of
`Stacks.ChaoticSite.unboundedComparison`, on the **unbounded** derived category `D(Cᵒᵖ ⥤ D)`, is an
isomorphism as soon as it is invertible on each free diagram
`CategoryTheory.Presheaf.freeYoneda X (S i)` placed in degree zero.

This is the dévissage of `StacksDraft.CompactDevissage.isIso_of_isIso_app_freeYoneda_anyModel` run
on the comparison, and it reduces [Stacks, Tag 08QA] on the unbounded derived category to a single
statement at the generators. Of the four inputs the dévissage needs, three were already available —
compatibility with the shift (`Stacks.ChaoticSite.commShift_unboundedComparison`),
triangulatedness and direct sums for `Lπ_!`
(`Stacks.CategoryHomology.totalDerivedColimit_isTriangulated`,
`Stacks.CategoryHomology.totalDerivedColimit_preservesColimitsOfSize`) — and the fourth is proved
here: the degreewise derived functor of restriction along `f` preserves direct sums.

## Main results

* `Stacks.ChaoticSite.preservesColimitsOfShape_discrete_restrictionMapDerivedCategory`:
  `g^{-1}` on the unbounded derived category preserves `J`-indexed direct sums.
* `Stacks.ChaoticSite.isIso_unboundedComparison_of_isIso_app_freeYoneda`: the reduction above.

## [Stacks, Tag 08QA] on the unbounded derived category is now proved

Nothing is open here any more. The hypothesis of the reduction is discharged in
`StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitUnboundedIsIso`, and the
conclusion is `Stacks.ChaoticSite.isIso_unboundedComparison_of_isPointResolutions`, with the
source's module coefficients spelled out as
`Stacks.ChaoticSite.ModuleValued.isIso_derivedColimitInverseImageUnboundedComparison`. The handle
on the hypothesis is `Stacks.ChaoticSite.unit_comp_unboundedComparison_comp_counit`, which computes
the transpose of the comparison composed with the derived-functor comparison; at a projective
diagram in degree zero the latter is invertible
(`Stacks.CategoryHomology.totalDerivedColimitObjSingleIso`), so the transpose computation pins the
comparison there. Since the transpose is a bijection, that hypothesis is equivalent to the
conjunction of

* **(i)** `L_nπ'_!(g^{-1}E) = 0` for `n > 0`, equivalently the invertibility of
  `Stacks.CategoryHomology.totalDerivedColimitCounit` for `C'` at `g^{-1}E` placed in degree zero;
* **(ii)** the invertibility of the underived comparison `colimit.pre E f.op`,

and of the identification of the pinned map with (ii), which is
`Stacks.ChaoticSite.unboundedComparison_app_comp_counit`.

**(ii) is proved**, for every diagram and at arbitrary coefficients, under the source's own
hypothesis of a cosimplicial object `U_•` of `C'` with `U_•` and `f(U_•)` point resolutions:
`Stacks.ChaoticSite.isIso_colimitPre_op_of_isPointResolutions`, packaged as the isomorphism of
functors `Stacks.ChaoticSite.diagramColimitRestrictionPreNatIso`. It rests on
`Stacks.ChaoticSite.final_op_of_isPointResolution`: a point resolution is an initial functor
`SimplexCategory ⥤ C'`, so both colimits are the colimit over `SimplexCategoryᵒᵖ` of the diagram
read on `f(U_•)` and the comparison is a factor of `CategoryTheory.Limits.colimit.pre_pre`.

**(i) is not a projectivity statement about `g^{-1}E`**: restriction along `f` does
*not* carry projective diagrams to projective diagrams, not even under the source's hypothesis. For
`C' = SimplexCategoryᵒᵖ`, `C` the terminal category and `U = ` the constant cosimplicial object at
`⦋0⦌` — a point resolution, every `Mor_{C'}(U_•, W) = Mor_{SimplexCategory}(W, ⦋0⦌)` being a
singleton on the nose — the restriction of a free diagram is the *constant cosimplicial object* on
a projective object `P` of `D`, whose projectivity is, through the adjunction
`const ⊣ lim`, the exactness of `lim` over `SimplexCategory`, which is a kernel of two cofaces and
is only left exact. So (i) has to be proved where the vanishing is visible, namely after
restricting along `U.op` to the simplicial diagrams `SimplexCategoryᵒᵖ ⥤ D`. The two projectivity
inputs it needs are proved in `StacksDraft.CategoryTheory.Sites.Cohomology.ChaoticSite`
`.PointResolutionProjectivity`:

* `Stacks.ChaoticSite.projective_restrict_freeYoneda`:
  `Projective (U.op ⋙ CategoryTheory.Presheaf.freeYoneda W P)` in `SimplexCategoryᵒᵖ ⥤ D` — the
  restriction of a free diagram along a point resolution is a simplicial object with projective
  terms homotopy equivalent to a constant one, hence projective by Dold–Kan
  (`CategoryTheory.SimplicialObject.projective_of_homotopyEquivalence_const`). Read at `U ⋙ f` in
  `C` it is the statement about `(U ⋙ f).op ⋙ Presheaf.freeYoneda X P`.
* `Stacks.ChaoticSite.preservesProjectiveObjects_restrictAlongPointResolution`: restriction along
  `U.op` preserves *all* projectives, a projective diagram being a retract of a coproduct of free
  diagrams (`Stacks.ChaoticSite.epi_freeYonedaPresentation`). The equivalent statement about the
  right adjoint, that `Ran_{U.op}` preserves epimorphisms, is
  `Stacks.ChaoticSite.preservesEpimorphisms_rightAdjoint_restrictAlongPointResolution`; it takes
  the right adjoint as *data*, so no limits in `D` are assumed in order to state it.

The transfer of `Stacks.CategoryHomology.totalDerivedColimit` along that restriction is then
`Stacks.ChaoticSite.isIso_totalDerivedColimitCounit_single_of_projective_restrict` (in
`StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.PointResolutionVanishing`), and **(i) is
proved**: for any diagram `Z` whose restriction `U.op ⋙ Z` along the point resolution is
projective, the left-derived comparison of `colim_{Cᵒᵖ}` is invertible at `Z` placed in degree
zero, i.e. `L_nπ_!(Z) = 0` for `n > 0`. Read for `C'`, at `Z = g^{-1}E` and with the projectivity
of `U.op ⋙ f.op ⋙ E = (U ⋙ f).op ⋙ E` supplied by the first item above at the point resolution
`U ⋙ f` of `C`, that is exactly (i). The proof takes a projective resolution of `Z` and moves the
comparison along it (`Stacks.Homology.isIso_leftDerivedCounit_app_of_isIso_map`): restriction along
`U.op` is exact and preserves projectives, so the resolution restricts to a K-projective complex,
`single 0 (U.op ⋙ Z)` is K-projective too, a quasi-isomorphism between K-projective complexes is a
homotopy equivalence, and `colim_{Cᵒᵖ} = colim_{Δᵒᵖ} ∘ (U.op ⋙ -)` by
`Stacks.ChaoticSite.final_op_of_isPointResolution`, packaged as
`Stacks.ChaoticSite.colimitPointResolutionPreNatIso`.

The coefficients' hypothesis `EnoughProjectives D` that (i) carries is not an extra assumption on
this reduction: it follows from the dévissage's own data by
`CategoryTheory.Limits.enoughProjectives_of_isSeparating_projective`, the family `S` being
separating and projective.

**The last identification is proved too**, in
`StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitUnboundedPinning`. The
pinned map of `Stacks.ChaoticSite.unit_comp_unboundedComparison_comp_counit` is identified with
`colimit.pre E f.op` read through the two counits: at a complex `K` of diagrams on `C` and with
`X = Q_h K`,

`τ_X ≫ ε_X = Lπ'_!(g^{-1}-factorisation) ≫ ε'_{g^{-1}X} ≫ Q_h(π_! comparison on complexes)`,

which is `Stacks.ChaoticSite.unboundedComparison_app_comp_counit`. Its underived input is
`CategoryTheory.Limits.colimit.ι_pre` in the shape
`Stacks.ChaoticSite.restrict_colimConstAdj_unit`, read degreewise and then on homotopy categories
by `Stacks.ChaoticSite.restrict_colimConstAdj_unit_mapHomotopyCategory`; the coherence between the
three comparison isomorphisms `CategoryTheory.Functor.mapDerivedCategoryFactorsh` of `g^{-1}`, of
`const_{Cᵒᵖ}` and of `const_{C'ᵒᵖ}` and `Stacks.ChaoticSite.derivedConstRestrictionIso` is the
`Q_h` form of `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q`, which could
not be obtained from the `Q` form by `rfl` — `DerivedCategory.Q.obj K = DerivedCategory.Qh.obj
(Q(K))` does not typecheck, `HomologicalComplexUpToQuasiIso.Qh` carrying no `@[expose]` — and is
now `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Qh`, got by conjugating
the `Q` form by `DerivedCategory.quotientCompQhIso` in the shape
`CategoryTheory.Functor.mapDerivedCategoryFactorsh_hom_app` uses.

## Implementation notes

The direct sums are established by the route of
`Stacks.preservesColimitsOfShape_discrete_jStar_mapDerivedCategory`: restriction along `f.op` is
precomposition, so it preserves all colimits, hence so does its action on complexes; the
localization `DerivedCategory.Q` preserves direct sums when the source has enough injectives and
exact countable products ([Stacks, Tag 07D9]) and is essentially surjective, so the property
transfers from `Q ⋙ g^{-1}` to `g^{-1}` by
`_root_.preservesColimitsOfShape_discrete_of_essSurj_comp`.

## References

* [Stacks Project, Tag 08QA](https://stacks.math.columbia.edu/tag/08QA)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
* [Stacks Project, Tag 07D9](https://stacks.math.columbia.edu/tag/07D9)
* [Stacks Project, Tag 09SN](https://stacks.math.columbia.edu/tag/09SN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CategoryHomology

universe uD u

namespace Stacks.ChaoticSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {C C' : Type u} [SmallCategory C] [SmallCategory C'] (f : C' ⥤ C)
  (D : Type uD) [Category.{u} D] [Abelian D] [IsGrothendieckAbelian.{u} D]
  [HasProductsOfShape ℕ D] [HasExactLimitsOfShape (Discrete ℕ) D]
  [HasColimitsOfShape ℕ D] [HasExactColimitsOfShape ℕ D]
  [EnoughProjectives (Cᵒᵖ ⥤ D)] [EnoughProjectives (C'ᵒᵖ ⥤ D)]
  [HasColimitsOfShape Cᵒᵖ D] [HasColimitsOfShape C'ᵒᵖ D]

omit [HasColimitsOfShape ℕ D] [HasExactColimitsOfShape ℕ D] [EnoughProjectives (Cᵒᵖ ⥤ D)]
  [EnoughProjectives (C'ᵒᵖ ⥤ D)] [HasColimitsOfShape Cᵒᵖ D] [HasColimitsOfShape C'ᵒᵖ D] in
/-- **Restriction along a functor, on the unbounded derived category, preserves direct sums.**
Restriction is precomposition, so it preserves every colimit, and so does its degreewise action on
complexes; `DerivedCategory.Q` preserves direct sums and is essentially surjective, so the
property descends to `Functor.mapDerivedCategory`. -/
theorem preservesColimitsOfShape_discrete_restrictionMapDerivedCategory (J : Type u) :
    PreservesColimitsOfShape (Discrete J)
      ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategory := by
  let : HasCoproducts.{u} D := fun K ↦ inferInstance
  have hQ' : PreservesColimitsOfShape (Discrete J)
      (DerivedCategory.Q (C := C'ᵒᵖ ⥤ D)) :=
    _root_.derivedCategory_Q_preservesCoproductsOfShape_of_enoughInjectives
      (C'ᵒᵖ ⥤ D) J
  have hQ : PreservesColimitsOfShape (Discrete J) (DerivedCategory.Q (C := Cᵒᵖ ⥤ D)) :=
    _root_.derivedCategory_Q_preservesCoproductsOfShape_of_enoughInjectives
      (Cᵒᵖ ⥤ D) J
  have : HasColimitsOfShape (Discrete J) (DerivedCategory (Cᵒᵖ ⥤ D)) :=
    Stacks.Injectives.hasCoproducts_derivedCategory_diagrams C D J
  have : PreservesColimitsOfShape (Discrete J)
      (DerivedCategory.Q (C := Cᵒᵖ ⥤ D) ⋙
        ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategory) :=
    preservesColimitsOfShape_of_natIso
      ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategoryFactors.symm
  exact _root_.preservesColimitsOfShape_discrete_of_essSurj_comp
    (DerivedCategory.Q (C := Cᵒᵖ ⥤ D))
    ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategory J

/-- **[Stacks, Tag 08QA] on the unbounded derived category, reduced to the free diagrams.** The
comparison `Lπ'_! ∘ g^{-1} ⟶ Lπ_!` of `Stacks.ChaoticSite.unboundedComparison` is an isomorphism
of functors on all of `D(Cᵒᵖ ⥤ D)` as soon as it is invertible on each free diagram
`CategoryTheory.Presheaf.freeYoneda X (S i)` placed in degree zero. Those objects compactly
generate `D(Cᵒᵖ ⥤ D)`, the comparison is compatible with the shift, and both functors it compares
are exact and preserve direct sums; the dévissage of
`StacksDraft.CompactDevissage.isIso_of_isIso_app_freeYoneda_anyModel` then applies at
`CategoryTheory.HasDerivedCategory.standard`, which is the model the comparison is stated over. -/
theorem isIso_unboundedComparison_of_isIso_app_freeYoneda
    {ι : Type u} (S : ι → D) [∀ i, Projective (S i)]
    (hcomp : ∀ i, IsCompactObject.{u} (S i))
    (hS : (ObjectProperty.ofObj S).IsSeparating)
    (hτ : ∀ (X : C) (i : ι),
      IsIso ((unboundedComparison f D).app
        ((DerivedCategory.singleFunctor (Cᵒᵖ ⥤ D) 0).obj
          (Presheaf.freeYoneda X (S i))))) :
    IsIso (unboundedComparison f D) := by
  have : ∀ J : Type u, PreservesColimitsOfShape (Discrete J)
      ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategory := fun J ↦
    preservesColimitsOfShape_discrete_restrictionMapDerivedCategory f D J
  exact StacksDraft.CompactDevissage.isIso_of_isIso_app_freeYoneda_anyModel S hcomp hS
    (unboundedComparison f D) hτ

/-- The natural isomorphism `Lπ'_! ∘ g^{-1} ≅ Lπ_!` on the unbounded derived category produced by
the reduction. -/
def unboundedComparisonNatIsoOfIsIsoAppFreeYoneda
    {ι : Type u} (S : ι → D) [∀ i, Projective (S i)]
    (hcomp : ∀ i, IsCompactObject.{u} (S i))
    (hS : (ObjectProperty.ofObj S).IsSeparating)
    (hτ : ∀ (X : C) (i : ι),
      IsIso ((unboundedComparison f D).app
        ((DerivedCategory.singleFunctor (Cᵒᵖ ⥤ D) 0).obj
          (Presheaf.freeYoneda X (S i))))) :
    ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategory ⋙
        totalDerivedColimit C' D ≅
      totalDerivedColimit C D :=
  have := isIso_unboundedComparison_of_isIso_app_freeYoneda f D S hcomp hS hτ
  asIso (unboundedComparison f D)

end Stacks.ChaoticSite

end
