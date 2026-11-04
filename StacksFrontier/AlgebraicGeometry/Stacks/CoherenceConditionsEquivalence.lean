module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherenceConditionsCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherenceChartConditions
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.CartesianTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageChartSections
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionFunctorCovering
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FppfLocalLifts
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveFlatFppfLocalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSectionsFinite
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionChartIndependence
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationNoetherian
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationFromCoherence
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentModules
public import Mathlib.Tactic.TFAE

/-!
# The four conditions characterizing coherence on a locally Noetherian stack (Stacks 0GR5)

Let `𝒳` be a locally Noetherian algebraic stack and `ℱ` an `𝒪_𝒳`-module.  Stacks 0GR5 asserts
that the following are equivalent:

1. `ℱ` is a quasi-coherent, finite type `𝒪_𝒳`-module;
2. `ℱ` is an `𝒪_𝒳`-module of finite presentation;
3. `ℱ` is quasi-coherent and for every morphism `f : U ⟶ 𝒳` with `U` a locally Noetherian
   algebraic space the pullback `f^*ℱ|_{U_étale}` is coherent;
4. `ℱ` is quasi-coherent and there are an algebraic space `U` and a morphism `f : U ⟶ 𝒳` which
   is locally of finite type, flat and surjective such that `f^*ℱ|_{U_étale}` is coherent.

The four conditions are `AlgebraicGeometry.Stack.IsQuasicoherentFiniteTypeModule`,
`SheafOfModules.IsFinitePresentationOnSite`,
`AlgebraicGeometry.Stack.IsCoherentOnNoetherianSpaceCharts` and
`AlgebraicGeometry.Stack.IsCoherentOnSomeFlatSpaceChart`, and this file proves them equivalent.

## Main results

* `AlgebraicGeometry.Stack.isCoherentOnNoetherianSpaceCharts_of_isQuasicoherentFiniteTypeModule`:
  the implication (1) ⟹ (3).
* `AlgebraicGeometry.Stack.isFinitePresentationOnSite_of_isCoherentOnSomeFlatSpaceChart`: the
  implication (4) ⟹ (2).
* `AlgebraicGeometry.Stack.tfae_coherenceConditions`: **Stacks 0GR5**, the equivalence of the four
  conditions.
* `AlgebraicGeometry.Stack.isCoherent_tfae`: the coherence of Stacks 0GR6 is each of the four
  conditions.

## The proof

The implication (2) ⟹ (1) holds on any ringed site
(`AlgebraicGeometry.Stack.isQuasicoherentFiniteTypeModule_of_isFinitePresentationOnSite`) and
(3) ⟹ (4) is the chart of Stacks 04YF
(`AlgebraicGeometry.Stack.isCoherentOnSomeFlatSpaceChart_of_isCoherentOnNoetherianSpaceCharts`).
The two remaining implications both run through the cartesian property of a quasi-coherent
module, `AlgebraicGeometry.Stack.isCartesianBetweenAffines_of_isQuasicoherentOnSite` (Stacks 0H0E,
through Descent, Proposition 03DX): over objects of `𝒳` lying over affine schemes the sections of
`ℱ` are the base change of one another.

* (1) ⟹ (3).  The restriction `f^*ℱ|_{U_étale}` has, over an étale chart `W` of `U`, the sections
  of `ℱ` over the object `f(u_U W)` of `𝒳`, so it is cartesian on affine charts
  (`AlgebraicGeometry.Stack.isCartesianOnAffineCharts_spaceChartRestriction`), hence
  quasi-coherent by Descent, Proposition 03DX(2).  Finite type of `ℱ` in the fppf topology makes
  its sections over objects lying over affine schemes finite modules, by faithfully flat descent
  along a finite fppf covering by affine objects
  (`AlgebraicGeometry.Stack.moduleFinite_sections_of_isFiniteTypeOnSite_fibred`); so the sections
  of the restriction over the affine charts are finite, and on a locally Noetherian algebraic space
  a quasi-coherent module with finite sections over the affine charts is coherent (Stacks 07UB).
  This is the source's appeal to Modules on Sites, Lemma 03DO and Cohomology of Spaces, Lemma 07UB,
  with the passage from the fppf to the étale topology made explicit.
* (4) ⟹ (2).  The chart is locally of finite presentation by Stacks 0DQJ and `U` is locally
  Noetherian by Stacks 06R6.  Every object of `𝒳` is covered, in the fppf topology, by objects
  with a morphism to the image of an affine étale chart `A` of `U`: an fppf covering on which
  the object lifts to `U` (Stacks 06QA), an étale covering of the lift by objects mapping to étale
  charts (Stacks 073M), and the affine opens of those charts
  (`AlgebraicGeometry.Stack.affineChartSieve_mem`).  The sections of `ℱ` over the image of `A` are
  the sections of the coherent module `f^*ℱ|_{U_étale}` over `A`, a finite module over a
  Noetherian ring and so finitely presented; and a module cartesian between affine objects whose
  sections over an affine object are finitely presented has a finite global presentation on the
  slice at that object
  (`AlgebraicGeometry.Stack.hasFiniteGlobalPresentation_over_of_finitePresentation`), which
  restricts to every object mapping to it.  This is the source's proof, with the base change
  `h_{small}^*` of Stacks 0GQD replaced by the cartesian property of the sections.

## Implementation notes

The module sections are taken in the universe `u` of the schemes of the site.  The source works
with sets of one fixed universe throughout, so this is the source's reading; it is also the
universe at which the cartesian property of quasi-coherent modules (Stacks 0H0E) is available.
The two implications proved elsewhere, (2) ⟹ (1) and (3) ⟹ (4), are stated at a free module
universe.

Local Noetherianity of `𝒳` is `AlgebraicGeometry.Stack.HasPropertyOnSomeSchemeAtlas` of
Stacks 04YG at `AlgebraicGeometry.IsLocallyNoetherian`, as in the statements of the conditions.

## References

* [Stacks Project, Tag 0GR5](https://stacks.math.columbia.edu/tag/0GR5)
* [Stacks Project, Tag 0GR6](https://stacks.math.columbia.edu/tag/0GR6)
* [Stacks Project, Tag 0H0E](https://stacks.math.columbia.edu/tag/0H0E)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 06QA](https://stacks.math.columbia.edu/tag/06QA)
* [Stacks Project, Tag 0DQJ](https://stacks.math.columbia.edu/tag/0DQJ)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite Stacks.PresheafOfModules

universe u t

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Restriction of scalars along a surjective ring homomorphism preserves finiteness. -/
theorem moduleFinite_restrictScalars_of_surjective {R₁ R₂ : RingCat.{u}} (φ : R₁ ⟶ R₂)
    (hφ : Function.Surjective φ) (N : ModuleCat.{u} R₂) [hN : Module.Finite R₂ N] :
    Module.Finite R₁ ((ModuleCat.restrictScalars φ.hom).obj N) := by
  obtain ⟨T, hT⟩ := hN.1
  let N' := (ModuleCat.restrictScalars φ.hom).obj N
  let T' : Finset N' := T
  refine ⟨⟨T', ?_⟩⟩
  have key : ∀ y : N, y ∈ Submodule.span R₂ (T : Set N) →
      (show N' from y) ∈ Submodule.span R₁ (T' : Set N') := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | smul c y _ hy =>
      obtain ⟨a, rfl⟩ := hφ c
      exact Submodule.smul_mem _ a hy
  exact eq_top_iff.2 fun x _ => key x (hT ▸ Submodule.mem_top)

/-- Finiteness over the source of a ring homomorphism, after restriction of scalars, gives
finiteness over its target. -/
theorem moduleFinite_of_restrictScalars {R₁ R₂ : RingCat.{u}} (φ : R₁ ⟶ R₂)
    (N : ModuleCat.{u} R₂) [hN : Module.Finite R₁ ((ModuleCat.restrictScalars φ.hom).obj N)] :
    Module.Finite R₂ N := by
  obtain ⟨T, hT⟩ := hN.1
  let T' : Finset N := T
  refine ⟨⟨T', ?_⟩⟩
  have key : ∀ y : (ModuleCat.restrictScalars φ.hom).obj N,
      y ∈ Submodule.span R₁ (T : Set ((ModuleCat.restrictScalars φ.hom).obj N)) →
      (show N from y) ∈ Submodule.span R₂ (T' : Set N) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | smul c y _ hy => exact Submodule.smul_mem _ (φ c) hy
  exact eq_top_iff.2 fun x _ => key x (hT ▸ Submodule.mem_top)

variable (𝒳 : AlgebraicStacks.{u, t} B S hS)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
  (f : algebraicSpaceStack.{u, t} B S hS F hF ⟶ 𝒳)

/-- The functor `U_étale ⥤ 𝒳` along which `spaceChartRestriction` restricts. -/
noncomputable abbrev spaceChartFunctor : Space.SmallEtale B S hS F ⥤ 𝒳.val.val.obj :=
  Space.etaleChartToFibred (U := ⟨F, hF⟩) B S hS
    (algebraicSpaceStack.{u, t} B S hS F hF).val.val.p
    (StacksRepresentableCFG.EquivalenceOver.refl _) (CatFiberedInGroupoids.homFunctor f.hom)

/-- The chart functor lies over the underlying-object functor of the small étale site. -/
theorem spaceChartFunctor_comp :
    spaceChartFunctor B S hS 𝒳 F hF f ⋙ 𝒳.val.val.p = Space.SmallEtale.toOver B S hS F :=
  Space.etaleChartToFibred_comp (U := ⟨F, hF⟩) B S hS
    (algebraicSpaceStack.{u, t} B S hS F hF).val.val.p 𝒳.val.val.p
    (StacksRepresentableCFG.EquivalenceOver.refl _) (CatFiberedInGroupoids.homFunctor f.hom)
    (BigFppfOver.isFibredOneMorphism_homFunctor B S hS f.hom)

/-- The image of an affine étale chart under the chart functor lies over an affine scheme. -/
theorem isAffine_spaceChartFunctor_obj (V : Space.SmallEtale B S hS F)
    (hV : IsAffine ((Space.SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V)) :
    IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj
      ((spaceChartFunctor B S hS 𝒳 F hF f).obj V)) := by
  have : IsAffine (((spaceChartFunctor B S hS 𝒳 F hF f ⋙ 𝒳.val.val.p) ⋙
      BigFppfOver.toScheme B S hS).obj V) := by
    rw [spaceChartFunctor_comp]; exact hV
  exact this

/-- The coefficient homomorphism of `spaceChartRestriction`. -/
noncomputable abbrev spaceChartStructureHom :=
  Space.etaleChartStructureHom (U := ⟨F, hF⟩) B S hS
    (algebraicSpaceStack.{u, t} B S hS F hF).val.val.p 𝒳.val.val.p
    (algebraicSpaceStack.{u, t} B S hS F hF).val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids
    (StacksRepresentableCFG.EquivalenceOver.refl _) (CatFiberedInGroupoids.homFunctor f.hom)
    (BigFppfOver.isFibredOneMorphism_homFunctor B S hS f.hom)

/-- The coefficient homomorphism of the restriction is an isomorphism at every chart. -/
theorem isIso_spaceChartStructureHom_app (Z : (Space.SmallEtale B S hS F)ᵒᵖ) :
    IsIso ((spaceChartStructureHom B S hS 𝒳 F hF f).hom.app Z) := by
  obtain ⟨W⟩ := Z
  have h := Space.etaleChartStructureHom_app (U := ⟨F, hF⟩) B S hS
    (algebraicSpaceStack.{u, t} B S hS F hF).val.val.p 𝒳.val.val.p
    (algebraicSpaceStack.{u, t} B S hS F hF).val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids
    (StacksRepresentableCFG.EquivalenceOver.refl _) (CatFiberedInGroupoids.homFunctor f.hom)
    (BigFppfOver.isFibredOneMorphism_homFunctor B S hS f.hom) W
  change IsIso ((spaceChartStructureHom B S hS 𝒳 F hF f).hom.app (op W))
  rw [h]
  exact Functor.map_isIso _ _

/-- **The restriction of a module cartesian between affine objects to an algebraic-space chart is
cartesian on affine charts.** -/
theorem isCartesianOnAffineCharts_spaceChartRestriction
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl))
    (hM : IsCartesianBetweenAffines 𝒳.val.isFiberedInGroupoids M) :
    Space.IsCartesianOnAffineCharts (spaceChartRestriction B S hS 𝒳 F hF f M) := by
  intro U V hU hV g
  rw [Space.bijective_sectionsBaseChange_iff_isIso_restrictionBaseChange.{u, u} B S hS F hF,
    ConcreteCategory.isIso_iff_bijective]
  refine (bijective_restrictionBaseChange_restrictScalars_pushforward₀_iff
    (spaceChartFunctor B S hS 𝒳 F hF f) (fibredRings B S hS 𝒳.val.val.p)
    (Space.structurePresheaf B S hS F) (spaceChartStructureHom B S hS 𝒳 F hF f).hom
    (isIso_spaceChartStructureHom_app B S hS 𝒳 F hF f) M.val g.op).2 ?_
  have h := hM ((spaceChartFunctor B S hS 𝒳 F hF f).map g)
    (isAffine_spaceChartFunctor_obj B S hS 𝒳 F hF f U hU)
    (isAffine_spaceChartFunctor_obj B S hS 𝒳 F hF f V hV)
  rw [show (fibredSectionsBaseChange _ M ((spaceChartFunctor B S hS 𝒳 F hF f).map g) : _ → _) = _
    from funext (fibredSectionsBaseChange_eq_restrictionBaseChange _ M _)] at h
  exact h

/-- **The sections of the restriction over an affine chart are finite** when the module is
cartesian between affine objects and of finite type. -/
theorem moduleFinite_spaceChartRestriction
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl))
    (hM : IsCartesianBetweenAffines 𝒳.val.isFiberedInGroupoids M) (hft : M.IsFiniteTypeOnSite)
    (A : Space.SmallEtale B S hS F) (hA : IsAffine (Space.chartScheme A)) :
    Module.Finite (Space.chartRing B S hS F hF A)
      ((spaceChartRestriction B S hS 𝒳 F hF f M).val.obj (op A)) := by
  have hfin := moduleFinite_sections_of_isFiniteTypeOnSite_fibred 𝒳.val.isFiberedInGroupoids M hM
    hft (isAffine_spaceChartFunctor_obj B S hS 𝒳 F hF f A hA)
  have hsurj : Function.Surjective ((spaceChartStructureHom B S hS 𝒳 F hF f).hom.app (op A)) := by
    have := isIso_spaceChartStructureHom_app B S hS 𝒳 F hF f (op A)
    exact (ConcreteCategory.bijective_of_isIso _).2
  exact moduleFinite_restrictScalars_of_surjective _ hsurj _ (hN := hfin)

/-- **Stacks 0GR5, the implication (1) ⟹ (3).** -/
theorem isCoherentOnNoetherianSpaceCharts_of_isQuasicoherentFiniteTypeModule
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl))
    (hM : IsQuasicoherentFiniteTypeModule B S hS 𝒳 M) :
    IsCoherentOnNoetherianSpaceCharts.{u, u, t} B S hS 𝒳 M := by
  obtain ⟨hqc, hft⟩ := hM
  have hcart := isCartesianBetweenAffines_of_isQuasicoherentOnSite _ M hqc
  refine ⟨hqc, fun F hF f hN => ?_⟩
  exact Space.isCoherent_of_isQuasicoherentOnSite_of_forall_affine_moduleFinite B S hS F hF hN _
    (Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
      (isCartesianOnAffineCharts_spaceChartRestriction B S hS 𝒳 F hF f M hcart))
    (moduleFinite_spaceChartRestriction B S hS 𝒳 F hF f M hcart hft)

/-! ### Objects of `𝒳` mapping to affine charts cover -/

/-- The sieve of morphisms into `x` whose source maps to the image of an affine étale chart of
the algebraic space `F` under the chart functor of `f`. -/
def affineChartSieve (x : 𝒳.val.val.obj) : Sieve x where
  arrows y _ := ∃ A : Space.SmallEtale B S hS F, IsAffine (Space.chartScheme A) ∧
    Nonempty (y ⟶ (spaceChartFunctor B S hS 𝒳 F hF f).obj A)
  downward_closed := by
    rintro y y' g ⟨A, hA, ⟨c⟩⟩ h
    exact ⟨A, hA, ⟨h ≫ c⟩⟩

/-- The affine chart sieve is stable under pullback. -/
theorem affineChartSieve_pullback {x y : 𝒳.val.val.obj} (h : y ⟶ x) :
    (affineChartSieve B S hS 𝒳 F hF f x).pullback h = affineChartSieve B S hS 𝒳 F hF f y :=
  rfl

/-- A continuous functor into `𝒳` for the étale topology sends covering sieves to fppf covers. -/
private theorem functorPushforward_mem_fppf {C : Type*} [Category C]
    (J : GrothendieckTopology C) (G : C ⥤ 𝒳.val.val.obj)
    [G.IsContinuous J (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale)]
    {X : C} {R : Sieve X} (hR : R ∈ J X) :
    R.functorPushforward G ∈ BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf (G.obj X) :=
  BigFppfOver.associatedTopology_le_fppf B S hS 𝒳.val.val.p .etale _
    ((CoverPreserving.of_isContinuous G J _).cover_preserve hR)

/-- An object mapping to the image of an étale chart is covered by objects mapping to images of
affine étale charts. -/
theorem affineChartSieve_mem_of_hom {y : 𝒳.val.val.obj} {V : Space.SmallEtale B S hS F}
    (δ : y ⟶ (spaceChartFunctor B S hS 𝒳 F hF f).obj V) :
    affineChartSieve B S hS 𝒳 F hF f y ∈
      BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf y := by
  have := Space.etaleChartToFibred_isContinuous (U := ⟨F, hF⟩) B S hS
    (algebraicSpaceStack.{u, t} B S hS F hF).val.val.p 𝒳.val.val.p
    (algebraicSpaceStack.{u, t} B S hS F hF).val.isFiberedInGroupoids
    (StacksRepresentableCFG.EquivalenceOver.refl _) (CatFiberedInGroupoids.homFunctor f.hom)
    (BigFppfOver.isFibredOneMorphism_homFunctor B S hS f.hom)
  obtain ⟨I, Y, a, hYaff, hcov, -⟩ := Space.SmallEtale.exists_affine_etale_ofArrows B S hS F V
  have hpull := (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf).pullback_stable δ
    (functorPushforward_mem_fppf B S hS 𝒳 (Space.SmallEtale.topology B S hS F)
      (spaceChartFunctor B S hS 𝒳 F hF f) hcov)
  refine (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf).superset_covering ?_ hpull
  rintro y' h ⟨Z, g, h', hg, hfac⟩
  obtain ⟨j, b, rfl⟩ := (Sieve.mem_ofArrows_iff Y a g).1 hg
  exact ⟨Y j, hYaff j, ⟨h' ≫ (spaceChartFunctor B S hS 𝒳 F hF f).map b⟩⟩

/-- A covering sieve each of whose arrows has a source mapping to the image of an étale chart
forces the affine chart sieve to cover. -/
theorem affineChartSieve_mem_of_forall {x : 𝒳.val.val.obj} {R : Sieve x}
    (hR : R ∈ BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf x)
    (hmap : ∀ ⦃y : 𝒳.val.val.obj⦄ (h : y ⟶ x), R h →
      ∃ V : Space.SmallEtale B S hS F, Nonempty (y ⟶ (spaceChartFunctor B S hS 𝒳 F hF f).obj V)) :
    affineChartSieve B S hS 𝒳 F hF f x ∈
      BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf x := by
  refine (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf).transitive hR _ ?_
  intro y h hh
  obtain ⟨V, ⟨δ⟩⟩ := hmap h hh
  rw [affineChartSieve_pullback]
  exact affineChartSieve_mem_of_hom B S hS 𝒳 F hF f δ

/-- The image of every object of the chart is covered by objects mapping to images of affine
étale charts. -/
theorem affineChartSieve_mem_homFunctor
    (z : (algebraicSpaceStack.{u, t} B S hS F hF).val.val.obj) :
    affineChartSieve B S hS 𝒳 F hF f ((CatFiberedInGroupoids.homFunctor f.hom).obj z) ∈
      BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf
        ((CatFiberedInGroupoids.homFunctor f.hom).obj z) := by
  have := (algebraicSpaceStack.{u, t} B S hS F hF).val.isFiberedInGroupoids.isFibered
  have := (BigFppfOver.isFibredOneMorphism_homFunctor B S hS f.hom).isContinuous_inheritedTopology
    (BigFppfOver.baseOverTopology B S hS .etale)
  have hT := Space.structuredArrowSieve_restrictionFunctor_mem B S hS F
    (algebraicSpaceStack.{u, t} B S hS F hF).val.val.p
    (algebraicSpaceStack.{u, t} B S hS F hF).val.isFiberedInGroupoids hF
    (StacksRepresentableCFG.EquivalenceOver.refl _) z
  refine affineChartSieve_mem_of_forall B S hS 𝒳 F hF f
    (functorPushforward_mem_fppf B S hS 𝒳 _ (CatFiberedInGroupoids.homFunctor f.hom) hT) ?_
  rintro y h ⟨w, t', h', ⟨σ⟩, rfl⟩
  exact ⟨σ.right, ⟨h' ≫ (CatFiberedInGroupoids.homFunctor f.hom).map σ.hom⟩⟩

/-- **For a surjective, flat, locally finitely presented chart, every object of `𝒳` is covered by
objects mapping to images of affine étale charts.** -/
theorem affineChartSieve_mem (hsurj : IsSurjective B S hS f)
    (hflat : AlgebraicStacks.IsFlat B S hS f)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f) (x : 𝒳.val.val.obj) :
    affineChartSieve B S hS 𝒳 F hF f x ∈
      BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf x := by
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  obtain ⟨T, m, hmflat, hmlfp, hmsurj, z, α, hα⟩ :=
    exists_scheme_lift_of_isSurjective_isFlat_isLfp B S hS f hsurj hflat hlfp
      (𝒳.val.val.p.obj x) (Functor.Fiber.mk rfl)
  have hgen : Sieve.generate (Presieve.singleton α) ∈
      BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf x := by
    refine Functor.generate_singleton_mem_inheritedTopology_of_isHomLift 𝒳.val.val.p
      (BigFppfOver.baseOverTopology B S hS .fppf) α
      (𝒳.val.isFiberedInGroupoids.isStronglyCartesian α) _ hα
      (mem_topology_of_family B S hS (I := PUnit.{u + 2}) (fun _ => T) (fun _ => m)
        (fun _ => hmflat) (fun _ => hmlfp) (fun x => ⟨PUnit.unit, hmsurj.1 x⟩)) ?_
    rintro W u ⟨W', k, -, ⟨i⟩, rfl⟩
    exact ⟨k, rfl⟩
  refine (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf).transitive hgen _ ?_
  rintro y h ⟨y', h', g, ⟨⟩, rfl⟩
  exact (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf).pullback_stable h'
    (affineChartSieve_mem_homFunctor B S hS 𝒳 F hF f z)

/-- **The sections of a module cartesian between affine objects over the image of a Noetherian
affine chart on which the restriction is coherent form a finitely presented module.** -/
theorem finitePresentation_sections_spaceChartFunctor
    (hN : Space.HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl))
    (hcoh : Space.IsCoherent B S hS F hF (spaceChartRestriction B S hS 𝒳 F hF f M))
    (A : Space.SmallEtale B S hS F) (hA : IsAffine (Space.chartScheme A)) :
    letI := fibredSectionsModule 𝒳.val.isFiberedInGroupoids M
      ((spaceChartFunctor B S hS 𝒳 F hF f).obj A)
    Module.FinitePresentation
      (fibredSectionRing B S hS 𝒳.val.val.p ((spaceChartFunctor B S hS 𝒳 F hF f).obj A))
      (M.val.obj (op ((spaceChartFunctor B S hS 𝒳 F hF f).obj A))) := by
  let := fibredSectionsModule 𝒳.val.isFiberedInGroupoids M
      ((spaceChartFunctor B S hS 𝒳 F hF f).obj A)
  have hfinG := Space.moduleFinite_sections_of_isCoherent B S hS F hF _ hcoh hA
  have hfin : Module.Finite
      (fibredSectionRing B S hS 𝒳.val.val.p ((spaceChartFunctor B S hS 𝒳 F hF f).obj A))
      (M.val.obj (op ((spaceChartFunctor B S hS 𝒳 F hF f).obj A))) :=
    moduleFinite_of_restrictScalars ((spaceChartStructureHom B S hS 𝒳 F hF f).hom.app (op A))
      _ (hN := hfinG)
  have hLN : IsLocallyNoetherian (Space.chartScheme A) :=
    (Space.exists_atlas_iff_forall_etale B S hS F
      (fun V : Scheme.{u} => IsLocallyNoetherian V) hF).1 hN A.obj.left A.obj.hom A.property
  have hnoeth : IsNoetherianRing
      (fibredSectionRing B S hS 𝒳.val.val.p ((spaceChartFunctor B S hS 𝒳 F hF f).obj A)) := by
    have e := Functor.congr_obj (spaceChartFunctor_comp B S hS 𝒳 F hF f) A
    show IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj
      ((spaceChartFunctor B S hS 𝒳 F hF f ⋙ 𝒳.val.val.p).obj A), ⊤)
    rw [e]
    exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  exact Module.finitePresentation_of_finite _ _

/-- **Stacks 0GR5, the implication (4) ⟹ (2).** -/
theorem isFinitePresentationOnSite_of_isCoherentOnSomeFlatSpaceChart
    (𝒳 : AlgebraicStacks.{u, t} B S hS)
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl))
    (hM : IsCoherentOnSomeFlatSpaceChart.{u, u, t} B S hS 𝒳 M) :
    M.IsFinitePresentationOnSite := by
  obtain ⟨hqc, F, hF, f, hlft, hflat, hsurj, hcoh⟩ := hM
  have hcart := isCartesianBetweenAffines_of_isQuasicoherentOnSite _ M hqc
  have hlfp := AlgebraicStacks.isLocallyOfFinitePresentation_of_isLocallyOfFiniteType
    B S hS f h𝒳 hlft
  have hN := hasEtaleLocalProperty_isLocallyNoetherian_of_chart B S hS 𝒳 h𝒳 hF f hlft
  refine ⟨fun x => ?_⟩
  refine ⟨Σ y : 𝒳.val.val.obj, {h : y ⟶ x // affineChartSieve B S hS 𝒳 F hF f x h},
    fun i => i.1, fun i => i.2.1, ?_, fun i => ?_⟩
  · refine (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf).superset_covering ?_
      (affineChartSieve_mem B S hS 𝒳 F hF f hsurj hflat hlfp x)
    intro y h hh
    exact ⟨y, 𝟙 y, h, Presieve.ofArrows.mk (⟨y, h, hh⟩ :
      Σ y : 𝒳.val.val.obj, {h : y ⟶ x // affineChartSieve B S hS 𝒳 F hF f x h}),
      Category.id_comp h⟩
  · obtain ⟨y, h, A, hA, ⟨c⟩⟩ := i
    exact Stacks.SheafOfModules.FinitePresentationTransport.hasFiniteGlobalPresentation_overMap
      M c (hasFiniteGlobalPresentation_over_of_finitePresentation _ M hcart
        (isAffine_spaceChartFunctor_obj B S hS 𝒳 F hF f A hA)
        (finitePresentation_sections_spaceChartFunctor B S hS 𝒳 F hF f hN M hcoh A hA))

/-! ### Stacks 0GR5 -/

/-- **Stacks 0GR5.**  Let `𝒳` be a locally Noetherian algebraic stack and `ℱ` an `𝒪_𝒳`-module.
The following are equivalent:

1. `ℱ` is a quasi-coherent, finite type `𝒪_𝒳`-module;
2. `ℱ` is an `𝒪_𝒳`-module of finite presentation;
3. `ℱ` is quasi-coherent and for any morphism `f : U ⟶ 𝒳` where `U` is a locally Noetherian
   algebraic space, the pullback `f^*ℱ|_{U_étale}` is coherent;
4. `ℱ` is quasi-coherent and there exists an algebraic space `U` and a morphism `f : U ⟶ 𝒳` which
   is locally of finite type, flat, and surjective, such that the pullback `f^*ℱ|_{U_étale}` is
   coherent.

Local Noetherianity of `𝒳` is the smooth scheme atlas criterion of Stacks 04YG. -/
@[stacks 0GR5]
theorem tfae_coherenceConditions (𝒳 : AlgebraicStacks.{u, t} B S hS)
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)) :
    [IsQuasicoherentFiniteTypeModule B S hS 𝒳 M, M.IsFinitePresentationOnSite,
      IsCoherentOnNoetherianSpaceCharts.{u, u, t} B S hS 𝒳 M,
      IsCoherentOnSomeFlatSpaceChart.{u, u, t} B S hS 𝒳 M].TFAE := by
  tfae_have 2 → 1 := isQuasicoherentFiniteTypeModule_of_isFinitePresentationOnSite B S hS 𝒳 h𝒳 M
  tfae_have 1 → 3 := isCoherentOnNoetherianSpaceCharts_of_isQuasicoherentFiniteTypeModule B S hS 𝒳 M
  tfae_have 3 → 4 :=
    isCoherentOnSomeFlatSpaceChart_of_isCoherentOnNoetherianSpaceCharts B S hS 𝒳 h𝒳 M
  tfae_have 4 → 2 := isFinitePresentationOnSite_of_isCoherentOnSomeFlatSpaceChart B S hS 𝒳 h𝒳 M
  tfae_finish

/-- **The coherence of Stacks 0GR6 is each of the four conditions of Stacks 0GR5.** On a locally
Noetherian algebraic stack, `AlgebraicGeometry.Stack.IsCoherent` — defined as conditions (1) and
(2) jointly — is equivalent to each of the four conditions separately. -/
theorem isCoherent_tfae (𝒳 : AlgebraicStacks.{u, t} B S hS)
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)) :
    [IsCoherent B S hS 𝒳 M, IsQuasicoherentFiniteTypeModule B S hS 𝒳 M,
      M.IsFinitePresentationOnSite, IsCoherentOnNoetherianSpaceCharts.{u, u, t} B S hS 𝒳 M,
      IsCoherentOnSomeFlatSpaceChart.{u, u, t} B S hS 𝒳 M].TFAE := by
  have h := tfae_coherenceConditions B S hS 𝒳 h𝒳 M
  tfae_have 1 ↔ 3 := isCoherent_iff_isCoherentModule B S hS 𝒳 h𝒳 M
  tfae_have 2 ↔ 3 := h.out 1 2
  tfae_have 2 ↔ 4 := h.out 1 3
  tfae_have 2 ↔ 5 := h.out 1 4
  tfae_finish

end AlgebraicGeometry.Stack

end
