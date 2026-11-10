module

public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.EssentiallySmallSchemes
public import StacksFrontier.AlgebraicGeometry.Stacks.EssentiallySmallSite
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategorySite
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.BaseTopologyComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsCoveringSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.SubcategoryAffineLineClosure

/-!
# Exactness of big lower shriek on the five big sites (Stacks 07AJ)

Let `X` be a scheme in a big fppf site `B`, let `τ` be one of the Zariski, étale, smooth,
syntomic and fppf topologies, and let `C₁ ⊆ C₂` be full subcategories of the big category over
`X`, each carrying the topology it inherits from the big `τ`-site over `X` (**Stacks 06NV**).
Stacks 07AJ assumes of `C₁` and `C₂` the closure condition (1)(a) — the members of a covering of
`(Sch/X)_τ` of an object of `C_t` are again objects of `C_t` — and of `C₁` moreover that it
contains the base object `X/X`, hypothesis (2), and the affine line over each of its objects,
hypothesis (1)(b). It concludes that the inclusion is fully faithful, continuous and
cocontinuous, and that for the resulting morphism of topoi `g : Sh(C₁) ⟶ Sh(C₂)` the canonical
map `g_!O₁ ⟶ O₂` is an isomorphism.

All five big sites are taken on the category of schemes of the chosen big fppf site `B`, with the
topology `AlgebraicGeometry.BigFppfSite.baseTopology` of `τ` (**Stacks 03FF**); by
`AlgebraicGeometry.overTopology_eq_baseOverTopology` this is the localization at `X` of a big
`τ`-site with the same cutoff. Both parts are stated for every `τ` at once, at the inherited
topologies. Everything the general theory needs beyond the three conditions of the source is
produced here:

* continuity and cocontinuity of the inclusion come from
  `CategoryTheory.ObjectProperty.isContinuous_ιOfLE_inheritedTopology` and
  `CategoryTheory.ObjectProperty.isCocontinuous_ιOfLE_inheritedTopology`, whose refinement
  hypothesis is discharged by transporting refinability of the chosen `τ`-covering families to
  the localization at `X`, and whose closure hypothesis is derived from (1)(a);
* the lower shriek `g_!` on abelian sheaves exists because the big category over `X` is
  essentially small (**Stacks 000J** through
  `AlgebraicGeometry.Stack.essentiallySmall_bigFppfOver`), so each full subcategory has
  sheafification with abelian coefficients and restriction along the inclusion has a left Kan
  extension — which is **Stacks 04BG** in the form Mathlib's
  `CategoryTheory.Functor.sheafPullbackConstruction` provides it;
* the sheaf condition on the structure presheaf of `C₂` comes from **Stacks 03DU** for the big
  fppf site over `X`, the comparison of the topology of `τ` with the fppf topology, and
  continuity of the inclusion of `C₂`.

## Main definitions

* `AlgebraicGeometry.BigFppfSite.chosenCovering`: the chosen covering families of the big
  `τ`-site, for each of the five topologies.
* `AlgebraicGeometry.IsClosedUnderCoverings`: hypothesis (1)(a) of Stacks 07AJ, that a full
  subcategory of the big category over `X` contains the members of every covering of `(Sch/X)_τ`
  of one of its objects.

## Main results

* `AlgebraicGeometry.IsClosedUnderCoverings.of_coveringMorphismProperty`: such a full
  subcategory contains the source of every `τ`-morphism into one of its objects, since that
  morphism is a member of a chosen covering together with the identity.
* `AlgebraicGeometry.fullyFaithful_isContinuous_isCocontinuous_ιOfLE_baseOverTopology`:
  **Stacks 07AJ (a)** for every `τ` — the inclusion `C₁ ⊆ C₂` is fully faithful, continuous and
  cocontinuous for the inherited topologies. Continuity and cocontinuity are
  `AlgebraicGeometry.isContinuous_ιOfLE_baseOverTopology` and
  `AlgebraicGeometry.isCocontinuous_ιOfLE_baseOverTopology`; full faithfulness is
  `CategoryTheory.ObjectProperty.fullyFaithfulιOfLE`, with no condition at all.
* `AlgebraicGeometry.isSheaf_inheritedTopology_bigOverPresheafAb`: the structure presheaf of
  abelian groups of a full subcategory is a sheaf for the inherited topology.
* `AlgebraicGeometry.isIso_lowerShriekStructureSheafHom_baseOverTopology`: **Stacks 07AJ (b)**
  at the inherited topologies, for every `τ` — the canonical map `g_!O₁ ⟶ O₂` is an isomorphism.
* `AlgebraicGeometry.isClosedUnderCoverings_top`, `AlgebraicGeometry.isClosedUnderAffineLine_top`
  and `AlgebraicGeometry.top_base_obj`: the whole big category over `X` satisfies all three
  conditions of the source, so
  `AlgebraicGeometry.isIso_lowerShriekStructureSheafHom_baseOverTopology_top` is the assertion
  for `C₁ = C₂ =` the whole big category over `X`, and the conditions above are satisfiable.

## Implementation notes

`AlgebraicGeometry.isIso_lowerShriekStructureSheafHom_of_isClosedUnderAffineLine` proves part (b)
for an arbitrary pair of topologies on the two full subcategories, for an arbitrary descent
witness of the structure presheaf, and with continuity of the inclusion and the existence of
`g_!` as instance arguments. The main theorem below instantiates it: the two topologies are the
inherited ones, continuity is the theorem above, the existence of `g_!` is found by instance
search from the essential smallness proved here, and the descent witness is
`AlgebraicGeometry.isSheaf_inheritedTopology_bigOverPresheafAb`. So the three conditions of the
source are all that is left.

The closure condition (1)(a) is stated literally: a covering of `(Sch/X)_τ` is a family over `X`
whose underlying family is one of the chosen `τ`-covering families of the big site, exactly as
`AlgebraicGeometry.BigFppfOver.IsCovering` (**Stacks 021S**) is for the fppf topology. The source's
conditions (1)(b) and (2) are used for `C₁` only, since that is all the comparison of structure
sheaves consumes.

## References

* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
* [Stacks Project, Tag 04BG](https://stacks.math.columbia.edu/tag/04BG)
* [Stacks Project, Tag 06NV](https://stacks.math.columbia.edu/tag/06NV)
* [Stacks Project, Tag 07AJ](https://stacks.math.columbia.edu/tag/07AJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe t

/-! ### The chosen covering families of the five big sites -/

namespace BigFppfSite

variable (B : BigFppfSite.{t})

/-- The chosen covering families of the big `τ`-site carried by a chosen big fppf site, for each
of the five topologies (**Stacks 03FF**): the chosen fppf families, and for the four coarser
topologies those chosen fppf families which are `τ`-coverings. -/
def chosenCovering : CoveringTopology → Covering B.Schemes → Prop
  | .fppf => B.IsCovering
  | .syntomic => B.syntomicCovering
  | .smooth => B.smoothCovering
  | .etale => B.etaleCovering
  | .zariski => B.zariskiCovering

/-- The topology of `τ` on a chosen big fppf site is generated by its chosen `τ`-covering
families. -/
theorem baseTopology_toSiteKind_eq (τ : CoveringTopology) :
    B.baseTopology τ.toSiteKind = (B.chosenPrecoverage (B.chosenCovering τ)).toGrothendieck := by
  cases τ <;> rfl

/-- A chosen `τ`-covering family is a `τ`-covering family of schemes. -/
theorem mem_precoverage_of_chosenCovering (τ : CoveringTopology) {X : B.Schemes}
    {E : PreZeroHypercover.{t + 1} X} (hE : B.chosenCovering τ ⟨X, E⟩) :
    (E.map B.inclusion).presieve₀ ∈
      Scheme.precoverage (coveringMorphismProperty τ) (B.inclusion.obj X) := by
  cases τ <;> exact B.mem_precoverage_of_mem_baseTopology_precoverage _ E hE

/-- **Every `τ`-covering family of `Sch_κ` has the presieve of a chosen `τ`-covering family.** A
`τ`-covering family is an fppf covering family, so the chosen fppf system has a combinatorially
equivalent representative; it has the same presieve, so it is again a `τ`-covering family. -/
theorem exists_chosenCovering_presieve₀_eq (τ : CoveringTopology) {X : B.Schemes}
    (E : PreZeroHypercover.{t + 1} X)
    (hE : (E.map B.inclusion).presieve₀ ∈
      Scheme.precoverage (coveringMorphismProperty τ) (B.inclusion.obj X)) :
    ∃ F : PreZeroHypercover.{t + 1} X,
      B.chosenCovering τ ⟨X, F⟩ ∧ F.presieve₀ = E.presieve₀ := by
  have hEs := (Scheme.presieve₀_mem_precoverage_iff _).1 hE
  have hfppf : IsFppfCovering (κ := B.cutoff) ⟨X, E⟩ := by
    change Presieve.map B.inclusion E.presieve₀ ∈ Scheme.fppfPrecoverage.coverings _
    rw [← PreZeroHypercover.presieve₀_map]
    exact (Scheme.presieve₀_mem_precoverage_iff _).2 ⟨hEs.1, fun i =>
      coveringMorphismProperty_le_flat_inf_locallyOfFinitePresentation τ _ (hEs.2 i)⟩
  obtain ⟨E', hE', hcomb⟩ := B.fppf_has_representative ⟨X, E⟩ hfppf
  obtain ⟨W, F⟩ := E'
  obtain ⟨hobj, hce⟩ := hcomb
  cases hobj
  dsimp only at hce
  have hpre : F.presieve₀ = E.presieve₀ :=
    (PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hce).symm
  have hF : (F.map B.inclusion).presieve₀ ∈
      Scheme.precoverage (coveringMorphismProperty τ) (B.inclusion.obj X) := by
    rw [PreZeroHypercover.presieve₀_map, hpre, ← PreZeroHypercover.presieve₀_map]
    exact hE
  refine ⟨F, ?_, hpre⟩
  cases τ with
  | fppf => exact hE'
  | zariski => exact ⟨hE', hF⟩
  | etale => exact ⟨hE', hF⟩
  | smooth => exact ⟨hE', hF⟩
  | syntomic =>
      have h := (Scheme.presieve₀_mem_precoverage_iff (F.map B.inclusion)).1 hF
      exact ⟨hE', h.2, Set.eq_univ_iff_forall.2 fun x => Set.mem_iUnion.2 (h.1 x)⟩

end BigFppfSite

/-- The covering morphism property of each of the five topologies contains the identities and is
stable under composition and under base change. -/
theorem coveringMorphismProperty_instances (τ : CoveringTopology) :
    (coveringMorphismProperty.{t} τ).ContainsIdentities ∧
      (coveringMorphismProperty.{t} τ).IsStableUnderComposition ∧
      (coveringMorphismProperty.{t} τ).IsStableUnderBaseChange := by
  refine ⟨⟨fun Y ↦ ExtendingFunctors.coveringMorphismProperty_of_isOpenImmersion τ (𝟙 Y)⟩,
    ⟨fun f g hf hg ↦ ?_⟩, ExtendingFunctors.isStableUnderBaseChange_coveringMorphismProperty τ⟩
  cases τ with
  | zariski => exact MorphismProperty.comp_mem _ _ _ hf hg
  | etale => exact MorphismProperty.comp_mem _ _ _ hf hg
  | smooth => exact MorphismProperty.comp_mem _ _ _ hf hg
  | syntomic => exact MorphismProperty.comp_mem _ _ _ hf hg
  | fppf =>
      exact ⟨MorphismProperty.comp_mem _ _ _ hf.1 hg.1, MorphismProperty.comp_mem _ _ _ hf.2 hg.2⟩

variable {B : BigFppfSite.{t}} {X : Scheme.{t}} {hX : B.Contains X}

/-! ### Essential smallness, sheafification and lower shriek -/

/-- A full subcategory of the big fppf category over `X` is essentially small at the universe of
its schemes: the big fppf category over `X` is (**Stacks 000J**), and a full subcategory of an
essentially small category is. -/
theorem essentiallySmall_fullSubcategory_bigFppfOver
    (P : ObjectProperty (BigFppfOver B X hX)) : EssentiallySmall.{t} P.FullSubcategory :=
  have := Stack.essentiallySmall_bigFppfOver B X hX
  CategoryTheory.essentiallySmall_fullSubcategory P

/-- Abelian presheaves on a full subcategory of the big fppf category over `X` have a
sheafification, for every topology on the full subcategory: the site is essentially small, so
sheafification can be computed in a small model. -/
instance hasSheafify_fullSubcategory_bigFppfOver
    {P : ObjectProperty (BigFppfOver B X hX)} (J : GrothendieckTopology P.FullSubcategory) :
    HasSheafify J AddCommGrpCat.{t} :=
  haveI := essentiallySmall_fullSubcategory_bigFppfOver P
  hasSheafifyEssentiallySmallSite.{_, _, _, _, t} _ _

/-- Restriction of abelian presheaves along the inclusion of one full subcategory of the big fppf
category over `X` into another admits a left Kan extension: the comma categories indexing it are
essentially small, so the colimits computing it exist in abelian groups. -/
instance hasLeftKanExtension_ιOfLE_bigFppfOver
    {P₁ P₂ : ObjectProperty (BigFppfOver B X hX)} (h₁₂ : P₁ ≤ P₂)
    (F : P₁.FullSubcategoryᵒᵖ ⥤ AddCommGrpCat.{t}) :
    (ObjectProperty.ιOfLE h₁₂).op.HasLeftKanExtension F := by
  have := essentiallySmall_fullSubcategory_bigFppfOver P₁
  have := essentiallySmall_fullSubcategory_bigFppfOver P₂
  have : (ObjectProperty.ιOfLE h₁₂).op.HasPointwiseLeftKanExtension F := fun Y ↦ by
    have := hasColimitsOfShape_of_essentiallySmall.{t}
      (CostructuredArrow (ObjectProperty.ιOfLE h₁₂).op Y) AddCommGrpCat.{t}
    infer_instance
  infer_instance

/-! ### Hypothesis (1)(a) of Stacks 07AJ -/

/-- **Hypothesis (1)(a) of Stacks 07AJ.** A full subcategory of the big category over `X`
contains the members of every covering of `(Sch/X)_τ` of one of its objects: if `{Uᵢ ⟶ U}` is a
family over `X` whose underlying family of schemes is a chosen `τ`-covering family of the big
site, and `U` is in the subcategory, then so is every `Uᵢ`.

For `τ` the fppf topology a covering of `(Sch/X)_τ` is literally an
`AlgebraicGeometry.BigFppfOver.IsCovering` family (**Stacks 021S**). -/
def IsClosedUnderCoverings (τ : CoveringTopology) (P : ObjectProperty (BigFppfOver B X hX)) :
    Prop :=
  ∀ ⦃U : BigFppfOver B X hX⦄ (E : PreZeroHypercover.{t + 1} U),
    B.chosenCovering τ ⟨(BigFppfOver.forget B X hX).obj U, E.map (BigFppfOver.forget B X hX)⟩ →
      P U → ∀ i, P (E.X i)

/-- An object of the big category over `X` is recovered from a morphism of schemes into the
target of a morphism `f` which agrees with the underlying morphism of `f`. -/
private lemma over_mk_comp_hom_eq {U V : BigFppfOver B X hX} (f : V ⟶ U) {Y : B.Schemes}
    (g : Y ⟶ U.left) (h : Y = V.left) (hg : f.left = eqToHom h.symm ≫ g) :
    Over.mk (g ≫ U.hom) = V := by
  subst h
  rw [eqToHom_refl, Category.id_comp] at hg
  subst hg
  rw [Over.w f]
  rfl

/-- **A full subcategory satisfying (1)(a) contains the source of every `τ`-morphism into one of
its objects.** A `τ`-morphism `f : V ⟶ U` together with the identity of `U` is a `τ`-covering
family; the chosen system has a family with the same presieve, which is a covering of
`(Sch/X)_τ` having `f` as a member. -/
theorem IsClosedUnderCoverings.of_coveringMorphismProperty {τ : CoveringTopology}
    {P : ObjectProperty (BigFppfOver B X hX)} (hP : IsClosedUnderCoverings τ P)
    ⦃U V : BigFppfOver B X hX⦄ (f : V ⟶ U)
    (hf : coveringMorphismProperty τ (B.inclusion.map f.left)) (hU : P U) : P V := by
  let E : PreZeroHypercover.{t + 1} U.left :=
    { I₀ := PUnit.{t + 2} ⊕ PUnit.{t + 2}
      X := Sum.elim (fun _ ↦ U.left) (fun _ ↦ V.left)
      f := fun i ↦ match i with
        | .inl _ => 𝟙 _
        | .inr _ => f.left }
  have hE : (E.map B.inclusion).presieve₀ ∈
      Scheme.precoverage (coveringMorphismProperty τ) (B.inclusion.obj U.left) := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ⟨.inl PUnit.unit, x, ?_⟩, fun i ↦ ?_⟩
    · change (B.inclusion.map (𝟙 U.left)) x = x
      simp
    · rcases i with _ | _
      · change coveringMorphismProperty τ (B.inclusion.map (𝟙 U.left))
        rw [B.inclusion.map_id]
        exact ExtendingFunctors.coveringMorphismProperty_of_isOpenImmersion τ _
      · exact hf
  obtain ⟨F, hF, hFE⟩ := B.exists_chosenCovering_presieve₀_eq τ E hE
  let F' : PreZeroHypercover.{t + 1} U :=
    { I₀ := F.I₀
      X := fun i ↦ Over.mk (F.f i ≫ U.hom)
      f := fun i ↦ Over.homMk (F.f i) }
  have hF' := hP F' hF hU
  have hmem : F.presieve₀ f.left := by
    rw [hFE]
    exact Presieve.ofArrows.mk (Sum.inr PUnit.unit)
  obtain ⟨i, hi, hfi⟩ := Presieve.ofArrows_surj _ _ hmem
  rw [← over_mk_comp_hom_eq f (F.f i) hi hfi]
  exact hF' i

/-- The property of a morphism of the big category over `X` that its underlying morphism of
schemes is a `τ`-morphism: étale, smooth, syntomic, an open immersion, or flat and locally of
finite presentation, according to `τ`. -/
abbrev bigFppfOverCoveringMorphismProperty (τ : CoveringTopology) (B : BigFppfSite.{t})
    (X : Scheme.{t}) (hX : B.Contains X) : MorphismProperty (BigFppfOver B X hX) :=
  ((coveringMorphismProperty.{t} τ).inverseImage B.inclusion).inverseImage
    (BigFppfOver.forget B X hX)

/-- Every covering sieve of the big `τ`-site over `X` is refined by a covering family of
`τ`-morphisms. The chosen `τ`-covering families consist of `τ`-morphisms, and refinability passes
from the generating families of a precoverage to all covering sieves of the topology it generates
and then to the localization at `X`. -/
theorem isRefinableBy_baseOverTopology (τ : CoveringTopology) ⦃V : BigFppfOver B X hX⦄
    (S : Sieve V) (hS : S ∈ BigFppfOver.baseOverTopology B X hX τ.toSiteKind V) :
    (BigFppfOver.baseOverTopology B X hX τ.toSiteKind).IsRefinableBy
      (bigFppfOverCoveringMorphismProperty τ B X hX) S := by
  obtain ⟨h₁, h₂, h₃⟩ := coveringMorphismProperty_instances.{t} τ
  refine (B.baseTopology τ.toSiteKind).isRefinableBy_over _ (B.obj hX) (fun W T hT ↦ ?_) S hS
  rw [B.baseTopology_toSiteKind_eq τ] at hT ⊢
  refine Stack.isRefinableBy_toGrothendieck_of_members B _ _ (fun Y R hR Z g hg ↦ ?_) T hT
  obtain ⟨E, rfl, hE⟩ := hR
  have h := B.mem_precoverage_of_chosenCovering τ hE
  rw [PreZeroHypercover.presieve₀_map] at h
  exact h.2 (Presieve.map_map hg)

/-! ### Part (a) of Stacks 07AJ for the inherited topologies -/

/-- **Continuity in Stacks 07AJ (a).** Let `τ` be any of the five topologies, let `C₁ ⊆ C₂` be full
subcategories of the big category over `X`, each with the topology it inherits from the big
`τ`-site over `X`, and let `C₁` satisfy the closure condition (1)(a) of the source. Then the
inclusion `C₁ ⊆ C₂` is continuous.

A covering family of `C₁` consisting of `τ`-morphisms and its image in `C₂` satisfy literally the
same sheaf condition, and such families generate the inherited topology because every covering
sieve of the big `τ`-site is refined by one. -/
theorem isContinuous_ιOfLE_baseOverTopology (τ : CoveringTopology)
    {P₁ P₂ : ObjectProperty (BigFppfOver B X hX)} (h₁₂ : P₁ ≤ P₂)
    (hcov₁ : IsClosedUnderCoverings τ P₁) :
    (ObjectProperty.ιOfLE h₁₂).IsContinuous
      (P₁.ι.inheritedTopology (BigFppfOver.baseOverTopology B X hX τ.toSiteKind))
      (P₂.ι.inheritedTopology (BigFppfOver.baseOverTopology B X hX τ.toSiteKind)) := by
  obtain ⟨h₁, h₂, h₃⟩ := coveringMorphismProperty_instances.{t} τ
  exact ObjectProperty.isContinuous_ιOfLE_inheritedTopology
    (Q := bigFppfOverCoveringMorphismProperty τ B X hX) (fun _ _ _ g f _ ↦ inferInstance)
    (fun _ _ f hf hU ↦ hcov₁.of_coveringMorphismProperty f hf hU)
    (isRefinableBy_baseOverTopology τ) h₁₂

/-- **Cocontinuity in Stacks 07AJ (a).** In the situation of
`AlgebraicGeometry.isContinuous_ιOfLE_baseOverTopology`, with the closure condition (1)(a) of the
source for both full subcategories, the inclusion `C₁ ⊆ C₂` is cocontinuous.

A covering sieve of `C₂` has a covering image downstairs, and the sieve that image pulls back to
in `C₁` is covering because the closure condition puts the sources of a refining family of
`τ`-morphisms in `C₁`. -/
theorem isCocontinuous_ιOfLE_baseOverTopology (τ : CoveringTopology)
    {P₁ P₂ : ObjectProperty (BigFppfOver B X hX)} (h₁₂ : P₁ ≤ P₂)
    (hcov₁ : IsClosedUnderCoverings τ P₁) (hcov₂ : IsClosedUnderCoverings τ P₂) :
    (ObjectProperty.ιOfLE h₁₂).IsCocontinuous
      (P₁.ι.inheritedTopology (BigFppfOver.baseOverTopology B X hX τ.toSiteKind))
      (P₂.ι.inheritedTopology (BigFppfOver.baseOverTopology B X hX τ.toSiteKind)) := by
  obtain ⟨h₁, h₂, h₃⟩ := coveringMorphismProperty_instances.{t} τ
  exact ObjectProperty.isCocontinuous_ιOfLE_inheritedTopology
    (Q := bigFppfOverCoveringMorphismProperty τ B X hX) (fun _ _ _ g f _ ↦ inferInstance)
    (fun _ _ f hf hU ↦ hcov₁.of_coveringMorphismProperty f hf hU)
    (fun _ _ f hf hU ↦ hcov₂.of_coveringMorphismProperty f hf hU)
    (isRefinableBy_baseOverTopology τ) h₁₂

/-- **Stacks 07AJ (a).** Let `τ` be any of the Zariski, étale, smooth, syntomic and fppf
topologies, and let `C₁ ⊆ C₂` be full subcategories of the big category over `X`, each with the
topology it inherits from the big `τ`-site over `X`, both satisfying the closure condition (1)(a)
of the source. Then the inclusion `C₁ ⊆ C₂` is fully faithful, continuous and cocontinuous.

Full faithfulness holds for any inclusion of full subcategories; continuity and cocontinuity are
`AlgebraicGeometry.isContinuous_ιOfLE_baseOverTopology` and
`AlgebraicGeometry.isCocontinuous_ιOfLE_baseOverTopology`. -/
@[stacks 07AJ "part (a), at the inherited topologies, for every τ"]
theorem fullyFaithful_isContinuous_isCocontinuous_ιOfLE_baseOverTopology (τ : CoveringTopology)
    {P₁ P₂ : ObjectProperty (BigFppfOver B X hX)} (h₁₂ : P₁ ≤ P₂)
    (hcov₁ : IsClosedUnderCoverings τ P₁) (hcov₂ : IsClosedUnderCoverings τ P₂) :
    (ObjectProperty.ιOfLE h₁₂).Full ∧ (ObjectProperty.ιOfLE h₁₂).Faithful ∧
      (ObjectProperty.ιOfLE h₁₂).IsContinuous
        (P₁.ι.inheritedTopology (BigFppfOver.baseOverTopology B X hX τ.toSiteKind))
        (P₂.ι.inheritedTopology (BigFppfOver.baseOverTopology B X hX τ.toSiteKind)) ∧
      (ObjectProperty.ιOfLE h₁₂).IsCocontinuous
        (P₁.ι.inheritedTopology (BigFppfOver.baseOverTopology B X hX τ.toSiteKind))
        (P₂.ι.inheritedTopology (BigFppfOver.baseOverTopology B X hX τ.toSiteKind)) :=
  ⟨(ObjectProperty.fullyFaithfulιOfLE h₁₂).full, (ObjectProperty.fullyFaithfulιOfLE h₁₂).faithful,
    isContinuous_ιOfLE_baseOverTopology τ h₁₂ hcov₁,
    isCocontinuous_ιOfLE_baseOverTopology τ h₁₂ hcov₁ hcov₂⟩

/-- **The structure sheaf of a full subcategory of the big category over `X`.** The structure
presheaf of abelian groups restricted to a full subcategory satisfying the closure condition
(1)(a) of Stacks 07AJ is a sheaf for the topology inherited from the big `τ`-site: the structure
presheaf of the big fppf category over `X` is a sheaf of rings (**Stacks 03DU**), hence of abelian
groups, hence a sheaf for the coarser topology of `τ`, and the inclusion of the full subcategory
is continuous, so restriction along it carries sheaves to sheaves. -/
theorem isSheaf_inheritedTopology_bigOverPresheafAb (τ : CoveringTopology)
    {P : ObjectProperty (BigFppfOver B X hX)} (hcov : IsClosedUnderCoverings τ P) :
    Presheaf.IsSheaf
      (P.ι.inheritedTopology (BigFppfOver.baseOverTopology B X hX τ.toSiteKind))
      (P.ι.op ⋙ bigOverPresheafAb B X hX) := by
  obtain ⟨h₁, h₂, h₃⟩ := coveringMorphismProperty_instances.{t} τ
  have : P.ι.IsContinuous
      (P.ι.inheritedTopology (BigFppfOver.baseOverTopology B X hX τ.toSiteKind))
      (BigFppfOver.baseOverTopology B X hX τ.toSiteKind) :=
    ObjectProperty.isContinuous_ι_inheritedTopology
      (Q := bigFppfOverCoveringMorphismProperty τ B X hX) (fun _ _ _ g f _ ↦ inferInstance)
      (fun _ _ f hf hU ↦ hcov.of_coveringMorphismProperty f hf hU)
      (isRefinableBy_baseOverTopology τ)
  refine P.ι.op_comp_isSheaf
    (P.ι.inheritedTopology (BigFppfOver.baseOverTopology B X hX τ.toSiteKind))
    (BigFppfOver.baseOverTopology B X hX τ.toSiteKind) ⟨bigOverPresheafAb B X hX, ?_⟩
  have hfppf := GrothendieckTopology.HasSheafCompose.isSheaf
    (F := forget₂ RingCat AddCommGrpCat) _ (BigFppfOver.structure_isSheaf B X hX)
  exact fun E ↦ Presieve.isSheaf_of_le _
    (BigFppfOver.baseOverTopology_le_fppf B X hX τ.toSiteKind) (hfppf E)

/-! ### The whole big category over `X` satisfies all three conditions -/

/-- The whole big category over `X` satisfies the closure condition (1)(a). -/
theorem isClosedUnderCoverings_top (τ : CoveringTopology) :
    IsClosedUnderCoverings τ (⊤ : ObjectProperty (BigFppfOver B X hX)) :=
  fun _ _ _ _ _ ↦ trivial

/-- The affine line over an object of the big fppf category over `X` is again an object of it:
the structure morphism of the affine line is affine, hence quasi-compact, and locally of finite
presentation, hence locally of finite type, so the size of the affine line is below the site's
cutoff with that of its base (**Stacks 000J**). -/
theorem contains_affineSpace_punit (U : BigFppfOver B X hX) :
    B.Contains 𝔸(PUnit.{t + 1}; (BigFppfOver.toScheme B X hX).obj U) :=
  Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
    (𝔸(PUnit.{t + 1}; (BigFppfOver.toScheme B X hX).obj U) ↘
      (BigFppfOver.toScheme B X hX).obj U) U.left.property

/-- The whole big fppf category over `X` satisfies the closure condition (1)(b): the affine line
over one of its objects is again one of its objects, with the composite of the projection and the
structure morphism as its structure morphism. -/
theorem isClosedUnderAffineLine_top :
    IsClosedUnderAffineLine (⊤ : ObjectProperty (BigFppfOver B X hX)) := fun U _ ↦
  ⟨BigFppfOver.mk B X hX (contains_affineSpace_punit U)
      ((𝔸(PUnit.{t + 1}; (BigFppfOver.toScheme B X hX).obj U) ↘
        (BigFppfOver.toScheme B X hX).obj U) ≫ BigFppfOver.str B X hX U),
    Iso.refl _, Category.id_comp _, trivial⟩

/-- The whole big fppf category over `X` satisfies the condition (2): it contains the base object
`X/X`. Together with the two lemmas above, the three conditions of Stacks 07AJ are satisfiable,
so the statements below are not vacuous. -/
theorem top_base_obj : (⊤ : ObjectProperty (BigFppfOver B X hX)) (Over.mk (𝟙 (B.obj hX))) :=
  trivial

/-! ### Part (b) of Stacks 07AJ for the inherited topologies -/

/-- **Stacks 07AJ (b).** Let `τ` be any of the Zariski, étale, smooth, syntomic and fppf
topologies, and let `C₁ ⊆ C₂` be full subcategories of the big category over a scheme `X`, each
with the topology it inherits from the big `τ`-site over `X`, both satisfying the closure
condition (1)(a) of the source, and let `C₁` contain the base object `X/X` and the affine line
over each of its objects — conditions (2) and (1)(b). Writing `g : Sh(C₁) ⟶ Sh(C₂)` for the
morphism of topoi of the inclusion, the canonical map `g_!O₁ ⟶ O₂` from the lower shriek of the
restriction of the structure sheaf to the structure sheaf is an isomorphism.

The continuity of the inclusion that `g` and `g_!` refer to is
`AlgebraicGeometry.isContinuous_ιOfLE_baseOverTopology`; the existence of `g_!` is instance
search on the essential smallness of the two sites; the descent witness for the structure
presheaf of `C₂` is `AlgebraicGeometry.isSheaf_inheritedTopology_bigOverPresheafAb`. With those
three supplied, the assertion is
`AlgebraicGeometry.isIso_lowerShriekStructureSheafHom_of_isClosedUnderAffineLine` read at the
inherited topologies. -/
@[stacks 07AJ "part (b), at the inherited topologies, for every τ"]
theorem isIso_lowerShriekStructureSheafHom_baseOverTopology (τ : CoveringTopology)
    {P₁ P₂ : ObjectProperty (BigFppfOver B X hX)} (h₁₂ : P₁ ≤ P₂)
    (hcov₁ : IsClosedUnderCoverings τ P₁) (hcov₂ : IsClosedUnderCoverings τ P₂)
    (hbase : P₁ (Over.mk (𝟙 (B.obj hX)))) (hline : IsClosedUnderAffineLine P₁) :
    letI : (ObjectProperty.ιOfLE h₁₂).IsContinuous
        (P₁.ι.inheritedTopology (BigFppfOver.baseOverTopology B X hX τ.toSiteKind))
        (P₂.ι.inheritedTopology (BigFppfOver.baseOverTopology B X hX τ.toSiteKind)) :=
      isContinuous_ιOfLE_baseOverTopology τ h₁₂ hcov₁
    IsIso (lowerShriekStructureSheafHom h₁₂
      (P₁.ι.inheritedTopology (BigFppfOver.baseOverTopology B X hX τ.toSiteKind))
      (P₂.ι.inheritedTopology (BigFppfOver.baseOverTopology B X hX τ.toSiteKind))
      (isSheaf_inheritedTopology_bigOverPresheafAb τ hcov₂)) :=
  let := isContinuous_ιOfLE_baseOverTopology τ h₁₂ hcov₁
  isIso_lowerShriekStructureSheafHom_of_isClosedUnderAffineLine h₁₂ _ _ _ hbase hline

/-- **Stacks 07AJ (b) for the whole big category over `X`.** The three conditions of the source
hold for `C₁ = C₂ =` the big category over `X` itself, so the theorem above applies to it; this
records that its conditions are satisfiable, for every `τ`. -/
theorem isIso_lowerShriekStructureSheafHom_baseOverTopology_top (τ : CoveringTopology) :
    letI : (ObjectProperty.ιOfLE (le_refl (⊤ : ObjectProperty (BigFppfOver B X hX)))).IsContinuous
        ((⊤ : ObjectProperty (BigFppfOver B X hX)).ι.inheritedTopology
          (BigFppfOver.baseOverTopology B X hX τ.toSiteKind))
        ((⊤ : ObjectProperty (BigFppfOver B X hX)).ι.inheritedTopology
          (BigFppfOver.baseOverTopology B X hX τ.toSiteKind)) :=
      isContinuous_ιOfLE_baseOverTopology τ _ (isClosedUnderCoverings_top τ)
    IsIso (lowerShriekStructureSheafHom (le_refl (⊤ : ObjectProperty (BigFppfOver B X hX)))
      ((⊤ : ObjectProperty (BigFppfOver B X hX)).ι.inheritedTopology
        (BigFppfOver.baseOverTopology B X hX τ.toSiteKind))
      ((⊤ : ObjectProperty (BigFppfOver B X hX)).ι.inheritedTopology
        (BigFppfOver.baseOverTopology B X hX τ.toSiteKind))
      (isSheaf_inheritedTopology_bigOverPresheafAb τ (isClosedUnderCoverings_top τ))) :=
  isIso_lowerShriekStructureSheafHom_baseOverTopology τ _ (isClosedUnderCoverings_top τ)
    (isClosedUnderCoverings_top τ) top_base_obj isClosedUnderAffineLine_top

end AlgebraicGeometry

end
