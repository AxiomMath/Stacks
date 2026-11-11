module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.EtalePhCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.PhCoveringProperSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDescentSchemeTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDescentSurjective

/-!
# Descent of étale sheaves along a surjective proper morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is surjective and
integral, or surjective and proper, or surjective, flat and locally of finite presentation. Then
sheaves on the spaces-étale site of `Y` are equivalent, through the canonical descent datum, to
descent data for `{X ⟶ Y}`.

## Main definitions

* `AlgebraicGeometry.Space.ProperSurjectiveDescentOver`: effective descent of spaces-étale sheaves
  along every surjective proper morphism with a given target.

## Main results

* `AlgebraicGeometry.Space.properSurjectiveDescentOver_of_isAffine`: the case of an affine target.
* `AlgebraicGeometry.Space.properSurjectiveDescentOver_of_isEtaleCovering`: descent along proper
  surjections is étale local on the target.
* `AlgebraicGeometry.Space.properSurjectiveDescentOver_of_isSeparated`,
  `AlgebraicGeometry.Space.properSurjectiveDescentOver_schemeSpace`: the cases of a target
  represented by a separated scheme and by any scheme.
* `AlgebraicGeometry.Space.descentEffectiveAlongProperSurjective`: spaces-étale sheaves descend
  effectively along every surjective proper morphism of algebraic spaces.
* `Space.isEquivalence_toDescentData_singleton_of_isSurjectiveIntegralProperOrFlatLfp`: descent
  along `f` surjective and integral, proper, or flat and locally of finite presentation.

## References

* [Stacks Project, Tag 0GFW](https://stacks.math.columbia.edu/tag/0GFW)
* [Stacks Project, Tag 0GFV](https://stacks.math.columbia.edu/tag/0GFV)
* [Stacks Project, Tag 0GFT](https://stacks.math.columbia.edu/tag/0GFT)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Effective descent of spaces-étale sheaves along every surjective proper morphism with target
`Z`. -/
abbrev ProperSurjectiveDescentOver (Z : AlgebraicSpaces B S hS) : Prop :=
  ∀ ⦃X : AlgebraicSpaces B S hS⦄ (f : X ⟶ Z), IsSurjective B S hS f.hom →
    IsProper B S hS f.hom →
    ((spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit => f)).IsEquivalence

/-- Effective descent along surjective proper morphisms with a given target transfers along an
isomorphism of the target. -/
theorem ProperSurjectiveDescentOver.of_iso {Z Z' : AlgebraicSpaces B S hS} (e : Z ≅ Z')
    (h : ProperSurjectiveDescentOver B S hS Z) : ProperSurjectiveDescentOver B S hS Z' := by
  intro X f hs hp
  refine Pseudofunctor.isEquivalence_toDescentData_singleton_of_arrowIso _ (f ≫ e.inv) f
    (Iso.refl X) e.symm (by simp) (h _ ?_ ?_)
  · exact isSurjective_comp B S hS hs (isSurjective_of_isIso B S hS e.inv.hom)
  · exact (isProper_comp_isIso_iff B S hS f.hom e.inv.hom).2 hp

/-- Spaces-étale sheaves descend effectively along every surjective proper morphism whose target is
represented by an affine object of the site. -/
theorem properSurjectiveDescentOver_of_isAffine (U : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)) :
    ProperSurjectiveDescentOver B S hS ((schemeSpaceFunctor B S hS).obj U) := by
  intro X f hs hp
  obtain ⟨V, ρ, hρp, hρs⟩ := exists_properSurjective_schemeCover_of_isProper_toAffine B S hS U hU
    X.property f.hom hp
  let π : (schemeSpaceFunctor B S hS).obj V ⟶ X := ObjectProperty.homMk ρ
  refine isEquivalence_toDescentData_singleton_of_relativelyRepresentable_comp B S hS π f
    (relativelyRepresentable_of_yonedaSpace_comp B S hS
      ((schemeSpaceFunctor B S hS).obj U).property (ρ ≫ f.hom)) ?_
  exact Or.inr (Or.inl ⟨isSurjective_comp B S hS hρs hs,
    isProper_comp B S hS (isAlgebraicSpace_yoneda B S hS V) X.property
      ((schemeSpaceFunctor B S hS).obj U).property ρ f.hom hρp hp⟩)

/-- **Descent along surjective proper morphisms is étale local on the target.** If
`{g i : Y i ⟶ Y}` is an étale covering and spaces-étale sheaves descend effectively along every
surjective proper morphism with target `Y i` or `Y i ×_Y Y j`, they descend effectively along every
surjective proper morphism with target `Y`. -/
theorem properSurjectiveDescentOver_of_isEtaleCovering {I : Type u} {Y : AlgebraicSpaces B S hS}
    (Ycov : I → AlgebraicSpaces B S hS) (g : ∀ i, Ycov i ⟶ Y)
    (hg : IsEtaleCovering B S hS (fun i => (Ycov i).1) (fun i => (g i).hom))
    (hY : ∀ i, ProperSurjectiveDescentOver B S hS (Ycov i))
    (hYY : ∀ i j, ProperSurjectiveDescentOver B S hS
      (spacesChosenPullback B S hS (g i) (g j)).pullback) :
    ProperSurjectiveDescentOver B S hS Y := by
  intro X f hs hp
  have hbc : ∀ {Z : AlgebraicSpaces B S hS} (h : Z ⟶ Y),
      IsSurjective B S hS (spacesChosenPullback B S hS f h).p₂.hom ∧
        IsProper B S hS (spacesChosenPullback B S hS f h).p₂.hom := fun h ↦
    ⟨isSurjective_of_isPullback B S hS (spacesChosenPullback B S hS f h).isPullback hs,
      (isProper_isStableUnderBaseChange B S hS).of_isPullback
        (spacesChosenPullback B S hS f h).isPullback hp⟩
  exact isEquivalence_toDescentData_singleton_of_isEtaleCovering B S hS f Ycov g hg
    (fun i ↦ hY i _ (hbc (g i)).1 (hbc (g i)).2)
    (fun i j ↦ hYY i j _ (hbc _).1 (hbc _).2)

/-- The algebraic space fibre product of the algebraic spaces represented by two morphisms of the
site with common target is the algebraic space represented by their fibre product. -/
def spacesChosenPullbackSchemeSpaceIso {V₁ V₂ W : BigFppfOver B S hS} (a : V₁ ⟶ W)
    (b : V₂ ⟶ W) :
    (schemeSpaceFunctor B S hS).obj (pullback a b) ≅
      (spacesChosenPullback B S hS ((schemeSpaceFunctor B S hS).map a)
        ((schemeSpaceFunctor B S hS).map b)).pullback :=
  ObjectProperty.isoMk _ (PreservesPullback.iso yoneda a b)

/-- An affine open covering of the scheme underlying an object of the site, as an étale covering of
the represented algebraic space by represented affine algebraic spaces along open immersions. -/
theorem exists_affine_open_isEtaleCovering (W : BigFppfOver B S hS) :
    ∃ (I : Type u) (V : I → BigFppfOver B S hS) (π : ∀ i, V i ⟶ W),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (V i))) ∧
      (∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map (π i))) ∧
      IsEtaleCovering B S hS (fun i ↦ ((schemeSpaceFunctor B S hS).obj (V i)).1)
        (fun i ↦ ((schemeSpaceFunctor B S hS).map (π i)).hom) := by
  obtain ⟨I, V, π, haff, hopen, -, hsurj⟩ := BigFppfOver.exists_affine_open_cover' B S hS W
  exact ⟨I, V, π, haff, hopen,
    isEtaleCovering_yoneda_of_etale B S hS V π (fun i ↦ have := hopen i; inferInstance) hsurj⟩

/-- Descent along surjective proper morphisms to the space represented by `W` follows from descent
to the spaces represented by the pairwise fibre products of an affine open covering of `W`. -/
private theorem properSurjectiveDescentOver_schemeSpace_of_pullbacks (W : BigFppfOver B S hS)
    (h : ∀ {V₁ V₂ : BigFppfOver B S hS} (a : V₁ ⟶ W) (b : V₂ ⟶ W),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V₁) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj V₂) →
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map b) →
      ProperSurjectiveDescentOver B S hS ((schemeSpaceFunctor B S hS).obj (pullback a b))) :
    ProperSurjectiveDescentOver B S hS ((schemeSpaceFunctor B S hS).obj W) := by
  obtain ⟨I, V, π, haff, hopen, hg⟩ := exists_affine_open_isEtaleCovering B S hS W
  exact properSurjectiveDescentOver_of_isEtaleCovering B S hS _
    (fun i ↦ (schemeSpaceFunctor B S hS).map (π i)) hg
    (fun i ↦ properSurjectiveDescentOver_of_isAffine B S hS (V i) (haff i))
    fun i j ↦ ProperSurjectiveDescentOver.of_iso B S hS
      (spacesChosenPullbackSchemeSpaceIso B S hS (π i) (π j)) (h _ _ (haff i) (haff j) (hopen j))

/-- Spaces-étale sheaves descend effectively along every surjective proper morphism whose target is
represented by an object of the site whose underlying scheme is separated. -/
theorem properSurjectiveDescentOver_of_isSeparated (W : BigFppfOver B S hS)
    (hW : ((BigFppfOver.toScheme B S hS).obj W).IsSeparated) :
    ProperSurjectiveDescentOver B S hS ((schemeSpaceFunctor B S hS).obj W) := by
  refine properSurjectiveDescentOver_schemeSpace_of_pullbacks B S hS W fun a b ha hb _ ↦
    properSurjectiveDescentOver_of_isAffine B S hS _ ?_
  have : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map b) :=
    _root_.AlgebraicGeometry.IsAffineHom.of_comp _
      (terminal.from ((BigFppfOver.toScheme B S hS).obj W))
  exact IsAffine.of_isIso (PreservesPullback.iso (BigFppfOver.toScheme B S hS) a b).hom

/-- Spaces-étale sheaves descend effectively along every surjective proper morphism whose target is
represented by an object of the site. -/
theorem properSurjectiveDescentOver_schemeSpace (W : BigFppfOver B S hS) :
    ProperSurjectiveDescentOver B S hS ((schemeSpaceFunctor B S hS).obj W) := by
  refine properSurjectiveDescentOver_schemeSpace_of_pullbacks B S hS W fun a b ha _ hb ↦
    properSurjectiveDescentOver_of_isSeparated B S hS _ ?_
  have hfst : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (pullback.fst a b)) := by
    rw [← PreservesPullback.iso_hom_fst (BigFppfOver.toScheme B S hS) a b]
    infer_instance
  refine ⟨?_⟩
  rw [show terminal.from ((BigFppfOver.toScheme B S hS).obj (pullback a b)) =
      (BigFppfOver.toScheme B S hS).map (pullback.fst a b) ≫
        terminal.from ((BigFppfOver.toScheme B S hS).obj _) from terminal.hom_ext _ _]
  infer_instance

/-- Spaces-étale sheaves descend effectively along every surjective proper morphism of algebraic
spaces over `S`. -/
@[sga "4 VIII 9.4" "more general"]
theorem descentEffectiveAlongProperSurjective : DescentEffectiveAlongProperSurjective B S hS := by
  intro X Y f hs hp
  obtain ⟨T, a, hasurj, haetale⟩ := Y.property.exists_atlas
  have hg : IsEtaleCovering B S hS
      (fun _ : PUnit.{u + 1} => ((schemeSpaceFunctor B S hS).obj T).1)
      (fun _ => (ObjectProperty.homMk a : (schemeSpaceFunctor B S hS).obj T ⟶ Y).hom) :=
    isEtaleCovering_atlas.{u, u} B S hS Y.property hasurj haetale
  refine properSurjectiveDescentOver_of_isEtaleCovering B S hS _ _ hg
    (fun _ ↦ properSurjectiveDescentOver_schemeSpace B S hS T) (fun _ _ ↦ ?_) f hs hp
  have := isRepresentable_pullback_of_yoneda B S hS a a
  exact ProperSurjectiveDescentOver.of_iso B S hS
    (ObjectProperty.isoMk _ (pullback a a).reprW)
    (properSurjectiveDescentOver_schemeSpace B S hS _)

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is surjective and integral, or
surjective and proper, or surjective, flat and locally of finite presentation. Then the functor
from sheaves on the spaces-étale site of `Y` to descent data for étale sheaves with respect to
`{X ⟶ Y}` is an equivalence of categories.

The proof applies the three-case analysis
`Space.isEquivalence_toDescentData_singleton_of_isSurjectiveDescentMorphism`, which is untagged,
to Stacks 0GFV (`Space.isEquivalence_toDescentData_singleton_of_relativelyRepresentable_comp`)
and to the proper case (`Space.descentEffectiveAlongProperSurjective`). -/
@[stacks 0GFW]
theorem isEquivalence_toDescentData_singleton_of_isSurjectiveIntegralProperOrFlatLfp
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsSurjectiveIntegralProperOrFlatLfp B S hS f) :
    ((spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit => f)).IsEquivalence :=
  isEquivalence_toDescentData_singleton_of_isSurjectiveDescentMorphism B S hS
    (fun π g hrep hcov ↦
      isEquivalence_toDescentData_singleton_of_relativelyRepresentable_comp B S hS π g hrep hcov)
    (descentEffectiveAlongProperSurjective B S hS) f hf

end AlgebraicGeometry.Space

end
