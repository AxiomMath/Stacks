module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.IdentityMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfSite
public import StacksFrontier.CategoryTheory.Sites.Pretopology.SmallSubsiteIndexUniverse

/-!
# A big fppf site of algebraic spaces over a big étale site

The fppf covering families of algebraic spaces over a scheme `S` satisfy the site axioms
(isomorphisms, composition and base change, Stacks 03Y9), so Stacks 000X bounds them by a
cardinal. This gives, for every big étale site `E` of algebraic spaces over `S`, a big fppf site
of algebraic spaces over `S` built on the same big fppf site of schemes as `E`.

## Main results

* `AlgebraicGeometry.Space.isSite_isFppfCoveringFamily`: the fppf covering families of algebraic
  spaces form a site.
* `AlgebraicGeometry.BigEtaleSpaceSite.bigFppfSpaceSite`: a big fppf site of algebraic spaces
  whose big fppf site of schemes is the one of `E`
  (`AlgebraicGeometry.BigEtaleSpaceSite.bigFppfSpaceSite_schemeSite`).

## References

* [Stacks Project, Tag 000X](https://stacks.math.columbia.edu/tag/000X)
* [Stacks Project, Tag 03Y9](https://stacks.math.columbia.edu/tag/03Y9)
* [Stacks Project, Tag 0DBV](https://stacks.math.columbia.edu/tag/0DBV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-- A class of covering families contains a family pushed forward along the identification
`eqToHom h` of its target with an equal object as soon as it contains the family itself. -/
theorem CategoryTheory.Covering.isCov_pushforward_eqToHom {C : Type*} [Category C]
    (IsCov : Covering C → Prop) {U U' : C} (E : PreZeroHypercover U) (h : U = U')
    (hE : IsCov ⟨U, E⟩) : IsCov ⟨U', E.pushforward (eqToHom h)⟩ := by
  subst h
  simpa [PreZeroHypercover.pushforward] using hE

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The fppf covering families of algebraic spaces satisfy the site axioms of Stacks 000X**:
an isomorphism is flat, locally of finite presentation and surjective, and fppf coverings are
stable under composition and base change (Stacks 03Y9). -/
theorem isSite_isFppfCoveringFamily : IsSite (IsFppfCoveringFamily B S hS) := by
  refine ⟨fun {U V} f _ ↦ ?_, fun 𝒰 h𝒰 𝒱 h𝒱 h ↦ ?_, fun 𝒰 h𝒰 V g ↦ ?_⟩
  · have : IsIso f.hom := (ObjectProperty.ι _).map_isIso f
    have sq : IsPullback f f (𝟙 U) (𝟙 U) := IsPullback.of_vert_isIso ⟨rfl⟩
    exact ⟨U.property, fun _ ↦ V.property,
      fun _ ↦ (isFlat_isStableUnderBaseChange B S hS).of_isPullback sq
        (isFlat_id B S hS U.property),
      fun _ ↦ (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq
        (isLocallyOfFinitePresentation_id B S hS U.property),
      Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr
        ⟨PUnit.unit, pointsMap_surjective_of_isIso B S hS f.hom x⟩⟩
  · exact isFppfCovering_comp B S hS _ (fun i ↦ (𝒱 i).2.I₀) _ _ _ _ h𝒰
      (fun i ↦ Covering.isCov_pushforward_eqToHom _ (𝒱 i).2 (h i) (h𝒱 i))
  · refine ⟨fun i ↦ AlgebraicSpaces.fiberProduct B S hS g (𝒰.2.f i),
      fun i ↦ ObjectProperty.homMk (pullback.snd g.hom (𝒰.2.f i).hom),
      fun i ↦ ObjectProperty.homMk (pullback.fst g.hom (𝒰.2.f i).hom),
      fun i ↦ (AlgebraicSpaces.isPullback_fiberProduct B S hS g (𝒰.2.f i)).flip, ?_⟩
    exact isFppfCovering_fibreProduct B S hS 𝒰.2.X 𝒰.2.f g h𝒰

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}}

/-- Stacks 000X for the fppf covering families of the algebraic spaces of a big étale site,
with index sets in the universe used by big fppf sites of algebraic spaces. -/
theorem exists_covBounded_isSite_isFppfCoveringFamily (E : BigEtaleSpaceSite S) :
    ∃ (κ : Cardinal.{u + 2}) (α : Ordinal.{u + 2}), Order.IsSuccLimit α ∧
      (∀ 𝒰 ∈ (∅ : Set (Covering.{_, _, u + 2} (AlgebraicSpaces E.fppfSite S E.fppf_mem))),
        CovBounded (Space.IsFppfCoveringFamily E.fppfSite S E.fppf_mem) κ 𝒰) ∧
      IsSite (CovBounded (Space.IsFppfCoveringFamily E.fppfSite S E.fppf_mem) κ) ∧
      (∀ 𝒰 : Covering (AlgebraicSpaces E.fppfSite S E.fppf_mem),
        Space.IsFppfCoveringFamily E.fppfSite S E.fppf_mem 𝒰 →
          ∃ 𝒰', CovBounded (Space.IsFppfCoveringFamily E.fppfSite S E.fppf_mem) κ 𝒰' ∧
            Covering.CombEquiv 𝒰 𝒰') :=
  exists_covBounded_isSite_of_univ.{_, _, u + 2}
    (Space.IsFppfCoveringFamily E.fppfSite S E.fppf_mem)
    (Space.isSite_isFppfCoveringFamily E.fppfSite S E.fppf_mem) ∅ (by intro U hU; cases hU)

/-- **A big fppf site of algebraic spaces over the same big fppf site of schemes as `E`**, with
no initial coverings and the covering bound of Stacks 000X. -/
noncomputable def bigFppfSpaceSite (E : BigEtaleSpaceSite S) : BigFppfSpaceSite S :=
  let h := exists_covBounded_isSite_isFppfCoveringFamily E
  { schemeSite := E.fppfSite
    scheme_mem := E.fppf_mem
    initialCoverings := ∅
    initialCoverings_small := inferInstance
    initialCoverings_fppf := by simp
    coveringBound := h.choose
    coveringOrdinal := h.choose_spec.choose
    coveringOrdinal_isSuccLimit := h.choose_spec.choose_spec.1
    initialCoverings_bounded := by simp
    coverings_isSite := h.choose_spec.choose_spec.2.2.1
    covering_representative := h.choose_spec.choose_spec.2.2.2 }

/-- The big fppf site of schemes of `E.bigFppfSpaceSite` is the one of `E`. -/
theorem bigFppfSpaceSite_schemeSite (E : BigEtaleSpaceSite S) :
    E.bigFppfSpaceSite.schemeSite = E.fppfSite :=
  rfl

end AlgebraicGeometry.BigEtaleSpaceSite

end
