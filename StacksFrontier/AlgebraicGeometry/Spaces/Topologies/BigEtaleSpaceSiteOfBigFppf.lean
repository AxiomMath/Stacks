module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfSpaceSiteOfBigEtale
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.EtaleSiteOfFppfSite
public import StacksFrontier.CategoryTheory.Sites.Pretopology.SmallSubsiteIndexUniverse

/-!
# A big étale site of algebraic spaces over a big fppf site

The étale covering families of algebraic spaces over a scheme `S` satisfy the site axioms
(isomorphisms, composition and base change, Stacks 041F), so Stacks 000X bounds them by a
cardinal. This gives, for every big fppf site `T` of algebraic spaces over `S`, a big étale site
of algebraic spaces over `S` whose algebraic spaces are those of `T`.

## Main results

* `AlgebraicGeometry.Space.isSite_isEtaleCoveringFamily`: the étale covering families of
  algebraic spaces form a site.
* `AlgebraicGeometry.BigFppfSpaceSite.bigEtaleSpaceSite`: a big étale site of algebraic spaces
  whose auxiliary big fppf site of schemes is the one of `T`
  (`AlgebraicGeometry.BigFppfSpaceSite.bigEtaleSpaceSite_fppfSite`), and whose big étale site of
  schemes is `AlgebraicGeometry.bigEtaleSiteOfFppfSite` of it.

## References

* [Stacks Project, Tag 000X](https://stacks.math.columbia.edu/tag/000X)
* [Stacks Project, Tag 041F](https://stacks.math.columbia.edu/tag/041F)
* [Stacks Project, Tag 0DBX](https://stacks.math.columbia.edu/tag/0DBX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The étale covering families of algebraic spaces satisfy the site axioms of Stacks 000X**:
an isomorphism is étale and surjective, and étale coverings are stable under composition and
base change (Stacks 041F). -/
theorem isSite_isEtaleCoveringFamily : IsSite (IsEtaleCoveringFamily B S hS) := by
  refine ⟨fun {U V} f _ ↦ ?_, fun 𝒰 h𝒰 𝒱 h𝒱 h ↦ ?_, fun 𝒰 h𝒰 V g ↦ ?_⟩
  · have : IsIso f.hom := (ObjectProperty.ι _).map_isIso f
    exact ⟨U.property, fun _ ↦ V.property, fun _ ↦ isEtale_of_isIso B S hS f.hom,
      Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr
        ⟨PUnit.unit, pointsMap_surjective_of_isIso B S hS f.hom x⟩⟩
  · exact isEtaleCovering_comp B S hS (fun i ↦ (𝒱 i).2.I₀) _ _ _ _ h𝒰
      (fun i ↦ Covering.isCov_pushforward_eqToHom _ (𝒱 i).2 (h i) (h𝒱 i))
  · exact ⟨fun i ↦ AlgebraicSpaces.fiberProduct B S hS g (𝒰.2.f i),
      fun i ↦ ObjectProperty.homMk (pullback.snd g.hom (𝒰.2.f i).hom),
      fun i ↦ ObjectProperty.homMk (pullback.fst g.hom (𝒰.2.f i).hom),
      fun i ↦ (AlgebraicSpaces.isPullback_fiberProduct B S hS g (𝒰.2.f i)).flip,
      isEtaleCovering_pullback B S hS g.hom V.property _ _ h𝒰⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}}

/-- Stacks 000X for the étale covering families of the algebraic spaces of a big fppf site,
with index sets in the universe used by big étale sites of algebraic spaces. -/
theorem exists_covBounded_isSite_isEtaleCoveringFamily (T : BigFppfSpaceSite S) :
    ∃ (κ : Cardinal.{u + 2}) (α : Ordinal.{u + 2}), Order.IsSuccLimit α ∧
      (∀ 𝒰 ∈ (∅ : Set (Covering.{_, _, u + 2} T.Spaces)),
        CovBounded (Space.IsEtaleCoveringFamily T.schemeSite S T.scheme_mem) κ 𝒰) ∧
      IsSite (CovBounded (Space.IsEtaleCoveringFamily T.schemeSite S T.scheme_mem) κ) ∧
      (∀ 𝒰 : Covering T.Spaces,
        Space.IsEtaleCoveringFamily T.schemeSite S T.scheme_mem 𝒰 →
          ∃ 𝒰', CovBounded (Space.IsEtaleCoveringFamily T.schemeSite S T.scheme_mem) κ 𝒰' ∧
            Covering.CombEquiv 𝒰 𝒰') :=
  exists_covBounded_isSite_of_univ.{_, _, u + 2}
    (Space.IsEtaleCoveringFamily T.schemeSite S T.scheme_mem)
    (Space.isSite_isEtaleCoveringFamily T.schemeSite S T.scheme_mem) ∅ (by intro U hU; cases hU)

/-- **A big étale site of algebraic spaces with the same algebraic spaces as `T`**: its
auxiliary big fppf site of schemes is that of `T`, its big étale site of schemes is the one
on the same schemes (`AlgebraicGeometry.bigEtaleSiteOfFppfSite`), and it has no initial
coverings and the covering bound of Stacks 000X. -/
noncomputable def bigEtaleSpaceSite (T : BigFppfSpaceSite S) : BigEtaleSpaceSite S :=
  let h := exists_covBounded_isSite_isEtaleCoveringFamily T
  { schemeSite := bigEtaleSiteOfFppfSite T.schemeSite
    scheme_mem := T.scheme_mem
    fppfSite := T.schemeSite
    fppf_mem := T.scheme_mem
    initialCoverings := ∅
    initialCoverings_small := inferInstance
    initialCoverings_etale := by simp
    coveringBound := h.choose
    coveringOrdinal := h.choose_spec.choose
    coveringOrdinal_isSuccLimit := h.choose_spec.choose_spec.1
    initialCoverings_bounded := by simp
    coverings_isSite := h.choose_spec.choose_spec.2.2.1
    covering_representative := h.choose_spec.choose_spec.2.2.2 }

/-- The auxiliary big fppf site of schemes of `T.bigEtaleSpaceSite` is the one of `T`. -/
theorem bigEtaleSpaceSite_fppfSite (T : BigFppfSpaceSite S) :
    T.bigEtaleSpaceSite.fppfSite = T.schemeSite :=
  rfl

end AlgebraicGeometry.BigFppfSpaceSite

end
