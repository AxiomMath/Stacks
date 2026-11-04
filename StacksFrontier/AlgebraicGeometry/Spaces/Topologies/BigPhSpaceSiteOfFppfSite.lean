module

public import StacksFrontier.AlgebraicGeometry.Simplicial.PhHypercoveringSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.PhCoveringComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleSpaceSiteOfBigFppf
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.CoveringsParts0DBI
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.PhCoveringOfHom

/-!
# A big ph site of algebraic spaces over a big fppf site of schemes

The ph coverings of schemes and of algebraic spaces satisfy the site axioms (Stacks 0DBI and
Stacks 0DFJ), so Stacks 000X bounds them by a cardinal. This gives, for every big fppf site `B`
of schemes containing `S`, a big ph site of schemes on the schemes of `B` and a big ph site of
algebraic spaces over `S` whose auxiliary big fppf site of schemes is `B` itself, so that its
algebraic spaces are the algebraic spaces over `S` built on `B`, on the nose. In this way every
statement about the small étale topoi of algebraic spaces over `S` may be proved through a big
ph site of algebraic spaces, as the Stacks project does throughout Chapter 85.

## Main definitions

* `AlgebraicGeometry.BigFppfSite.bigPHSite`: a big ph site of schemes with the cutoff of `B`.
* `AlgebraicGeometry.BigFppfSite.bigPHSpaceSite`: a big ph site of algebraic spaces over `S`
  with auxiliary big fppf site `B`.

## Main results

* `AlgebraicGeometry.isSite_isPHCoveringInCutoff`: the ph covering families of the schemes of
  size below a cardinal satisfy the site axioms.
* `AlgebraicGeometry.Space.isSite_isPHCoveringFamily`: the ph covering families of algebraic
  spaces over `S` satisfy the site axioms.

## References

* [Stacks Project, Tag 000X](https://stacks.math.columbia.edu/tag/000X)
* [Stacks Project, Tag 0DBI](https://stacks.math.columbia.edu/tag/0DBI)
* [Stacks Project, Tag 0DBJ](https://stacks.math.columbia.edu/tag/0DBJ)
* [Stacks Project, Tag 0DFJ](https://stacks.math.columbia.edu/tag/0DFJ)
* [Stacks Project, Tag 0DFK](https://stacks.math.columbia.edu/tag/0DFK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The ph covering families of algebraic spaces satisfy the site axioms of Stacks 000X**: an
isomorphism is a ph covering, and ph coverings are stable under composition and base change
(Stacks 0DFJ). -/
theorem isSite_isPHCoveringFamily : IsSite (IsPHCoveringFamily B S hS) := by
  refine ⟨fun {U V} f _ ↦ ?_, fun 𝒰 h𝒰 𝒱 h𝒱 h ↦ ?_, fun 𝒰 h𝒰 V g ↦ ?_⟩
  · have : IsIso f.hom := (ObjectProperty.ι _).map_isIso f
    exact IsPHCovering.punit B S hS (isPHCovering_of_isIso B S hS f.hom U.property)
  · exact isPHCovering_comp B S hS _ _ _ _ h𝒰
      (fun i ↦ Covering.isCov_pushforward_eqToHom _ (𝒱 i).2 (h i) (h𝒱 i))
  · refine ⟨fun i ↦ AlgebraicSpaces.fiberProduct B S hS g (𝒰.2.f i),
      fun i ↦ ObjectProperty.homMk (pullback.snd g.hom (𝒰.2.f i).hom),
      fun i ↦ ObjectProperty.homMk (pullback.fst g.hom (𝒰.2.f i).hom),
      fun i ↦ (AlgebraicSpaces.isPullback_fiberProduct B S hS g (𝒰.2.f i)).flip, ?_⟩
    exact isPHCovering_baseChange B S hS _ _ g h𝒰

end AlgebraicGeometry.Space

namespace AlgebraicGeometry

open CategoryTheory.Limits

/-- **The ph covering families of the schemes of size below `κ` satisfy the site axioms**: an
isomorphism is a ph covering, and ph coverings are stable under composition and base change
(Stacks 0DBI); the fibre products of the bounded category are fibre products of schemes. -/
theorem isSite_isPHCoveringInCutoff (κ : Cardinal.{u}) :
    IsSite (IsPHCoveringInCutoff (κ := κ)) := by
  let F := schemeBelowInclusion κ
  refine ⟨fun {U V} f _ ↦ ?_, fun 𝒰 h𝒰 𝒱 h𝒱 h ↦ ?_, fun 𝒰 h𝒰 V g ↦ ?_⟩
  · have : IsIso (F.map f) := inferInstance
    exact IsPHCovering.reindex (isPHCovering_of_isIso (F.map f)) Equiv.punitEquivPUnit
  · have hV : ∀ i, IsPHCovering ((((𝒱 i).2.pushforward (eqToHom (h i))).map F).X)
        ((((𝒱 i).2.pushforward (eqToHom (h i))).map F).f) := fun i ↦
      Covering.isCov_pushforward_eqToHom (IsPHCoveringInCutoff (κ := κ)) (𝒱 i).2 (h i) (h𝒱 i)
    have hb := isPHCovering_bind (𝒰.2.map F) h𝒰 _ hV
    refine IsPHCovering.of_hom hb ⟨_root_.id, fun _ ↦ 𝟙 _, fun _ ↦ ?_⟩ fun ij ↦ ?_
    · simp [PreZeroHypercover.bind, PreZeroHypercover.map]
      rfl
    · exact hb.1 ij
  · refine ⟨fun i ↦ pullback (𝒰.2.f i) g, fun i ↦ pullback.fst _ _, fun i ↦ pullback.snd _ _,
      fun i ↦ IsPullback.of_hasPullback _ _, ?_⟩
    have hp := isPHCovering_pullback h𝒰 (F.map g)
    have sq : ∀ i, IsPullback (F.map (pullback.fst (𝒰.2.f i) g)) (F.map (pullback.snd (𝒰.2.f i) g))
        (F.map (𝒰.2.f i)) (F.map g) := fun i ↦ (IsPullback.of_hasPullback _ _).map F
    refine IsPHCovering.of_hom (E := ⟨𝒰.2.I₀, fun i ↦ pullback (F.map (𝒰.2.f i)) (F.map g),
      fun i ↦ pullback.snd _ _⟩) hp ⟨_root_.id, fun i ↦ (sq i).isoPullback.inv, fun i ↦ ?_⟩
      fun i ↦ ?_
    · exact (sq i).isoPullback_inv_snd
    · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (sq i) (h𝒰.1 i)

end AlgebraicGeometry

namespace AlgebraicGeometry.BigFppfSite

/-- **A big ph site of schemes with the cutoff of `B`** (Stacks 0DBJ): no initial schemes or
coverings, and the covering bound of Stacks 000X. -/
def bigPHSite (B : BigFppfSite.{u}) : BigPHSite.{u} := by
  classical
  let h := exists_covBounded_isSite (IsPHCoveringInCutoff (κ := B.cutoff))
    (isSite_isPHCoveringInCutoff B.cutoff) (∅ : Set (Covering (SchemeBelow B.cutoff)))
    (by intro 𝒰 h𝒰; cases h𝒰)
  exact
    { initialSchemes := ∅
      initialSchemes_small := inferInstance
      cutoff := B.cutoff
      aleph0_lt_cutoff := B.aleph0_lt_cutoff
      cutoff_isStrongPrelimit := B.cutoff_isStrongPrelimit
      aleph0_lt_cutoff_cof := B.aleph0_lt_cutoff_cof
      initialSchemes_mem := by simp
      initialCoverings := ∅
      initialCoverings_small := inferInstance
      initialCoverings_supported := by simp
      coveringBound := h.choose
      coveringOrdinal := h.choose_spec.choose
      coveringOrdinal_isSuccLimit := h.choose_spec.choose_spec.1
      initialCoverings_mem := by simp
      coverings_isSite := h.choose_spec.choose_spec.2.2.1
      covering_representative := h.choose_spec.choose_spec.2.2.2 }

/-- The cutoff of `B.bigPHSite` is that of `B`. -/
theorem bigPHSite_cutoff (B : BigFppfSite.{u}) : B.bigPHSite.cutoff = B.cutoff := rfl

/-- **A big ph site of algebraic spaces over `S` whose auxiliary big fppf site of schemes is `B`**
(Stacks 0DFK): its big ph site of schemes is `B.bigPHSite`, and it has no initial coverings and
the covering bound of Stacks 000X. The definition is reducible, so that its algebraic spaces are
seen to be those built on `B`. -/
abbrev bigPHSpaceSite (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    BigPHSpaceSite S :=
  let h := exists_covBounded_isSite_of_univ.{_, _, u + 2}
    (Space.IsPHCoveringFamily B S hS)
    (Space.isSite_isPHCoveringFamily B S hS) ∅ (by intro U hU; cases hU)
  { schemeSite := B.bigPHSite
    scheme_mem := hS
    fppfSite := B
    fppf_mem := hS
    cutoff_eq := rfl
    initialCoverings := ∅
    initialCoverings_small := inferInstance
    initialCoverings_ph := by simp
    coveringBound := h.choose
    coveringOrdinal := h.choose_spec.choose
    coveringOrdinal_isSuccLimit := h.choose_spec.choose_spec.1
    initialCoverings_bounded := by simp
    coverings_isSite := h.choose_spec.choose_spec.2.2.1
    covering_representative := h.choose_spec.choose_spec.2.2.2 }

end AlgebraicGeometry.BigFppfSite

/-- The auxiliary big fppf site of schemes of `B.bigPHSpaceSite S hS` is `B`. -/
theorem AlgebraicGeometry.BigFppfSite.bigPHSpaceSite_fppfSite (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : (B.bigPHSpaceSite S hS).fppfSite = B :=
  rfl

end
