module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineBaseEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeLocal

/-!
# Reducing a surjective étale descent datum to an affine source over an affine base

`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` quantifies over a morphism
`h : yoneda.obj a ⟶ Y` out of a representable presheaf and a surjective étale `q : c ⟶ a` of the
big fppf site of `S`. Step 1 of Stacks 02W8 replaces an arbitrary fppf covering by a single
faithfully flat morphism *of affines*. Half of that is
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_affineBase`, which makes the
base object `a` affine. This file supplies the other half and combines the two: the source
object `c` may be assumed affine as well.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_affine_surjective_etale_refinement`: over an *affine*
  base object, every surjective étale morphism of the site is refined by one whose source is an
  affine object of the site. Quasi-compactness of the refinement is recorded as well, since a
  morphism between affine schemes is affine and hence quasi-compact; that is the form in which
  the single faithfully flat morphism of Stacks 02W3 is usually consumed.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_affineBase_affineSource`:
  **step 1 of Stacks 02W8 in full.** If the defining condition of
  `AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` holds whenever both the base
  object and the source object of the covering morphism are affine, then it holds for every
  datum.

## Implementation notes

*Why the refinement has to come second.*
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_refinement` already refines
the covering, but its hypothesis `hT` quantifies over *all* base objects, and no refinement with
affine source exists over a base that is not quasi-compact: the images of finitely many affine
opens of `c` need not cover `a`. The refinement is therefore produced here only after
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_affineBase` has reduced to an
affine base, and the base-change plumbing of the refinement theorem — the datum over the
refinement is the base change of the given datum, and
`CategoryTheory.MorphismProperty.relative` is stable under base change unconditionally — is
repeated inline rather than invoked.

*The geometric content of the refinement.* An étale morphism of schemes is flat and locally of
finite presentation, hence universally open
(`AlgebraicGeometry.UniversallyOpen.of_flat`), so the image of each affine open of `c` is open
in `a`; those images cover `a` because `q` is surjective; and `a` is quasi-compact because it is
affine, so finitely many suffice. The affine opens of `c` are objects of the site by
`AlgebraicGeometry.BigFppfOver.exists_affineOpen_restrict`, their coproduct is an object of the
site by `AlgebraicGeometry.BigFppfOver.exists_coproduct_of_mk_le_aleph0` — a finite index type
is in particular countable, which is all the size calculus of Stacks 000R (2) asks — and it is
affine because a finite coproduct of affine schemes is affine. Surjectivity and étaleness of the
composite are read off from the coproduct description: the comparison isomorphism identifies it
with `CategoryTheory.Limits.Sigma.desc` of the composites, surjectivity is
`AlgebraicGeometry.Surjective.sigmaDesc_of_union_range_eq_univ` and étaleness is
`AlgebraicGeometry.IsZariskiLocalAtSource.sigmaDesc`.

*This is the surjective-étale predicate, not the fpqc one.* The covering here is a single
surjective étale morphism of the site, whereas
`AlgebraicGeometry.Space.IsEffectiveAffineDescentAlongFpqc` — the hypothesis of Stacks 041Z —
quantifies over finite fpqc coverings of an affine object by affine objects. A flat quasi-compact
surjection of affines need not be étale, so neither predicate implies the other, and for the
fpqc predicate the reduction carried out here is *vacuous*: affineness of the base and of the
members of the covering is already part of its statement.

## References

* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Over an affine base object, a surjective étale morphism of the big fppf site of `S` is
refined by one whose source is affine. -/
theorem BigFppfOver.exists_affine_surjective_etale_refinement
    {a c : BigFppfOver B S hS} (ha : IsAffine ((BigFppfOver.toScheme B S hS).obj a))
    (q : c ⟶ a) (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q)) :
    ∃ (c' : BigFppfOver B S hS) (p : c' ⟶ c),
      IsAffine ((BigFppfOver.toScheme B S hS).obj c') ∧
        Surjective ((BigFppfOver.toScheme B S hS).map (p ≫ q)) ∧
          Etale ((BigFppfOver.toScheme B S hS).map (p ≫ q)) ∧
            QuasiCompact ((BigFppfOver.toScheme B S hS).map (p ≫ q)) := by
  classical
  set Q := (BigFppfOver.toScheme B S hS).map q with hQ
  -- the affine opens of the source, as objects of the site
  choose V u hu hurange hVaff using fun U =>
    BigFppfOver.exists_affineOpen_restrict B S hS c U
  -- the images of the affine opens of the source cover the affine base
  have hopen : ∀ U : ((BigFppfOver.toScheme B S hS).obj c).affineOpens,
      IsOpen (Q.base '' (U.1 : Set ((BigFppfOver.toScheme B S hS).obj c))) :=
    fun U => Q.isOpenMap _ U.1.2
  have hsub : (Set.univ : Set ((BigFppfOver.toScheme B S hS).obj a)) ⊆
      ⋃ U : ((BigFppfOver.toScheme B S hS).obj c).affineOpens,
        Q.base '' (U.1 : Set ((BigFppfOver.toScheme B S hS).obj c)) := by
    intro x _
    obtain ⟨y, hy⟩ := Surjective.surj (f := Q) x
    have hy' : y ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj c).Opens) := trivial
    rw [← iSup_affineOpens_eq_top] at hy'
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 hy'
    exact Set.mem_iUnion.2 ⟨U, ⟨y, hU, hy⟩⟩
  obtain ⟨t, ht⟩ := (CompactSpace.isCompact_univ
    (X := ((BigFppfOver.toScheme B S hS).obj a))).elim_finite_subcover _ hopen hsub
  -- the finitely many chosen affine opens, as a family indexed by a type in `Type u`
  have _ : ∀ U : {U // U ∈ t}, IsAffine ((BigFppfOver.toScheme B S hS).obj (V U.1)) :=
    fun U => hVaff U.1
  have _ : MorphismProperty.RespectsIso (@Surjective.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨c', inj, e, he, hdesc⟩ :=
    BigFppfOver.exists_coproduct_of_mk_le_aleph0 (σ := {U // U ∈ t})
      (Cardinal.mk_le_aleph0) (fun U => V U.1)
  obtain ⟨p, hp⟩ := hdesc (fun U => u U.1)
  -- the underlying morphism of the refinement, read through the coproduct
  have key : e.hom ≫ (BigFppfOver.toScheme B S hS).map (p ≫ q) =
      Sigma.desc fun U : {U // U ∈ t} =>
        (BigFppfOver.toScheme B S hS).map (u U.1) ≫ Q := by
    refine Sigma.hom_ext _ _ fun U => ?_
    rw [← Category.assoc, he U, Sigma.ι_desc, Functor.map_comp, ← Category.assoc,
      ← Functor.map_comp, hp U]
  have hrange : ∀ U : {U // U ∈ t},
      Q.base '' (U.1.1 : Set ((BigFppfOver.toScheme B S hS).obj c)) ⊆
        Set.range ((BigFppfOver.toScheme B S hS).map (u U.1) ≫ Q) := by
    intro U x hx
    obtain ⟨y, hyU, rfl⟩ := hx
    have hy : y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (u U.1)) := by
      rw [hurange U.1]; exact hyU
    obtain ⟨z, hz⟩ := hy
    exact ⟨z, by rw [Scheme.Hom.comp_apply, hz]⟩
  have hc'aff : IsAffine ((BigFppfOver.toScheme B S hS).obj c') := IsAffine.of_isIso e.inv
  -- a property invariant under isomorphisms may be checked on the coproduct description
  have transfer : ∀ (P : MorphismProperty Scheme.{u}) [P.RespectsIso],
      P (Sigma.desc fun U : {U // U ∈ t} => (BigFppfOver.toScheme B S hS).map (u U.1) ≫ Q) →
        P ((BigFppfOver.toScheme B S hS).map (p ≫ q)) := fun P _ h => by
    rw [← key] at h
    exact (MorphismProperty.cancel_left_of_respectsIso P e.hom _).mp h
  refine ⟨c', p, hc'aff, transfer @Surjective.{u} ?_, transfer @Etale.{u} ?_, ?_⟩
  · refine Surjective.sigmaDesc_of_union_range_eq_univ (Set.eq_univ_of_univ_subset ?_)
    refine ht.trans (Set.iUnion₂_subset fun U hU => ?_)
    exact Set.subset_iUnion_of_subset ⟨U, hU⟩ (hrange ⟨U, hU⟩)
  · have _ : IsZariskiLocalAtSource (@Etale.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
    refine IsZariskiLocalAtSource.sigmaDesc fun U => ?_
    have _ := hu U.1
    infer_instance
  · have _ : IsAffineHom ((BigFppfOver.toScheme B S hS).map (p ≫ q)) := inferInstance
    infer_instance

namespace Space

/-- **The affine-base-and-affine-source reduction for effective descent along surjective étale
morphisms.** Effective descent along the surjective étale morphisms of the big fppf site of `S`
may be verified over data in which *both* the base object `a` and the source object `c` of the
covering morphism are affine.

The hypothesis `H` is the body of
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` with the two extra assumptions
`IsAffine ((BigFppfOver.toScheme B S hS).obj a)` and
`IsAffine ((BigFppfOver.toScheme B S hS).obj c)`; no quantifier is restricted and no other
hypothesis is added.

This is step 1 of Stacks 02W8 in full: the base reduction is
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_affineBase`, and the source
reduction is `AlgebraicGeometry.BigFppfOver.exists_affine_surjective_etale_refinement`,
whose geometric input is free once the base is affine — an étale morphism is open and an affine
scheme is quasi-compact, so finitely many affine opens of `c` already have images covering `a`,
and their coproduct is an affine object of the site. Refining the source is harmless because the
conclusion of the defining condition does not mention the covering, exactly as in
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_refinement`; the difference
is that the refinement is produced *after* the base has been made affine, which is what the
quantifier order of that theorem forbids. -/
theorem isEffectiveDescentAlongSurjectiveEtale_of_affineBase_affineSource
    {P : MorphismProperty Scheme.{u}}
    [P.RespectsIso] [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (H : ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
      ∀ ⦃a c : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (q : c ⟶ a),
        IsAffine ((BigFppfOver.toScheme B S hS).obj a) →
        IsAffine ((BigFppfOver.toScheme B S hS).obj c) →
        Surjective ((BigFppfOver.toScheme B S hS).map q) →
        Etale ((BigFppfOver.toScheme B S hS).map q) →
        QuasiCompact ((BigFppfOver.toScheme B S hS).map q) →
        ∀ ⦃A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (m : A ⟶ X) (r : A ⟶ yoneda.obj c),
          IsPullback m r f (yoneda.map q ≫ h) →
          (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r →
          (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h)) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS P := by
  refine isEffectiveDescentAlongSurjectiveEtale_of_affineBase ?_
  intro X Y f hX hY a c h q ha hqs hqe A m r sq hr
  have hstable := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (P.inverseImage (BigFppfOver.toScheme B S hS))
  obtain ⟨c', p, hc'aff, hps, hpe, hpqc⟩ :=
    BigFppfOver.exists_affine_surjective_etale_refinement ha q hqs hqe
  have hbc : IsPullback (pullback.fst r (yoneda.map p)) (pullback.snd r (yoneda.map p)) r
      (yoneda.map p) := IsPullback.of_hasPullback _ _
  have hsq : IsPullback (pullback.fst r (yoneda.map p) ≫ m) (pullback.snd r (yoneda.map p)) f
      (yoneda.map (p ≫ q) ≫ h) := by
    simpa [Functor.map_comp] using hbc.paste_horiz sq
  exact H f hX hY h (p ≫ q) ha hc'aff hps hpe hpqc _ _ hsq
    (MorphismProperty.of_isPullback hbc hr)

end Space

end AlgebraicGeometry

end
