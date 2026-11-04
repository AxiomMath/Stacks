module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FppfCoverings

/-!
# Open immersions of algebraic spaces are fppf local on the base

Being an open immersion of Stacks 02YU, part (1) -- a representable morphism of algebraic spaces
over `S` every represented base change of which is an open immersion of schemes -- is local on
the target for the fppf topology of Stacks 03YH.

This is the fppf form of **Stacks 041X**, which states the same for the coarser fpqc topology.
The source's argument for the fpqc form glues the images of the base changes along the covering
and descends the inverse of the resulting open immersion, which needs Gabber's theorem
Stacks 0APL -- that an algebraic space is a sheaf for the fpqc topology and not merely for the
fppf topology of its defining site. The fppf form proved here needs nothing of the kind, and is
what the fppf descent tools of `StacksFrontier/AlgebraicGeometry/Spaces/AtlasCovering.lean`
consume. It is therefore left untagged.

## Main results

* `AlgebraicGeometry.Space.openImmersion_isLocalAtTarget_fppf`: being an open immersion of
  algebraic spaces over `S` is local on the base for the fppf topology.

## Implementation notes

The proof is the one of the sibling `AlgebraicGeometry.Space.isImmersion_isLocalAtTarget_fppf`
for immersions, Stacks 042U, with the scheme-level descent at the end taken for open immersions
instead: Stacks 02L3, `Stacks.Descent.isOpenImmersion_isLocalAtTarget_fpqc`, restricted to the
fppf precoverage of schemes.

The base-change half is Stacks 02YW and uses nothing about the covering. For the descent half,
an open immersion is an immersion, so each base change of `f` to a member of the covering is
separated by Stacks 042R and locally quasi-finite by Stacks 03XM; by the fpqc locality of those
two properties, Stacks 0421 and Stacks 0427, `f` itself is separated and locally quasi-finite,
hence relatively representable by Stacks 0418. What is left is the condition on the represented
base changes of `f`, and that is checked after refining the pullback of the given covering by a
covering whose members are schemes of the site (Stacks 03Y9 and Stacks 042T): the base change of
the representing morphism along a member of the refinement is a base change of the base change
of `f` to a member of the given covering, hence an open immersion of schemes.

## References

* [Stacks Project, Tag 02L3](https://stacks.math.columbia.edu/tag/02L3)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 02YW](https://stacks.math.columbia.edu/tag/02YW)
* [Stacks Project, Tag 03XM](https://stacks.math.columbia.edu/tag/03XM)
* [Stacks Project, Tag 03Y9](https://stacks.math.columbia.edu/tag/03Y9)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 041X](https://stacks.math.columbia.edu/tag/041X)
* [Stacks Project, Tag 0418](https://stacks.math.columbia.edu/tag/0418)
* [Stacks Project, Tag 0421](https://stacks.math.columbia.edu/tag/0421)
* [Stacks Project, Tag 0427](https://stacks.math.columbia.edu/tag/0427)
* [Stacks Project, Tag 042R](https://stacks.math.columbia.edu/tag/042R)
* [Stacks Project, Tag 042T](https://stacks.math.columbia.edu/tag/042T)
* [Stacks Project, Tag 042U](https://stacks.math.columbia.edu/tag/042U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

/-- **Being an open immersion is fppf local on the base for morphisms of algebraic spaces over
`S`:** such a morphism is an open immersion exactly when its base change to every member of some
fppf covering of its target is an open immersion. This is the fppf form of Stacks 041X. -/
theorem openImmersion_isLocalAtTarget_fppf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (openImmersionProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fppf B S hS) where
  pullbackSnd _ _ hf := isOpenImmersion_of_isPullback B S hS (IsPullback.of_hasPullback _ _) hf
  of_forall_pullbackSnd := by
    intro T A f R hR hbc
    have hRc := hR
    obtain ⟨I, Yi, gi, rfl, hcov⟩ := hRc
    -- being an open immersion, as a property of morphisms of presheaves
    set Q := (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
    have hQbc : Q.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange _
    -- the base change of `f` to each member of the covering, read on presheaves
    have hoi : ∀ i, Q (pullback.snd f.hom (gi i).hom) := fun i =>
      (AlgebraicSpaces.hom_pullback_snd_iff B S hS Q f (gi i)).mp
        (hbc (g := gi i) (Presieve.ofArrows.mk i))
    -- Stacks 042R and 0421: `f` is separated
    have hsepLoc : (separatedProperty B S hS).IsLocalAtTarget
        (Topology.precoverage.{u, v} .fppf B S hS) :=
      .of_le (fppfPrecoverage_le_fpqcPrecoverage B S hS)
    have hsep : IsSeparated B S hS f.hom :=
      hsepLoc.of_forall_pullbackSnd hR fun hg =>
        isSeparated_of_isImmersion B S hS (isImmersion_of_isOpenImmersion B S hS (hbc hg))
    -- Stacks 03XM and 0427: `f` is locally quasi-finite
    have hlqf : IsLocallyQuasiFinite B S hS f.hom :=
      (isLocallyQuasiFinite_isLocalAtTarget_fppf.{u, v} B S hS).of_forall_pullbackSnd hR
        fun hg => isLocallyQuasiFinite_of_isImmersion B S hS _
          (isImmersion_of_isOpenImmersion B S hS (hbc hg))
    -- Stacks 0418: `f` is relatively representable
    have hrep : yoneda.relativelyRepresentable f.hom :=
      relativelyRepresentable_of_isLocallyQuasiFinite_isSeparated B S hS f.hom
        A.property T.property hlqf hsep
    refine ⟨hrep, ?_⟩
    intro Z V k fst₀ snd₀ hpb
    -- Stacks 03Y9: the covering pulled back along `k`
    have hcovZ : IsFppfCovering B S hS (fun i => Limits.pullback k (gi i).hom)
        (fun i => pullback.fst k (gi i).hom) :=
      isFppfCovering_fibreProduct B S hS Yi gi
        (ObjectProperty.homMk k : (⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩ :
          AlgebraicSpaces B S hS) ⟶ T) hcov.2.2
    -- Stacks 042T: refine it by a covering whose members are schemes of the site
    obtain ⟨Tj, hT, hcovT⟩ := exists_fppfCovering_scheme_refinement B S hS _ _ hcovZ
    let n : ∀ i, Tj i ⟶ Z := fun i =>
      Yoneda.fullyFaithful.preimage (hT i ≫ pullback.fst k (gi i).hom)
    have hn : ∀ i, yoneda.map (n i) = hT i ≫ pullback.fst k (gi i).hom := fun i =>
      Yoneda.fullyFaithful.map_preimage _
    have hcovT' : IsFppfCovering B S hS (fun i => yoneda.obj (Tj i))
        (fun i => yoneda.map (n i)) := by
      simpa only [hn] using hcovT
    have hmem := yoneda_fppfCovering_mem_fppfPrecoverage B S hS Tj Z n hcovT'
    -- each member of the refinement factors through a member of the given covering
    have hfac : ∀ i, yoneda.map (n i) ≫ k
        = (hT i ≫ pullback.snd k (gi i).hom) ≫ (gi i).hom := fun i => by
      rw [hn i, Category.assoc, pullback.condition, Category.assoc]
    -- Stacks 02L3: being an open immersion of schemes is fppf local on the base
    have : MorphismProperty.IsLocalAtTarget
        (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        Scheme.fppfPrecoverage :=
      .of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
    refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
      (P := (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}))
      (K := Scheme.fppfPrecoverage) hmem ?_
    rintro W q _ ⟨i⟩
    -- the base change of `snd₀` along the member `n i`, formed in the site
    have hsqSite : IsPullback (pullback.fst snd₀ (n i)) (pullback.snd snd₀ (n i)) snd₀ (n i) :=
      IsPullback.of_hasPullback _ _
    -- that square in presheaves, pasted with the square defining `snd₀`
    have hsqPre := (hsqSite.map (yoneda : BigFppfOver B S hS ⥤ _)).paste_horiz hpb
    rw [hfac i] at hsqPre
    -- Stacks 02YW: it is a base change of the base change of `f` to `Yi i`
    have hOI : AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map (pullback.snd snd₀ (n i))) :=
      (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _
        (pullback.snd snd₀ (n i))).mp
        (hQbc.of_isPullback
          (hsqPre.of_right' (IsPullback.of_hasPullback f.hom (gi i).hom)) (hoi i))
    -- compare the base change formed in the site with the chosen one in schemes
    have hsqSch := hsqSite.map (BigFppfOver.toScheme B S hS)
    have hsqCh := IsPullback.of_hasPullback ((BigFppfOver.toScheme B S hS).map snd₀)
      ((BigFppfOver.toScheme B S hS).map (n i))
    have he : (hsqSch.isoIsPullback _ _ hsqCh).hom ≫
        pullback.snd ((BigFppfOver.toScheme B S hS).map snd₀)
          ((BigFppfOver.toScheme B S hS).map (n i))
        = (BigFppfOver.toScheme B S hS).map (pullback.snd snd₀ (n i)) :=
      hsqSch.isoIsPullback_hom_snd _ _ hsqCh
    rw [← he] at hOI
    exact (MorphismProperty.cancel_left_of_respectsIso
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (hsqSch.isoIsPullback _ _ hsqCh).hom
      (pullback.snd ((BigFppfOver.toScheme B S hS).map snd₀)
        ((BigFppfOver.toScheme B S hS).map (n i)))).mp hOI

end AlgebraicGeometry.Space

end
