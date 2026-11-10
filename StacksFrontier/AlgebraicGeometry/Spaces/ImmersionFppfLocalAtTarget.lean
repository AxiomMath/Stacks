module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismPropertyTopology.FppfLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FppfCoverings

/-!
# Immersions of algebraic spaces are fppf local on the base

Being an immersion of Stacks 02YU, part (5) — a representable morphism of algebraic spaces over
`S` every represented base change of which is an immersion of schemes — is local on the base for
the fppf topology of Stacks 03YH. This is **Stacks 042U**.

Locality on the base for one of the topologies `τ` of Stacks 03YH is
`CategoryTheory.MorphismProperty.IsLocalAtTarget` for the precoverage
`AlgebraicGeometry.Space.Topology.precoverage` that `τ` presents, so the assertion has two
halves: a morphism with the property has it after base change to every member of a `τ`-covering
of its target, and a morphism whose base changes to the members of some `τ`-covering all have
the property has it.

The first half is base change of immersions, **Stacks 02YW**, and uses nothing about the
covering. For the second, let `{Y i ⟶ Y}` be an fppf covering and suppose every base change of
`f : X ⟶ Y` to a member of it is an immersion. Each such base change is then separated by
**Stacks 042R** and locally quasi-finite by **Stacks 03XM**, so `f` itself is separated by
**Stacks 0421** and locally quasi-finite by **Stacks 0427**; both of those are locality
statements for the coarser fpqc topology, and each is applied along the given covering to the
same morphism, one member at a time. By **Stacks 0418** a separated, locally quasi-finite
morphism of algebraic spaces is relatively representable along the Yoneda embedding of the site,
which is the first clause of being an immersion and leaves only the condition on the represented
base changes.

For that condition, let `k : h_Z ⟶ Y` be a morphism from a representable presheaf and let
`v : V ⟶ Z` be a morphism of the site representing the base change of `f` along `k`. Pulling
`{Y i ⟶ Y}` back along `k` is again an fppf covering by **Stacks 03Y9**, and refining the result
by schemes using **Stacks 042T** gives an fppf covering `{Z i ⟶ Z}` by objects of the site whose
members factor through the members of the original covering. The base change of `v` along
`Z i ⟶ Z`, formed in the site, is therefore a base change of the base change of `f` to `Y i`,
hence an immersion of schemes; and being an immersion of schemes is fppf local on the base by
**Stacks 02YM**, which identifies `v` itself as an immersion.

That last step is what confines the statement to the fppf topology. Being an immersion of
schemes is not known to be fpqc local on the base, so Stacks 02YM is available only at the fppf
precoverage of schemes; and the refinement of a covering of an algebraic space by a covering
whose members are schemes, Stacks 042T, is likewise an fppf statement. The two ingredients which
do come from the fpqc topology, Stacks 0421 and Stacks 0427, transfer to the fppf topology
because every fppf covering family of algebraic spaces is an fpqc covering family,
`AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage`.

## Main results

* `AlgebraicGeometry.Space.isImmersion_isLocalAtTarget_fppf`: being an immersion is fppf local on
  the base.

## Implementation notes

The index type of a covering family lives in a universe `v` independent of the universe `u` of
the schemes, and it is existentially quantified in `AlgebraicGeometry.Space.Topology.precoverage`,
so `v` is a free universe parameter of the statement. The result is therefore a plain theorem
rather than an instance, as `AlgebraicGeometry.Space.isClosedImmersion_isLocalAtTarget_fpqc` is
for the same reason.

## References

* [Stacks Project, Tag 02YM](https://stacks.math.columbia.edu/tag/02YM)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 02YW](https://stacks.math.columbia.edu/tag/02YW)
* [Stacks Project, Tag 03XM](https://stacks.math.columbia.edu/tag/03XM)
* [Stacks Project, Tag 03Y9](https://stacks.math.columbia.edu/tag/03Y9)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
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

set_option synthInstance.maxHeartbeats 400000 in
-- the `HasPullbacks` search for presheaves on the big fppf site times out at the default
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
private instance hasPullbacks_presheaf_immersionFppf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_immersionFppf (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
-- the `HasPullbacks` search for the big fppf site over `S` times out at the default
/-- Pullbacks in the big fppf site over `S` (instance search times out without this shortcut). -/
private instance hasPullbacks_site_immersionFppf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : HasPullbacks (BigFppfOver B S hS) := inferInstance

private instance (priority := high) hasPullback_site_immersionFppf (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {X Y Z : BigFppfOver B S hS}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- Being an immersion is fppf local on the base for morphisms of algebraic spaces over `S`: such
a morphism is an immersion exactly when its base change to every member of some fppf covering of
its target is an immersion. -/
@[stacks 042U]
theorem isImmersion_isLocalAtTarget_fppf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (immersionProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fppf B S hS) where
  pullbackSnd _ _ hf := isImmersion_of_isPullback B S hS (IsPullback.of_hasPullback _ _) hf
  of_forall_pullbackSnd := by
    intro T A f R hR hbc
    obtain ⟨I, Yi, gi, rfl, hcov⟩ := id hR
    set Q := (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
    have hQiso : Q.RespectsIso := MorphismProperty.relative_respectsIso _
    have hQbc : Q.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange _
    have himm : ∀ i, Q (pullback.snd f.hom (gi i).hom) := fun i =>
      (AlgebraicSpaces.hom_pullback_snd_iff B S hS Q f (gi i)).mp
        (hbc (g := gi i) (Presieve.ofArrows.mk i))
    have hsepLoc : (separatedProperty B S hS).IsLocalAtTarget
        (Topology.precoverage.{u, v} .fppf B S hS) :=
      .of_le (fppfPrecoverage_le_fpqcPrecoverage B S hS)
    have hsep : IsSeparated B S hS f.hom :=
      hsepLoc.of_forall_pullbackSnd hR fun hg => isSeparated_of_isImmersion B S hS (hbc hg)
    have hlqf : IsLocallyQuasiFinite B S hS f.hom :=
      (isLocallyQuasiFinite_isLocalAtTarget_fppf.{u, v} B S hS).of_forall_pullbackSnd hR
        fun hg => isLocallyQuasiFinite_of_isImmersion B S hS _ (hbc hg)
    have hrep : yoneda.relativelyRepresentable f.hom :=
      relativelyRepresentable_of_isLocallyQuasiFinite_isSeparated B S hS f.hom
        A.property T.property hlqf hsep
    refine ⟨hrep, fun Z V k fst₀ snd₀ hpb => ?_⟩
    have hcovZ : IsFppfCovering B S hS (fun i => Limits.pullback k (gi i).hom)
        (fun i => pullback.fst k (gi i).hom) :=
      isFppfCovering_fibreProduct B S hS Yi gi
        (ObjectProperty.homMk k : (⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩ :
          AlgebraicSpaces B S hS) ⟶ T) hcov.2.2
    obtain ⟨Tj, hT, hcovT⟩ := exists_fppfCovering_scheme_refinement B S hS _ _ hcovZ
    let n : ∀ i, Tj i ⟶ Z := fun i =>
      Yoneda.fullyFaithful.preimage (hT i ≫ pullback.fst k (gi i).hom)
    have hn : ∀ i, yoneda.map (n i) = hT i ≫ pullback.fst k (gi i).hom := fun i =>
      Yoneda.fullyFaithful.map_preimage _
    have hcovT' : IsFppfCovering B S hS (fun i => yoneda.obj (Tj i))
        (fun i => yoneda.map (n i)) := by
      simpa only [hn] using hcovT
    have hmem := yoneda_fppfCovering_mem_fppfPrecoverage B S hS Tj Z n hcovT'
    have hfac : ∀ i, yoneda.map (n i) ≫ k
        = (hT i ≫ pullback.snd k (gi i).hom) ≫ (gi i).hom := fun i => by
      rw [hn i, Category.assoc, pullback.condition, Category.assoc]
    refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
      (P := (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}))
      (K := Scheme.fppfPrecoverage) hmem ?_
    rintro W q _ ⟨i⟩
    have hsqSite : IsPullback (pullback.fst snd₀ (n i)) (pullback.snd snd₀ (n i)) snd₀ (n i) :=
      IsPullback.of_hasPullback _ _
    have hsqPre := (hsqSite.map (yoneda : BigFppfOver B S hS ⥤ _)).paste_horiz hpb
    rw [hfac i] at hsqPre
    have hImm : AlgebraicGeometry.IsImmersion
        ((BigFppfOver.toScheme B S hS).map (pullback.snd snd₀ (n i))) :=
      (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ (pullback.snd snd₀ (n i))).mp
        (hQbc.of_isPullback
          (hsqPre.of_right' (IsPullback.of_hasPullback f.hom (gi i).hom)) (himm i))
    have _ : MorphismProperty.RespectsIso
        (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have hsqSch := hsqSite.map (BigFppfOver.toScheme B S hS)
    have hsqCh := IsPullback.of_hasPullback ((BigFppfOver.toScheme B S hS).map snd₀)
      ((BigFppfOver.toScheme B S hS).map (n i))
    have he : (hsqSch.isoIsPullback _ _ hsqCh).hom ≫
        pullback.snd ((BigFppfOver.toScheme B S hS).map snd₀)
          ((BigFppfOver.toScheme B S hS).map (n i))
        = (BigFppfOver.toScheme B S hS).map (pullback.snd snd₀ (n i)) :=
      hsqSch.isoIsPullback_hom_snd _ _ hsqCh
    rw [← he] at hImm
    exact (MorphismProperty.cancel_left_of_respectsIso
      (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
      (hsqSch.isoIsPullback _ _ hsqCh).hom
      (pullback.snd ((BigFppfOver.toScheme B S hS).map snd₀)
        ((BigFppfOver.toScheme B S hS).map (n i)))).mp hImm

end AlgebraicGeometry.Space

end
