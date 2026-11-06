module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.ImmersionEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.Immersion
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedFpqcLocalAtTarget

/-!
# Quasi-compact immersions of algebraic spaces are fpqc local on the base

Being a quasi-compact immersion — an immersion of **Stacks 02YU**, part (5), which is
quasi-compact in the sense of **Stacks 03HE** — is local on the base for the fpqc topology of
**Stacks 03YH**: a morphism of algebraic spaces over `S` is a quasi-compact immersion exactly
when its base change to every member of some fpqc covering of its target is a quasi-compact
immersion. This is **Stacks 0424**.

Locality on the base for a topology `τ` of Stacks 03YH is
`CategoryTheory.MorphismProperty.IsLocalAtTarget` for the precoverage
`AlgebraicGeometry.Space.Topology.precoverage` which `τ` presents, so the assertion has two
halves. The first is base change of immersions (**Stacks 02YW**) and of quasi-compact morphisms
(**Stacks 03HF**), and uses nothing about the covering.

For the second, let `{Y i ⟶ Y}` be an fpqc covering of the target and suppose every base change
of `f : X ⟶ Y` to a member of it is a quasi-compact immersion. Quasi-compactness of `f` itself
is then **Stacks 041L**. Each base change is separated by **Stacks 042R** and locally
quasi-finite by **Stacks 03XM**, so `f` is separated by **Stacks 0421** and locally quasi-finite
by **Stacks 0427**, and hence relatively representable along the Yoneda embedding of the site by
**Stacks 0418**. Over an affine object `Z` of the site the base change of `f` is therefore
represented by an object `W` of the site, whose underlying scheme is quasi-compact because `Z`
is affine and `f` is quasi-compact; and the fpqc covering condition of **Stacks 03MQ** refines
the covering pulled back to `Z` by a finite fpqc covering of `Z` by affine objects. Each member
of that refinement pulls `W ⟶ Z` back to a base change of one of the given base changes of `f`,
so **Stacks 02L8** — being a quasi-compact immersion of schemes is fpqc local on the base —
identifies `W ⟶ Z` as an immersion. The affine criterion of **Stacks 03M4** for immersions then
gives the conclusion for `f`.

The scheme-level input is what confines the argument to quasi-compact immersions. Being an
immersion of schemes is not known to be fpqc local on the base, only fppf local, which is why
immersions alone are available only at the fppf precoverage
(`AlgebraicGeometry.Space.isImmersion_isLocalAtTarget_fppf`, **Stacks 042U**); the infimum with
quasi-compactness is fpqc local on the base at the level of schemes, and the quasi-compactness
is also exactly what makes the representing scheme over an affine object quasi-compact.

## Main results

* `AlgebraicGeometry.Space.immersion_inf_quasiCompact_isLocalAtTarget_fpqc`: **Stacks 0424**.

## References

* [Stacks Project, Tag 02L8](https://stacks.math.columbia.edu/tag/02L8)
* [Stacks Project, Tag 03M4](https://stacks.math.columbia.edu/tag/03M4)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 0418](https://stacks.math.columbia.edu/tag/0418)
* [Stacks Project, Tag 041L](https://stacks.math.columbia.edu/tag/041L)
* [Stacks Project, Tag 0421](https://stacks.math.columbia.edu/tag/0421)
* [Stacks Project, Tag 0424](https://stacks.math.columbia.edu/tag/0424)
* [Stacks Project, Tag 0427](https://stacks.math.columbia.edu/tag/0427)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullback_presheaf_QuasiCompactImmersionFpqcLocalAtTarget
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H) : HasPullback f g :=
  HasLimitsOfShape.has_limit _

/-- A representable presheaf isomorphic to a quasi-compact algebraic space over `S` has
quasi-compact representing scheme. -/
private theorem compactSpace_of_isQuasiCompactSpace_of_iso
    {W : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : yoneda.obj W ≅ F) (hF : IsQuasiCompactSpace B S hS F) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj W) := by
  obtain ⟨U, q, hU, hs, -⟩ := hF
  have hs' := MorphismProperty.RespectsIso.postcomp
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) e.inv q hs
  obtain ⟨k, hk⟩ := yoneda.map_surjective (q ≫ e.inv)
  rw [← hk] at hs'
  have hk' : _root_.AlgebraicGeometry.Surjective
      ((BigFppfOver.toScheme B S hS).map k) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ k).mp hs'
  exact hk'.surj.compactSpace (Scheme.Hom.continuous _)

/-- The descent step of Stacks 0424 over an affine object of the site. Let `f : X ⟶ Y` be a
morphism of algebraic spaces over `S` whose base change to every member of an fpqc covering of
`Y` is an immersion, and let `p : W ⟶ T` be a morphism of the site, with `T` affine and `W`
quasi-compact, which represents the base change of `f` along a morphism `yoneda.obj T ⟶ Y`.
Then `p` is an immersion of schemes. -/
private theorem isImmersion_map_of_isFpqcCovering
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {I : Type v} {Yi : I → AlgebraicSpaces B S hS} {gi : ∀ i, Yi i ⟶ Y}
    (hcover : IsFpqcCovering B S hS (fun i ↦ (gi i).hom))
    (hlocal : ∀ i, IsImmersion B S hS (pullback.snd f (gi i)).hom)
    (T : BigAffineFppf B S hS)
    {g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj T) ⟶ Y.obj}
    {W : BigFppfOver B S hS} {p : W ⟶ (BigAffineFppf.inclusion B S hS).obj T}
    {a : yoneda.obj W ⟶ X.obj}
    (hp : IsPullback a (yoneda.map p) f.hom g)
    (hc : CompactSpace ((BigFppfOver.toScheme B S hS).obj W)) :
    _root_.AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map p) := by
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj T)) := T.property
  have _ : _root_.AlgebraicGeometry.QuasiCompact
    ((BigFppfOver.toScheme B S hS).map p) := inferInstance
  obtain ⟨U, -, hU, hrefine⟩ := hcover.2 T g
  let V : Scheme.fpqcPrecoverage.ZeroHypercover
      ((BigAffineFppf.toScheme B S hS).obj T) :=
    ⟨U.map (BigAffineFppf.toScheme B S hS), by
      rw [PreZeroHypercover.presieve₀_map]
      exact hU⟩
  suffices h : (@_root_.AlgebraicGeometry.IsImmersion ⊓
      @_root_.AlgebraicGeometry.QuasiCompact : MorphismProperty Scheme.{u})
      ((BigFppfOver.toScheme B S hS).map p) from h.1
  apply MorphismProperty.IsLocalAtTarget.of_zeroHypercover
    (P := (@_root_.AlgebraicGeometry.IsImmersion ⊓
      @_root_.AlgebraicGeometry.QuasiCompact : MorphismProperty Scheme.{u})) V
  intro j
  refine ⟨?_, inferInstance⟩
  obtain ⟨i, b, hb⟩ := hrefine j
  have hsq := (IsPullback.of_hasPullback p
    ((BigAffineFppf.inclusion B S hS).map (U.f j))).map (BigFppfOver.toScheme B S hS)
  have hy := (IsPullback.of_hasPullback p
    ((BigAffineFppf.inclusion B S hS).map (U.f j))).map
      (yoneda : BigFppfOver B S hS ⥤ _)
  have ht := hy.paste_horiz hp
  rw [← hb] at ht
  have hq : IsImmersion B S hS
      (yoneda.map (pullback.snd p ((BigAffineFppf.inclusion B S hS).map (U.f j)))) :=
    (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).of_isPullback
      (ht.of_right' (AlgebraicSpaces.isPullback_hom B S hS
        (IsPullback.of_hasPullback f (gi i)))) (hlocal i)
  have hq' : _root_.AlgebraicGeometry.IsImmersion
      ((BigFppfOver.toScheme B S hS).map
        (pullback.snd p ((BigAffineFppf.inclusion B S hS).map (U.f j)))) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).mp hq
  have _ : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hch := IsPullback.of_hasPullback ((BigFppfOver.toScheme B S hS).map p)
    ((BigFppfOver.toScheme B S hS).map ((BigAffineFppf.inclusion B S hS).map (U.f j)))
  have he : (hsq.isoIsPullback _ _ hch).hom ≫
      pullback.snd ((BigFppfOver.toScheme B S hS).map p)
        ((BigFppfOver.toScheme B S hS).map ((BigAffineFppf.inclusion B S hS).map (U.f j)))
      = (BigFppfOver.toScheme B S hS).map
        (pullback.snd p ((BigAffineFppf.inclusion B S hS).map (U.f j))) :=
    hsq.isoIsPullback_hom_snd _ _ hch
  rw [← he] at hq'
  exact (MorphismProperty.cancel_left_of_respectsIso
    (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
    (hsq.isoIsPullback _ _ hch).hom _).mp hq'

/-- The descent half of Stacks 0424: a morphism of algebraic spaces over `S` whose base change
to every member of an fpqc covering of its target is a quasi-compact immersion is itself a
quasi-compact immersion. -/
@[ega "IV 2.7.1" "more general"]
private theorem immersion_inf_quasiCompact_of_forall_pullbackSnd
    {T A : AlgebraicSpaces B S hS} {f : A ⟶ T} {R : Presieve T}
    (hR : R ∈ (Topology.precoverage.{u, v} .fpqc B S hS).coverings T)
    (hbc : ∀ {U : AlgebraicSpaces B S hS} {g : U ⟶ T} [HasPullback f g], R g →
      (immersionProperty B S hS ⊓ quasiCompactProperty B S hS) (pullback.snd f g)) :
    (immersionProperty B S hS ⊓ quasiCompactProperty B S hS) f := by
    -- Stacks 041L: `f` is quasi-compact
    have hqc : quasiCompactProperty B S hS f :=
      (quasiCompact_isLocalAtTarget_fpqc.{u, v} B S hS).of_forall_pullbackSnd hR
        fun hg ↦ (hbc hg).2
    refine ⟨?_, hqc⟩
    -- Stacks 042R and 0421: `f` is separated
    have hsep : IsSeparated B S hS f.hom :=
      (separated_isLocalAtTarget_fpqc.{u, v} B S hS).of_forall_pullbackSnd hR
        fun hg ↦ isSeparated_of_isImmersion B S hS (hbc hg).1
    -- Stacks 03XM and 0427: `f` is locally quasi-finite
    have hlqf : IsLocallyQuasiFinite B S hS f.hom :=
      (isLocallyQuasiFinite_isLocalAtTarget_fpqc.{u, v} B S hS).of_forall_pullbackSnd hR
        fun hg ↦ isLocallyQuasiFinite_of_isImmersion B S hS _ (hbc hg).1
    -- Stacks 0418: `f` is relatively representable
    have hrep : yoneda.relativelyRepresentable f.hom :=
      relativelyRepresentable_of_isLocallyQuasiFinite_isSeparated B S hS f.hom
        A.property T.property hlqf hsep
    obtain ⟨Idx, Yi, gi, hReq, hcov⟩ := hR
    have hmem : ∀ i, R (gi i) := fun i ↦ by rw [hReq]; exact Presieve.ofArrows.mk i
    -- Stacks 03M4: it suffices to test on the affine objects of the site
    refine ((isImmersion_tfae_of_isAlgebraicSpace A.property T.property
      f.hom).out 1 3).mpr ?_
    intro Z g hZ
    let Taff : BigAffineFppf B S hS := ⟨Z, hZ⟩
    -- the representing object of the base change of `f` along `g`, and its quasi-compactness
    have hcs : CompactSpace ((BigFppfOver.toScheme B S hS).obj (hrep.pullback g)) :=
      compactSpace_of_isQuasiCompactSpace_of_iso B S hS
        ((hrep.isPullback g).isoPullback ≪≫ pullbackSymmetry f.hom g)
        (hqc (yoneda.obj Z) (isAlgebraicSpace_yoneda B S hS Z)
          (isQuasiCompactSpace_yoneda_of_isAffine B S hS Z hZ) g)
    have himm : _root_.AlgebraicGeometry.IsImmersion
        ((BigFppfOver.toScheme B S hS).map (hrep.snd g)) :=
      isImmersion_map_of_isFpqcCovering B S hS f hcov.2.2
        (fun i ↦ (hbc (hmem i)).1) Taff (hrep.isPullback g) hcs
    have himm' : IsImmersion B S hS (yoneda.map (hrep.snd g)) :=
      (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).mpr himm
    have _ : MorphismProperty.RespectsIso
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) :=
      MorphismProperty.relative_respectsIso _
    have hpre := MorphismProperty.RespectsIso.precomp
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)))
      (hrep.isPullback g).isoPullback.inv (yoneda.map (hrep.snd g)) himm'
    rwa [(hrep.isPullback g).isoPullback_inv_snd] at hpre

/-- **Stacks 0424.** Being a quasi-compact immersion is fpqc local on the base for morphisms of
algebraic spaces over `S`: such a morphism is a quasi-compact immersion exactly when its base
change to every member of some fpqc covering of its target is a quasi-compact immersion. -/
@[stacks 0424, sga "4 IV 8.5.5" "more general"]
theorem immersion_inf_quasiCompact_isLocalAtTarget_fpqc :
    (immersionProperty B S hS ⊓ quasiCompactProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) where
  toRespects := (MorphismProperty.IsStableUnderBaseChange.inf
    (P := immersionProperty B S hS)
    (Q := quasiCompactProperty B S hS)).respectsIso
  pullbackSnd _ _ hf :=
    ⟨isImmersion_of_isPullback B S hS (IsPullback.of_hasPullback _ _) hf.1,
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback _ _) hf.2⟩
  of_forall_pullbackSnd hR hbc :=
    immersion_inf_quasiCompact_of_forall_pullbackSnd.{u, v} B S hS hR hbc

end AlgebraicGeometry.Space

end
