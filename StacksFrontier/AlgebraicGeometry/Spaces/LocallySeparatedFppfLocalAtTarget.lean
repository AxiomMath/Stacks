module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionFppfLocalAtTarget

/-!
# Local separatedness of morphisms of algebraic spaces is fppf local on the base

Local separatedness of a morphism of algebraic spaces over a scheme `S` (Stacks 03HL, part (2))
is local on the base for the fppf topology of Stacks 03YH. This is **Stacks 042F**. The file
packages the condition as a `CategoryTheory.MorphismProperty` on the category of algebraic spaces
over `S` and proves the locality.

The ascent half is base change, which is Stacks 03KL: local separatedness of `f : X ⟶ Y` is the
assertion that the relative diagonal `Δ_f : X ⟶ X ×_Y X` is an immersion, and the diagonal of a
base-change-stable property of morphisms of presheaves is again base-change stable. The descent
half is the corresponding statement for immersions, **Stacks 042U**, applied to that diagonal:
an fppf covering `{Y i ⟶ Y}` pulls back along `X ×_Y X ⟶ Y` to an fppf covering of `X ×_Y X` by
Stacks 03Y9, the base changes of `Δ_f` along it are the relative diagonals of the base changes
of `f`, and those are immersions by hypothesis.

Only the fppf topology is available here, because Stacks 042U is: being an immersion of schemes
is not known to descend along fpqc coverings.

## Main results

* `AlgebraicGeometry.Space.locallySeparated_isLocalAtTarget_fppf`: **Stacks 042F**.

## Implementation notes

The index type of a covering family lives in a universe `v` independent of the universe `u` of
the schemes and is existentially quantified in
`AlgebraicGeometry.Space.Topology.precoverage`, so `v` is a free universe parameter of the
statement, exactly as for `AlgebraicGeometry.Space.isImmersion_isLocalAtTarget_fppf`.

Local separatedness is packaged here, next to the proof of its locality, as
`AlgebraicGeometry.Space.quasiSeparatedProperty` is packaged next to the proof of its
own locality; `AlgebraicGeometry.Space.separatedProperty`, whose Stacks 03YK clients ask for it
in `StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties`, lives there instead.

The two sides of Mathlib's `CategoryTheory.MorphismProperty.IsLocalAtTarget` speak of
`CategoryTheory.Limits.pullback.snd` in the category of algebraic spaces, whereas the diagonal
comparison and the covering families are stated for the presheaf fibre product of Stacks 02X2;
`AlgebraicGeometry.AlgebraicSpaces.hom_pullback_snd_iff` moves between the two. The identification
of the diagonal of a base change with a base change of the diagonal is
`Stacks.SeparationLocal.isPullback_diagonal_pullbackSnd` together with
`Stacks.SeparationLocal.isPullback_diagonalObjMap`, which identifies the diagonal object
`(X ×_Y Y i) ×_{Y i} (X ×_Y Y i)` with `(X ×_Y X) ×_Y Y i`; the pulled-back covering is taken
with its first projections, so that comparison is used in its flipped form.

Stacks 042U is a theorem rather than an instance in this library, so it is introduced as a local
instance at `AlgebraicGeometry.Space.immersionProperty` before the locality of the diagonal is
read off.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 03KL](https://stacks.math.columbia.edu/tag/03KL)
* [Stacks Project, Tag 03Y9](https://stacks.math.columbia.edu/tag/03Y9)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 042F](https://stacks.math.columbia.edu/tag/042F)
* [Stacks Project, Tag 042U](https://stacks.math.columbia.edu/tag/042U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

open Stacks.SeparationLocal

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)


/-- Being locally separated (**Stacks 03HL**, part (2)), as a property of morphisms in the
category of algebraic spaces over `S`. -/
abbrev locallySeparatedMorphismProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f ↦ IsLocallySeparated B S hS f.hom

/-- **Stacks 03KL**, the locally separated case, for an arbitrary cartesian square in the
category of algebraic spaces over `S`: local separatedness is the relative diagonal being an
immersion, and the diagonal of a base-change-stable property of morphisms of presheaves is again
base-change stable. This is `AlgebraicGeometry.Space.isLocallySeparated_pullback` in the form the
relative properties of Stacks 03YK consume. -/
instance locallySeparatedMorphismProperty_isStableUnderBaseChange :
    (locallySeparatedMorphismProperty B S hS).IsStableUnderBaseChange where
  of_isPullback sq hg := by
    have : (immersionPresheafProperty B S hS).IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange _
    have : (immersionPresheafProperty B S hS).RespectsIso :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact (MorphismProperty.IsStableUnderBaseChange.diagonal
      (P := immersionPresheafProperty B S hS)).of_isPullback
        (AlgebraicSpaces.isPullback_hom B S hS sq) hg

/-- **Stacks 042F.** Local separatedness of morphisms of algebraic spaces over `S` is local on
the base for the fppf topology: a morphism is locally separated exactly when its base change to
every member of some fppf covering of its target is locally separated.

Local separatedness of `f : X ⟶ Y` is the relative diagonal `Δ_f : X ⟶ X ×_Y X` being an
immersion. Pulling a covering `{Y i ⟶ Y}` back along `X ×_Y X ⟶ Y` gives a covering of
`X ×_Y X` whose base changes of `Δ_f` are the relative diagonals of the base changes of `f`, so
Stacks 042U for immersions applies. -/
@[stacks 042F]
theorem locallySeparated_isLocalAtTarget_fppf :
    (locallySeparatedMorphismProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fppf B S hS) := by
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff
    (P := locallySeparatedMorphismProperty B S hS)
    (K := Topology.precoverage.{u, v} .fppf B S hS) ?_
  rintro X Y f _ ⟨I, Yi, gi, rfl, hcover⟩
  refine ⟨fun hf U g _ _ ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback f g) hf, fun hlocal ↦ ?_⟩
  let : (immersionProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fppf B S hS) :=
    isImmersion_isLocalAtTarget_fppf B S hS
  let Q : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  have : Q.RespectsIso := MorphismProperty.relative_respectsIso _
  -- The relative diagonal of `f`, as a morphism of algebraic spaces to `X ×_Y X`.
  let Z : AlgebraicSpaces B S hS := AlgebraicSpaces.fiberProduct B S hS f f
  let d : X ⟶ Z := ObjectProperty.homMk (pullback.diagonal f.hom)
  let q : Z ⟶ Y := ObjectProperty.homMk (pullback.fst f.hom f.hom ≫ f.hom)
  -- The covering of `X ×_Y X` obtained by pulling the given covering back along `q`.
  let W : I → AlgebraicSpaces B S hS := fun i ↦ AlgebraicSpaces.fiberProduct B S hS q (gi i)
  let k : ∀ i, W i ⟶ Z := fun i ↦ ObjectProperty.homMk (pullback.fst q.hom (gi i).hom)
  have hmem : Presieve.ofArrows W k ∈ (Topology.precoverage.{u, v} .fppf B S hS) Z :=
    ⟨I, W, k, rfl, Z.property, fun i ↦ (W i).property,
      isFppfCovering_fibreProduct B S hS Yi gi q hcover.2.2⟩
  show immersionProperty B S hS d
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (K := Topology.precoverage.{u, v} .fppf B S hS) hmem ?_
  rintro U g _ ⟨i⟩
  refine (AlgebraicSpaces.hom_pullback_snd_iff B S hS Q d (k i)).mpr ?_
  -- The relative diagonal of the base change of `f` along `g i`, which is an immersion.
  have hsep : Q (pullback.diagonal (pullback.snd f.hom (gi i).hom)) :=
    (AlgebraicSpaces.hom_pullback_snd_iff B S hS Q.diagonal f (gi i)).mp
      (hlocal (gi i) (.mk i))
  -- The diagonal object of that base change is `(X ×_Y X) ×_Y Y i`.
  have hq := (IsPullback.of_hasPullback q.hom (gi i).hom).flip
  have hd := IsPullback.of_hasPullback (pullback.diagonal f.hom) (pullback.fst q.hom (gi i).hom)
  let e := (isPullback_diagonalObjMap f.hom (gi i).hom).isoIsPullback _ _ hq
  have hdiag : IsPullback (pullback.fst f.hom (gi i).hom)
      (pullback.diagonal (pullback.snd f.hom (gi i).hom) ≫ e.hom)
      (pullback.diagonal f.hom) (pullback.fst q.hom (gi i).hom) :=
    (Stacks.SeparationLocal.isPullback_diagonal_pullbackSnd f.hom (gi i).hom).of_iso
      (Iso.refl _) (Iso.refl _) e (Iso.refl _) (by simp) (by simp) (by simp)
      ((isPullback_diagonalObjMap f.hom (gi i).hom).isoIsPullback_hom_snd _ _ hq).symm
  refine (Q.cancel_left_of_respectsIso (hdiag.isoIsPullback _ _ hd).hom
    (pullback.snd (pullback.diagonal f.hom) (pullback.fst q.hom (gi i).hom))).mp ?_
  rw [hdiag.isoIsPullback_hom_snd _ _ hd]
  exact MorphismProperty.RespectsIso.postcomp Q e.hom _ hsep

end AlgebraicGeometry.Space

end
