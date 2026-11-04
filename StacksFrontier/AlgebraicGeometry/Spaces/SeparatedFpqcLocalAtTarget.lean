module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties

/-!
# Separatedness of morphisms of algebraic spaces is fpqc local on the base

Separatedness of a morphism of algebraic spaces over a scheme `S` (Stacks 03HL, part (1)) is
local on the base for the fpqc topology of Stacks 03YH. This is **Stacks 0421**.

The ascent half is base change, which is Stacks 03KL and is already registered as the instance
`AlgebraicGeometry.Space.separatedProperty_isStableUnderBaseChange`. The descent half is the
corresponding statement for closed immersions, **Stacks 0420**, applied to the relative
diagonal: separatedness of `f : X ⟶ Y` is the assertion that `Δ_f : X ⟶ X ×_Y X` is a closed
immersion, an fpqc covering `{Y i ⟶ Y}` pulls back along `X ×_Y X ⟶ Y` to an fpqc covering of
`X ×_Y X` by Stacks 03MR, and the base changes of `Δ_f` along that covering are the relative
diagonals of the base changes of `f`. The last identification is the comparison morphism
`Stacks.SeparationLocal.diagonalObjMap` of the relative diagonal objects together with the two
cartesian squares it sits in, exactly as in the quasi-separated case
`AlgebraicGeometry.Space.quasiSeparated_isLocalAtTarget_fpqc` (**Stacks 041N**).

## Main results

* `AlgebraicGeometry.Space.separated_isLocalAtTarget_fpqc`: **Stacks 0421**.

## Implementation notes

The property is the already existing `AlgebraicGeometry.Space.separatedProperty`, which is what
`AlgebraicGeometry.Space.properProperty_isLocalAtTarget` consumes, so no new packaging of
separatedness is introduced here.

The two sides of Mathlib's `CategoryTheory.MorphismProperty.IsLocalAtTarget` speak of
`CategoryTheory.Limits.pullback.snd` in the category of algebraic spaces, whereas the diagonal
comparison and the covering families are stated for the presheaf fibre product of Stacks 02X2.
`AlgebraicGeometry.AlgebraicSpaces.hom_pullback_snd_iff` is that comparison, and it is used here
three times — once to read the local hypothesis on the diagonal of a base change, and twice to
move between the two fibre products of the diagonal's own base change.

Stacks 0420 is a theorem rather than an instance in this library, so it is introduced as a local
instance at `AlgebraicGeometry.Space.closedImmersionProperty` before the locality of the diagonal
is read off.

## References

* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 03KL](https://stacks.math.columbia.edu/tag/03KL)
* [Stacks Project, Tag 03MR](https://stacks.math.columbia.edu/tag/03MR)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 0420](https://stacks.math.columbia.edu/tag/0420)
* [Stacks Project, Tag 0421](https://stacks.math.columbia.edu/tag/0421)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

open Stacks.SeparationLocal

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0421.** Separatedness of morphisms of algebraic spaces over `S` is local on the
base for the fpqc topology: a morphism is separated exactly when its base change to every member
of some fpqc covering of its target is separated.

Separatedness of `f : X ⟶ Y` is the relative diagonal `Δ_f : X ⟶ X ×_Y X` being a closed
immersion. Pulling a covering `{Y i ⟶ Y}` back along `X ×_Y X ⟶ Y` gives a covering of `X ×_Y X`
whose base changes of `Δ_f` are the relative diagonals of the base changes of `f`, so Stacks
0420 for closed immersions applies. -/
@[stacks 0421, sga "4 IV 8.5.5" "more general"]
instance separated_isLocalAtTarget_fpqc :
    (separatedProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) := by
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff (P := separatedProperty B S hS)
    (K := Topology.precoverage.{u, v} .fpqc B S hS) fun X Y f R hR ↦
      ⟨fun hf U g _ _ ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback f g) hf, fun hlocal ↦ ?_⟩
  obtain ⟨I, Yi, gi, rfl, hcover⟩ := hR
  let : (closedImmersionProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) :=
    isClosedImmersion_isLocalAtTarget_fpqc B S hS
  let Q : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  have : Q.RespectsIso := MorphismProperty.relative_respectsIso _
  -- The relative diagonal of `f`, as a morphism of algebraic spaces to `X ×_Y X`.
  let Z : AlgebraicSpaces B S hS := AlgebraicSpaces.fiberProduct B S hS f f
  let d : X ⟶ Z := ObjectProperty.homMk (pullback.diagonal f.hom)
  let q : Z ⟶ Y := ObjectProperty.homMk (pullback.fst f.hom f.hom ≫ f.hom)
  -- The covering of `X ×_Y X` obtained by pulling the given covering back along `q`.
  let W : I → AlgebraicSpaces B S hS := fun i ↦ AlgebraicSpaces.fiberProduct B S hS (gi i) q
  let k : ∀ i, W i ⟶ Z := fun i ↦ ObjectProperty.homMk (pullback.snd (gi i).hom q.hom)
  have hmem : Presieve.ofArrows W k ∈ (Topology.precoverage.{u, v} .fpqc B S hS) Z :=
    ⟨I, W, k, rfl, Z.property, fun i ↦ (W i).property,
      isFpqcCovering_pullback B S hS gi q hcover.2.2⟩
  change closedImmersionProperty B S hS d
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (K := Topology.precoverage.{u, v} .fpqc B S hS) hmem ?_
  rintro U g _ ⟨i⟩
  refine (AlgebraicSpaces.hom_pullback_snd_iff B S hS Q d (k i)).mpr ?_
  -- The relative diagonal of the base change of `f` along `g i`, which is a closed immersion.
  have hsep : Q (pullback.diagonal (pullback.snd f.hom (gi i).hom)) :=
    (AlgebraicSpaces.hom_pullback_snd_iff B S hS Q.diagonal f (gi i)).mp (hlocal (gi i) (.mk i))
  -- The diagonal object of that base change is `Y i ×_Y (X ×_Y X)`.
  let e := (isPullback_diagonalObjMap f.hom (gi i).hom).isoIsPullback _ _
    (IsPullback.of_hasPullback (gi i).hom q.hom)
  have hdiag : IsPullback (pullback.fst f.hom (gi i).hom)
      (pullback.diagonal (pullback.snd f.hom (gi i).hom) ≫ e.hom)
      (pullback.diagonal f.hom) (pullback.snd (gi i).hom q.hom) :=
    (Stacks.SeparationLocal.isPullback_diagonal_pullbackSnd f.hom (gi i).hom).of_iso
      (Iso.refl _) (Iso.refl _) e (Iso.refl _) (by simp) (by simp) (by simp)
      ((isPullback_diagonalObjMap f.hom (gi i).hom).isoIsPullback_hom_snd _ _
        (IsPullback.of_hasPullback (gi i).hom q.hom)).symm
  let eL := hdiag.isoIsPullback _ _ (IsPullback.of_hasPullback
    (pullback.diagonal f.hom) (pullback.snd (gi i).hom q.hom))
  refine (Q.cancel_left_of_respectsIso eL.hom
    (pullback.snd (pullback.diagonal f.hom) (pullback.snd (gi i).hom q.hom))).mp ?_
  rw [hdiag.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback
    (pullback.diagonal f.hom) (pullback.snd (gi i).hom q.hom))]
  exact MorphismProperty.RespectsIso.postcomp Q e.hom _ hsep

end AlgebraicGeometry.Space

end
