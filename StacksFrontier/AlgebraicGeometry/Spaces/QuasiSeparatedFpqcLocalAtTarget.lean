module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.CategoryTheory.Limits.PullbackDiagonalBaseChange

/-!
# Quasi-separatedness of morphisms of algebraic spaces is fpqc local on the base (Stacks 041N)

Let `S` be a scheme contained in a big fppf site `B`. A morphism of algebraic spaces over `S` is
quasi-separated when its relative diagonal is quasi-compact (**Stacks 03HL**, part (3)), and that
condition is local on the target for the fpqc topology of **Stacks 03YH**. That is **Stacks
041N**, and the fppf form that the relative properties of Stacks 03YK ask for follows from it by
`CategoryTheory.MorphismProperty.IsLocalAtTarget.of_le` over
`AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage`.

## Main results

* `AlgebraicGeometry.Space.isQuasiSeparated_isLocalAtTarget_fpqc`: **Stacks 041N**.
* `AlgebraicGeometry.Space.isQuasiSeparated_isLocalAtTarget_fppf`: the same at the fppf
  precoverage.

## Implementation notes

The route is the one the source takes: quasi-separatedness of `f : X ⟶ Y` is carried across the
relative diagonal and then **Stacks 041L** is applied to `Δ_f : X ⟶ X ×_Y X`. Given an fpqc
covering `{Y i ⟶ Y}` of the target, the pullbacks `(X ×_Y X) ×_Y Y i` form an fpqc covering of
`X ×_Y X` by part (3) of **Stacks 03MR**, and the base change of `Δ_f` along each of them is the
relative diagonal of the base change `X ×_Y Y i ⟶ Y i`. So quasi-compactness of `Δ_f` follows
from quasi-compactness of those diagonals, which is the hypothesis.

Both halves of that last identification are
`CategoryTheory.Limits.isPullback_diagonal_pullbackSnd` and
`CategoryTheory.Limits.isPullback_pullbackSelfProductMap`, which are statements about an
arbitrary category with pullbacks and carry none of the geometry. Here they are applied in the
category of presheaves on the big fppf site of `S`, which is where the relative diagonal lives:
the category of algebraic spaces over `S` is a full subcategory of it closed under fibre
products, so `AlgebraicGeometry.Space.IsQuasiSeparated` is a condition on the *presheaf*
diagonal, and the two transfer lemmas below move between the fibre product chosen in presheaves
and the one chosen among algebraic spaces.

The converse direction of the locality — that a base change of a quasi-separated morphism is
quasi-separated — is `AlgebraicGeometry.Space.isQuasiSeparated_pullback` of **Stacks
03KL**, registered as a `CategoryTheory.MorphismProperty.IsStableUnderBaseChange` instance, so
nothing about fpqc coverings is needed for it.

With this instance `AlgebraicGeometry.Space.quasiSeparatedProperty` has the two instance
arguments of Stacks 03YK, so `AlgebraicGeometry.Stack.HasRelativeProperty` at it is statable with
no hypothesis; stability under composition, which is what Stacks 045B asks for on top, is Stacks
03KQ and is `AlgebraicGeometry.Space.quasiSeparatedProperty_isStableUnderComposition` in
`StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedComposition`.

The tag proved here belongs to Chapter 74.

## References

* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 03KL](https://stacks.math.columbia.edu/tag/03KL)
* [Stacks Project, Tag 03MR](https://stacks.math.columbia.edu/tag/03MR)
* [Stacks Project, Tag 041L](https://stacks.math.columbia.edu/tag/041L)
* [Stacks Project, Tag 041N](https://stacks.math.columbia.edu/tag/041N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism property of algebraic spaces over `S` which respects isomorphisms holds for the
second projection of the chosen fibre product exactly when it holds for the underlying morphism of
presheaves. The two projections differ by the comparison isomorphism of two cartesian squares on
one cospan. -/
private theorem pullback_snd_iff_homMk {P : MorphismProperty (AlgebraicSpaces B S hS)}
    [P.RespectsIso] {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Z) (g : Y ⟶ Z) :
    P (pullback.snd f g) ↔ P (ObjectProperty.homMk (pullback.snd f.hom g.hom) :
      AlgebraicSpaces.fiberProduct B S hS f g ⟶ Y) := by
  rw [← (AlgebraicSpaces.isPullback_fiberProduct B S hS f g).isoIsPullback_hom_snd _ _
    (IsPullback.of_hasPullback f g)]
  exact (MorphismProperty.cancel_left_of_respectsIso P _ _).symm

/-- Quasi-separatedness of the second projection of the chosen fibre product in the category of
algebraic spaces over `S`, read on the underlying morphism of presheaves. -/
theorem isQuasiSeparated_pullback_snd_hom {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Z) (g : Y ⟶ Z)
    (hf : quasiSeparatedProperty B S hS (pullback.snd f g)) :
    IsQuasiSeparated B S hS (pullback.snd f.hom g.hom) :=
  (pullback_snd_iff_homMk B S hS (P := quasiSeparatedProperty B S hS) f g).mp hf

/-- Quasi-compactness of the underlying morphism of presheaves of the second projection of the
chosen fibre product in the category of algebraic spaces over `S`, read back as the packaged
property. This is the converse of `AlgebraicGeometry.Space.isQuasiCompact_pullback_snd_hom`. -/
theorem quasiCompactProperty_pullback_snd {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Z) (g : Y ⟶ Z)
    (hf : IsQuasiCompact B S hS (pullback.snd f.hom g.hom)) :
    quasiCompactProperty B S hS (pullback.snd f g) := by
  have : (quasiCompactProperty B S hS).IsStableUnderBaseChange :=
    ⟨fun sq hg => isQuasiCompact_of_isPullback B S hS
      (AlgebraicSpaces.isPullback_hom B S hS sq) hg⟩
  have : (quasiCompactProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (pullback_snd_iff_homMk B S hS (P := quasiCompactProperty B S hS) f g).mpr hf

/-- The base change of the relative diagonal of `f` along the projection of `(X ×_Y X) ×_Y Y'` is
quasi-compact as soon as the base change of `f` along `g : Y' ⟶ Y` is quasi-separated: that base
change of the diagonal *is* the relative diagonal of the base change, up to the comparison
isomorphism identifying `(X ×_Y Y') ×_{Y'} (X ×_Y Y')` with `(X ×_Y X) ×_Y Y'`. -/
theorem isQuasiCompact_diagonal_pullback
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hf : IsQuasiSeparated B S hS (pullback.snd f g)) :
    IsQuasiCompact B S hS (pullback.snd (pullback.diagonal f)
      (pullback.snd g (pullback.fst f f ≫ f))) := by
  have hcomp := isPullback_pullbackSelfProductMap f g
  have hchosen := IsPullback.of_hasPullback g (pullback.fst f f ≫ f)
  have he : (hcomp.isoIsPullback _ _ hchosen).hom ≫
      pullback.snd g (pullback.fst f f ≫ f) = pullbackSelfProductMap f g :=
    hcomp.isoIsPullback_hom_snd _ _ hchosen
  have hdiag : IsPullback (pullback.fst f g)
      (pullback.diagonal (pullback.snd f g) ≫ (hcomp.isoIsPullback _ _ hchosen).hom)
      (pullback.diagonal f) (pullback.snd g (pullback.fst f f ≫ f)) := by
    refine (isPullback_diagonal_pullbackSnd f g).of_iso (Iso.refl _) (Iso.refl _)
      (hcomp.isoIsPullback _ _ hchosen) (Iso.refl _) (by simp) (by simp) (by simp) ?_
    simp [he]
  have h₂ : quasiCompactPresheafProperty B S hS
      (hdiag.isoPullback.hom ≫ pullback.snd (pullback.diagonal f)
        (pullback.snd g (pullback.fst f f ≫ f))) := by
    rw [IsPullback.isoPullback_hom_snd]
    exact MorphismProperty.RespectsIso.postcomp _ _ _ hf
  exact (MorphismProperty.cancel_left_of_respectsIso (quasiCompactPresheafProperty B S hS)
    hdiag.isoPullback.hom _).mp h₂

/-- **Stacks 041N.** Quasi-separatedness of a morphism of algebraic spaces over `S` is local on
the target for the fpqc topology.

One direction is stability under base change (**Stacks 03KL**). In the other, quasi-separatedness
of `f : X ⟶ Y` is quasi-compactness of `Δ_f : X ⟶ X ×_Y X`; the given fpqc covering of `Y` pulls
back to one of `X ×_Y X` by part (3) of **Stacks 03MR**, the base change of `Δ_f` along each
member of it is the relative diagonal of the corresponding base change of `f`, and so
quasi-compactness of `Δ_f` follows from **Stacks 041L**. -/
@[stacks 041N, ega "IV 2.7.1" "more general", sga "4 IV 8.5.5" "more general"]
instance isQuasiSeparated_isLocalAtTarget_fpqc :
    (quasiSeparatedProperty B S hS).IsLocalAtTarget
      (Topology.fpqc.precoverage.{u, v} B S hS) := by
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff
    (P := quasiSeparatedProperty B S hS) ?_
  rintro X Y f R ⟨I, Yi, gi, rfl, hcover⟩
  refine ⟨fun hf U g _ _ =>
    MorphismProperty.pullback_snd (P := quasiSeparatedProperty B S hS) f g hf, fun hlocal => ?_⟩
  let Z := AlgebraicSpaces.fiberProduct B S hS f f
  let q : Z ⟶ Y := ObjectProperty.homMk (pullback.fst f.hom f.hom ≫ f.hom)
  let d : X ⟶ Z := ObjectProperty.homMk (pullback.diagonal f.hom)
  let W : I → AlgebraicSpaces B S hS := fun i => AlgebraicSpaces.fiberProduct B S hS (gi i) q
  let k : ∀ i, W i ⟶ Z := fun i => ObjectProperty.homMk (pullback.snd (gi i).hom q.hom)
  have hcov : Topology.IsCovering .fpqc B S hS (fun i => (W i).obj) (fun i => (k i).hom) :=
    ⟨Z.property, fun i => (W i).property, isFpqcCovering_pullback B S hS gi q hcover.2.2⟩
  have hmem : (Presieve.ofArrows W k) ∈ (Topology.fpqc.precoverage.{u, v} B S hS) Z :=
    ⟨I, W, k, rfl, hcov⟩
  change quasiCompactProperty B S hS d
  exact MorphismProperty.IsLocalAtTarget.of_zeroHypercover (P := quasiCompactProperty B S hS)
    (⟨{ I₀ := I, X := W, f := k }, hmem⟩ : Precoverage.ZeroHypercover.{v} _ Z) fun i =>
      quasiCompactProperty_pullback_snd B S hS d (k i)
        (isQuasiCompact_diagonal_pullback B S hS f.hom (gi i).hom
          (isQuasiSeparated_pullback_snd_hom B S hS f (gi i)
            (hlocal (gi i) (Presieve.ofArrows.mk i))))

/-- **Stacks 041N** at the fppf precoverage: quasi-separatedness of a morphism of algebraic
spaces over `S` is local at the target for the fppf topology. This is the form in which Stacks
03YK's relative properties ask for it, and it follows from the fpqc form because every fppf
covering family of algebraic spaces is an fpqc covering family. -/
@[sga "4 IV 8.5.5" "special case"]
instance isQuasiSeparated_isLocalAtTarget_fppf :
    (quasiSeparatedProperty B S hS).IsLocalAtTarget
      (Topology.fppf.precoverage.{u, v} B S hS) :=
  .of_le (fppfPrecoverage_le_fpqcPrecoverage B S hS)

end AlgebraicGeometry.Space

end
