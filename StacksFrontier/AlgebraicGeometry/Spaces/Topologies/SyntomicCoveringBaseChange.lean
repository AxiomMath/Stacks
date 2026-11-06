module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Syntomic
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback

/-!
# Base change of syntomic coverings of algebraic spaces (Stacks 041B, base change)

Let `S` be a scheme contained in a big fppf site `B`. Given a syntomic covering `{Yᵢ ⟶ X}` of an
algebraic space over `S` and an arbitrary morphism `g : X' ⟶ X` into its target, the first
projections `X' ×_X Yᵢ ⟶ X'` of the presheaf fibre products form a syntomic covering of `X'`.
This is part (3) of **Stacks 041B**; part (1) is
`AlgebraicGeometry.Space.isSyntomicCovering_of_isIso` in
`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SyntomicCoverings`, and part (2) is
`AlgebraicGeometry.Space.isSyntomicCovering_comp` in
`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SyntomicCoveringComposition`.

## Main results

* `AlgebraicGeometry.Space.isSyntomic_of_isPullback`: **Stacks 03Z9**, read off a cartesian
  square.
* `AlgebraicGeometry.Space.isSyntomicCovering_pullback`: **Stacks 041B**, the base-change
  clause.

## Implementation notes

Each member of the base-changed family sits in the cartesian square of
`AlgebraicGeometry.Space.AlgebraicSpaces.isPullback_fiberProduct`, so it is syntomic because
syntomic morphisms of algebraic spaces are stable under base change (**Stacks 03Z9**). Joint
surjectivity is **Stacks 03H4**: a point of `X'` and a point of some `Yᵢ` lying over its image
in `X` amalgamate to a point of the fibre product, which is
`AlgebraicGeometry.Space.exists_point_of_isPullback`.

The family is stated for the *first* projections, as for the other four topologies of
Stacks 03YH. The orientation with second projections, which the source-locality transfer
consumes, is `AlgebraicGeometry.Space.isSyntomicCovering_pullback_snd` in
`StacksFrontier.AlgebraicGeometry.Spaces.SyntomicSourceLocalityTransfer`.

## References

* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03Z9](https://stacks.math.columbia.edu/tag/03Z9)
* [Stacks Project, Tag 041B](https://stacks.math.columbia.edu/tag/041B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Base change of a syntomic morphism in a cartesian square -/

/-- **Stacks 03Z9**, read off a cartesian square: in a pullback square of algebraic spaces over
`S`, the base change of a syntomic morphism is syntomic. -/
theorem isSyntomic_of_isPullback {X' X Z Y : AlgebraicSpaces B S hS}
    (p : X' ⟶ X) (f' : X' ⟶ Z) (f : X ⟶ Y) (g : Z ⟶ Y)
    (h : IsPullback p f' f g) (hf : IsSyntomic B S hS f.hom) :
    IsSyntomic B S hS f'.hom :=
  (isSyntomic_isStableUnderBaseChange B S hS).of_isPullback h hf

/-! ### Stacks 041B, the base-change clause -/

/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search for
them times out under Lean v4.35.0. -/
private instance (priority := high) hasPullback_presheaf_syntomicCoveringBaseChange
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
/-- **Stacks 041B**, the base-change clause. The first projections of the presheaf fibre
products of a syntomic covering of an algebraic space over `S` with a morphism `g` into its
target form a syntomic covering of the source of `g`. -/
@[stacks 041B "part (3), base change"]
theorem isSyntomicCovering_pullback {I : Type v}
    {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : X' ⟶ X) (hX' : IsAlgebraicSpace B S hS X')
    (Y : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, Y i ⟶ X)
    (h : IsSyntomicCovering B S hS Y f) :
    IsSyntomicCovering B S hS (fun i => pullback g (f i))
      (fun i => pullback.fst g (f i)) := by
  let XObj : AlgebraicSpaces B S hS := ⟨X, h.target_isAlgebraicSpace⟩
  let X'Obj : AlgebraicSpaces B S hS := ⟨X', hX'⟩
  let YObj (i : I) : AlgebraicSpaces B S hS := ⟨Y i, h.source_isAlgebraicSpace i⟩
  let gObj : X'Obj ⟶ XObj := ObjectProperty.homMk g
  let fObj (i : I) : YObj i ⟶ XObj := ObjectProperty.homMk (f i)
  let pObj (i : I) : AlgebraicSpaces.fiberProduct B S hS gObj (fObj i) ⟶ X'Obj :=
    ObjectProperty.homMk (pullback.fst g (f i))
  let qObj (i : I) : AlgebraicSpaces.fiberProduct B S hS gObj (fObj i) ⟶ YObj i :=
    ObjectProperty.homMk (pullback.snd g (f i))
  have hsquare (i : I) : IsPullback (pObj i) (qObj i) gObj (fObj i) :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS gObj (fObj i)
  refine ⟨hX', fun i => isAlgebraicSpace_pullback B S hS g (f i) hX'
      (h.source_isAlgebraicSpace i) h.target_isAlgebraicSpace,
    fun i => isSyntomic_of_isPullback B S hS (qObj i) (pObj i) (fObj i) gObj
      (hsquare i).flip (h.syntomic i), ?_⟩
  refine Set.eq_univ_of_forall fun x' => ?_
  obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp h.jointly_surjective
    (pointsMap B S hS X' g x'))
  obtain ⟨wpt, hwp, -⟩ := exists_point_of_isPullback B S hS (hsquare i) x' y hy.symm
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_range.mpr ⟨wpt, hwp⟩⟩

end AlgebraicGeometry.Space

end
