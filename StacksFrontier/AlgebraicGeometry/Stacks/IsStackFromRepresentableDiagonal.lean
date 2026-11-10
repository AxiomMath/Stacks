module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.CategoryTheory.Sites.Stack.GroupoidTFAE
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge

/-!
# A representable diagonal makes the isomorphism presheaves sheaves

Let `S` be a scheme contained in a big fppf site `B` and let `𝒳` be a category fibred in groupoids
over the big fppf site of `S`.  If the diagonal of `𝒳` is representable by algebraic spaces then
each isomorphism presheaf `Isom(x, y)` of two objects of a fibre is a *sheaf* on the slice site,
because by Stacks 045G it is an algebraic space and an algebraic space is by definition an fppf
sheaf (Stacks 025Y).

This is the half of the argument that the proof of Stacks 08KC makes when it says that "the
statement on `Isom` follows from Lemma 08W6, see Algebraic Stacks, Lemma 045G", and it is the
reason a category fibred in groupoids with representable diagonal needs only the effectivity of
descent data in order to be a stack.  Nothing here is specific to any particular `𝒳`.

## Main results

* `AlgebraicGeometry.Stack.isSheaf_isomPresheaf_of_isAlgebraicSpaceIsomPresheaf`: condition (2)
  of Stacks 045G makes each `Isom(x, y)` a sheaf on the slice site.
* `AlgebraicGeometry.Stack.isSheaf_isomPresheaf_of_hasRepresentableDiagonal`: the same from
  condition (1) of Stacks 045G, that is from a diagonal representable by algebraic spaces.
* `AlgebraicGeometry.Stack.isStack_of_hasRepresentableDiagonal` and
  `AlgebraicGeometry.Stack.isStackInGroupoids_of_hasRepresentableDiagonal`: a category fibred in
  groupoids over the big fppf site of `S` whose diagonal is representable by algebraic spaces and
  relative to which descent data are effective is a stack in the sense of Stacks 026F and a stack
  in groupoids in the sense of Stacks 02ZI.

## Implementation notes

Condition (2) of Stacks 045G, `AlgebraicGeometry.Stack.IsAlgebraicSpaceIsomPresheaf`, supplies an
algebraic space `F` on the big fppf site *of `U`* together with an isomorphism of `F` with the
restriction of `Isom(x, y)` along `CategoryTheory.Over.iteratedSliceBackward`, both sides lifted
to a common universe; the sheaf condition wanted is for `Isom(x, y)` itself, on the *slice* of the
big fppf site of `S` at `U`.  Three transports bridge the two.  The universe lifts are removed by
`CategoryTheory.Presieve.isSheaf_comp_uliftFunctor_iff`, which is an equivalence and so may be
used in either direction.  The change of site is the equivalence `Over.iteratedSliceEquiv U`,
whose two functors are continuous for the two topologies; the direction needed here is the one
that pushes a sheaf *forward*, so it is the continuity of `Over.iteratedSliceForward` that is
used, applied to the restricted presheaf and then composed back with the unit of the equivalence.
The topologies have to be presented as `B.topology.over U.left` and
`(B.topology.over (B.obj hS)).over U` for the continuity instances to be found, which is what the
`change` in the proof does.

The passage from the two conditions to the stack conditions is the equivalence (1) ⟺ (3) of
Stacks 02ZJ, `CategoryTheory.Functor.stackInGroupoids_tfae`, and then the implication (3) ⟹ (1)
of the same tag, `CategoryTheory.Functor.IsStack.isStackInGroupoids`, for the family-indexed
rendering.  No tag attribute sits on anything in this file: the statements are the general
implications that the proofs of 045G and 02ZJ already carry combined with the sheaf clause of
Stacks 025Y, not a new assertion of the source.

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 02ZJ](https://stacks.math.columbia.edu/tag/02ZJ)
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))

/-- **Condition (2) of Stacks 045G makes the isomorphism presheaves sheaves.**  If every
isomorphism presheaf `Isom(x, y)` of two objects of a fibre of `𝒳` is an algebraic space over the
scheme the fibre sits over, then it is a sheaf for the topology induced on the slice of the big
fppf site of `S` at that scheme: an algebraic space is an fppf sheaf by the first clause of
Stacks 025Y, and the two sites and the two universes are matched by the equivalence
`CategoryTheory.Over.iteratedSliceEquiv` and by
`CategoryTheory.Presieve.isSheaf_comp_uliftFunctor_iff`. -/
theorem isSheaf_isomPresheaf_of_isAlgebraicSpaceIsomPresheaf
    (h : IsAlgebraicSpaceIsomPresheaf B S hS 𝒳) :
    letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
    ∀ (U : BigFppfOver B S hS) (x y : 𝒳.val.p.Fiber U),
      Presheaf.IsSheaf ((BigFppfOver.topology B S hS).over U)
        (𝒳.val.p.isomPresheaf x y) := by
  have : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  intro U x y
  obtain ⟨F, hF, ⟨i⟩⟩ := h U x y
  have hcont : (Over.iteratedSliceForward U).IsContinuous
      ((BigFppfOver.topology B S hS).over U) (BigFppfOver.topology B U.left.1 U.left.2) := by
    change (Over.iteratedSliceForward U).IsContinuous
      ((B.topology.over (B.obj hS)).over U) (B.topology.over U.left)
    infer_instance
  have h1 : Presheaf.IsSheaf (BigFppfOver.topology B U.left.1 U.left.2)
      (F ⋙ uliftFunctor.{v, u}) := by
    rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff,
      ← isSheaf_iff_isSheaf_of_type]
    exact hF.isSheaf
  have h2 : Presieve.IsSheaf (BigFppfOver.topology B U.left.1 U.left.2)
      ((Over.iteratedSliceBackward U).op ⋙
        (𝒳.val.p.isomPresheaf x y ⋙ uliftFunctor.{u, v})) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp ((Presheaf.isSheaf_of_iso_iff i).mp h1)
  have h3 : Presieve.IsSheaf ((BigFppfOver.topology B S hS).over U)
      ((Over.iteratedSliceForward U).op ⋙ ((Over.iteratedSliceBackward U).op ⋙
        (𝒳.val.p.isomPresheaf x y ⋙ uliftFunctor.{u, v}))) :=
    (Over.iteratedSliceForward U).op_comp_isSheaf_of_isSheaf_type
      (J := (BigFppfOver.topology B S hS).over U)
      (K := BigFppfOver.topology B U.left.1 U.left.2) h2
  have h4 : Presieve.IsSheaf ((BigFppfOver.topology B S hS).over U)
      (𝒳.val.p.isomPresheaf x y ⋙ uliftFunctor.{u, v}) :=
    Presieve.isSheaf_iso _
      (Functor.isoWhiskerRight (Over.iteratedSliceEquiv U).op.unitIso
        (𝒳.val.p.isomPresheaf x y ⋙ uliftFunctor.{u, v})).symm h3
  rw [isSheaf_iff_isSheaf_of_type]
  exact (Presieve.isSheaf_comp_uliftFunctor_iff
    ((BigFppfOver.topology B S hS).over U)).mp h4

/-- **A diagonal representable by algebraic spaces makes the isomorphism presheaves sheaves.**
This is `AlgebraicGeometry.Stack.isSheaf_isomPresheaf_of_isAlgebraicSpaceIsomPresheaf` read
through the equivalence of conditions (1) and (2) of Stacks 045G. -/
theorem isSheaf_isomPresheaf_of_hasRepresentableDiagonal
    (h : HasRepresentableDiagonal B S hS 𝒳) :
    letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
    ∀ (U : BigFppfOver B S hS) (x y : 𝒳.val.p.Fiber U),
      Presheaf.IsSheaf ((BigFppfOver.topology B S hS).over U)
        (𝒳.val.p.isomPresheaf x y) :=
  isSheaf_isomPresheaf_of_isAlgebraicSpaceIsomPresheaf B S hS 𝒳
    ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).mp h)

/-- **A category fibred in groupoids with representable diagonal and effective descent is a
stack.**  The isomorphism presheaves are sheaves by
`AlgebraicGeometry.Stack.isSheaf_isomPresheaf_of_hasRepresentableDiagonal`, so the first clause
of Stacks 02ZJ holds, and the equivalence of that tag turns it into the stack condition of
Stacks 026F. -/
theorem isStack_of_hasRepresentableDiagonal (h : HasRepresentableDiagonal B S hS 𝒳)
    (hdesc : letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
      𝒳.val.p.HasEffectiveDescent (BigFppfOver.topology B S hS)) :
    𝒳.val.p.IsStack (BigFppfOver.topology B S hS) := by
  have key := (Functor.stackInGroupoids_tfae 𝒳.val.p (BigFppfOver.topology B S hS)).out 1 3
  exact (key.mp ⟨𝒳.isFiberedInGroupoids,
    isSheaf_isomPresheaf_of_hasRepresentableDiagonal B S hS 𝒳 h, hdesc⟩).2

/-- **A category fibred in groupoids with representable diagonal and effective descent is a stack
in groupoids.**  This is `AlgebraicGeometry.Stack.isStack_of_hasRepresentableDiagonal` followed by
the implication (3) ⟹ (1) of Stacks 02ZJ. -/
theorem isStackInGroupoids_of_hasRepresentableDiagonal (h : HasRepresentableDiagonal B S hS 𝒳)
    (hdesc : letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
      𝒳.val.p.HasEffectiveDescent (BigFppfOver.topology B S hS)) :
    𝒳.val.p.IsStackInGroupoids.{w'} (BigFppfOver.topology B S hS) :=
  (isStack_of_hasRepresentableDiagonal B S hS 𝒳 h hdesc).isStackInGroupoids
    𝒳.isFiberedInGroupoids

end AlgebraicGeometry.Stack

end
