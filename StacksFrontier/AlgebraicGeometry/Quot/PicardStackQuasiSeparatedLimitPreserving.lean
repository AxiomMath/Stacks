module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentToBaseLimitPreservingOnObjects
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentToBaseRelativeDiagonal
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOverBase

/-!
# The Picard stack is quasi-separated and limit preserving over the base

Let `f : X ⟶ B` be a morphism of algebraic spaces over `S` which is flat, proper and of finite
presentation, the standing hypotheses of Section 0DM9. Stacks 0DMB says that the structure
morphism `Picardstack_{X/B} ⟶ B` is quasi-separated and locally of finite presentation. Its proof:
`Picardstack_{X/B}` is an open substack of `Cohstack_{X/B}` (Stacks 0D03), so this follows from
the same statement for `Cohstack_{X/B} ⟶ B` (Stacks 0DLZ).

Here `Picardstack_{X/B}` is a category fibred in groupoids over the big fppf site of `S`, and both
properties are stated in the form that makes sense for categories fibred in groupoids:

* *quasi-separated* (Stacks 04YW): the relative diagonal of the structure morphism is
  representable by algebraic spaces, quasi-compact and quasi-separated (Stacks 04XB);
* *locally of finite presentation*: the structure morphism is limit preserving on objects
  (Stacks 06CU), which for a 1-morphism of algebraic stacks is equivalent to local finite
  presentation (Stacks 0CMY, `AlgebraicGeometry.Stack.AlgebraicStacks.isLimitPreserving_tfae`).

The structure morphism is the natural map `Picardstack_{X/B} ⟶ Cohstack_{X/B}` followed by the
projection `Cohstack_{X/B} ⟶ 𝒮_B`
(`AlgebraicGeometry.Space.picardToCoherent_comp_coherentToBaseCFG`).

## Main results

* `AlgebraicGeometry.Space.PicardOverBase.quasiSeparated_limitPreservingOnObjects_picardToBase`:
  for `f : X ⟶ B` flat, proper and of finite presentation, the structure morphism
  `Picardstack_{X/B} ⟶ 𝒮_B` is quasi-separated and limit preserving on objects.

## References

* [Stacks Project, Tag 0DMB](https://stacks.math.columbia.edu/tag/0DMB)
* [Stacks Project, Tag 0DLZ](https://stacks.math.columbia.edu/tag/0DLZ)
* [Stacks Project, Tag 0D03](https://stacks.math.columbia.edu/tag/0D03)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 0CMY](https://stacks.math.columbia.edu/tag/0CMY)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space.PicardOverBase

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Let `f : X ⟶ B` be a morphism of algebraic spaces over `S` which is flat, proper and of finite
presentation. Then the structure morphism `Picardstack_{X/B} ⟶ 𝒮_B` is quasi-separated, i.e. its
relative diagonal is representable by algebraic spaces, quasi-compact and quasi-separated
(Stacks 04YW, 04XB), and locally of finite presentation in the sense of categories fibred in
groupoids, i.e. limit preserving on objects (Stacks 06CU; for a 1-morphism of algebraic stacks
this is local finite presentation, Stacks 0CMY). -/
@[stacks 0DMB "quasi-separated: the relative diagonal is representable by algebraic spaces, \
quasi-compact and quasi-separated; locally of finite presentation: limit preserving on objects"]
theorem quasiSeparated_limitPreservingOnObjects_picardToBase
    (s : PicardSituation B S hS) (hfp : IsFinitePresentation B S hS s.f.hom)
    (hflat : IsFlat B S hS s.f.hom) (hproper : IsProper B S hS s.f.hom) :
    (∃ _ : Stack.IsRepresentableByAlgebraicSpaces B S hS
        (Stack.relativeDiagonal.{u, u + 1, u + 1} B S hS _ _
          (picardToBase (modulePushforwardCoherence B S hS) s)).hom,
      Stack.IsQuasiCompact B S hS
          (Stack.relativeDiagonal.{u, u + 1, u + 1} B S hS _ _
            (picardToBase (modulePushforwardCoherence B S hS) s)) ∧
        Stack.IsQuasiSeparated B S hS
          (Stack.relativeDiagonal.{u, u + 1, u + 1} B S hS _ _
            (picardToBase (modulePushforwardCoherence B S hS) s))) ∧
      BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS _ _
        (picardToBase (modulePushforwardCoherence B S hS) s) := by
  let D : CoherentSituation B S hS := ⟨s.X, s.base, s.f, hfp⟩
  obtain ⟨hrep, hqc, hqs⟩ := CoherentSituation.relativeDiagonal_coherentToBaseCFG D
  exact ⟨relativeDiagonal_picardToCoherent_comp D hflat hproper _ hrep hqc hqs,
    isLimitPreservingOnObjects_picardToCoherent_comp D hflat hproper _
      (isLimitPreservingOnObjects_coherentToBaseCFG D)⟩

end AlgebraicGeometry.Space.PicardOverBase

end
