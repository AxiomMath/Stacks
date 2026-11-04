module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentStackDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.IsStackFromRepresentableDiagonal

/-!
# The stack of coherent sheaves as a stack in groupoids and as an algebraic stack

In the standing data of Stacks 08KB — a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` of a big fppf site, of finite presentation — write `𝒳 = Coh_{X/Y}` for the category of
coherent sheaves with proper support of that tag.  Stacks 08KC asserts that the projection
`p : 𝒳 ⟶ (Sch/S)_fppf` is a stack in groupoids, and Stacks 09DS asserts that for `f` of finite
presentation *and separated* the category `𝒳` is an algebraic stack over `S`.

This file records how far the development gets towards those two statements, and exactly what is
missing.  **Neither tag is carried here**, and the reasons are different for the two; see the
implementation notes.

## Main results

* `AlgebraicGeometry.Space.coherentIsomPresheaf_isSheaf`: clause (2) of Stacks 02ZI for
  `Coh_{X/Y}` — the isomorphism presheaves are sheaves — granted the conclusion of Stacks 08W6
  in the form of condition (2) of Stacks 045G.  This is the step the proof of Stacks 08KC takes
  when it says that the statement on `Isom` follows from Stacks 08W6 via Stacks 045G.
* `AlgebraicGeometry.Space.coherentProjection_isStack` and
  `AlgebraicGeometry.Space.coherentProjection_isStackInGroupoids`: the conclusion of
  Stacks 08KC, granted in addition the effectivity of fppf descent data for `Coh_{X/Y}`.

## Implementation notes

**What is proved, and what is granted.**  The projection of `Coh_{X/Y}` to the schemes of the
site is fibred in groupoids by Stacks 08W5
(`AlgebraicGeometry.Space.coherentProjection_isFiberedInGroupoids`, itself conditional on the
three base-change stability results carried by `hst`), and that is clause (1) of Stacks 02ZI.
Clause (2) is obtained from the conclusion of Stacks 08W6 by
`AlgebraicGeometry.Stack.isSheaf_isomPresheaf_of_hasRepresentableDiagonal`.  Clause (3),
effectivity of descent data, is granted: it is the bulk of the proof of Stacks 08KC in the
source, and it needs the effectivity clause of Stacks 04W8 for quasi-coherent modules on
algebraic spaces together with the descent of flatness (Stacks 05VY), of finite presentation
(Stacks 060V) and of properness of the scheme-theoretic support (Stacks 0422, with Stacks 089C
for the compatibility of the support with flat base change).  The effectivity clause of
Stacks 04W8 is not carried in this development.

**Why there is no tag.**  Clause (2) rests on the conclusion of Stacks 08W6, which is itself not
carried (see `StacksFrontier/AlgebraicGeometry/Stacks/CoherentStackDiagonal.lean`: Proposition 08K9
and the reduction to a common base map over the equalizer are both absent), and clause (3) rests
on a hypothesis with no proof behind it.  Deleting the two hypotheses leaves only clause (1),
which is Stacks 08W5 and is already carried elsewhere.  A `@[stacks 08KC]` attribute here would
therefore claim the tag on the strength of its own hypotheses, so none is attached.

Stacks 09DS is further away still and no statement of it appears below.  Beyond Stacks 08KC and
Stacks 08W6 it needs a scheme `W` and a smooth surjective `W ⟶ 𝒳`, which the source obtains from
Artin's Axioms, Lemma 07Y4 after verifying axioms [0]–[3] (Stacks 08KC, 08KD, 08LQ, 08W8),
Stacks 08W9, openness of versality through Artin's Axioms, Lemma 0CXU, and the strong formal
effectiveness of Flatness on Spaces, Theorem 0CXB.  None of 07Y4, 08KD, 08LQ, 08W8, 08W9, 0CXU,
0CXB is carried anywhere in this development, and the separatedness hypothesis of Stacks 09DS —
which distinguishes it from Situation 08KB, where `f` is only of finite presentation — enters
exactly there.  Writing the conclusion of Stacks 09DS with all of that granted would leave a
statement with no content at all, so it is not written.

## References

* [Stacks Project, Tag 08KC](https://stacks.math.columbia.edu/tag/08KC)
* [Stacks Project, Tag 09DS](https://stacks.math.columbia.edu/tag/09DS)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 08W5](https://stacks.math.columbia.edu/tag/08W5)
* [Stacks Project, Tag 08W6](https://stacks.math.columbia.edu/tag/08W6)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {hc : ModulePushforwardCoherence B S hS} {D : CoherentSituation B S hS}

/-- **Clause (2) of Stacks 02ZI for `Coh_{X/Y}`**, granted the conclusion of Stacks 08W6.  Each
isomorphism presheaf `Isom(x, y)` of two objects of a fibre of `Coh_{X/Y}` is a sheaf for the
topology induced on the slice of the big fppf site of `S` at the scheme the fibre sits over.

This is the step the proof of Stacks 08KC makes when it says that the statement on `Isom` follows
from Stacks 08W6 by Algebraic Stacks, Lemma 045G: by Stacks 045G the isomorphism presheaf is an
algebraic space, and an algebraic space is an fppf sheaf.  The hypothesis `h045G2` is condition
(2) of Stacks 045G for `Coh_{X/Y}`, equivalent to the conclusion of Stacks 08W6 by
`AlgebraicGeometry.Space.coherentHasRepresentableDiagonal`. -/
theorem coherentIsomPresheaf_isSheaf (hst : ModulePullbackStability B S hS)
    (cd : CoherentCategoryData hc D)
    (h045G2 : Stack.IsAlgebraicSpaceIsomPresheaf B S hS
      (coherentCatFiberedInGroupoids hst cd)) :
    letI : (coherentBasedCategory cd).p.IsFibered :=
      (coherentCatFiberedInGroupoids hst cd).isFiberedInGroupoids.isFibered
    ∀ (U : BigFppfOver B S hS) (x y : (coherentBasedCategory cd).p.Fiber U),
      Presheaf.IsSheaf ((BigFppfOver.topology B S hS).over U)
        ((coherentBasedCategory cd).p.isomPresheaf x y) :=
  Stack.isSheaf_isomPresheaf_of_isAlgebraicSpaceIsomPresheaf B S hS
    (coherentCatFiberedInGroupoids hst cd) h045G2

/-- The conclusion of Stacks 08KC in the sieve-indexed form of Stacks 026F: the projection
`p : Coh_{X/Y} ⟶ (Sch/S)_fppf` is a stack.

**This carries no tag.**  Clause (1) is Stacks 08W5; clause (2) comes from `h045G2`, which is the
conclusion of Stacks 08W6 and is not carried in this development; clause (3) is `hdesc`, the
effectivity of fppf descent data, which is the bulk of the proof in the source and rests on the
effectivity clause of Stacks 04W8 together with Stacks 05VY, 060V, 0422 and 089C, none of which
is carried.  See the implementation notes of the file. -/
theorem coherentProjection_isStack (hst : ModulePullbackStability B S hS)
    (cd : CoherentCategoryData hc D)
    (h045G2 : Stack.IsAlgebraicSpaceIsomPresheaf B S hS
      (coherentCatFiberedInGroupoids hst cd))
    (hdesc : letI : (coherentBasedCategory cd).p.IsFibered :=
        (coherentCatFiberedInGroupoids hst cd).isFiberedInGroupoids.isFibered
      (coherentBasedCategory cd).p.HasEffectiveDescent (BigFppfOver.topology B S hS)) :
    (coherentBasedCategory cd).p.IsStack (BigFppfOver.topology B S hS) :=
  Stack.isStack_of_hasRepresentableDiagonal B S hS (coherentCatFiberedInGroupoids hst cd)
    (coherentHasRepresentableDiagonal hst cd h045G2) hdesc

/-- The conclusion of Stacks 08KC in the family-indexed form of Stacks 02ZI: the projection
`p : Coh_{X/Y} ⟶ (Sch/S)_fppf` is a stack in groupoids.

**This carries no tag**, for the reasons given on
`AlgebraicGeometry.Space.coherentProjection_isStack` and in the implementation notes of the
file. -/
theorem coherentProjection_isStackInGroupoids (hst : ModulePullbackStability B S hS)
    (cd : CoherentCategoryData hc D)
    (h045G2 : Stack.IsAlgebraicSpaceIsomPresheaf B S hS
      (coherentCatFiberedInGroupoids hst cd))
    (hdesc : letI : (coherentBasedCategory cd).p.IsFibered :=
        (coherentCatFiberedInGroupoids hst cd).isFiberedInGroupoids.isFibered
      (coherentBasedCategory cd).p.HasEffectiveDescent (BigFppfOver.topology B S hS)) :
    (coherentBasedCategory cd).p.IsStackInGroupoids.{w} (BigFppfOver.topology B S hS) :=
  Stack.isStackInGroupoids_of_hasRepresentableDiagonal B S hS
    (coherentCatFiberedInGroupoids hst cd)
    (coherentHasRepresentableDiagonal hst cd h045G2) hdesc

end AlgebraicGeometry.Space

end
