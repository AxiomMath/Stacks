module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BaseChange

/-!
# The transformation of Tag 0A9K is the conjugate of the derived base change map

Let

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

be a commutative square of schemes, let `a` and `a'` be the twisted inverse images of
[Stacks, Tag 0A9E] along `f` and `f'`, and let

`ξ : Rg'_* ∘ a' ⟶ a ∘ Rg_*`

be the transformation `Stacks.Duality.twistedInverseImagePushforwardBaseChange` underlying
[Stacks, Tag 0A9K]. The assertion of Tag 0A9K is that `ξ` is invertible when `f` and `g` are Tor
independent, and the source's proof is a single sentence: the derived base change map
`Lg^* ∘ Rf_* ⟶ Rf'_* ∘ L(g')^*` of [Stacks, Tag 08HY] is invertible in that case by
[Stacks, Tag 08IB], "thus the corresponding transformation between adjoint functors is an
isomorphism as well".

This module carries that sentence, and carries it as an equivalence rather than an implication.

## The four adjunctions

The square has four left adjoints on it — `Rf_*` and `Rf'_*` horizontally, with right adjoints `a`
and `a'`, and `Lg^*` and `L(g')^*` vertically, with right adjoints `Rg_*` and `Rg'_*` — so the
mates correspondence may be taken in either direction, and the two directions see three
transformations:

* the derived base change map `β : Rf_* ⋙ Lg^* ⟶ L(g')^* ⋙ Rf'_*`, between composites of left
  adjoints;
* the comparison `w : Rg'_* ⋙ Rf_* ≅ Rf'_* ⋙ Rg_*` of derived direct image around the square,
  which is the mate of `β` across the two vertical adjunctions;
* `ξ : a' ⋙ Rg'_* ⟶ Rg_* ⋙ a`, between composites of right adjoints, which is the mate of `w`
  across the two horizontal adjunctions, and so the iterated mate of `β`.

The iterated mate of a transformation of left adjoints is the conjugate of that transformation
with respect to the two composite adjunctions — `CategoryTheory.iterated_mateEquiv_conjugateEquiv`
— and conjugation preserves and reflects invertibility, by
`CategoryTheory.conjugateEquiv_iso` and `CategoryTheory.conjugateEquiv_of_iso`. Hence `ξ` is
invertible **if and only if** `β` is.

Note that `w` is invertible with no hypothesis on the square at all
(`Stacks.Duality.quasiCoherentDerivedPushforwardSquareIso`); it is the comparison of derived direct
image along one morphism with itself, read around the two sides. A mate of an invertible
transformation need not be invertible, which is why that costs nothing and why Tag 0A9K is not
formal.

## Main definitions

All in the namespace `Stacks.Duality`.

* `quasiCoherentDerivedBaseChangeSquare` — the derived base change map
  `β : Rf_* ⋙ Lg^* ⟶ L(g')^* ⋙ Rf'_*` on the quasi-coherent derived categories.

## Main results

* `twistedInverseImagePushforwardBaseChange_eq_conjugateEquiv_square` — `ξ` is the conjugate of `β`
  with respect to the composite adjunctions `L(g')^* ⋙ Rf'_* ⊣ a' ⋙ Rg'_*` and
  `Rf_* ⋙ Lg^* ⊣ Rg_* ⋙ a`.
* `isIso_twistedInverseImagePushforwardBaseChange_iff` — `ξ` is invertible if and only if `β` is.
* `isIso_twistedInverseImagePushforwardBaseChange_of_isIso_baseChangeSquare` — the direction that
  discharges the `IsIso ξ` instance argument of
  `Stacks.Duality.twistedInverseImageBaseChangeMap` and of
  `Stacks.Duality.OpenImmersion.twistedInverseImageRestrictionMap`.

## Implementation notes

*Why `β` is constructed here rather than imported.* The derived base change map of
[Stacks, Tag 08HY] exists in this repository as
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap`, but the file carrying it installs
`CategoryTheory.HasDerivedCategory.standard` as a local instance, so its derived categories are
the standard ones, whereas every quasi-coherent statement in `Duality/` is at the locally small
model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` — see the design note of
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/BaseChange.lean`, and the notes of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/BaseChangeMap.lean` for what blocks
freeing its model. Rather than transport across the two models, `β` is defined here as the mate
of the comparison `w` read backwards, which is the construction of Tag 08HY: the composite of the
unit of `L(g')^* ⊣ Rg'_*`, the comparison `w`, and the counit of `Lg^* ⊣ Rg_*`.

*Relation to Tag 08IB.* [Stacks, Tag 08IB] says that `β` is invertible on `D_QCoh(𝒪_X)` when `f`
is quasi-compact and quasi-separated and `X` and `Y'` are Tor independent over `Y`. By
`isIso_twistedInverseImagePushforwardBaseChange_iff`, Tag 0A9K at this model is equivalent to
Tag 08IB at this model; the results below take the conclusion of Tag 08IB as a hypothesis, so
neither tag is registered here. When `g` is an open immersion, `IsIso ξ` is proved in the file
`TwistedInverseImageRestrictionBaseChange.lean` of the directory
`StacksFrontier/AlgebraicGeometry/Duality/OpenImmersion/` from [Stacks, Tag 08FE].

## References

* [Stacks Project, Tag 0A9J](https://stacks.math.columbia.edu/tag/0A9J)
* [Stacks Project, Tag 0A9K](https://stacks.math.columbia.edu/tag/0A9K)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace Stacks.Duality

variable {X' X Y' Y : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
  (hpushg' : ∀ (K : quasiCoherentDerivedCategory X') (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPushforward g').obj K.obj)).IsQuasicoherent)
  (hpushf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (hpushf' : ∀ (K : quasiCoherentDerivedCategory X') (i : ℤ),
    ((DerivedCategory.homologyFunctor Y'.Modules i).obj
      ((derivedPushforward f').obj K.obj)).IsQuasicoherent)
  (hpushg : ∀ (K : quasiCoherentDerivedCategory Y') (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward g).obj K.obj)).IsQuasicoherent)
  (hpullg : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y'.Modules i).obj
      ((derivedPullback g).obj K.obj)).IsQuasicoherent)
  (hpullg' : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor X'.Modules i).obj
      ((derivedPullback g').obj K.obj)).IsQuasicoherent)

/-- **The derived base change map `β : Lg^* ∘ Rf_* ⟶ Rf'_* ∘ L(g')^*`** of [Stacks, Tag 08HY] on
the quasi-coherent derived categories of a commutative square of schemes, as the mate of the
comparison `Stacks.Duality.quasiCoherentDerivedPushforwardSquareIso` of derived direct image around
the square, read backwards across the two derived adjunctions `L(g')^* ⊣ Rg'_*` and `Lg^* ⊣ Rg_*`.

Reading the mate backwards unfolds to the source's own composite: the unit of `L(g')^* ⊣ Rg'_*`,
then the comparison, then the counit of `Lg^* ⊣ Rg_*`.

[Stacks, Tag 08IB] asserts that this is invertible for a Tor-independent cartesian square with `f`
quasi-compact and quasi-separated. That is not proved in this repository; see the module
documentation. -/
def quasiCoherentDerivedBaseChangeSquare (w : g' ≫ f = f' ≫ g) :
    quasiCoherentDerivedPushforward f hpushf ⋙ quasiCoherentDerivedPullback g hpullg ⟶
      quasiCoherentDerivedPullback g' hpullg' ⋙ quasiCoherentDerivedPushforward f' hpushf' :=
  (mateEquiv (quasiCoherentDerivedAdjunction g' hpullg' hpushg')
      (quasiCoherentDerivedAdjunction g hpullg hpushg)).symm
    (TwoSquare.mk _ _ _ _
      (quasiCoherentDerivedPushforwardSquareIso g' f' f g hpushg' hpushf hpushf' hpushg w).hom)

/-- The mate of the derived base change map across the two vertical adjunctions is the comparison
of derived direct image around the square, by construction. -/
theorem mateEquiv_quasiCoherentDerivedBaseChangeSquare (w : g' ≫ f = f' ≫ g) :
    mateEquiv (quasiCoherentDerivedAdjunction g' hpullg' hpushg')
        (quasiCoherentDerivedAdjunction g hpullg hpushg)
        (TwoSquare.mk _ _ _ _ (quasiCoherentDerivedBaseChangeSquare g' f' f g hpushg' hpushf
          hpushf' hpushg hpullg hpullg' w)) =
      TwoSquare.mk _ _ _ _
        (quasiCoherentDerivedPushforwardSquareIso g' f' f g hpushg' hpushf hpushf' hpushg w).hom :=
  Equiv.apply_symm_apply _ _

section Conjugate

variable [(quasiCoherentDerivedPushforward f hpushf).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward f' hpushf').IsLeftAdjoint]

/-- **The transformation `ξ` of [Stacks, Tag 0A9K] is the conjugate of the derived base change map
of [Stacks, Tag 08HY]**, with respect to the composite adjunctions
`L(g')^* ⋙ Rf'_* ⊣ a' ⋙ Rg'_*` and `Rf_* ⋙ Lg^* ⊣ Rg_* ⋙ a`.

`ξ` is by construction the mate of the comparison of derived direct image around the square, and
that comparison is the mate of the base change map; the iterated mate of a transformation of left
adjoints is its conjugate, which is `CategoryTheory.iterated_mateEquiv_conjugateEquiv`. This is the
whole of the source's proof of Tag 0A9K apart from the invertibility of the base change map
itself. -/
theorem twistedInverseImagePushforwardBaseChange_eq_conjugateEquiv_square
    (sq : IsPullback g' f' f g) :
    twistedInverseImagePushforwardBaseChange g' f' f g hpushg' hpushf hpushf' hpushg sq =
      conjugateEquiv
        ((quasiCoherentDerivedAdjunction g' hpullg' hpushg').comp
          (twistedInverseImageAdjunction f' hpushf'))
        ((twistedInverseImageAdjunction f hpushf).comp
          (quasiCoherentDerivedAdjunction g hpullg hpushg))
        (quasiCoherentDerivedBaseChangeSquare g' f' f g hpushg' hpushf hpushf' hpushg hpullg
          hpullg' sq.w) := by
  have h := iterated_mateEquiv_conjugateEquiv (quasiCoherentDerivedAdjunction g' hpullg' hpushg')
    (quasiCoherentDerivedAdjunction g hpullg hpushg) (twistedInverseImageAdjunction f hpushf)
    (twistedInverseImageAdjunction f' hpushf')
    (TwoSquare.mk _ _ _ _ (quasiCoherentDerivedBaseChangeSquare g' f' f g hpushg' hpushf hpushf'
      hpushg hpullg hpullg' sq.w))
  rw [mateEquiv_quasiCoherentDerivedBaseChangeSquare] at h
  exact h

/-- **The transformation `ξ` of [Stacks, Tag 0A9K] is invertible if and only if the derived base
change map of [Stacks, Tag 08HY] is.** Conjugation preserves and reflects invertibility, so the
one-sentence proof of Tag 0A9K is an equivalence: at this model Tag 0A9K is neither more nor less
than [Stacks, Tag 08IB]. -/
theorem isIso_twistedInverseImagePushforwardBaseChange_iff (sq : IsPullback g' f' f g) :
    IsIso (twistedInverseImagePushforwardBaseChange g' f' f g hpushg' hpushf hpushf' hpushg sq) ↔
      IsIso (quasiCoherentDerivedBaseChangeSquare g' f' f g hpushg' hpushf hpushf' hpushg hpullg
        hpullg' sq.w) := by
  rw [twistedInverseImagePushforwardBaseChange_eq_conjugateEquiv_square g' f' f g hpushg' hpushf
    hpushf' hpushg hpullg hpullg' sq]
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  exact conjugateEquiv_of_iso
    ((quasiCoherentDerivedAdjunction g' hpullg' hpushg').comp
      (twistedInverseImageAdjunction f' hpushf'))
    ((twistedInverseImageAdjunction f hpushf).comp
      (quasiCoherentDerivedAdjunction g hpullg hpushg)) _

/-- **The invertibility of the derived base change map of [Stacks, Tag 08HY] gives the
invertibility of `ξ`**, and so discharges the instance argument of
`Stacks.Duality.twistedInverseImageBaseChangeMap`, of
`Stacks.Duality.OpenImmersion.twistedInverseImageRestrictionMap` and of every other consumer of
[Stacks, Tag 0A9K]. For a Tor-independent cartesian square the hypothesis is the conclusion of
[Stacks, Tag 08IB], which this repository does not prove. -/
theorem isIso_twistedInverseImagePushforwardBaseChange_of_isIso_baseChangeSquare
    (sq : IsPullback g' f' f g)
    [IsIso (quasiCoherentDerivedBaseChangeSquare g' f' f g hpushg' hpushf hpushf' hpushg hpullg
      hpullg' sq.w)] :
    IsIso (twistedInverseImagePushforwardBaseChange g' f' f g hpushg' hpushf hpushf' hpushg sq) :=
  (isIso_twistedInverseImagePushforwardBaseChange_iff g' f' f g hpushg' hpushf hpushf' hpushg
    hpullg hpullg' sq).2 ‹_›

end Conjugate

end Stacks.Duality

end
