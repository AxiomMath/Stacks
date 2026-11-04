module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BaseChange

/-!
# The base change map of the twisted inverse image is a mate

Let

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

be a cartesian square of schemes, let `a` and `a'` be the twisted inverse images of
[Stacks, Tag 0A9E] along `f` and `f'`, and let `ξ : Rg'_* ∘ a' ⟶ a ∘ Rg_*` be the transformation
of [Stacks, Tag 0A9K]. The base change map of [Stacks, Tag 0AA6],
`Stacks.Duality.twistedInverseImageBaseChangeMap`, is written in the source as a composite of
three arrows, the middle one being `ξ⁻¹`; the source then remarks that "alternatively, we can
think of (0AA6) by adjointness of `L(g')^*` and `R(g')_*`" as a transformation `a ⟶ Rg'_* ∘ a'
∘ Lg^*`. That remark is exactly the statement that the base change map is the **mate** of `ξ⁻¹`
under the two derived adjunctions `Lg^* ⊣ Rg_*` and `L(g')^* ⊣ Rg'_*`, and that is what is proved
below.

## Main results

All in the namespace `Stacks.Duality`.

* `twistedInverseImageBaseChangeMap_eq_mateEquiv_symm` — the base change map of
  [Stacks, Tag 0AA6] is `CategoryTheory.mateEquiv` of the inverse of the transformation `ξ`
  of [Stacks, Tag 0A9K], read backwards.

## Why this is worth recording

The compatibilities of the base change map with stacking cartesian squares —
[Stacks, Tag 0ATQ] for a vertical stack and [Stacks, Tag 0ATR], [Stacks, Tag 0ATS] for a
horizontal one — are proved in the source by a long diagram chase through the units and counits
that the composite definition exposes. Once the map is identified with a mate, those chases are
instances of the mates calculus: `CategoryTheory.mateEquiv_vcomp` and
`CategoryTheory.mateEquiv_hcomp`. This is the same reduction that
`Stacks.Duality.twistedInverseImageCompIso_hom_eq` performs for the composition isomorphism of
[Stacks, Tag 0ATX], and which makes the cocycle identity
`Stacks.Duality.twistedInverseImageCompIso_hom_assoc_whiskering` a formal consequence.

## Where the vertical stack is carried out

[Stacks, Tag 0ATQ] states that for a vertical stack of two cartesian squares

```
X' --k--> X        Y' --l--> Y
|f'       |f       |g'       |g
Y' --l--> Y        Z' --m--> Z
```

with `f`, `l` and `g`, `m` Tor-independent, the base change maps `γ_top` and `γ_bot` of
[Stacks, Tag 0AA6] for the two squares compose to the base change map `γ_rect` for the outer
rectangle. Reading each `γ` as the mate of the corresponding `ξ⁻¹`, as below, that statement
becomes the compatibility of `CategoryTheory.mateEquiv` with vertical composition applied to
`γ_bot` and `γ_top`, together with the identity

  `ξ_rect = ξ_bot ≫ₕ ξ_top`

which is where the source's proof ends ("it suffices to prove that ... is equal to `ξ_rect`").
That identity is in turn the compatibility of the mates correspondence with pasting, because `ξ`
is by construction the mate of the comparison
`Stacks.Duality.quasiCoherentDerivedPushforwardSquareIso` of derived direct image around the
square, and the vertical composition of the comparisons for the two squares is the comparison for
the rectangle.

Both steps, and the bridging between the two readings of the rectangle's adjoint — the
rectangle's `ξ_rect` is the mate under
`Stacks.Duality.twistedInverseImageAdjunction (f' ≫ g')`, whereas pasting delivers the mate under
the composite adjunction of the adjunctions for `f'` and `g'`, and the comparison between them is
`Stacks.Duality.twistedInverseImageCompIso` of [Stacks, Tag 0ATX] — are in
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/BaseChangeStackingMate.lean`, where
`Stacks.Duality.twistedInverseImageBaseChangeMap_vcomp` carries [Stacks, Tag 0ATQ]. No attribute
is attached to the lemma below, which is a statement about one square, not about a stack of two.

## References

* [Stacks Project, Tag 0AA6](https://stacks.math.columbia.edu/tag/0AA6)
* [Stacks Project, Tag 0A9K](https://stacks.math.columbia.edu/tag/0A9K)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0ATQ](https://stacks.math.columbia.edu/tag/0ATQ)
* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
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
  [(quasiCoherentDerivedPushforward f hpushf).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward f' hpushf').IsLeftAdjoint]

/-- **The base change map of [Stacks, Tag 0AA6] is a mate.** Under the two derived adjunctions
`Lg^* ⊣ Rg_*` and `L(g')^* ⊣ Rg'_*`, the transformation
`L(g')^* ∘ a ⟶ a' ∘ Lg^*` of `Stacks.Duality.twistedInverseImageBaseChangeMap` corresponds to the
inverse of the transformation `ξ : Rg'_* ∘ a' ⟶ a ∘ Rg_*` of [Stacks, Tag 0A9K].

This is the source's own alternative description of the map, and it is what reduces the
compatibilities of base change with stacking cartesian squares to the mates calculus; see the
module documentation. -/
theorem twistedInverseImageBaseChangeMap_eq_mateEquiv_symm (sq : IsPullback g' f' f g)
    [IsIso (twistedInverseImagePushforwardBaseChange g' f' f g hpushg' hpushf hpushf' hpushg
      sq)] :
    twistedInverseImageBaseChangeMap g' f' f g hpushg' hpushf hpushf' hpushg sq =
      (mateEquiv (quasiCoherentDerivedAdjunction g (isQuasicoherent_homology_derivedPullback' g)
            hpushg)
          (quasiCoherentDerivedAdjunction g' (isQuasicoherent_homology_derivedPullback' g')
            hpushg')).symm
        (TwoSquare.mk _ _ _ _
          (inv (twistedInverseImagePushforwardBaseChange g' f' f g hpushg' hpushf hpushf'
            hpushg sq))) := by
  ext K
  simp [twistedInverseImageBaseChangeMap, mateEquiv]

end Stacks.Duality

end
