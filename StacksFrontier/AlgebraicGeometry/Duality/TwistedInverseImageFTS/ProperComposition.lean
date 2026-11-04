module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.Composition
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekAffineComparison.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.CompositionExtra

/-!
# The exceptional inverse image of a composite of proper morphisms

Let `S` be a scheme and let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of
`AlgebraicGeometry.FTS S`, the category of schemes separated and of finite type over `S` of
[Stacks, Tag 0F42], whose underlying morphisms of schemes are proper. A proper morphism is its
own compactification — `Stacks.Duality.properCompactification`, with `X̄ = X` — so the
exceptional inverse image `f^!` of [Stacks, Tag 0A9Y] is defined for `f` with no appeal to
[Stacks, Tag 0F41] (Nagata), and at that compactification `f^!` is the twisted inverse image
`f^×` composed with derived pullback along `𝟙_X`, which is the identity.

[Stacks, Tag 0ATX] (Lemma 48.16.3) is the canonical isomorphism `(g ∘ f)^! ≅ f^! ∘ g^!`. For
proper `f` and `g` at these compactifications it follows from the composition law for the twisted
inverse image, `Stacks.Duality.twistedInverseImageCompIso`, together with the two identifications
`L(𝟙)^* ≅ 𝟭` of `Stacks.Duality.quasiCoherentDerivedPullbackIdIsoOfIsQuasicoherent`.

## Main definitions

All in the namespace `Stacks.Duality`.

* `properUpperShriek` — `f^!` of a proper morphism of `FTS S`, that is
  `Stacks.Duality.upperShriek` at `Stacks.Duality.properCompactification`. The `hpull` argument
  of the general construction is discharged here by
  `Stacks.Duality.isQuasicoherent_homology_derivedPullback_id`, derived pullback along `𝟙_X`
  preserving quasi-coherence of cohomology.
* `properUpperShriekCompIso` — **[Stacks, Tag 0ATX] for proper morphisms**:
  `(f ≫ g)^! ≅ g^! ⋙ f^!`, which in the source's order of composition is
  `(g ∘ f)^! ≅ f^! ∘ g^!`.

## Main results

* `properUpperShriekCompIso_obj` — the isomorphism read on an object of `D_QCoh(𝒪_Z)`, which is
  the shape in which the source uses it.

## Implementation notes

*What the restriction to proper morphisms costs.* The source's `f^!` is attached to an arbitrary
compactification of an arbitrary morphism of `FTS S`, and the substance of its Lemma 48.16.3 is
that the comparison does not depend on the compactifications chosen: it compares the functors
built from compactifications `X ⟶ X̄` over `Ȳ` and `Y ⟶ Ȳ` over `Z` with one built from a
compactification of `X` over `Z`, and then dominates any two such choices by a third. None of
that is claimed here. For a proper morphism there is nothing to choose — the identity open
immersion is a compactification — and the comparison is the composition law for the right
adjoints, which is formal. The general case needs the independence half of [Stacks, Tag 0A9Y] and
the base change isomorphism of [Stacks, Tag 0A9H], neither of which this repository has.

*Why the statement is not about `Stacks.Duality.upperShriek` with the compactification free.*
`upperShriek f j` depends on `j`, and for a general `j` the composite of
`upperShriek f j_f` with `upperShriek g j_g` is built from the three schemes `X̄`, `Ȳ` and the
ambient scheme of a compactification of `f ≫ g`, which are unrelated. `properUpperShriek` pins
the compactification to the canonical one, which is the only choice at which the statement is
formal.

*`(f ≫ g).left = f.left ≫ g.left`, `(properCompactification f).toBase = f.left` and
`(properCompactification f).immersion = 𝟙 X.left` hold by `rfl`*, which is what lets the
quasi-coherence arguments below be written in terms of the underlying morphisms of schemes and
passed to `Stacks.Duality.upperShriek` unchanged. The `@`-applications are needed for the
adjointness instances, as in `Stacks.Duality.openImmersionUpperShriek`: instance search does not
unfold `Stacks.Duality.properCompactification` far enough to see that its structure morphism is
`f.left`.

## References

* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
* [Stacks Project, Tag 0A9Y](https://stacks.math.columbia.edu/tag/0A9Y)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0F41](https://stacks.math.columbia.edu/tag/0F41)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace Stacks.Duality

/-! ### `f^!` of a proper morphism -/

section Proper

variable {S : Scheme.{u}} {X Y : AlgebraicGeometry.FTS S} (f : X ⟶ Y)
  (hpush : ∀ (K : quasiCoherentDerivedCategory X.left) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.left.Modules i).obj
      ((derivedPushforward f.left).obj K.obj)).IsQuasicoherent)
  [(quasiCoherentDerivedPushforward f.left hpush).IsLeftAdjoint]

/-- **`f^!` of a proper morphism of `FTS S`**, computed at the compactification `X̄ = X` of
`Stacks.Duality.properCompactification`: the twisted inverse image `f^×` followed by derived
pullback along `𝟙_X`, which is what `Stacks.Duality.upperShriek` computes at that
compactification. It is written out rather than read off `upperShriek`, which asks for a
quasi-compact quasi-separated base and takes the pushforward and its right adjoint from there,
because here they are the binders `hpush` and the `IsLeftAdjoint` instance. -/
abbrev properUpperShriek :
    quasiCoherentDerivedCategory Y.left ⥤ quasiCoherentDerivedCategory X.left :=
  twistedInverseImage f.left hpush ⋙
    quasiCoherentDerivedPullback (𝟙 X.left) (isQuasicoherent_homology_derivedPullback_id X.left)

end Proper

/-! ### Tag 0ATX for proper morphisms -/

section Composition

variable {S : Scheme.{u}} {X Y Z : AlgebraicGeometry.FTS S} (f : X ⟶ Y) (g : Y ⟶ Z)
  (hpushf : ∀ (K : quasiCoherentDerivedCategory X.left) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.left.Modules i).obj
      ((derivedPushforward f.left).obj K.obj)).IsQuasicoherent)
  (hpushg : ∀ (K : quasiCoherentDerivedCategory Y.left) (i : ℤ),
    ((DerivedCategory.homologyFunctor Z.left.Modules i).obj
      ((derivedPushforward g.left).obj K.obj)).IsQuasicoherent)
  (hpushfg : ∀ (K : quasiCoherentDerivedCategory X.left) (i : ℤ),
    ((DerivedCategory.homologyFunctor Z.left.Modules i).obj
      ((derivedPushforward (f ≫ g).left).obj K.obj)).IsQuasicoherent)
  [(quasiCoherentDerivedPushforward f.left hpushf).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward g.left hpushg).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward (f ≫ g).left hpushfg).IsLeftAdjoint]

/-- **Stacks Project, Tag 0ATX (Lemma 48.16.3) for proper morphisms.** Let `f : X ⟶ Y` and
`g : Y ⟶ Z` be morphisms of `AlgebraicGeometry.FTS S` whose underlying morphisms of schemes are
proper. Then, with each exceptional inverse image computed at the compactification by the source
itself, there is a canonical isomorphism

  `(f ≫ g)^! ≅ g^! ⋙ f^!`,

which written in the source's order of composition is `(g ∘ f)^! ≅ f^! ∘ g^!`.

A proper morphism is its own compactification, so `f^!` is `f^×` followed by derived pullback
along the identity; the latter is the identity functor by
`Stacks.Duality.quasiCoherentDerivedPullbackIdIsoOfIsQuasicoherent`, and the composition law for
`f^×` is `Stacks.Duality.twistedInverseImageCompIso`, which is uniqueness of right adjoints applied
to `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*`.

For a general morphism of `FTS S` the source's statement compares the functors attached to
arbitrary compactifications of the factors and of the composite, and asserts that the comparison
is independent of those choices; that is `Stacks.Duality.upperShriekCompIsoAtModel`, which carries
[Stacks, Tag 0ATX]. -/
def properUpperShriekCompIso :
    properUpperShriek (f ≫ g) hpushfg ≅
      properUpperShriek g hpushg ⋙ properUpperShriek f hpushf :=
  have : (quasiCoherentDerivedPushforward (f.left ≫ g.left) hpushfg).IsLeftAdjoint :=
    inferInstanceAs ((quasiCoherentDerivedPushforward (f ≫ g).left hpushfg).IsLeftAdjoint)
  Functor.isoWhiskerRight (twistedInverseImageCompIso f.left g.left hpushf hpushg hpushfg)
      (quasiCoherentDerivedPullback (𝟙 X.left)
        (isQuasicoherent_homology_derivedPullback_id X.left)) ≪≫
    Functor.associator _ _ _ ≪≫
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (twistedInverseImage g.left hpushg)
          (Functor.isoWhiskerRight (quasiCoherentDerivedPullbackIdIsoOfIsQuasicoherent Y.left) _ ≪≫
            Functor.leftUnitor _)).symm

/-- **Tag 0ATX for proper morphisms, on an object.** For `K ∈ D_QCoh(𝒪_Z)` the exceptional
inverse image of `K` along `f ≫ g` is `f^!` of `g^! K`. This is
`Stacks.Duality.properUpperShriekCompIso` evaluated at `K`, and it is the shape in which the
source states the comparison. -/
def properUpperShriekCompIso_obj (K : quasiCoherentDerivedCategory Z.left) :
    (properUpperShriek (f ≫ g) hpushfg).obj K ≅
      (properUpperShriek f hpushf).obj ((properUpperShriek g hpushg).obj K) :=
  (properUpperShriekCompIso f g hpushf hpushg hpushfg).app K

end Composition

end Stacks.Duality

end
