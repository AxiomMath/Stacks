module

public import StacksFrontier.AlgebraicGeometry.Duality.Compactification.ShriekOfCompactification
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.Composition
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekAffineComparison.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointPredicateSupplement
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.CompositionExtra

/-!
# The comparison `α_g` of the upper shriek functors of two compactifications

Let `f : X ⟶ Y` be a morphism of `AlgebraicGeometry.FTS S` for a Noetherian `S` and let
`g : j ⟶ k` be a morphism of compactifications of `X` over `Y` which **preserves the interior**,
with underlying morphism `G : X̄₁ ⟶ X̄₂` of ambient schemes.  Writing `ā₁`, `ā₂` and `c̄` for the
twisted inverse images of `j.toBase`, `k.toBase` and `G`, the source constructs an isomorphism

```
α_g : j₁^* ∘ ā₁ ⟶ j₁^* ∘ c̄ ∘ ā₂ ⟶ j₂^* ∘ ā₂
```

whose two steps are: the comparison `ā₁ ≅ c̄ ∘ ā₂` of [Stacks, Tag 0ATX], valid because
`j.toBase = G ≫ k.toBase`; and the base change map of [Stacks, Tag 0AA6] for the cartesian square

```
X --j₁--> X̄₁
|𝟙         |G
X --j₂--> X̄₂
```

followed by the identification of the twisted inverse image of `𝟙_X` with the identity functor.
This file constructs `α_g` and records that it is an isomorphism.

## Main definitions

All in the namespace `Stacks.Duality`.

* `refinementTwisted` — `c̄ = G^×`.
* `refinementXi` — the transformation `ξ` of [Stacks, Tag 0A9K] for the square of `g`.
* `refinementBaseChange` — the base change map of [Stacks, Tag 0AA6] for the square of `g`.
* `refinementBaseChangePlus` — that map restricted along `ā₂` on `D⁺_QCoh(𝒪_Y)`, which is where
  [Stacks, Tag 0A9P] asserts it to be invertible.
* `refinementTwistedCompIso` — the comparison `ā₁ ≅ ā₂ ⋙ c̄` of [Stacks, Tag 0ATX].
* `refinementIso` — **the comparison `α_g`**, as functors out of `D⁺_QCoh(𝒪_Y)`.

## Implementation notes

*What is assumed, and why.*  Everything that [Stacks, Tag 08D5] part (1), [Stacks, Tag 08DW] part
(1) and [Stacks, Tag 0A9E] contribute is discharged, as in
`StacksFrontier.AlgebraicGeometry.Duality.Compactification.ShriekOfCompactification`: every
morphism in the diagram is quasi-compact and quasi-separated with quasi-compact target, the base
being Noetherian.  Two inputs remain, and both are instance arguments:

* `IsIso (refinementXi ..)` — invertibility of `ξ`, which is [Stacks, Tag 0A9K].  The base change
  map of [Stacks, Tag 0AA6] contains `ξ⁻¹` literally, so it does not exist without this; it is an
  instance argument of `Stacks.Duality.twistedInverseImageBaseChangeMap` itself.  For the square
  above `j₂` is an open immersion, hence flat, so the square is Tor-independent and Tag 0A9K
  applies; and that case of Tag 0A9K is proved here, as the instance
  `Stacks.Duality.isIso_refinementXi` of
  `StacksFrontier.AlgebraicGeometry.Duality.Compactification.ShriekRefinementXi`, so this
  instance argument is discharged by instance search.
* `IsIso (refinementBaseChangePlus ..)` — invertibility of the base change map **on the
  bounded-below part**, which is **[Stacks, Tag 0A9P]** (its case (2), `Y` Noetherian) read
  through [Stacks, Tag 0A9N] part **(1)**: `G` is proper, `X̄₂` is Noetherian, and `j₂(X)` is a
  quasi-compact open of `X̄₂` with inverse image `j₁(X)`.  Part (1) of Tag 0A9N — and so Tag
  0A9P — concludes that the base change map is invertible as a transformation of functors
  `D⁺_QCoh(𝒪_{X̄₂}) ⥤ D⁺_QCoh(𝒪_X)`, and nothing more: the unbounded conclusion is part (2),
  which part (3) derives from part (1) only through [Stacks, Tag 0A9R] given
  [Stacks, Tag 0B6G], and Tag 0B6G fails in general for these refinement morphisms.  So the
  instance argument below is the bounded-below one, `refinementBaseChangePlus`, and not
  `IsIso (refinementBaseChange ..)`, which would be Tag 0A9N part (2).  It is discharged, as
  the instance `Stacks.Duality.isIso_refinementBaseChangePlus` of
  `StacksFrontier.AlgebraicGeometry.Duality.Compactification.ShriekRefinementBaseChange`.

*Why `Lj^*` and not the exact restriction.*  `Stacks.Duality.upperShriek` is defined with the
derived pullback `Lj^*` as its second factor, and so is the base change map of
[Stacks, Tag 0AA6]; the construction below therefore stays with `Lj^*` throughout and never needs
the comparison between `Stacks.Duality.derivedPullback` and
`Stacks.Duality.OpenImmersion.derivedRestrict`, which this repository does not have.  Using
Tag 0AA6 rather than [Stacks, Tag 0A9L] is what makes this possible: the two maps are conjugate,
by `StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BaseChangeConjugate`.

## References

* [Stacks Project, Tag 0AA0](https://stacks.math.columbia.edu/tag/0AA0)
* [Stacks Project, Tag 0AA6](https://stacks.math.columbia.edu/tag/0AA6)
* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
* [Stacks Project, Tag 0A9K](https://stacks.math.columbia.edu/tag/0A9K)
* [Stacks Project, Tag 0A9P](https://stacks.math.columbia.edu/tag/0A9P)
* [Stacks Project, Tag 0A9N](https://stacks.math.columbia.edu/tag/0A9N)
* [Stacks Project, Tag 0A9I](https://stacks.math.columbia.edu/tag/0A9I)
* [Stacks Project, Tag 0A9R](https://stacks.math.columbia.edu/tag/0A9R)
* [Stacks Project, Tag 0B6G](https://stacks.math.columbia.edu/tag/0B6G)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe u

namespace Stacks.Duality

/-! ### Transport of the twisted inverse image along an equality of morphisms -/

section Congr

variable {W Z : Scheme.{u}} {h h' : W ⟶ Z}
  (hph : ∀ (K : quasiCoherentDerivedCategory W) (i : ℤ),
    ((DerivedCategory.homologyFunctor Z.Modules i).obj
      ((derivedPushforward h).obj K.obj)).IsQuasicoherent)
  (hph' : ∀ (K : quasiCoherentDerivedCategory W) (i : ℤ),
    ((DerivedCategory.homologyFunctor Z.Modules i).obj
      ((derivedPushforward h').obj K.obj)).IsQuasicoherent)
  [(quasiCoherentDerivedPushforward h hph).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward h' hph').IsLeftAdjoint]

/-- The twisted inverse images of two equal morphisms are the same functor.  Both the
quasi-coherence argument and the adjointness instance are `Prop`-valued, so after substituting the
equality nothing is left to compare. -/
theorem twistedInverseImage_congr (e : h = h') :
    twistedInverseImage h hph = twistedInverseImage h' hph' := by
  subst e
  rfl

/-- The identification of the twisted inverse images of two equal morphisms, as an isomorphism:
`CategoryTheory.eqToIso` of `Stacks.Duality.twistedInverseImage_congr`. -/
def twistedInverseImageCongrIso (e : h = h') :
    twistedInverseImage h hph ≅ twistedInverseImage h' hph' :=
  eqToIso (twistedInverseImage_congr hph hph' e)

end Congr

/-- The identification of the twisted inverse image of a morphism with itself is the identity:
an equality of morphisms is a `Prop`, so which proof it is read off does not matter, and neither
does which quasi-coherence argument is supplied. -/
@[simp]
theorem twistedInverseImageCongrIso_self {W Z : Scheme.{u}} {h : W ⟶ Z}
    (hph : ∀ (K : quasiCoherentDerivedCategory W) (i : ℤ),
      ((DerivedCategory.homologyFunctor Z.Modules i).obj
        ((derivedPushforward h).obj K.obj)).IsQuasicoherent)
    (hph' : ∀ (K : quasiCoherentDerivedCategory W) (i : ℤ),
      ((DerivedCategory.homologyFunctor Z.Modules i).obj
        ((derivedPushforward h).obj K.obj)).IsQuasicoherent)
    [(quasiCoherentDerivedPushforward h hph).IsLeftAdjoint]
    [(quasiCoherentDerivedPushforward h hph').IsLeftAdjoint] (e : h = h) :
    twistedInverseImageCongrIso hph hph' e = Iso.refl _ :=
  rfl

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  {j k : CompactificationOf (Over.mk f.left)} (g : j ⟶ k)

/-! ### The twisted inverse image of a morphism of compactifications -/

/-- **`c̄ = G^×`, the twisted inverse image of the morphism of ambient schemes** underlying a
morphism `g : j ⟶ k` of compactifications.  `G` is proper, so [Stacks, Tag 08D5] part (1) and
[Stacks, Tag 0A9E] are available for it. -/
def refinementTwisted :
    quasiCoherentDerivedCategory k.space ⥤ quasiCoherentDerivedCategory j.space :=
  letI := CompactificationOf.isProper_homMap g
  letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
    (CompactificationOf.Hom.map g)
  twistedInverseImage (CompactificationOf.Hom.map g)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (CompactificationOf.Hom.map g))

/-- **The comparison `ā₁ ≅ ā₂ ⋙ c̄` of [Stacks, Tag 0ATX]** for a morphism of compactifications:
the structure morphism of the source factors as `j.toBase = G ≫ k.toBase`, and the twisted
inverse image of a composite is the composite of the twisted inverse images in the other order. -/
def refinementTwistedCompIso :
    compactificationTwisted f j ≅ compactificationTwisted f k ⋙ refinementTwisted f g :=
  letI := CompactificationOf.isProper_homMap g
  @twistedInverseImageCongrIso j.space Y.left j.toBase
      (CompactificationOf.Hom.map g ≫ k.toBase)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs
        (CompactificationOf.Hom.map g ≫ k.toBase))
      (AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward j.toBase)
      (AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
        (CompactificationOf.Hom.map g ≫ k.toBase))
      (CompactificationOf.homMap_comp_toBase g).symm ≪≫
    @twistedInverseImageCompIso j.space k.space Y.left (CompactificationOf.Hom.map g) k.toBase
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (CompactificationOf.Hom.map g))
      (isQuasicoherent_homology_derivedPushforward_of_qcqs k.toBase)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs
        (CompactificationOf.Hom.map g ≫ k.toBase))
      (AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
        (CompactificationOf.Hom.map g))
      (AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward k.toBase)
      (AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
        (CompactificationOf.Hom.map g ≫ k.toBase))

/-! ### The base change map of the cartesian square -/

/-- **The transformation `ξ` of [Stacks, Tag 0A9K] for the cartesian square of an
interior-preserving morphism of compactifications.**  Its invertibility, which is the assertion
of Tag 0A9K (the instance `Stacks.Duality.isIso_refinementXi`), is what makes the base change
map of [Stacks, Tag 0AA6] exist. -/
abbrev refinementXi (hg : CompactificationOf.PreservesInterior g) :
    twistedInverseImage (𝟙 X.left)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X.left)) ⋙
        quasiCoherentDerivedPushforward j.immersion
          (isQuasicoherent_homology_derivedPushforward_of_qcqs j.immersion) ⟶
      quasiCoherentDerivedPushforward k.immersion
          (isQuasicoherent_homology_derivedPushforward_of_qcqs k.immersion) ⋙
        refinementTwisted f g :=
  letI := CompactificationOf.isProper_homMap g
  @twistedInverseImagePushforwardBaseChange X.left j.space X.left k.space
    j.immersion (𝟙 X.left) (CompactificationOf.Hom.map g) k.immersion
    (isQuasicoherent_homology_derivedPushforward_of_qcqs j.immersion)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (CompactificationOf.Hom.map g))
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X.left))
    (isQuasicoherent_homology_derivedPushforward_of_qcqs k.immersion)
    (AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
      (CompactificationOf.Hom.map g))
    (isLeftAdjoint_quasiCoherentDerivedPushforward_id X.left
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X.left)))
    (CompactificationOf.isPullback_of_preservesInterior g hg).flip

/-- **The base change map `c̄ ∘ j₁^* ⟶ j₂^* ∘ (𝟙_X)^×` of [Stacks, Tag 0AA6]** for the cartesian
square of an interior-preserving morphism of compactifications.  Its invertibility is
[Stacks, Tag 0A9P]. -/
abbrev refinementBaseChange (hg : CompactificationOf.PreservesInterior g)
    [IsIso (refinementXi f g hg)] :
    refinementTwisted f g ⋙ compactificationRestrict f j ⟶
      compactificationRestrict f k ⋙
        twistedInverseImage (𝟙 X.left)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X.left)) :=
  letI := CompactificationOf.isProper_homMap g
  @twistedInverseImageBaseChangeMap X.left j.space X.left k.space
    j.immersion (𝟙 X.left) (CompactificationOf.Hom.map g) k.immersion
    (isQuasicoherent_homology_derivedPushforward_of_qcqs j.immersion)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (CompactificationOf.Hom.map g))
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X.left))
    (isQuasicoherent_homology_derivedPushforward_of_qcqs k.immersion)
    (AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
      (CompactificationOf.Hom.map g))
    (isLeftAdjoint_quasiCoherentDerivedPushforward_id X.left
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X.left)))
    (CompactificationOf.isPullback_of_preservesInterior g hg).flip
    (inferInstanceAs (IsIso (refinementXi f g hg)))

/-- **The base change map of [Stacks, Tag 0AA6] read on the bounded-below part**, that is,
restricted along `ā_k : D⁺_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_{X̄₂})`.  Its invertibility is what
[Stacks, Tag 0A9P] delivers: the tag asserts that the base change map is invertible as a
transformation of functors `D⁺_QCoh(𝒪_{X̄₂}) ⥤ D⁺_QCoh(𝒪_X)`, and `ā_k` carries
`D⁺_QCoh(𝒪_Y)` into `D⁺_QCoh(𝒪_{X̄₂})` by [Stacks, Tag 0A9I].  This, and not invertibility on
the whole of `D_QCoh(𝒪_{X̄₂})` — which is [Stacks, Tag 0A9N] part (2) — is the instance argument
of `Stacks.Duality.refinementIso`. -/
abbrev refinementBaseChangePlus (hg : CompactificationOf.PreservesInterior g)
    [IsIso (refinementXi f g hg)] :
    compactificationTwistedPlus f k ⋙ refinementTwisted f g ⋙ compactificationRestrict f j ⟶
      compactificationTwistedPlus f k ⋙ compactificationRestrict f k ⋙
        twistedInverseImage (𝟙 X.left)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X.left)) :=
  Functor.whiskerLeft (compactificationTwistedPlus f k) (refinementBaseChange f g hg)

/-! ### The comparison `α_g` -/

/-- **The comparison `α_g : f^!_j ≅ f^!_k`** attached to an interior-preserving morphism
`g : j ⟶ k` of compactifications, as functors out of `D⁺_QCoh(𝒪_Y)`.  It is the comparison of
[Stacks, Tag 0ATX] for `j.toBase = G ≫ k.toBase`, then the base change map of
[Stacks, Tag 0AA6] for the cartesian square of `g`, then the identification of the twisted
inverse image of `𝟙_X` with the identity functor.

The two instance arguments are [Stacks, Tag 0A9K] and [Stacks, Tag 0A9P], the latter in the
bounded-below form `Stacks.Duality.refinementBaseChangePlus` that the tag actually asserts; see
the module documentation. -/
def refinementIso (hg : CompactificationOf.PreservesInterior g) [IsIso (refinementXi f g hg)]
    [IsIso (refinementBaseChangePlus f g hg)] :
    compactificationUpperShriek f j ≅ compactificationUpperShriek f k :=
  isoWhiskerRight
      (isoWhiskerLeft (ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Y.left))
        (refinementTwistedCompIso f g))
      (compactificationRestrict f j) ≪≫
    associator (compactificationTwistedPlus f k) (refinementTwisted f g)
      (compactificationRestrict f j) ≪≫
    asIso (refinementBaseChangePlus f g hg) ≪≫
    isoWhiskerLeft (compactificationTwistedPlus f k)
      (isoWhiskerLeft (compactificationRestrict f k)
          (twistedInverseImageIdIso X.left
            (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X.left))) ≪≫
        rightUnitor (compactificationRestrict f k))

end Stacks.Duality

end
