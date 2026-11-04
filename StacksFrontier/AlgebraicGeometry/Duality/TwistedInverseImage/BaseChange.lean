module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change for the twisted inverse image

Let

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

be a cartesian square of schemes, and let `a` and `a'` be the right adjoints of the restricted
derived direct images `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` and `Rf'_*` — the twisted inverse images
of [Stacks, Tag 0A9E]. This is Situation [Stacks, Tag 0A9J], and it carries two canonical
transformations.

The first is `ξ : Rg'_* ∘ a' ⟶ a ∘ Rg_*`. Pushforward around the two sides of the square is one
functor, `R(g' ≫ f)_* = R(f' ≫ g)_*`, so `Rg'_* ⋙ Rf_*` and `Rf'_* ⋙ Rg_*` are canonically
isomorphic; `ξ` is the mate of that isomorphism under the two adjunctions `Rf_* ⊣ a` and
`Rf'_* ⊣ a'`. Its construction uses no hypothesis on the square beyond commutativity. The content
of [Stacks, Tag 0A9K] is that `ξ` is invertible when `f` and `g` are Tor-independent; that is
`Stacks.Duality.isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent`.

The second, Equation 48.5.0.1 of [Stacks, Tag 0AA6], is the base change map
`L(g')^* ∘ a ⟶ a' ∘ Lg^*`, the composite

```
L(g')^* ∘ a ⟶ L(g')^* ∘ a ∘ Rg_* ∘ Lg^* ⟵ L(g')^* ∘ Rg'_* ∘ a' ∘ Lg^* ⟶ a' ∘ Lg^*
```

of the unit of `Lg^* ⊣ Rg_*`, the inverse of `L(g')^* ⋆ ξ ⋆ Lg^*`, and the counit of
`L(g')^* ⊣ Rg'_*`.

## Main definitions

All in the namespace `Stacks.Duality`.

* `derivedPushforwardCompIso` — the composition formula `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` for derived
  direct image of sheaves of modules on schemes.
* `derivedPushforwardSquareIso` and `quasiCoherentDerivedPushforwardSquareIso` — the comparison
  of derived direct image around the two sides of a commutative square, on the unbounded and on
  the quasi-coherent derived categories.
* `twistedInverseImagePushforwardBaseChange` — the transformation `ξ : Rg'_* ∘ a' ⟶ a ∘ Rg_*`
  underlying [Stacks, Tag 0A9K].
* `twistedInverseImageBaseChangeMap` — the base change map `L(g')^* ∘ a ⟶ a' ∘ Lg^*` of
  [Stacks, Tag 0AA6].

## Implementation notes

*Invertibility of `ξ` is an instance argument here.* `twistedInverseImageBaseChangeMap` is the
composite for any cartesian square at which `ξ` is invertible. For a Tor-independent cartesian
square of quasi-compact, quasi-separated schemes the invertibility is [Stacks, Tag 0A9K], and the
map of Tag 0AA6 at the source's hypotheses is
`Stacks.Duality.torIndependentTwistedInverseImageBaseChange` in
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/TorIndependentBaseChangeMap.lean`.

*`ξ` is built from derived direct image alone.* The source presents `ξ` as the mate of the
derived base change map `Lg^* ∘ Rf_* ⟶ Rf'_* ∘ L(g')^*` of [Stacks, Tag 08HY], which is available
here as `Stacks.Cohomology.DerivedBaseChange.Canonical.derivedBaseChangeMap`. That declaration is
unusable at this generality: the file carrying it opens with
`attribute [local instance] HasDerivedCategory.standard`, so the derived categories in its type
are the standard ones, whereas every quasi-coherent statement in `Duality/` is at the locally
small model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` — the only model at which
`D_QCoh(𝒪_X)` has the direct sums Brown representability needs, the standard model making that
hypothesis false rather than unavailable. The route taken here instead takes the mate of the
comparison of the two pushforwards around the square, which mentions no derived pullback and so
needs no statement that is pinned to the standard model. Both are the canonical transformation,
and they agree by the compatibility of mates with pasting, but that equality is not proved here.
No declaration below mentions `CategoryTheory.HasDerivedCategory.standard`.

*The composition formula for derived direct image is restated.*
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso` is the same
isomorphism for a morphism of ringed spaces, and it is pinned to the standard model for the same
reason. Its construction — uniqueness of right adjoints applied to the composite of the two
derived adjunctions of [Stacks, Tag 079W], transported along the composition formula for derived
pullback of [Stacks, Tag 0D5S] — is repeated here from `Stacks.Duality.derivedAdjunction` and
`Stacks.Duality.derivedPullbackCompIso`, both of which are at the locally small model.

*No `@[stacks]` attribute on `ξ`.* The assertion of Tag 0A9K is the invertibility, not the
construction, and the audit scanner keys on the bare four-character tag; an attribute on the
transformation would report the whole tag formalized on the strength of a definition. Tag 0AA6
is a definition, so it is carried.

## References

* [Stacks Project, Tag 0A9J](https://stacks.math.columbia.edu/tag/0A9J)
* [Stacks Project, Tag 0A9K](https://stacks.math.columbia.edu/tag/0A9K)
* [Stacks Project, Tag 0AA6](https://stacks.math.columbia.edu/tag/0AA6)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace Stacks.Duality

/-! ### The composition formula for derived direct image -/

section Composition

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **The composition formula `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*`** for derived direct image of sheaves
of modules on schemes. Both functors are right adjoints of `L(f ≫ g)^*`, the left side through
the composite of the two derived adjunctions of [Stacks, Tag 079W] read along the composition
formula for derived pullback, so the isomorphism is the uniqueness isomorphism of right
adjoints. -/
def derivedPushforwardCompIso :
    derivedPushforward f ⋙ derivedPushforward g ≅ derivedPushforward (f ≫ g) :=
  Adjunction.rightAdjointUniq
    (((derivedAdjunction g).comp (derivedAdjunction f)).ofNatIsoLeft
      (derivedPullbackCompIso f g))
    (derivedAdjunction (f ≫ g))

end Composition

/-! ### Derived direct image around a commutative square -/

section Square

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

/-- **Derived direct image around the two sides of a commutative square of schemes.** For
`g' ≫ f = f' ≫ g` both `Rg'_* ⋙ Rf_*` and `Rf'_* ⋙ Rg_*` are derived direct image along that
one morphism, and the isomorphism between them is the composition formula at each corner. -/
def derivedPushforwardSquareIso (w : g' ≫ f = f' ≫ g) :
    derivedPushforward g' ⋙ derivedPushforward f ≅
      derivedPushforward f' ⋙ derivedPushforward g :=
  derivedPushforwardCompIso g' f ≪≫
    eqToIso (congrArg (fun h : X' ⟶ Y => derivedPushforward h) w) ≪≫
      (derivedPushforwardCompIso f' g).symm

/-- `Stacks.Duality.derivedPushforwardSquareIso` on the quasi-coherent derived categories, for a
square along each of whose four morphisms derived direct image preserves quasi-coherence of
cohomology. It is the ambient isomorphism read on the full subcategories. -/
def quasiCoherentDerivedPushforwardSquareIso (w : g' ≫ f = f' ≫ g) :
    quasiCoherentDerivedPushforward g' hpushg' ⋙ quasiCoherentDerivedPushforward f hpushf ≅
      quasiCoherentDerivedPushforward f' hpushf' ⋙ quasiCoherentDerivedPushforward g hpushg :=
  NatIso.ofComponents
    (fun K => ObjectProperty.isoMk _ ((derivedPushforwardSquareIso g' f' f g w).app K.obj))
    fun e => ObjectProperty.hom_ext _ <|
      (derivedPushforwardSquareIso g' f' f g w).hom.naturality e.hom

end Square

/-! ### The two base change transformations -/

section BaseChange

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

/-- **The transformation `ξ : Rg'_* ∘ a' ⟶ a ∘ Rg_*` underlying [Stacks, Tag 0A9K]**, for a
cartesian square of schemes along each of whose morphisms derived direct image preserves
quasi-coherence of cohomology. It is the mate, under the two twisted inverse image adjunctions
`Rf_* ⊣ a` and `Rf'_* ⊣ a'`, of the comparison of derived direct image around the square.

Tag 0A9K asserts that `ξ` is invertible when `f` and `g` are Tor-independent; that is the
separate statement
`Stacks.Duality.isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent`. The source
presents the same transformation as the mate of the derived base change map of
[Stacks, Tag 08HY]. -/
def twistedInverseImagePushforwardBaseChange (sq : IsPullback g' f' f g) :
    twistedInverseImage f' hpushf' ⋙ quasiCoherentDerivedPushforward g' hpushg' ⟶
      quasiCoherentDerivedPushforward g hpushg ⋙ twistedInverseImage f hpushf :=
  mateEquiv (twistedInverseImageAdjunction f' hpushf') (twistedInverseImageAdjunction f hpushf)
    (quasiCoherentDerivedPushforwardSquareIso g' f' f g hpushg' hpushf hpushf' hpushg sq.w).hom

/-- **The base change map `L(g')^* ∘ a ⟶ a' ∘ Lg^*`** of [Stacks, Tag 0AA6], Equation 48.5.0.1,
for a cartesian square of schemes: the unit of `Lg^* ⊣ Rg_*`, then the inverse of
`L(g')^* ⋆ ξ ⋆ Lg^*`, then the counit of `L(g')^* ⊣ Rg'_*`.

Invertibility of `ξ` is an instance argument; for a Tor-independent square of quasi-compact
quasi-separated schemes it is [Stacks, Tag 0A9K], and the map at those hypotheses is
`Stacks.Duality.torIndependentTwistedInverseImageBaseChange`. -/
@[stacks 0AA6 "variant: the composite for any cartesian square at which ξ is invertible; the tag \
  is Stacks.Duality.torIndependentTwistedInverseImageBaseChange"]
def twistedInverseImageBaseChangeMap (sq : IsPullback g' f' f g)
    [IsIso (twistedInverseImagePushforwardBaseChange g' f' f g hpushg' hpushf hpushf' hpushg
      sq)] :
    twistedInverseImage f hpushf ⋙ quasiCoherentDerivedPullback' g' ⟶
      quasiCoherentDerivedPullback' g ⋙ twistedInverseImage f' hpushf' :=
  let a := twistedInverseImage f hpushf
  let a' := twistedInverseImage f' hpushf'
  let L := quasiCoherentDerivedPullback' g
  let L' := quasiCoherentDerivedPullback' g'
  let R := quasiCoherentDerivedPushforward g hpushg
  let R' := quasiCoherentDerivedPushforward g' hpushg'
  let adjg := quasiCoherentDerivedAdjunction g
    (isQuasicoherent_homology_derivedPullback' g) hpushg
  let adjg' := quasiCoherentDerivedAdjunction g'
    (isQuasicoherent_homology_derivedPullback' g') hpushg'
  let ξ := twistedInverseImagePushforwardBaseChange g' f' f g hpushg' hpushf hpushf' hpushg sq
  Functor.whiskerRight (a.leftUnitor.inv ≫ Functor.whiskerRight adjg.unit a) L' ≫
    Functor.whiskerRight ((Functor.associator L R a).hom ≫
      Functor.whiskerLeft L (inv ξ) ≫ (Functor.associator L a' R').inv) L' ≫
    (Functor.associator (L ⋙ a') R' L').hom ≫
      Functor.whiskerLeft (L ⋙ a') adjg'.counit ≫ (L ⋙ a').rightUnitor.hom

end BaseChange

end Stacks.Duality

end
