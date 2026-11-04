module

public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedRestrictCounit
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BaseChange

/-!
# The twisted inverse image and restriction to opens

Let `f : X ⟶ Y` be a morphism of schemes, let `j : V ⟶ Y` be an open immersion and let

```
U --j'--> X
|         |
f'        f
v         v
V --j---> Y
```

be the base change of `j` along `f`, so that `j' : U ⟶ X` is again an open immersion and
`U = f^{-1}(V)`. Write `a` for the right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` and `a'`
for the right adjoint of `Rf'_*` — the twisted inverse images of [Stacks, Tag 0A9E]. This is the
situation of the section "Right adjoint of pushforward and restriction to opens", and
[Stacks, Tag 0A9L] records the canonical transformation

```
(j')^* ∘ a ⟶ (j')^* ∘ a ∘ Rj_* ∘ j^* ⟵ (j')^* ∘ Rj'_* ∘ a' ∘ j^* ⟶ a' ∘ j^*
```

built from three arrows. The first is the unit of `j^* ⊣ Rj_*`, whiskered by `(j')^* ∘ a` on the
left; the second is the inverse of `(j')^* ⋆ ξ ⋆ j^*`, where
`ξ : Rj'_* ∘ a' ⟶ a ∘ Rj_*` is the transformation of [Stacks, Tag 0A9K] attached to the square;
the third is the counit of `(j')^* ⊣ Rj'_*`, whiskered by `a' ∘ j^*` on the right. Along an open
immersion the counit is invertible and `Rj_*` is fully faithful, so the composite is the unique
arrow compatible with the two adjunctions.

## Main definitions

All in the namespace `Stacks.Duality.OpenImmersion`.

* `quasiCoherentDerivedRestrict` — the exact restriction `j^* : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_V)` along
  an open immersion, given that it preserves quasi-coherence of cohomology.
* `quasiCoherentDerivedRestrictAdjunction` — the adjunction `j^* ⊣ Rj_*` on the quasi-coherent
  derived categories.
* `twistedInverseImageRestrictionMap` — the transformation `(j')^* ∘ a ⟶ a' ∘ j^*` of
  [Stacks, Tag 0A9L], for an arbitrary cartesian square along an open immersion. The tag itself is
  registered on its instance at quasi-compact quasi-separated schemes,
  `Stacks.Duality.OpenImmersion.qcqsTwistedInverseImageRestrictionMap` in
  `StacksFrontier/AlgebraicGeometry/Duality/OpenImmersion/TwistedInverseImageRestrictionQcqs.lean`,
  where every argument below is proved.

## Implementation notes

*The exact restriction, not the derived pullback.* [Stacks, Tag 0A9L] is stated with `j^*` and
`(j')^*`, restriction of sheaves of modules along an open immersion, and not with the derived
pullback `Lj^*`. Restriction along an open immersion is exact, so it needs no derivation: the
functor used here is `Stacks.Duality.OpenImmersion.derivedRestrict`, which is
`Functor.mapDerivedCategory` of `AlgebraicGeometry.Scheme.Modules.restrictFunctor`, together with
its adjunction `Stacks.Duality.OpenImmersion.liftDerivedRestrictPushforwardAdjunction`. The two
functors `Lj^*` and `j^*` agree for an exact restriction, but no isomorphism between
`Stacks.Duality.derivedPullback j` and `derivedRestrict j` is available in this repository, and
none is used: reading the statement with `Stacks.Duality.quasiCoherentDerivedPullback` would make
it a special case of [Stacks, Tag 0AA6] rather than Tag 0A9L. The gain is real — the counit of
`j^* ⊣ Rj_*` is invertible by
`Stacks.Duality.OpenImmersion.isIso_derivedRestrictPushforwardAdjunction_counit`, which has no
analogue for a general derived pullback.

*Invertibility of `ξ` is an instance argument.* [Stacks, Tag 0A9K] asserts that `ξ` is an
isomorphism for a Tor-independent cartesian square of quasi-compact, quasi-separated schemes; it is
`Stacks.Duality.isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent`, and the
open-immersion case is
`Stacks.Duality.isIso_twistedInverseImagePushforwardBaseChange_of_isOpenImmersion`. Both lie
downstream of this module. Since the displayed composite literally contains `ξ⁻¹`, it does
not exist without that invertibility, so it is carried as an instance argument exactly as in
`Stacks.Duality.twistedInverseImageBaseChangeMap`.

*Quasi-coherence and adjointness are hypotheses.* Preservation of quasi-coherence of cohomology by
derived direct image along each of the four morphisms, and by restriction along `j` and `j'`, are
explicit arguments; this is the open-immersion case of [Stacks, Tag 08D5] and the first half of
[Stacks, Tag 0A9E], both proved downstream of this module. That `Rf_*` and `Rf'_*` have right
adjoints — the second half of Tag 0A9E — is an instance argument, as in
`StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizingModule.lean`. Openness of `j'` is likewise
an instance argument, although it follows from the square, because `(j')^*` occurs in the type.

*The model of the derived categories.* The derived categories here are the locally small ones of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, as in
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/BaseChange.lean`, whose design note
explains why that model is forced for the quasi-coherent statements: it is the only one at which
`D_QCoh(𝒪_X)` has the direct sums Brown representability needs. The two auxiliary definitions
below, which mention no derived pullback, are stated at a free morphism universe as the rest of
`Duality/OpenImmersion/` is.

*No `@[stacks]` attribute here.* The arguments of `twistedInverseImageRestrictionMap` are
discharged at quasi-compact quasi-separated schemes downstream, by [Stacks, Tag 08D5], Tag 0A9E
and the open-immersion case of Tag 0A9K
(`Stacks.Duality.isIso_twistedInverseImagePushforwardBaseChange_of_isOpenImmersion`), and Tag 0A9L
is registered there; this module lies upstream of those results and cannot discharge them.

## References

* [Stacks Project, Tag 0A9L](https://stacks.math.columbia.edu/tag/0A9L)
* [Stacks Project, Tag 0AA6](https://stacks.math.columbia.edu/tag/0AA6)
* [Stacks Project, Tag 0A9K](https://stacks.math.columbia.edu/tag/0A9K)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe w u

namespace Stacks.Duality.OpenImmersion

/-! ### Restriction along an open immersion on the quasi-coherent derived categories -/

section Restriction

variable {V Y : Scheme.{u}} (j : V ⟶ Y) [IsOpenImmersion j]
  [HasDerivedCategory.{w} V.Modules] [HasDerivedCategory.{w} Y.Modules]
  (hres : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
    ((DerivedCategory.homologyFunctor V.Modules i).obj
      ((derivedRestrict j).obj K.obj)).IsQuasicoherent)
  (hpush : ∀ (K : quasiCoherentDerivedCategory V) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((Stacks.Duality.derivedPushforward j).obj K.obj)).IsQuasicoherent)

/-- **The exact restriction `j^* : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_V)`** along an open immersion of
schemes, given that it preserves quasi-coherence of the cohomology sheaves. No derivation is
involved: restriction of sheaves of modules along an open immersion is exact. -/
abbrev quasiCoherentDerivedRestrict :
    quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory V :=
  liftDerivedRestrict j _ _ hres

/-- **The adjunction `j^* ⊣ Rj_*` on the quasi-coherent derived categories** of an open immersion
of schemes, for which both functors preserve quasi-coherence of cohomology. It is
`Stacks.Duality.OpenImmersion.liftDerivedRestrictPushforwardAdjunction` for the pair of full
subcategories `D_QCoh(𝒪_Y)`, `D_QCoh(𝒪_V)`. -/
abbrev quasiCoherentDerivedRestrictAdjunction :
    quasiCoherentDerivedRestrict j hres ⊣ Stacks.Duality.quasiCoherentDerivedPushforward j hpush :=
  liftDerivedRestrictPushforwardAdjunction j _ _ hres hpush

end Restriction

/-! ### The twisted inverse image and restriction to opens -/

section BaseChange

variable {U X V Y : Scheme.{u}} (j' : U ⟶ X) (f' : U ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
  [IsOpenImmersion j'] [IsOpenImmersion j]
  (hpushj' : ∀ (K : quasiCoherentDerivedCategory U) (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((Stacks.Duality.derivedPushforward j').obj K.obj)).IsQuasicoherent)
  (hpushf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((Stacks.Duality.derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (hpushf' : ∀ (K : quasiCoherentDerivedCategory U) (i : ℤ),
    ((DerivedCategory.homologyFunctor V.Modules i).obj
      ((Stacks.Duality.derivedPushforward f').obj K.obj)).IsQuasicoherent)
  (hpushj : ∀ (K : quasiCoherentDerivedCategory V) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((Stacks.Duality.derivedPushforward j).obj K.obj)).IsQuasicoherent)
  (hresj : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
    ((DerivedCategory.homologyFunctor V.Modules i).obj
      ((derivedRestrict j).obj K.obj)).IsQuasicoherent)
  (hresj' : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor U.Modules i).obj
      ((derivedRestrict j').obj K.obj)).IsQuasicoherent)
  [(Stacks.Duality.quasiCoherentDerivedPushforward f hpushf).IsLeftAdjoint]
  [(Stacks.Duality.quasiCoherentDerivedPushforward f' hpushf').IsLeftAdjoint]

/-- **The transformation `(j')^* ∘ a ⟶ a' ∘ j^*`** of [Stacks, Tag 0A9L], for an open immersion
`j : V ⟶ Y` and its base change `j' : U ⟶ X` along `f : X ⟶ Y`: the unit of `j^* ⊣ Rj_*`, then the
inverse of `(j')^* ⋆ ξ ⋆ j^*`, then the counit of `(j')^* ⊣ Rj'_*`.

Here `a` and `a'` are the twisted inverse images of `f` and `f'`, and `ξ` is the transformation
`Rj'_* ∘ a' ⟶ a ∘ Rj_*` attached to the square. Invertibility of `ξ` is an instance argument; it is
supplied by [Stacks, Tag 0A9K]
(`Stacks.Duality.isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent`, and for an open
immersion `Stacks.Duality.isIso_twistedInverseImagePushforwardBaseChange_of_isOpenImmersion`). At
quasi-compact quasi-separated schemes every argument is discharged in
`Stacks.Duality.OpenImmersion.qcqsTwistedInverseImageRestrictionMap`, which carries the tag. -/
def twistedInverseImageRestrictionMap (sq : IsPullback j' f' f j)
    [IsIso (Stacks.Duality.twistedInverseImagePushforwardBaseChange j' f' f j hpushj' hpushf
      hpushf' hpushj sq)] :
    Stacks.Duality.twistedInverseImage f hpushf ⋙ quasiCoherentDerivedRestrict j' hresj' ⟶
      quasiCoherentDerivedRestrict j hresj ⋙ Stacks.Duality.twistedInverseImage f' hpushf' :=
  let a := Stacks.Duality.twistedInverseImage f hpushf
  let a' := Stacks.Duality.twistedInverseImage f' hpushf'
  let L := quasiCoherentDerivedRestrict j hresj
  let L' := quasiCoherentDerivedRestrict j' hresj'
  let R := Stacks.Duality.quasiCoherentDerivedPushforward j hpushj
  let R' := Stacks.Duality.quasiCoherentDerivedPushforward j' hpushj'
  let adjj := quasiCoherentDerivedRestrictAdjunction j hresj hpushj
  let adjj' := quasiCoherentDerivedRestrictAdjunction j' hresj' hpushj'
  let ξ := Stacks.Duality.twistedInverseImagePushforwardBaseChange j' f' f j hpushj' hpushf
    hpushf' hpushj sq
  Functor.whiskerRight (a.leftUnitor.inv ≫ Functor.whiskerRight adjj.unit a) L' ≫
    Functor.whiskerRight ((Functor.associator L R a).hom ≫
      Functor.whiskerLeft L (inv ξ) ≫ (Functor.associator L a' R').inv) L' ≫
    (Functor.associator (L ⋙ a') R' L').hom ≫
      Functor.whiskerLeft (L ⋙ a') adjj'.counit ≫ (L ⋙ a').rightUnitor.hom

end BaseChange

end Stacks.Duality.OpenImmersion

end
