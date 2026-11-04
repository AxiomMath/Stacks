module

public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.TwistedInverseImageRestriction
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BaseChangeConjugate

/-!
# Over an open of the base, Tag 0A9K is Tag 08FE

Let `f : X ⟶ Y` be a morphism of schemes, let `j : V ⟶ Y` be an open immersion and let

```
U --j'--> X
|         |
f'        f
v         v
V --j---> Y
```

be the base change of `j` along `f`. Write `a` and `a'` for the twisted inverse images of
[Stacks, Tag 0A9E] along `f` and `f'`, and let `ξ : Rj'_* ∘ a' ⟶ a ∘ Rj_*` be the transformation
of [Stacks, Tag 0A9K] attached to the square — the one whose inverse the transformation of
[Stacks, Tag 0A9L] is built from, in
`StacksFrontier/AlgebraicGeometry/Duality/OpenImmersion/TwistedInverseImageRestriction.lean`.

`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/BaseChangeConjugate.lean` identifies
`ξ` as the conjugate of the derived base change map `Lj^* ∘ Rf_* ⟶ Rf'_* ∘ L(j')^*`, so that
Tag 0A9K is equivalent to [Stacks, Tag 08IB]. Along an open immersion a sharper reading is
available, and it is the point of this module: restriction along an open immersion is exact, so the
left adjoint of `Rj_*` may be taken to be the exact restriction `j^*` of
`Stacks.Duality.OpenImmersion.quasiCoherentDerivedRestrict` rather than a derived pullback, and
the conjugate of `ξ` is then the comparison

`(Rf_*K)|_V ⟶ Rf'_*(K|_U)`

of [Stacks, Tag 08FE]. So over an open of the base, invertibility of `ξ` is equivalent to Tag 08FE
and does not need Tag 08IB at all.

## Main definitions

All in the namespace `Stacks.Duality.OpenImmersion`.

* `quasiCoherentDerivedRestrictBaseChangeSquare` — the comparison
  `Rf_* ⋙ j^* ⟶ (j')^* ⋙ Rf'_*` of [Stacks, Tag 08FE] on the quasi-coherent derived categories,
  as the mate of the comparison of derived direct image around the square, read backwards.

## Main results

* `twistedInverseImagePushforwardBaseChange_eq_conjugateEquiv_restrict` — `ξ` is the conjugate of
  that comparison.
* `isIso_twistedInverseImagePushforwardBaseChange_iff_restrict` — `ξ` is invertible if and only if
  the comparison of [Stacks, Tag 08FE] is.
* `isIso_twistedInverseImagePushforwardBaseChange_of_isIso_restrictBaseChangeSquare` — the
  direction that discharges the `IsIso ξ` instance argument of
  `Stacks.Duality.OpenImmersion.twistedInverseImageRestrictionMap`.

## Implementation notes

*Why this is a strictly nearer blocker than Tag 08IB.* [Stacks, Tag 08FE] is proved in this
repository, for ringed spaces and — unlike the derived base change map of [Stacks, Tag 08HY] — at
an arbitrary model of the derived category and for arbitrary choices of right derived functors of
the four degreewise functors: `Stacks.Cohomology.derivedPushforwardRestrictIso` of
`StacksFrontier/Topology/Sheaves/Cohomology/CechAndResolutions/KInjectiveRestriction.lean`, with its
canonicality statement `Stacks.Cohomology.derivedPushforwardRestrictIso_isCanonical`. So the
locally small model is no obstacle here, and nothing has to be transported.

The identification of that isomorphism with the comparison below is not made here, and it
is not needed:
`StacksFrontier/AlgebraicGeometry/Duality/OpenImmersion/TwistedInverseImageRestrictionBaseChange.lean`
proves `IsIso (quasiCoherentDerivedRestrictBaseChangeSquare ..)`, and so `IsIso ξ`, from the
*existence* of the isomorphism Tag 08FE delivers and nothing more. Tag 08FE delivers *some*
isomorphism `Rf ⋙ Rj ≅ Ri ⋙ Rg`, got from the universal property of the right derived functor
applied to a homotopy-level mate, whereas `quasiCoherentDerivedRestrictBaseChangeSquare` is the
mate of `Stacks.Duality.quasiCoherentDerivedPushforwardSquareIso`, which is built from uniqueness
of right adjoints at each corner; matching the two would be the same obstruction that
`StacksFrontier/AlgebraicGeometry/BaseChange/TorIndependence/DerivedBaseChangeGlobal.lean` records for
the affine case of [Stacks, Tag 0DJ9], and
`Stacks.Cohomology.DerivedBaseChange.isIso_mateEquiv_app_of_isIso_counit` goes around it.

*Where the two invertible arrows go.* Reading the mate backwards, the comparison below is the
composite of `j^*` applied to `Rf_*` of the unit of `(j')^* ⊣ Rj'_*`, then `j^*` of the comparison
around the square, then the counit of `j^* ⊣ Rj_*`. The last two are invertible — the second
always, the third because `j` is an open immersion, by
`Stacks.Duality.OpenImmersion.isIso_derivedRestrictPushforwardAdjunction_counit`. So the whole
content sits in the first arrow, `(Rf_*K)|_V ⟶ (Rf_*Rj'_*(K|_U))|_V`; that is the shape in which
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/SupportedPushforward.lean` proves the vanishing half of
Tag 08FE, in the private declaration `isZero_derivedRestrict_derivedPushforward`.

*No `@[stacks]` attribute.* Nothing below asserts Tag 0A9K or Tag 08FE: the results are
equivalences, and their hypothesis is the conclusion of Tag 08FE at this model. That hypothesis is
discharged in
`StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.TwistedInverseImageRestrictionBaseChange`,
which carries both tags.

## References

* [Stacks Project, Tag 0A9K](https://stacks.math.columbia.edu/tag/0A9K)
* [Stacks Project, Tag 0A9L](https://stacks.math.columbia.edu/tag/0A9L)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace Stacks.Duality.OpenImmersion

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

/-- **The comparison `(Rf_*K)|_V ⟶ Rf'_*(K|_U)` of [Stacks, Tag 08FE]** on the quasi-coherent
derived categories, for an open immersion `j : V ⟶ Y` and its base change `j' : U ⟶ X` along
`f : X ⟶ Y`. It is the mate of the comparison
`Stacks.Duality.quasiCoherentDerivedPushforwardSquareIso` of derived direct image around the
square, read backwards across the two adjunctions `(j')^* ⊣ Rj'_*` and `j^* ⊣ Rj_*`: the unit of
the first, then the comparison, then the counit of the second.

Tag 08FE asserts that this is invertible. That is proved in this repository only for ringed spaces
and for the isomorphism got from the universal property of the right derived functor, which has not
been matched with this mate; see the module documentation. -/
def quasiCoherentDerivedRestrictBaseChangeSquare (w : j' ≫ f = f' ≫ j) :
    Stacks.Duality.quasiCoherentDerivedPushforward f hpushf ⋙ quasiCoherentDerivedRestrict j hresj ⟶
      quasiCoherentDerivedRestrict j' hresj' ⋙
        Stacks.Duality.quasiCoherentDerivedPushforward f' hpushf' :=
  (mateEquiv (quasiCoherentDerivedRestrictAdjunction j' hresj' hpushj')
      (quasiCoherentDerivedRestrictAdjunction j hresj hpushj)).symm
    (TwoSquare.mk _ _ _ _ (Stacks.Duality.quasiCoherentDerivedPushforwardSquareIso j' f' f j
      hpushj' hpushf hpushf' hpushj w).hom)

/-- The mate of the comparison of [Stacks, Tag 08FE] across the two restriction adjunctions is the
comparison of derived direct image around the square, by construction. -/
theorem mateEquiv_quasiCoherentDerivedRestrictBaseChangeSquare (w : j' ≫ f = f' ≫ j) :
    mateEquiv (quasiCoherentDerivedRestrictAdjunction j' hresj' hpushj')
        (quasiCoherentDerivedRestrictAdjunction j hresj hpushj)
        (TwoSquare.mk _ _ _ _ (quasiCoherentDerivedRestrictBaseChangeSquare j' f' f j hpushj'
          hpushf hpushf' hpushj hresj hresj' w)) =
      TwoSquare.mk _ _ _ _ (Stacks.Duality.quasiCoherentDerivedPushforwardSquareIso j' f' f j
        hpushj' hpushf hpushf' hpushj w).hom :=
  Equiv.apply_symm_apply _ _

section Conjugate

variable [(Stacks.Duality.quasiCoherentDerivedPushforward f hpushf).IsLeftAdjoint]
  [(Stacks.Duality.quasiCoherentDerivedPushforward f' hpushf').IsLeftAdjoint]

/-- **The transformation `ξ` of [Stacks, Tag 0A9K] over an open of the base is the conjugate of the
comparison of [Stacks, Tag 08FE]**, with respect to the composite adjunctions
`(j')^* ⋙ Rf'_* ⊣ a' ⋙ Rj'_*` and `Rf_* ⋙ j^* ⊣ Rj_* ⋙ a`. -/
theorem twistedInverseImagePushforwardBaseChange_eq_conjugateEquiv_restrict
    (sq : IsPullback j' f' f j) :
    Stacks.Duality.twistedInverseImagePushforwardBaseChange j' f' f j hpushj' hpushf hpushf'
        hpushj sq =
      conjugateEquiv
        ((quasiCoherentDerivedRestrictAdjunction j' hresj' hpushj').comp
          (Stacks.Duality.twistedInverseImageAdjunction f' hpushf'))
        ((Stacks.Duality.twistedInverseImageAdjunction f hpushf).comp
          (quasiCoherentDerivedRestrictAdjunction j hresj hpushj))
        (quasiCoherentDerivedRestrictBaseChangeSquare j' f' f j hpushj' hpushf hpushf' hpushj
          hresj hresj' sq.w) := by
  have h := iterated_mateEquiv_conjugateEquiv
    (quasiCoherentDerivedRestrictAdjunction j' hresj' hpushj')
    (quasiCoherentDerivedRestrictAdjunction j hresj hpushj)
    (Stacks.Duality.twistedInverseImageAdjunction f hpushf)
    (Stacks.Duality.twistedInverseImageAdjunction f' hpushf')
    (TwoSquare.mk _ _ _ _ (quasiCoherentDerivedRestrictBaseChangeSquare j' f' f j hpushj' hpushf
      hpushf' hpushj hresj hresj' sq.w))
  rw [mateEquiv_quasiCoherentDerivedRestrictBaseChangeSquare] at h
  exact h

/-- **Over an open of the base, the transformation `ξ` of [Stacks, Tag 0A9K] is invertible if and
only if the comparison of [Stacks, Tag 08FE] is.** Conjugation preserves and reflects
invertibility. -/
theorem isIso_twistedInverseImagePushforwardBaseChange_iff_restrict (sq : IsPullback j' f' f j) :
    IsIso (Stacks.Duality.twistedInverseImagePushforwardBaseChange j' f' f j hpushj' hpushf
        hpushf' hpushj sq) ↔
      IsIso (quasiCoherentDerivedRestrictBaseChangeSquare j' f' f j hpushj' hpushf hpushf' hpushj
        hresj hresj' sq.w) := by
  rw [twistedInverseImagePushforwardBaseChange_eq_conjugateEquiv_restrict j' f' f j hpushj' hpushf
    hpushf' hpushj hresj hresj' sq]
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  exact conjugateEquiv_of_iso
    ((quasiCoherentDerivedRestrictAdjunction j' hresj' hpushj').comp
      (Stacks.Duality.twistedInverseImageAdjunction f' hpushf'))
    ((Stacks.Duality.twistedInverseImageAdjunction f hpushf).comp
      (quasiCoherentDerivedRestrictAdjunction j hresj hpushj)) _

/-- **[Stacks, Tag 08FE] at this model gives the invertibility of `ξ` over an open of the base**,
and so discharges the instance argument of
`Stacks.Duality.OpenImmersion.twistedInverseImageRestrictionMap`, which is [Stacks, Tag 0A9L].
Unlike the general case this does not go through [Stacks, Tag 08IB]. -/
theorem isIso_twistedInverseImagePushforwardBaseChange_of_isIso_restrictBaseChangeSquare
    (sq : IsPullback j' f' f j)
    [IsIso (quasiCoherentDerivedRestrictBaseChangeSquare j' f' f j hpushj' hpushf hpushf' hpushj
      hresj hresj' sq.w)] :
    IsIso (Stacks.Duality.twistedInverseImagePushforwardBaseChange j' f' f j hpushj' hpushf
      hpushf' hpushj sq) :=
  (isIso_twistedInverseImagePushforwardBaseChange_iff_restrict j' f' f j hpushj' hpushf hpushf'
    hpushj hresj hresj' sq).2 ‹_›

end Conjugate

end Stacks.Duality.OpenImmersion

end
