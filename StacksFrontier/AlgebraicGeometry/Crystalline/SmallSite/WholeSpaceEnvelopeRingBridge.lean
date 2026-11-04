module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceEnvelope
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceSystemLevelRings

/-!
# The ring of the object `D(n)` of the site is the degree `n` of the cosimplicial ring `D(*)`

Two constructions in this chapter produce the `p`-adically completed divided power envelope
`D(n)` of the `(n + 1)`-fold tensor power presentation, and until this module nothing related
them.

* `Crystalline.tensorPowerEnvelopeThickening` realises `D(n)` as an *object of the completed
  affine crystalline site* `Cris^∧(C/A)`, which is what
  `Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceSystem` transports the finite
  levels of.  Its ring is produced by an essential-surjectivity argument and the definition
  producing it is sealed (`no_expose`), so outside the module that builds it the ring is opaque:
  nothing about it reduces.
* `Crystalline.cosimplicialEnvelopeRing` — and so
  `...SmallSite.wholeSpaceEnvelopeRing` — has `D(n)` as the *transparent* type
  `Crystalline.pAdicCompletedTensorPowerEnvelope`, an `AdicCompletion` of a divided power
  envelope, and it is over that cosimplicial ring that [Stacks, Tag 07L9] and
  [Stacks, Tag 07LA] are read.

`Crystalline.CompletedEnvelopeThickening.ring_eq` is the one statement in the tree that connects
them, and before this module it had no consumer.  This module turns it into the ring
isomorphism, and records what it does to the image of the presentation algebra, which is the
only handle a map out of `D(n)` is ever pinned by.

## Main definitions

* `DividedPowerRing.ringEquivOfEq` — an equality of divided power rings, read as a ring
  isomorphism of their carriers.
* `Crystalline.completedEnvelopeThickeningRingEquiv` — **the ring of the site-theoretic
  realisation `D` of a polynomial presentation is the completed divided power envelope of the
  presentation.**
* `Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceSystemEnvelopeRingEquiv` — **the
  ring of the object `D(n)` the system of [Stacks, Tag 07JN] is built from is the degree `n` of
  the cosimplicial ring `...SmallSite.wholeSpaceEnvelopeRing`.**

## Main results

* `Crystalline.completedEnvelopeThickeningRingEquiv_presentationMap` and
  `...SmallSite.wholeSpaceSystemEnvelopeRingEquiv_presentationMap` — the isomorphism carries the
  image of the presentation algebra `P` to the image of `P`, i.e. it is the identification under
  which both realisations have the same canonical map out of `P`.  Since a morphism out of a
  completed envelope is determined by its restriction to the image of `P`, this is the statement
  any comparison of the two `D(•)` structure maps has to be built from.

## What is and is not proved

Everything here is proved and nothing is assumed beyond what the two constructions carry.

**This does not compare the two cosimplicial structures.**  The structure map of
`Crystalline.envelopeCosimplicial` is a `Cofan.IsColimit.desc` out of the coproduct of
[Stacks, Tag 07L4], pinned only by `Crystalline.envelopeCosimplicial_coprojection_comp_map`;
the structure map of `Crystalline.cosimplicialEnvelopeRing` is the explicit
`Crystalline.adicCompletionRingMap` of `Crystalline.envelopeReindex`, pinned by
`Crystalline.cosimplicialEnvelopeRing_map_polynomial`.  That the isomorphism below intertwines
them is **not proved here**; it is proved in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/EnvelopeCosimplicialComparison.lean`, as
`Crystalline.tensorPowerEnvelopeThickeningRingEquiv_envelopeCosimplicial_map` and
`...SmallSite.wholeSpaceSystemEnvelopeRingEquiv_map`, so it is no longer among the things
[Stacks, Tag 07LF] owes.  **No tag attribute is placed.**

## References

* [Stacks Project, Tag 07L4](https://stacks.math.columbia.edu/tag/07L4)
* [Stacks Project, Tag 07J8](https://stacks.math.columbia.edu/tag/07J8)
* [Stacks Project, Tag 07JF](https://stacks.math.columbia.edu/tag/07JF)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v w r a

noncomputable section

namespace DividedPowerRing

/-- **An equality of divided power rings, read as a ring isomorphism of their carriers.**  The
divided power ideals and the divided powers are carried along too, the equality being one of
whole structures; what is used below is only the ring isomorphism. -/
def ringEquivOfEq {R S : DividedPowerRing.{r}} (h : R = S) : (R : Type r) ≃+* (S : Type r) := by
  cases h
  exact RingEquiv.refl _

/-- The ring isomorphism induced by `rfl` is the identity. -/
@[simp]
theorem ringEquivOfEq_rfl {R : DividedPowerRing.{r}} :
    ringEquivOfEq (rfl : R = R) = RingEquiv.refl _ := rfl

/-- **Two ring homomorphisms into equal divided power rings which agree up to the equality agree
after it is read as an isomorphism.**  This is the form in which the `HEq` fields of
`Crystalline.CompletedEnvelopeThickening` are consumed. -/
theorem ringEquivOfEq_apply_of_heq {R S : DividedPowerRing.{r}} {P : Type a} [CommRing P]
    (h : R = S) (f : P →+* (R : Type r)) (g : P →+* (S : Type r)) (hfg : HEq f g) (q : P) :
    ringEquivOfEq h (f q) = g q := by
  cases h
  cases hfg
  rfl

end DividedPowerRing

namespace Crystalline

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
  (g : MvPolynomial ι s.A →ₐ[s.A] s.C) (hg : Function.Surjective g)

/-- **The ring of the object of `Cris^∧(C/A)` realising a polynomial presentation's completed
divided power envelope is that envelope.**

The realisation `Crystalline.completedEnvelopeThickening` is produced by an
essential-surjectivity argument and its definition is sealed, so its ring is not the envelope on
the nose and no reduction reaches it; the field
`Crystalline.CompletedEnvelopeThickening.ring_eq` is the identification, and this is it read as
a ring isomorphism. -/
def completedEnvelopeThickeningRingEquiv :
    ((completedEnvelopeThickening s g hg).thickening.ring : Type (max u w)) ≃+*
      pAdicCompletedDividedPowerEnvelope s g hg :=
  DividedPowerRing.ringEquivOfEq (completedEnvelopeThickening s g hg).ring_eq

/-- **The identification carries the image of the presentation algebra to the image of the
presentation algebra.**  Both realisations carry a canonical map out of `P`, and the
identification of the rings matches them; this is the field
`Crystalline.CompletedEnvelopeThickening.presentationMap_eq` read through the isomorphism.

A morphism out of a completed divided power envelope is determined by its restriction along the
map out of `P`, so this is the statement from which any comparison of maps out of the two
realisations must be built. -/
theorem completedEnvelopeThickeningRingEquiv_presentationMap (q : MvPolynomial ι s.A) :
    completedEnvelopeThickeningRingEquiv s g hg
        ((completedEnvelopeThickening s g hg).presentationMap q) =
      toPAdicCompletedDividedPowerEnvelope s g hg q :=
  DividedPowerRing.ringEquivOfEq_apply_of_heq _ _ _
    (completedEnvelopeThickening s g hg).presentationMap_eq q

/-- **The ring of the object `D(n)` of `Cris^∧(C/A)` is
`Crystalline.pAdicCompletedTensorPowerEnvelope`**, the degree `n` of the cosimplicial ring
`Crystalline.cosimplicialEnvelopeRing`. -/
def tensorPowerEnvelopeThickeningRingEquiv (n : ℕ) :
    ((tensorPowerEnvelopeThickening s g hg n).thickening.ring : Type (max u w)) ≃+*
      pAdicCompletedTensorPowerEnvelope s g hg n :=
  completedEnvelopeThickeningRingEquiv s (tensorPowerPresentation s g n)
    (tensorPowerPresentation_surjective s g hg n)

/-- The isomorphism `tensorPowerEnvelopeThickeningRingEquiv` carries the canonical map out of the
`(n + 1)`-fold tensor power presentation algebra to `tensorPowerEnvelopeMap`. -/
theorem tensorPowerEnvelopeThickeningRingEquiv_presentationMap (n : ℕ)
    (q : MvPolynomial (Fin (n + 1) × ι) s.A) :
    tensorPowerEnvelopeThickeningRingEquiv s g hg n
        ((tensorPowerEnvelopeThickening s g hg n).presentationMap q) =
      tensorPowerEnvelopeMap s g hg n q :=
  completedEnvelopeThickeningRingEquiv_presentationMap s _ _ q

end Crystalline

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}} (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [WholeSpacePresentation S hp]
  [IsAffine S.X] [IsAffine S.S.scheme]

/-- **The ring of the object `D(n)` the system of [Stacks, Tag 07JN] is built from is the degree
`n` of the cosimplicial ring `...SmallSite.wholeSpaceEnvelopeRing`.**

`...SmallSite.wholeSpaceSystemEnvelope hp n` is the object of `Cris^∧(Γ(X, ⊤)/Γ(S, ⊤))` whose
finite levels the system transports, and `...SmallSite.wholeSpaceSystemLevelRingEquiv` reads the
sections of `𝒪_{X/S}` over a level as a quotient of *its* ring; `...SmallSite.wholeSpaceEnvelope`
is the cosimplicial envelope over whose cosimplicial ring [Stacks, Tag 07LA] is read.  This is
the identification of the two, in each degree. -/
def wholeSpaceSystemEnvelopeRingEquiv (n : ℕ) :
    ((wholeSpaceSystemEnvelope hp n).ring : Type u) ≃+*
      ((wholeSpaceEnvelopeRing hp).obj (SimplexCategory.mk n) : Type u) :=
  tensorPowerEnvelopeThickeningRingEquiv (affineSituation S hp)
    (wholeSpacePresentation S hp)
    (wholeSpacePresentation_surjective S hp) n

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- **The identification of the two `D(n)` matches their canonical maps out of the tensor power
of the presentation algebra.** -/
theorem wholeSpaceSystemEnvelopeRingEquiv_presentationMap (n : ℕ)
    (q : MvPolynomial (Fin (n + 1) × wholeSpaceIndex S hp) (affineSituation S hp).A) :
    wholeSpaceSystemEnvelopeRingEquiv hp n
        ((_root_.Crystalline.tensorPowerEnvelopeThickening (affineSituation S hp)
          (wholeSpacePresentation S hp)
          (wholeSpacePresentation_surjective S hp) n).presentationMap q) =
      _root_.Crystalline.tensorPowerEnvelopeMap (affineSituation S hp)
        (wholeSpacePresentation S hp)
        (wholeSpacePresentation_surjective S hp) n q :=
  tensorPowerEnvelopeThickeningRingEquiv_presentationMap _ _ _ n q

/-! ### The cosimplicial direction of the identification of the level rings -/

/-- **The identifications of the level rings are compatible with the cosimplicial direction.**
Restricting a section of `𝒪_{X/S}` along the transition map `T(m)_e ⟶ T(n)_e` of the system
becomes, through the identifications, the reduction to the level `N + e` of the structure map
`D(n) ⟶ D(m)` of `Crystalline.envelopeCosimplicial`.

This is the companion in the `n`-direction of
`...SmallSite.wholeSpaceSystemLevelRingEquiv_restrict`, and like it the proof is the naturality
of the counit of the affine-to-global equivalence and nothing else.  The structure map that
appears is the one of `Crystalline.envelopeCosimplicial`, which is how the system is built;
identifying it with the structure map of `...SmallSite.wholeSpaceEnvelopeRing` is the comparison
this module does not prove, and it is
`...SmallSite.wholeSpaceEnvelopeRingLevelEquiv_map` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/EnvelopeCosimplicialComparison.lean` that
restates this lemma over that structure map. -/
theorem wholeSpaceSystemLevelRingEquiv_map {n m : ℕ} (φ : SimplexCategory.mk n ⟶
    SimplexCategory.mk m) (e : ℕ)
    (x : (structureSheaf S).obj.obj
      (op (((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n))).obj e))) :
    wholeSpaceSystemLevelRingEquiv hp m e
        (((structureSheaf S).obj.map
          (((wholeSpaceSystem S hp).map φ.op).app e).op).hom x) =
      (_root_.Crystalline.levelThickeningMap
          (_root_.Crystalline.isPAdicLevel_uniformLevel_add _ e)
          (_root_.Crystalline.isPAdicLevel_uniformLevel_add _ e)
          ((_root_.Crystalline.envelopeCosimplicial (affineSituation S hp)
            (wholeSpacePresentation S hp)
            (wholeSpacePresentation_surjective S hp)).map φ)
          (le_refl _)).hom.hom.toRingHom
        (wholeSpaceSystemLevelRingEquiv hp n e x) :=
  wholeSiteInverseSectionsRingEquiv_naturality hp _ x

end Crystalline.GlobalCrystallineSituation.SmallSite

end
