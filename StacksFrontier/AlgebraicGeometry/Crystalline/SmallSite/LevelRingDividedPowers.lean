module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.EnvelopeCosimplicialComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.QuotientForms
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystallineDifferentials

/-!
# The section ring of a level object is `D(n)/(p)^{N+e}` as a divided power algebra

Fix a global crystalline situation `(p, (S, I, γ), X)` with `X` and `S` affine.  The
identification

`Γ((X, T(n)_e, δ(n)), 𝒪_{X/S})  ≅  D(n)/(p)^{N + e}`

of `...SmallSite.wholeSpaceEnvelopeRingLevelEquiv` is a bare `RingEquiv`: it is the composite of
`...SmallSite.wholeSpaceSystemLevelRingEquiv`, whose divided power half is
`...SmallSite.isDPMorphism_wholeSpaceSystemLevelRingEquiv`, with the quotient of
`...SmallSite.wholeSpaceSystemEnvelopeRingEquiv`, which had **no** divided power half at all —
`DividedPowerRing.ringEquivOfEq` keeps only the ring isomorphism attached to an equality of
divided power rings and discards the ideal and the divided powers, just as
`Crystalline.DividedPowerThickening.ringEquivOfIso` discards the divided power fields of an
isomorphism of thickenings.

This module recovers the discarded half, in both factors and then in the composite, so that the
section ring of a level object is `D(n)/(p)^{N + e}` *as a divided power ring* in the spelling
`...SmallSite.wholeSpaceEnvelopeRing` uses.  That is what
`Crystalline.tensorFormsLevelEquiv` of `ModuleDifferentials/QuotientForms.lean` and
`Crystalline.differentialFormsEquivOfAlgEquiv` of `ModuleDifferentials/FormsAlgEquiv.lean` need
before the sections of `Ω^i_{X/S}` over a level object — which
`Crystalline.GlobalCrystallineSituation.affineCrysDifferentialFormsIso` presents through
`Crystalline.GlobalCrystallineSituation.crysDividedPowers` — can be read as the divided power
differential forms of the level of `D(n)`.

The same two equivalences also drop the compatibility with the maps from the **base** divided
power ring `Γ(S, ⊤)`, and that is recovered here too: an isomorphism of divided power
thickenings carries a field `fromBase_comp` saying it is a morphism over the base, and
`Crystalline.CompletedEnvelopeThickening` carries a field `fromBase_eq` saying that the
structure map of its realisation of `D(n)` is the canonical `algebraMap`.  The composite
statement is `...SmallSite.wholeSpaceEnvelopeRingLevelEquiv_crysBaseAppLE`: the identification
of the section ring of the level `(n, e)` with `D(n)/(p)^{N + e}` carries
`Crystalline.GlobalCrystallineSituation.crysBaseAppLE` — the map on global sections of
`T(n)_e ⟶ S`, which is `...affineBaseAppLE` at `V = ⊤` — to the reduction of `algebraMap`.
Without it the identification is not an isomorphism of `Γ(S, ⊤)`-algebras, and
`Crystalline.differentialFormsEquivOfAlgEquiv`, which asks for a `B ≃ₐ[A] C`, cannot be applied
to it at all.

Nothing is computed.  Each statement is the forgotten field of a structure that already carries
it: `DividedPowerRing.ringEquivOfEq` is the identity after `cases` on the equality, so it is a
divided power morphism and carries the ideal onto the ideal; and the `fromBase_comp` and
`fromBase_eq` fields are the base compatibilities verbatim.

## Main definitions

* `...SmallSite.wholeSpaceEnvelopeDPRing` — `D(n)` as a `DividedPowerRing`, with its carrier the
  degree `n` of `...SmallSite.wholeSpaceEnvelopeRing`.
* `...SmallSite.wholeSpaceEnvelopeFromBase` — the structure map `Γ(S, ⊤) ⟶ D(n)` of that degree,
  named once as a ring homomorphism into the spelling
  `(wholeSpaceEnvelopeRing hp).obj ⦋n⦌` uses.  The `Algebra` instance of
  `Crystalline.pAdicCompletedDividedPowerEnvelope` is declared at the bare carrier and is
  invisible at the `CommRingCat` spelling — a different `DiscrTree` key — so the crossing is
  paid here, in a definition, and never inside a proof.

## Main results

* `DividedPowerRing.isDPMorphism_ringEquivOfEq`, `..._symm` and
  `DividedPowerRing.ideal_map_ringEquivOfEq` — an equality of divided power rings, read as a
  ring isomorphism, is an **isomorphism of divided power rings**.
* `Crystalline.DividedPowerThickening.fromBase_comp_ringEquivOfIso` — the ring isomorphism of an
  isomorphism of divided power thickenings **commutes with the maps from the base**.
* `Crystalline.isDPMorphism_quotientMap_pAdic` — a divided power morphism descends to the finite
  `p`-adic levels as a divided power morphism of the quotient divided powers.  This is
  `Crystalline.isDPMorphism_quotientMapₐ` at `K = (p)^k` with no base algebra in sight: the
  conclusion is about ring homomorphisms, and the levels of two different rings are not
  algebras over one ring in any way this needs.
* `...SmallSite.isDPMorphism_wholeSpaceSystemEnvelopeRingEquiv` — the identification of the two
  realisations of `D(n)` is a divided power isomorphism.
* `...SmallSite.isPAdicLevel_wholeSpaceEnvelopeDPRing` — `N + e` is a `p`-adic level of `D(n)` in
  the `...SmallSite.wholeSpaceEnvelopeRing` spelling, for the uniform cutoff `N`.
* `Crystalline.ideal_map_of_isDPMorphism_symm` — a ring isomorphism which is a divided power
  morphism in both directions carries the divided power ideal **onto** the divided power ideal,
  which is what `Crystalline.differentialFormsEquivOfAlgEquiv` asks and what an `IsDPMorphism`,
  an inclusion, does not give.
* `...SmallSite.isDPMorphism_wholeSpaceEnvelopeRingLevelEquiv` and its `_symm` — **the main
  result**: the section ring of the level `(n, e)` is `D(n)/(p)^{N + e}` as a divided power ring,
  in both directions.
* `Crystalline.completedEnvelopeThickeningRingEquiv_fromBase` and
  `...SmallSite.wholeSiteInverseSectionsRingEquiv_fromBase` — the two halves of the base
  compatibility, and `...SmallSite.wholeSpaceEnvelopeRingLevelEquiv_crysBaseAppLE` — **the second
  main result**: the same identification is one of `Γ(S, ⊤)`-algebras.

## What is and is not proved

**No tag attribute is placed and [Stacks, Tag 07LF] is not proved here.**  This is one of the
crossings the isomorphism `ε` of that tag has to make, the one listed first in the "What is left
of `ε`" note of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/TensorRestrictionVanishing.lean`.  Neither
the degreewise composite nor its assembly is built here.

## References

* [Stacks Project, Tag 07J8](https://stacks.math.columbia.edu/tag/07J8)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07L4](https://stacks.math.columbia.edu/tag/07L4)
* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u v w r

namespace DividedPowerRing

/-- **An equality of divided power rings, read as a ring isomorphism, is a divided power
morphism.**  After `cases` on the equality it is the identity, whose divided power compatibility
is `DividedPowers.DPMorphism.id`. -/
theorem isDPMorphism_ringEquivOfEq {R S : DividedPowerRing.{r}} (h : R = S) :
    DividedPowers.IsDPMorphism R.dividedPowers S.dividedPowers
      (ringEquivOfEq h : (R : Type r) →+* (S : Type r)) := by
  cases h
  exact (DividedPowers.DPMorphism.id R.dividedPowers).isDPMorphism

/-- **The inverse is a divided power morphism too**, so `DividedPowerRing.ringEquivOfEq` is an
isomorphism of divided power rings and not merely a ring isomorphism of two rings that happen to
carry divided powers. -/
theorem isDPMorphism_ringEquivOfEq_symm {R S : DividedPowerRing.{r}} (h : R = S) :
    DividedPowers.IsDPMorphism S.dividedPowers R.dividedPowers
      ((ringEquivOfEq h).symm : (S : Type r) →+* (R : Type r)) := by
  cases h
  exact (DividedPowers.DPMorphism.id R.dividedPowers).isDPMorphism

/-- **The divided power ideal is carried onto the divided power ideal.**  This is the hypothesis
`hJ` of `Crystalline.differentialFormsEquivOfAlgEquiv`, which an `IsDPMorphism` — an *inclusion*
of the image in the target ideal — does not give. -/
theorem ideal_map_ringEquivOfEq {R S : DividedPowerRing.{r}} (h : R = S) :
    R.ideal.map (ringEquivOfEq h : (R : Type r) →+* (S : Type r)) = S.ideal := by
  cases h
  exact Ideal.map_id _

end DividedPowerRing

namespace Crystalline

namespace DividedPowerThickening

variable {s : AffineCrystallineSituation.{u, v}}

/-- **The ring isomorphism of an isomorphism of divided power thickenings commutes with the maps
from the base.**

`Crystalline.DividedPowerThickening.ringEquivOfIso` keeps only the underlying ring map of
`e.hom`, dropping both the divided power fields — recovered by
`...isDPMorphism_ringEquivOfIso` — and the field `fromBase_comp`, which says that `e.hom` is a
morphism *over* the fixed divided power ring `A`.  This recovers that last field.  Nothing is
computed: `e.hom.fromBase_comp` is the equation, and the only point is that the ring
equivalence and `e.hom.hom` have the same underlying function. -/
theorem fromBase_comp_ringEquivOfIso {X Y : DividedPowerThickening.{u, v, w} s} (e : X ≅ Y)
    (a : (s.A : Type u)) :
    ringEquivOfIso e (X.fromBase a) = Y.fromBase a :=
  congrArg (fun f : DividedPowers.DPMorphism s.A.dividedPowers Y.ring.dividedPowers ↦ f a)
    e.hom.fromBase_comp

end DividedPowerThickening

section CompletedEnvelope

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
  (g : MvPolynomial ι s.A →ₐ[s.A] s.C) (hg : Function.Surjective g)

/-- **The identification of the ring of the realisation `D` of a completed divided power envelope
with the envelope itself carries the structure map from the base to the canonical
`algebraMap`.**

`Crystalline.completedEnvelopeThickening` is produced by an essential-surjectivity argument and
its definition is sealed, so its structure map from `A` is not the canonical one on the nose; the
field `Crystalline.CompletedEnvelopeThickening.fromBase_eq` is the identification, as a `HEq`
across `ring_eq`, and this is it read through `DividedPowerRing.ringEquivOfEq`. -/
theorem completedEnvelopeThickeningRingEquiv_fromBase (a : (s.A : Type u)) :
    completedEnvelopeThickeningRingEquiv s g hg
        ((completedEnvelopeThickening s g hg).thickening.fromBase a) =
      algebraMap s.A (pAdicCompletedDividedPowerEnvelope s g hg) a :=
  DividedPowerRing.ringEquivOfEq_apply_of_heq _ _ _
    (completedEnvelopeThickening s g hg).fromBase_eq a

end CompletedEnvelope

/-- The quotient map `B ⟶ B/(p)^k` is a divided power morphism of the quotient divided powers. -/
private theorem isDPMorphism_mk_pAdic {B : Type*} [CommRing B] {J : Ideal B}
    (delta : DividedPowers J) (p k : ℕ) (hc : DividedPowers.pAdicIdeal (A := B) p ^ k ≤ J)
    (hs : delta.IsSubDPIdeal (DividedPowers.pAdicIdeal (A := B) p ^ k)) :
    DividedPowers.IsDPMorphism delta (DividedPowers.quotientDividedPowers J delta p k hc hs)
      (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := B) p ^ k)) :=
  DividedPowers.Quotient.isDPMorphism delta (by simpa [inf_eq_left.mpr hc] using hs)

/-- **A divided power morphism descends to the finite `p`-adic levels.**  For a divided power
morphism `f : (B, J, δ) ⟶ (C, L, ε)` of plain commutative rings and a level `k` at which both
sides carry quotient divided powers, the descent

`B/(p)^k ⟶ C/(p)^k`

is a divided power morphism of those quotient divided powers.

This is `Crystalline.isDPMorphism_quotientMapₐ` at `K = (p)^k`, with the base algebra removed:
the conclusion is a statement about ring homomorphisms, the two levels are not algebras over one
ring in any way the proof uses, and the hypothesis `K ≤ K'.comap f` is automatic, being
`Crystalline.pAdicIdeal_pow_le_comap_ringHom`.  The quotient map `B ⟶ B/(p)^k` is a surjective
divided power morphism carrying `J` onto the divided power ideal of the quotient, so
`DividedPowers.IsDPMorphism.of_comp` reduces the claim to the composite `B ⟶ C/(p)^k`. -/
theorem isDPMorphism_quotientMap_pAdic {B C : Type*} [CommRing B] [CommRing C]
    {J : Ideal B} {L : Ideal C} (delta : DividedPowers J) (epsilon : DividedPowers L)
    (p k : ℕ)
    (hcB : DividedPowers.pAdicIdeal (A := B) p ^ k ≤ J)
    (hsB : delta.IsSubDPIdeal (DividedPowers.pAdicIdeal (A := B) p ^ k))
    (hcC : DividedPowers.pAdicIdeal (A := C) p ^ k ≤ L)
    (hsC : epsilon.IsSubDPIdeal (DividedPowers.pAdicIdeal (A := C) p ^ k))
    (f : B →+* C) (hf : delta.IsDPMorphism epsilon f) :
    DividedPowers.IsDPMorphism
      (DividedPowers.quotientDividedPowers J delta p k hcB hsB)
      (DividedPowers.quotientDividedPowers L epsilon p k hcC hsC)
      (Ideal.quotientMap (DividedPowers.pAdicIdeal (A := C) p ^ k) f
        (pAdicIdeal_pow_le_comap_ringHom p k f)) := by
  have heq : (Ideal.quotientMap (DividedPowers.pAdicIdeal (A := C) p ^ k) f
        (pAdicIdeal_pow_le_comap_ringHom p k f)).comp
        (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := B) p ^ k)) =
      (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := C) p ^ k)).comp f := by
    ext x
    rfl
  exact DividedPowers.IsDPMorphism.of_comp delta
    (DividedPowers.quotientDividedPowers J delta p k hcB hsB)
    (DividedPowers.quotientDividedPowers L epsilon p k hcC hsC)
    (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := B) p ^ k))
    (Ideal.quotientMap (DividedPowers.pAdicIdeal (A := C) p ^ k) f
      (pAdicIdeal_pow_le_comap_ringHom p k f))
    rfl (isDPMorphism_mk_pAdic delta p k hcB hsB)
    (Eq.subst (motive := fun φ ↦ DividedPowers.IsDPMorphism delta
        (DividedPowers.quotientDividedPowers L epsilon p k hcC hsC) φ) heq.symm
      (DividedPowers.IsDPMorphism.comp
        (DividedPowers.quotientDividedPowers L epsilon p k hcC hsC)
        (isDPMorphism_mk_pAdic epsilon p k hcC hsC) hf))

/-- **A ring isomorphism which is a divided power morphism in both directions carries the divided
power ideal *onto* the divided power ideal.**

`DividedPowers.IsDPMorphism` asks only for the inclusion `J.map f ≤ L`, which is all a morphism
gives; the hypothesis `hJ` of `Crystalline.differentialFormsEquivOfAlgEquiv` is the equality, and
the reverse inclusion is the forward one for the inverse. -/
theorem ideal_map_of_isDPMorphism_symm {B C : Type*} [CommRing B] [CommRing C]
    {J : Ideal B} {L : Ideal C} (delta : DividedPowers J) (epsilon : DividedPowers L)
    (f : B ≃+* C) (hf : delta.IsDPMorphism epsilon (f : B →+* C))
    (hg : epsilon.IsDPMorphism delta (f.symm : C →+* B)) :
    J.map (f : B →+* C) = L := by
  refine le_antisymm hf.1 fun y hy ↦ ?_
  have hx : f.symm y ∈ J := hg.1 (Ideal.mem_map_of_mem _ hy)
  exact Eq.subst (motive := fun z ↦ z ∈ J.map (f : B →+* C)) (f.apply_symm_apply y)
    (Ideal.mem_map_of_mem _ hx)

end Crystalline

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}} (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [WholeSpacePresentation S hp]
  [IsAffine S.X] [IsAffine S.S.scheme]

/-- **`D(n)` as a divided power ring**, with its carrier the degree `n` of the cosimplicial ring
`...SmallSite.wholeSpaceEnvelopeRing`: the completed divided power ideal of
[Stacks, Tag 07KD] and the unique extension of the envelope's divided powers to it.

This is the realisation in which [Stacks, Tag 07L9] and [Stacks, Tag 07LA] are read, as against
`(wholeSpaceSystemEnvelope hp n).ring`, which is the one the system of [Stacks, Tag 07JN] is
built from; `...SmallSite.wholeSpaceSystemEnvelopeRingEquiv` identifies them. -/
noncomputable abbrev wholeSpaceEnvelopeDPRing (n : ℕ) : DividedPowerRing.{u} :=
  _root_.Crystalline.completedTensorPowerDividedPowerRing (affineSituation S hp)
    (wholeSpacePresentation S hp)
    (wholeSpacePresentation_surjective S hp) n

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- **The identification of the two realisations of `D(n)` is an isomorphism of divided power
rings.**

`...SmallSite.wholeSpaceSystemEnvelopeRingEquiv` is `DividedPowerRing.ringEquivOfEq` of the
equality `Crystalline.tensorPowerEnvelopeThickening_ring_eq`, which identifies whole divided
power ring structures; the ideal and the divided powers are therefore carried along, and only
the ring isomorphism was kept.  This is the divided power half. -/
theorem isDPMorphism_wholeSpaceSystemEnvelopeRingEquiv (n : ℕ) :
    DividedPowers.IsDPMorphism
      (wholeSpaceSystemEnvelope hp n).ring.dividedPowers
      (wholeSpaceEnvelopeDPRing hp n).dividedPowers
      (wholeSpaceSystemEnvelopeRingEquiv hp n :
        ((wholeSpaceSystemEnvelope hp n).ring : Type u) →+*
          ((wholeSpaceEnvelopeRing hp).obj (SimplexCategory.mk n) : Type u)) :=
  DividedPowerRing.isDPMorphism_ringEquivOfEq
    (_root_.Crystalline.tensorPowerEnvelopeThickening_ring_eq (affineSituation S hp)
      (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp) n)

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- **The divided power ideal of `D(n)` is carried onto the divided power ideal**, in the same
identification. -/
theorem ideal_map_wholeSpaceSystemEnvelopeRingEquiv (n : ℕ) :
    (wholeSpaceSystemEnvelope hp n).ring.ideal.map
        (wholeSpaceSystemEnvelopeRingEquiv hp n :
          ((wholeSpaceSystemEnvelope hp n).ring : Type u) →+*
            ((wholeSpaceEnvelopeRing hp).obj (SimplexCategory.mk n) : Type u)) =
      (wholeSpaceEnvelopeDPRing hp n).ideal :=
  DividedPowerRing.ideal_map_ringEquivOfEq
    (_root_.Crystalline.tensorPowerEnvelopeThickening_ring_eq (affineSituation S hp)
      (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp) n)

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- **The uniform cutoff `N` of `Crystalline.uniformLevel` makes `N + e` a `p`-adic level of
`D(n)` in the `...SmallSite.wholeSpaceEnvelopeRing` spelling.**  This is
`Crystalline.isPAdicLevel_uniformLevel_add` at the object `D(n)` of the completed site,
transported across the equality of the two realisations. -/
theorem isPAdicLevel_wholeSpaceEnvelopeDPRing (n e : ℕ) :
    _root_.Crystalline.IsPAdicLevel (wholeSpaceEnvelopeDPRing hp n).ideal
      (wholeSpaceEnvelopeDPRing hp n).dividedPowers (affineSituation S hp).p
      (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) :=
  Eq.subst (motive := fun R : DividedPowerRing.{u} ↦
      _root_.Crystalline.IsPAdicLevel R.ideal R.dividedPowers (affineSituation S hp).p
        (_root_.Crystalline.uniformLevel (affineSituation S hp) + e))
    (_root_.Crystalline.tensorPowerEnvelopeThickening_ring_eq (affineSituation S hp)
      (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp) n)
    (_root_.Crystalline.isPAdicLevel_uniformLevel_add (wholeSpaceSystemEnvelope hp n) e)

/-- **The section ring of the level `(n, e)` of the system of [Stacks, Tag 07JN] is
`D(n)/(p)^{N + e}` as a divided power ring**, in the spelling
`...SmallSite.wholeSpaceEnvelopeRing` uses: the divided powers
`Crystalline.GlobalCrystallineSituation.crysDividedPowers` on the sections correspond, under
`...SmallSite.wholeSpaceEnvelopeRingLevelEquiv`, to `DividedPowers.quotientDividedPowers` of
`...SmallSite.wholeSpaceEnvelopeDPRing`.

This is `...SmallSite.isDPMorphism_wholeSpaceSystemLevelRingEquiv` — the same statement for the
realisation the system is built from — composed with the descent to the levels of
`isDPMorphism_wholeSpaceSystemEnvelopeRingEquiv`, which is
`Crystalline.isDPMorphism_quotientMap_pAdic`.

It is the compatibility that lets `Crystalline.tensorFormsLevelEquiv` of
`ModuleDifferentials/QuotientForms.lean` be read at the level object `T(n)_e` over `D(n)` in the
realisation `[Stacks, Tag 07LA]` speaks about; before it, only the realisation of
[Stacks, Tag 07JN] was covered, and the two are not the same term.  **No tag attribute is
placed.** -/
theorem isDPMorphism_wholeSpaceEnvelopeRingLevelEquiv (n e : ℕ) :
    DividedPowers.IsDPMorphism
      (crysDividedPowers S (((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n))).obj e).obj)
      (DividedPowers.quotientDividedPowers (wholeSpaceEnvelopeDPRing hp n).ideal
        (wholeSpaceEnvelopeDPRing hp n).dividedPowers (affineSituation S hp).p
        (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)
        (isPAdicLevel_wholeSpaceEnvelopeDPRing hp n e).1
        (isPAdicLevel_wholeSpaceEnvelopeDPRing hp n e).2)
      (wholeSpaceEnvelopeRingLevelEquiv hp n e :
        ((structureSheaf S).obj.obj
            (op (((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n))).obj e)) : Type u) →+*
          (((wholeSpaceEnvelopeRing hp).obj (SimplexCategory.mk n) : Type u) ⧸
            DividedPowers.pAdicIdeal
                (A := ((wholeSpaceEnvelopeRing hp).obj (SimplexCategory.mk n) : Type u))
                (affineSituation S hp).p ^
              (_root_.Crystalline.uniformLevel (affineSituation S hp) + e))) :=
  DividedPowers.IsDPMorphism.comp _
    (_root_.Crystalline.isDPMorphism_quotientMap_pAdic
      (wholeSpaceSystemEnvelope hp n).ring.dividedPowers
      (wholeSpaceEnvelopeDPRing hp n).dividedPowers (affineSituation S hp).p
      (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)
      (_root_.Crystalline.isPAdicLevel_uniformLevel_add (wholeSpaceSystemEnvelope hp n) e).1
      (_root_.Crystalline.isPAdicLevel_uniformLevel_add (wholeSpaceSystemEnvelope hp n) e).2
      (isPAdicLevel_wholeSpaceEnvelopeDPRing hp n e).1
      (isPAdicLevel_wholeSpaceEnvelopeDPRing hp n e).2
      (wholeSpaceSystemEnvelopeRingEquiv hp n :
        ((wholeSpaceSystemEnvelope hp n).ring : Type u) →+*
          ((wholeSpaceEnvelopeRing hp).obj (SimplexCategory.mk n) : Type u))
      (isDPMorphism_wholeSpaceSystemEnvelopeRingEquiv hp n))
    (isDPMorphism_wholeSpaceSystemLevelRingEquiv hp n e)

/-- **The inverse identification is a divided power morphism too**, so the section ring of the
level `(n, e)` is `D(n)/(p)^{N + e}` as an **isomorphism** of divided power rings and not merely
a ring isomorphism of two rings that happen to carry divided powers.  With
`Crystalline.ideal_map_of_isDPMorphism_symm` this supplies the hypothesis `hJ` of
`Crystalline.differentialFormsEquivOfAlgEquiv`, which asks that the divided power ideal be
carried *onto* the divided power ideal and not merely into it. -/
theorem isDPMorphism_wholeSpaceEnvelopeRingLevelEquiv_symm (n e : ℕ) :
    DividedPowers.IsDPMorphism
      (DividedPowers.quotientDividedPowers (wholeSpaceEnvelopeDPRing hp n).ideal
        (wholeSpaceEnvelopeDPRing hp n).dividedPowers (affineSituation S hp).p
        (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)
        (isPAdicLevel_wholeSpaceEnvelopeDPRing hp n e).1
        (isPAdicLevel_wholeSpaceEnvelopeDPRing hp n e).2)
      (crysDividedPowers S (((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n))).obj e).obj)
      ((wholeSpaceEnvelopeRingLevelEquiv hp n e).symm :
          (((wholeSpaceEnvelopeRing hp).obj (SimplexCategory.mk n) : Type u) ⧸
            DividedPowers.pAdicIdeal
                (A := ((wholeSpaceEnvelopeRing hp).obj (SimplexCategory.mk n) : Type u))
                (affineSituation S hp).p ^
              (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)) →+*
        ((structureSheaf S).obj.obj
            (op (((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n))).obj e)) : Type u)) :=
  DividedPowers.IsDPMorphism.comp _
    (isDPMorphism_wholeSpaceSystemLevelRingEquiv_symm hp n e)
    (_root_.Crystalline.isDPMorphism_quotientMap_pAdic
      (wholeSpaceEnvelopeDPRing hp n).dividedPowers
      (wholeSpaceSystemEnvelope hp n).ring.dividedPowers (affineSituation S hp).p
      (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)
      (isPAdicLevel_wholeSpaceEnvelopeDPRing hp n e).1
      (isPAdicLevel_wholeSpaceEnvelopeDPRing hp n e).2
      (_root_.Crystalline.isPAdicLevel_uniformLevel_add (wholeSpaceSystemEnvelope hp n) e).1
      (_root_.Crystalline.isPAdicLevel_uniformLevel_add (wholeSpaceSystemEnvelope hp n) e).2
      ((wholeSpaceSystemEnvelopeRingEquiv hp n).symm :
        ((wholeSpaceEnvelopeRing hp).obj (SimplexCategory.mk n) : Type u) →+*
          ((wholeSpaceSystemEnvelope hp n).ring : Type u))
      (DividedPowerRing.isDPMorphism_ringEquivOfEq_symm
        (_root_.Crystalline.tensorPowerEnvelopeThickening_ring_eq (affineSituation S hp)
          (wholeSpacePresentation S hp)
          (wholeSpacePresentation_surjective S hp) n)))

/-! ### The base compatibility -/

omit [WholeSpacePresentation S hp] in
/-- **The identification of the section ring of a transported object with the ring of the affine
object carries the map from the base to the map from the base.**

The identification is `Crystalline.DividedPowerThickening.ringEquivOfIso` of the counit of the
affine-to-global equivalence, and `ringEquivOfIso` discards the field `fromBase_comp` of that
isomorphism.  The map from the base on the global side is the map on global sections of the
structure morphism `T ⟶ S`, because the `fromBase` of
`Crystalline.GlobalCrystallineSituation.wholeThickeningToAffine` is
`Crystalline.globalSectionsDPMorphism` of it. -/
theorem wholeSiteInverseSectionsRingEquiv_fromBase
    (Y : _root_.Crystalline.CrystallineThickening.{u, u, u} (affineSituation S hp))
    (a : ((affineSituation S hp).A : Type u)) :
    wholeSiteInverseSectionsRingEquiv hp Y
        (((wholeSiteEquivLittleAffine hp).inverse.obj
          Y).unop.obj.obj.toBase.hom.appTop.hom a) =
      Y.obj.fromBase a :=
  DividedPowerThickening.fromBase_comp_ringEquivOfIso
    ((affineIsCrystalline hp).ι.mapIso ((wholeSiteEquivLittleAffine hp).counitIso.app Y)) a

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- **`Crystalline.GlobalCrystallineSituation.crysBaseAppLE` is the map on global sections of the
structure morphism.**  It is defined as `Scheme.Hom.appLE ⊤ ⊤`, which is `appTop` but not
syntactically; this is the one rewrite, and it is the form
`Crystalline.GlobalCrystallineSituation.wholeThickeningToAffine` states its `fromBase` in. -/
theorem crysBaseAppLE_eq_appTop (A : Thickening S) (a : Γ(S.S.scheme, ⊤)) :
    crysBaseAppLE S A a = A.toBase.hom.appTop.hom a := by
  rw [crysBaseAppLE, baseAppLE, appLE_top_top]

omit [WholeSpacePresentation S hp] [IsAffine S.X] [IsAffine S.S.scheme] in
/-- **The map from the base of a finite level is the reduction of the map from the base.**  Holds
by `rfl`: the structure map of `Crystalline.levelThickening` is the quotient map composed with
the structure map of the completed thickening. -/
theorem levelThickening_fromBase
    (X : _root_.Crystalline.CompletedCrystallineThickening.{u, u, u} (affineSituation S hp))
    (k : ℕ) (h : _root_.Crystalline.IsPAdicLevel X.ring.ideal X.ring.dividedPowers
      (affineSituation S hp).p k) (a : ((affineSituation S hp).A : Type u)) :
    (_root_.Crystalline.levelThickening X k h).obj.fromBase a =
      Ideal.Quotient.mk _ (X.fromBase a) :=
  rfl

/-- **The structure map `Γ(S, ⊤) ⟶ D(n)` of the degree `n` of
`...SmallSite.wholeSpaceEnvelopeRing`**, named once.

The `Algebra (affineSituation S hp).A` instance that
`Crystalline.pAdicCompletedDividedPowerEnvelope` carries is declared at the bare carrier; at the
`CommRingCat` spelling `(wholeSpaceEnvelopeRing hp).obj ⦋n⦌` — the same type, a different
`DiscrTree` key — instance search does not find it, and `algebraMap` cannot be written down.
Naming the renaming once removes the problem. -/
noncomputable def wholeSpaceEnvelopeFromBase (n : ℕ) :
    ((affineSituation S hp).A : Type u) →+*
      ((wholeSpaceEnvelopeRing hp).obj (SimplexCategory.mk n) : Type u) :=
  algebraMap (affineSituation S hp).A
    (_root_.Crystalline.pAdicCompletedTensorPowerEnvelope (affineSituation S hp)
      (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp) n)

/-- **The identification of the section ring of the level `(n, e)` with `D(n)/(p)^{N + e}` is one
of `Γ(S, ⊤)`-algebras.**

`...SmallSite.wholeSpaceEnvelopeRingLevelEquiv` carries
`Crystalline.GlobalCrystallineSituation.crysBaseAppLE` of the level object — the map on global
sections of `T(n)_e ⟶ S`, which is `...affineBaseAppLE` at `V = ⊤`, by
`crysBaseAppLE_eq_appTop` — to the reduction modulo `(p)^{N + e}` of the structure map
`Γ(S, ⊤) ⟶ D(n)`.

Three forgotten fields in a row and nothing else: `wholeSiteInverseSectionsRingEquiv_fromBase`
for the transport across the affine-to-global equivalence, `levelThickening_fromBase` for the
passage to the finite level, and
`Crystalline.completedEnvelopeThickeningRingEquiv_fromBase` for the identification of the two
realisations of `D(n)`.

This is the hypothesis `Crystalline.differentialFormsEquivOfAlgEquiv` needs of the level
identification before the sections of `Ω^i_{X/S}` over `T(n)_e` can be carried along it, and it
is the second of the crossings the isomorphism `ε` of [Stacks, Tag 07LF] has to make.  **No tag
attribute is placed and [Stacks, Tag 07LF] is not proved.** -/
theorem wholeSpaceEnvelopeRingLevelEquiv_crysBaseAppLE (n e : ℕ)
    (a : ((affineSituation S hp).A : Type u)) :
    wholeSpaceEnvelopeRingLevelEquiv hp n e
        (crysBaseAppLE S (((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n))).obj e).obj
          a) =
      Ideal.Quotient.mk _ (wholeSpaceEnvelopeFromBase hp n a) := by
  have h1 : wholeSpaceSystemLevelRingEquiv hp n e
      (crysBaseAppLE S (((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n))).obj e).obj a) =
      Ideal.Quotient.mk _ ((wholeSpaceSystemEnvelope hp n).fromBase a) :=
    Eq.trans
      (congrArg (fun x ↦ wholeSpaceSystemLevelRingEquiv hp n e x)
        (crysBaseAppLE_eq_appTop
          (((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n))).obj e).obj a))
      (wholeSiteInverseSectionsRingEquiv_fromBase hp (wholeSpaceSystemLevel hp n e) a)
  refine Eq.trans (wholeSpaceEnvelopeRingLevelEquiv_apply hp n e _) ?_
  refine Eq.trans (congrArg (fun x ↦ Ideal.quotientEquiv _ _
    (wholeSpaceSystemEnvelopeRingEquiv hp n)
    (wholeSpaceSystemEnvelope_pAdicIdeal_pow_map hp n _) x) h1) ?_
  exact congrArg (Ideal.Quotient.mk _)
    (_root_.Crystalline.completedEnvelopeThickeningRingEquiv_fromBase (affineSituation S hp)
      (_root_.Crystalline.tensorPowerPresentation (affineSituation S hp)
        (wholeSpacePresentation S hp) n)
      (_root_.Crystalline.tensorPowerPresentation_surjective (affineSituation S hp)
        (wholeSpacePresentation S hp)
        (wholeSpacePresentation_surjective S hp) n) a)

end Crystalline.GlobalCrystallineSituation.SmallSite

end
