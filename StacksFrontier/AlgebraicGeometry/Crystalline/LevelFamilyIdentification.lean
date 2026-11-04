module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineCosimplicialSystem
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineGlobalNonempty

/-!
# The two families of finite levels agree

Chapter 60 carries **two** families of finite levels of the divided power envelope of a
presentation `f : P → C` of an affine crystalline situation, built in opposite orders.

* `Crystalline.levelCrystallineThickening` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/AffineSite/Completed.lean` is the **envelope of the
  reduced presentation**: first reduce `P` modulo `(p)^e`, then take the divided power envelope
  `Crystalline.levelEnvelope` of the image of `ker f`.  This is the family
  [Stacks, Tag 07HP] produces its morphisms out of.
* `Crystalline.levelThickening` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineCosimplicialSystem.lean` is the
  **reduction of the completed envelope**: form the `p`-adically completed envelope `D̂` of
  [Stacks, Tag 07J8], then quotient by `(p)^k`.  This is the family the cosimplicial system
  `...SmallSite.wholeSpaceSystem` of [Stacks, Tag 07JN] is built from, hence the family the
  hypothesis `hdet` of
  `...SmallSite.LevelComparison07JG.faithful_functor_of_isLevel` is stated over.

Envelope-of-the-reduction against reduction-of-the-envelope.  Nothing in the tree related them:
`levelCrystallineThickening` occurred in two files and in neither of them did `levelThickening`,
`...SmallSite.wholeSpaceSystem` or `Crystalline.tensorPowerEnvelopeThickening` occur.  **This
module identifies them**, as divided power rings and then as objects of the site, and transports
[Stacks, Tag 07HP] onto the second family.

The ring-level ingredients were already in the tree and entirely unused: the two halves of
[Stacks, Tag 07KG] part (2), `Crystalline.eventually_quotient_envelope_equiv` (`D/(p)^e` is the
envelope of the reduced presentation) and `Crystalline.eventually_completed_quotient_equiv`
(completion does not change the finite quotients).  Each is a `Σ'`-packaged *ring* equivalence
with its divided power compatibilities and its own `Classical.choose` cutoff, and neither was an
isomorphism of divided power rings, let alone of objects of the site.  What this module adds is
the composition, its promotion to an isomorphism in `DividedPowerRing`, the compatibility of
that isomorphism with the two structural maps, and the resulting morphism out of a level of the
second family.

## Main definitions

Everything is in the namespace `Crystalline`.

* `DividedPowerRing.isoOfRingEquiv` — a ring equivalence that is a divided power morphism in
  both directions is an isomorphism of divided power rings.
* `completedPresentationEnvelope` — the completed envelope `D̂` of a presentation as a divided
  power ring, named so that its finite levels can be spoken about without a `let`.
* `completedLevelEnvelopeIso` — **the reduction `D̂/(p)^e` of the completed envelope is the
  envelope `Crystalline.levelEnvelope` of the reduced presentation**, as divided power rings and
  compatibly with the maps out of `P`.  This is the composite of the two halves of
  [Stacks, Tag 07KG] part (2), at a level past both of their cutoffs.
* `levelFamilyIso` — **the two families are isomorphic as objects of `CRIS(C/A)`**: the level
  `Crystalline.levelThickeningObj` of the completed envelope is isomorphic to the level
  `Crystalline.levelCrystallineThickening` of the reduced presentation, for every level past both
  cutoffs.  The ring isomorphism is the previous item; what is added is that it respects the two
  structural maps of [Stacks, Tag 07HM].  Both objects are crystalline, so the same isomorphism
  identifies them in `Crystalline.CrystallineThickening`.
* `completedLevelFamilyIso` — the same with no hypothesis beyond surjectivity of the
  presentation, at the object of `Cris^∧(C/A)` that part (5) of [Stacks, Tag 07KG] produces.

## Main results

* `levelCrystallineThickening_cutoff` — the cutoff of the first family is
  `Classical.choose s.prime_nilpotent`, the nilpotency exponent of `p` in `C`.
* `uniformLevel_eq_two_mul_levelCrystallineThickening_cutoff` — **the two cutoffs are related on
  the nose**: `Crystalline.uniformLevel` is twice the cutoff of
  `Crystalline.levelCrystallineThickening`.  Both hold by `rfl`; they were unavailable because
  the two are reached by different routes and nothing named the common `Classical.choose`.
* `freePolynomialPresentation_eq_canonicalPresentation` — the presentation
  `Crystalline.freePolynomialPresentation` that [Stacks, Tag 07HP] is applied to in
  `...SmallSite.AffineGlobalNonempty` is the presentation
  `Crystalline.canonicalPresentation` that `...SmallSite.wholeSpaceSystem` is built from.  Again
  `rfl`: the two differ only in the universe constraints of their statements, `id` against
  `fun c => c`, and nothing recorded that.
* `presentationEnvelope_eq_polynomialDividedPowerEnvelope` and
  `completedEnvelopeDPRing_eq` — the envelope of `AffineSite/Completed.lean` is the envelope of
  `Crystal.lean`, and the completed envelope divided power ring of `AffineSite/Coproduct.lean`
  is the ring whose finite quotients `AffineSite/Completed.lean` compares.  Both `rfl`, and both
  needed before a statement about one family can be read against the other.
* `exists_levelThickening_hom` — **[Stacks, Tag 07HP] for the second family: every divided power
  thickening of `C/A` receives a morphism from a finite level `D̂/(p)^e` of the completed
  envelope.**  The level is the one [Stacks, Tag 07HP] needs *and* past the two cutoffs of
  [Stacks, Tag 07KG] part (2), which is possible because
  `Crystalline.exists_forall_le_levelEnvelope_hom` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/AffineSite/Completed.lean` gives the morphism out of
  the first family at every sufficiently large level, not only at one.

## What is and is not proved

**[Stacks, Tag 07JH] is `...SmallSite.crystalPairFunctor_isEquivalence`; no `@[stacks 07JH]`
attribute is placed in this module.**
Its full and essentially-surjective halves are untouched and `Functor.IsEquivalence` is not
mentioned.  `hdet`, on the other hand, is **proved downstream from this module**, in
`StacksFrontier/AlgebraicGeometry/Crystalline/LevelFamilyFinality.lean`, and the route there runs
through this module's `Crystalline.levelFamilyIso`.

`hdet` is **not discharged here** but is discharged there.  Two things lie between
`exists_levelThickening_hom` and
`hdet`, and both are available.

* **The crystal property.**  A morphism `B ⟶ T_e` for every `B` becomes "a morphism of crystals
  is determined by its restrictions to the levels" only through the comparison
  `ℱ(T_e) ⊗_{𝒪(T_e)} 𝒪(B) ≅ ℱ(B)`, naturally in `ℱ`.  That is not in this module; it is
  available as
  `...SmallSite.moduleRestrictionSheafMap_eq_of_hom` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/LevelCrystalDeterminacy.lean`, which cancels the
  comparison isomorphism on the two sides of the naturality square and so does not need a
  sections description of the base change at all.
* **The global site.**  `hdet` is about `Cris(X/S)` and crystals in quasi-coherent
  `𝒪_{X/S}`-modules, while the statement below is about the affine category `CRIS(C/A)`.  The
  transport is `Crystalline.GlobalCrystallineSituation.wholeSiteEquivLittleAffine`, and the
  levels of `...SmallSite.wholeSpaceSystem` are already known to be the transport of the levels
  `Crystalline.levelThickening` — `...SmallSite.wholeSpaceSystem_obj_eq_level` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/WholeSpaceSystemLevelRings.lean`, which
  holds by `rfl` — so what is needed there is the passage of the morphism across the
  equivalence, in degree zero, and not an identification of objects.  That passage is the unit of
  the equivalence, in `...SmallSite.exists_hom_to_wholeSpaceSystem_level` of
  `LevelFamilyFinality.lean`.

Weak finality of a *fixed* level is false — the module note of
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalsQuasiCoherentToPairs.lean` records that "an
object of `Cris(X/S)` on which `p^m` does not vanish admits no morphism to `T_e` with
`N + e < m`" — and nothing below asserts it: the level varies with the thickening, exactly as in
[Stacks, Tag 07HP], so the statement is an existence statement.  Weak finality of the
*completed* envelope `D̂` is true and is a different statement, in a different category:
`Crystalline.exists_hom_from_completedPolynomialEnvelope`, [Stacks, Tag 07KI].

## References

* [Stacks Project, Tag 07HP](https://stacks.math.columbia.edu/tag/07HP)
* [Stacks Project, Tag 07J8](https://stacks.math.columbia.edu/tag/07J8)
* [Stacks Project, Tag 07KG](https://stacks.math.columbia.edu/tag/07KG)
* [Stacks Project, Tag 07KH](https://stacks.math.columbia.edu/tag/07KH)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public section

open CategoryTheory

universe u v w

noncomputable section

namespace DividedPowerRing

/-- **A ring equivalence that is a divided power morphism in both directions is an isomorphism
of divided power rings.**  The two halves of [Stacks, Tag 07KG] part (2) are packaged as ring
equivalences together with exactly these two compatibilities, so this is what promotes them to
isomorphisms in `DividedPowerRing`. -/
def isoOfRingEquiv {R R' : DividedPowerRing.{w}} (φ : (R : Type w) ≃+* (R' : Type w))
    (h : R.dividedPowers.IsDPMorphism R'.dividedPowers φ.toRingHom)
    (h' : R'.dividedPowers.IsDPMorphism R.dividedPowers φ.symm.toRingHom) :
    R ≅ R' where
  hom := DividedPowers.DPMorphism.mk' h
  inv := DividedPowers.DPMorphism.mk' h'
  hom_inv_id := by ext x; exact φ.symm_apply_apply x
  inv_hom_id := by ext x; exact φ.apply_symm_apply x

/-- The forward morphism of `isoOfRingEquiv φ h h'` has underlying ring map `φ`. -/
@[simp]
theorem isoOfRingEquiv_hom_toRingHom {R R' : DividedPowerRing.{w}}
    (φ : (R : Type w) ≃+* (R' : Type w))
    (h : R.dividedPowers.IsDPMorphism R'.dividedPowers φ.toRingHom)
    (h' : R'.dividedPowers.IsDPMorphism R.dividedPowers φ.symm.toRingHom) :
    (isoOfRingEquiv φ h h').hom.toRingHom = φ.toRingHom := rfl

end DividedPowerRing

namespace Crystalline

/-! ### The two cutoffs -/

section Cutoffs

variable (s : AffineCrystallineSituation.{u, v})
variable {P : Type u} [CommRing P] [Algebra s.A P]
variable (f : P →ₐ[s.A] s.C)

/-- **The cutoff of the first family of levels is the nilpotency exponent of `p` in `C`.**  It is
reached inside the construction of `Crystalline.levelCrystallineThickening` as a
`Classical.choose` and was never named, so no statement about the family could be compared with
one about `Crystalline.uniformLevel`, which chooses out of the same existence statement. -/
theorem levelCrystallineThickening_cutoff (hf : Function.Surjective f) :
    (levelCrystallineThickening s f hf).1 = Classical.choose s.prime_nilpotent := rfl

/-- **The two cutoffs are related on the nose**: the uniform cutoff of
`Crystalline.uniformLevel`, which serves every object of `Cris^∧(C/A)` at once, is twice the
cutoff of `Crystalline.levelCrystallineThickening`.  Both are `2`- and `1`-fold multiples of the
same `Classical.choose s.prime_nilpotent`, but the two reach it by different routes, so not even
this `rfl` was available by name. -/
theorem uniformLevel_eq_two_mul_levelCrystallineThickening_cutoff
    (hf : Function.Surjective f) :
    uniformLevel s = 2 * (levelCrystallineThickening s f hf).1 := rfl

/-- The cutoff of the first family is below every level of the second: `N ≤ 2 * N + e`. -/
theorem levelCrystallineThickening_cutoff_le_uniformLevel_add
    (hf : Function.Surjective f) (e : ℕ) :
    (levelCrystallineThickening s f hf).1 ≤ uniformLevel s + e :=
  le_trans (le_trans (Nat.le_mul_of_pos_left _ Nat.zero_lt_two)
    (le_of_eq (uniformLevel_eq_two_mul_levelCrystallineThickening_cutoff s f hf).symm))
    (Nat.le_add_right _ _)

end Cutoffs

/-! ### The two presentations and the two spellings of the envelope -/

section Presentations

/-- **The presentation [Stacks, Tag 07HP] is applied to is the presentation the cosimplicial
system is built from.**  `Crystalline.freePolynomialPresentation` is stated only for a situation
with both universe parameters equal, because that is where
`Crystalline.exists_crystalline_hom` needs it, and
`Crystalline.canonicalPresentation` for a general situation; the formulas are `MvPolynomial.aeval
id` and `MvPolynomial.aeval fun c => c`, which are the same map. -/
theorem freePolynomialPresentation_eq_canonicalPresentation
    (s : AffineCrystallineSituation.{u, u}) :
    freePolynomialPresentation s = canonicalPresentation s := rfl

variable (s : AffineCrystallineSituation.{u, v})

/-- **The envelope of `AffineSite/Completed.lean` is the envelope of `Crystal.lean`**, for a
polynomial presentation.  `Crystalline.presentationEnvelope` is stated for an arbitrary
`s.A`-algebra `P` and `Crystalline.polynomialDividedPowerEnvelope` for a polynomial algebra;
on a polynomial algebra both are `Crystalline.dividedPowerEnvelope` of the same kernel. -/
theorem presentationEnvelope_eq_polynomialDividedPowerEnvelope {ι : Type u}
    (g : MvPolynomial ι s.A →ₐ[s.A] s.C) :
    presentationEnvelope s g = polynomialDividedPowerEnvelope s g := rfl


end Presentations

/-! ### The completed envelope of a presentation, as a divided power ring -/

section CompletedRing

variable (s : AffineCrystallineSituation.{u, v})
variable {P : Type u} [CommRing P] [Algebra s.A P]
variable (f : P →ₐ[s.A] s.C)

/-- **The `p`-adically completed divided power envelope of a presentation, as a divided power
ring.**  This is the ring of `Crystalline.completedCrystallineThickening`, hence of
`Crystalline.completedEnvelopeThickening` and of every `D(n)` of
`Crystalline.tensorPowerEnvelopeThickening`; see `Crystalline.completedEnvelopeDPRing_eq`.  It is
named here so that the finite levels `Crystalline.dpQuotientLevelRing` of it can be spoken about
without a `let`. -/
abbrev completedPresentationEnvelope
    (hp : IsNilpotent (Ideal.Quotient.mk (presentationEnvelope s f).object.ideal
      (s.p : (presentationEnvelope s f).object))) : DividedPowerRing.{u} :=
  DividedPowerRing.of
    (AdicCompletion (DividedPowers.pAdicIdeal
      (A := (presentationEnvelope s f).object) s.p) (presentationEnvelope s f).object)
    (DividedPowers.completionIdeal (presentationEnvelope s f).object.ideal s.p hp)
    (DividedPowers.completedDividedPowers (presentationEnvelope s f).object.ideal
      (presentationEnvelope s f).object.dividedPowers s.p hp).1

/-- **The completed envelope divided power ring of `AffineSite/Coproduct.lean` is the ring whose
finite quotients `AffineSite/Completed.lean` compares.**  `Crystalline.completedEnvelopeDPRing` is
the ring of `Crystalline.tensorPowerEnvelopeThickening`, hence of every level of
`...SmallSite.wholeSpaceSystem`; the right-hand side is the ring
`Crystalline.eventually_completed_quotient_equiv` takes the finite quotients of. -/
theorem completedEnvelopeDPRing_eq {ι : Type u} (g : MvPolynomial ι s.A →ₐ[s.A] s.C)
    (hg : Function.Surjective g)
    (hp : IsNilpotent (Ideal.Quotient.mk (presentationEnvelope s g).object.ideal
      (s.p : (presentationEnvelope s g).object))) :
    completedEnvelopeDPRing s g hg hp = completedPresentationEnvelope s g hp := rfl

end CompletedRing

/-! ### The identification of the two families -/

section Identification

variable (s : AffineCrystallineSituation.{u, v})
variable {P : Type u} [CommRing P] [Algebra s.A P]
variable (f : P →ₐ[s.A] s.C)

/-- **The reduction of the completed envelope is the envelope of the reduced presentation**, as
divided power rings, compatibly with the maps out of the presentation algebra `P`.

This is the composite of the two halves of [Stacks, Tag 07KG] part (2) already in the tree,
`Crystalline.eventually_completed_quotient_equiv` and
`Crystalline.eventually_quotient_envelope_equiv`:

`D̂/(p)^e ≅ D/(p)^e ≅ (levelEnvelope s f e).object`.

Each half is a ring equivalence carrying its divided power compatibilities in both directions and
its own `Classical.choose` cutoff; the cutoff here is the maximum of the two, and the divided
power compatibilities compose, so the composite is an isomorphism in `DividedPowerRing` and not
merely of rings.  The left-hand side is the ring of the level `Crystalline.levelThickening` of the
completed envelope, by `Crystalline.levelThickening_ring`; the right-hand side is the ring of the
level `Crystalline.levelCrystallineThickening`.  So this identifies the two families of finite
levels at the level of their rings, and `Crystalline.levelFamilyIso` promotes it to an isomorphism
of objects of the site. -/
@[stacks 07KG "part (2), the reduction of the completed envelope is the finite-level envelope"]
def completedLevelEnvelopeIso (hf : Function.Surjective f) :
    Σ' hp : IsNilpotent (Ideal.Quotient.mk (presentationEnvelope s f).object.ideal
      (s.p : (presentationEnvelope s f).object)),
      Σ' N : ℕ, ∀ e, N ≤ e →
        Σ' h : IsPAdicLevel (completedPresentationEnvelope s f hp).ideal
            (completedPresentationEnvelope s f hp).dividedPowers s.p e,
          {ψ : dpQuotientLevelRing s.p (completedPresentationEnvelope s f hp) e h ≅
                (levelEnvelope s f e).object //
            ∀ x : P,
              (levelProj s.p (completedPresentationEnvelope s f hp) e h ≫ ψ.hom).toRingHom
                  (algebraMap (presentationEnvelope s f).object
                    (completedPresentationEnvelope s f hp)
                    ((presentationEnvelope s f).algebraMap.toRingHom x)) =
                (levelEnvelope s f e).algebraMap.toRingHom
                  (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := P) s.p ^ e) x)} := by
  classical
  obtain ⟨hp, N₂, h₂⟩ := eventually_completed_quotient_equiv s f hf
  obtain ⟨N₁, h₁⟩ := eventually_quotient_envelope_equiv s f hf
  refine ⟨hp, max N₁ N₂, ?_⟩
  intro e he
  obtain ⟨hc, hst, φ₁, hφ₁pres, hφ₁dp, hφ₁dpsymm⟩ := h₁ e ((le_max_left _ _).trans he)
  obtain ⟨hD, hDst, hhat, hhatst, φ₂, hφ₂pres, hφ₂dp, hφ₂dpsymm⟩ :=
    h₂ e ((le_max_right _ _).trans he)
  refine ⟨⟨hhat, hhatst⟩, DividedPowerRing.isoOfRingEquiv (φ₂.trans φ₁)
    (DividedPowers.IsDPMorphism.comp _ hφ₁dp hφ₂dp)
    (DividedPowers.IsDPMorphism.comp _ hφ₂dpsymm hφ₁dpsymm), fun x => ?_⟩
  exact (congrArg φ₁ (hφ₂pres ((presentationEnvelope s f).algebraMap.toRingHom x))).trans
    (hφ₁pres x)

end Identification

/-! ### The two families are isomorphic as objects of the site -/

section ThickeningIso

variable {s : AffineCrystallineSituation.{u, u}}
variable {P : Type u} [CommRing P] [Algebra s.A P]
variable (f : P →ₐ[s.A] s.C)

/-- **The two families of finite levels are isomorphic as objects of `CRIS(C/A)`.**  For every
level `e` past the cutoffs of both constructions, the finite level `D̂/(p)^e` of the completed
envelope, `Crystalline.levelThickeningObj`, is isomorphic to the level
`Crystalline.levelCrystallineThickening` of the envelope of the reduced presentation.  Both are
crystalline — `Crystalline.levelThickening` and part (3) of [Stacks, Tag 07KG] — so the same
isomorphism identifies them in `Crystalline.CrystallineThickening`.

The underlying isomorphism of divided power rings is `Crystalline.completedLevelEnvelopeIso`, the
composite of the two halves of [Stacks, Tag 07KG] part (2); what is added here is that it respects
the two structural maps of [Stacks, Tag 07HM], so that
`Crystalline.DividedPowerThickening.isoOfRingIso` applies.  For the map from the base this is the
compatibility `Crystalline.DividedPowerEnvelope.algebraMap_comp` of each envelope's map out of the
presentation with its map out of the base; for the structural map from `C` it is surjectivity of
`f` together with the two descriptions of the quotient.

The three hypotheses on `X` are **not stand-ins and not weakenings**: they are exactly the fields
`Crystalline.completedCrystallineThickening` produces, and they are what pins `X` down to the
completed envelope of this presentation.  None can be dropped: for an arbitrary object of
`Cris^∧(C/A)` the conclusion is false, the levels of `X` being quotients of `X.ring`. -/
def levelFamilyIso (hf : Function.Surjective f)
    (X : CompletedCrystallineThickening.{u, u, u} s)
    (hp : IsNilpotent (Ideal.Quotient.mk (presentationEnvelope s f).object.ideal
      (s.p : (presentationEnvelope s f).object)))
    (hXring : X.ring = completedPresentationEnvelope s f hp)
    (hXfrom : HEq X.fromBase.toRingHom
      ((algebraMap (presentationEnvelope s f).object
        (completedPresentationEnvelope s f hp)).comp
          (presentationEnvelope s f).structureMap.toRingHom))
    (hXquot : ∀ x : P, HEq (X.toQuotient (f x))
      (Ideal.Quotient.mk (completedPresentationEnvelope s f hp).ideal
        (algebraMap (presentationEnvelope s f).object (completedPresentationEnvelope s f hp)
          ((presentationEnvelope s f).algebraMap.toRingHom x)))) :
    Σ' N : ℕ, ∀ e, N ≤ e →
      Σ' h : IsPAdicLevel X.ring.ideal X.ring.dividedPowers s.p e,
        Σ' he : (levelCrystallineThickening s f hf).1 ≤ e,
          (levelThickeningObj X e h ≅ ((levelCrystallineThickening s f hf).2 e he).1) := by
  classical
  obtain ⟨Xring, XfromBase, XisComplete, XtoQuotient, Xcommutes, Xbij⟩ := X
  dsimp only at hXring hXfrom hXquot ⊢
  subst hXring
  have hXfrom' := eq_of_heq hXfrom
  have hXquot' : ∀ x : P, XtoQuotient (f x) =
      Ideal.Quotient.mk (completedPresentationEnvelope s f hp).ideal
        (algebraMap (presentationEnvelope s f).object (completedPresentationEnvelope s f hp)
          ((presentationEnvelope s f).algebraMap.toRingHom x)) :=
    fun x => eq_of_heq (hXquot x)
  obtain ⟨hp', N₀, hiso⟩ := completedLevelEnvelopeIso s f hf
  refine ⟨max N₀ (levelCrystallineThickening s f hf).1, ?_⟩
  intro e he
  obtain ⟨h, ψ, hψpres⟩ := hiso e ((le_max_left _ _).trans he)
  have heN : (levelCrystallineThickening s f hf).1 ≤ e := (le_max_right _ _).trans he
  refine ⟨h, heN, ?_⟩
  set Y := (levelCrystallineThickening s f hf).2 e heN with hYdef
  clear_value Y
  clear hYdef
  obtain ⟨⟨Yring, YfromBase, YprimeNilpotent, YtoQuotient, Ycommutes⟩,
    hYcrys, hYring, hYfrom, hYquot⟩ := Y
  dsimp only at hYring hYfrom hYquot ⊢
  cases hYring
  have hYfrom' : YfromBase.toRingHom = (levelEnvelope s f e).structureMap.toRingHom :=
    eq_of_heq hYfrom
  refine DividedPowerThickening.isoOfRingIso ψ ?_ ?_
  · apply DividedPowers.DPMorphism.ext
    funext a
    have hbase := RingHom.congr_fun (presentationEnvelope s f).algebraMap_comp a
    have hlevel := RingHom.congr_fun (levelEnvelope s f e).algebraMap_comp a
    calc (levelProj s.p (completedPresentationEnvelope s f hp') e h ≫ ψ.hom).toRingHom
            (XfromBase.toRingHom a)
        = (levelProj s.p (completedPresentationEnvelope s f hp') e h ≫ ψ.hom).toRingHom
            (algebraMap (presentationEnvelope s f).object
              (completedPresentationEnvelope s f hp')
              ((presentationEnvelope s f).algebraMap.toRingHom (algebraMap s.A P a))) := by
          rw [hXfrom']
          exact congrArg (fun z => (levelProj s.p (completedPresentationEnvelope s f hp') e h ≫
            ψ.hom).toRingHom (algebraMap (presentationEnvelope s f).object
              (completedPresentationEnvelope s f hp') z)) hbase.symm
      _ = (levelEnvelope s f e).algebraMap.toRingHom
            (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := P) s.p ^ e)
              (algebraMap s.A P a)) := hψpres (algebraMap s.A P a)
      _ = YfromBase.toRingHom a := by rw [hYfrom']; exact hlevel
  · refine RingHom.ext fun c => ?_
    obtain ⟨x, rfl⟩ := hf c
    calc DividedPowerRing.quotientRingHom ψ.hom
            (levelQuotientMap s.p (completedPresentationEnvelope s f hp') e h
              (XtoQuotient (f x)))
        = DividedPowerRing.quotientRingHom ψ.hom
            (Ideal.Quotient.mk
              (dpQuotientLevelRing s.p (completedPresentationEnvelope s f hp') e h).ideal
              ((levelProj s.p (completedPresentationEnvelope s f hp') e h).toRingHom
                (algebraMap (presentationEnvelope s f).object
                  (completedPresentationEnvelope s f hp')
                  ((presentationEnvelope s f).algebraMap.toRingHom x)))) := by
          rw [hXquot', levelQuotientMap_mk]
          rfl
      _ = Ideal.Quotient.mk (levelEnvelope s f e).object.ideal
            ((levelEnvelope s f e).algebraMap.toRingHom
              (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := P) s.p ^ e) x)) := by
          rw [DividedPowerRing.quotientRingHom_mk]
          exact congrArg (Ideal.Quotient.mk (levelEnvelope s f e).object.ideal) (hψpres x)
      _ = YtoQuotient (f x) := (eq_of_heq (hYquot x)).symm

/-- **The two families of finite levels of a presentation are isomorphic**, with no hypothesis
beyond surjectivity of the presentation: `Crystalline.levelFamilyIso` at the object
`Crystalline.completedCrystallineThickening` of `Cris^∧(C/A)` that part (5) of
[Stacks, Tag 07KG] produces, whose three defining fields are exactly the three hypotheses that
construction takes, supplied here by projection. -/
def completedLevelFamilyIso (hf : Function.Surjective f) :
    Σ' N : ℕ, ∀ e, N ≤ e →
      Σ' h : IsPAdicLevel ((completedCrystallineThickening s f hf).2.1).ring.ideal
          ((completedCrystallineThickening s f hf).2.1).ring.dividedPowers s.p e,
        Σ' he : (levelCrystallineThickening s f hf).1 ≤ e,
          (levelThickeningObj (completedCrystallineThickening s f hf).2.1 e h ≅
            ((levelCrystallineThickening s f hf).2 e he).1) :=
  levelFamilyIso f hf (completedCrystallineThickening s f hf).2.1
    (completedCrystallineThickening s f hf).1
    (completedCrystallineThickening s f hf).2.2.1
    (completedCrystallineThickening s f hf).2.2.2.1
    (completedCrystallineThickening s f hf).2.2.2.2

/-- **[Stacks, Tag 07HP] for the second family of levels: every divided power thickening of `C/A`
receives a morphism from a finite level `D̂/(p)^e` of the completed envelope.**

This is the statement the hypothesis `hdet` of
`...SmallSite.LevelComparison07JG.faithful_functor_of_isLevel` wants, on the family `hdet` is
stated over: the levels of `...SmallSite.wholeSpaceSystem` are the levels
`Crystalline.levelThickening` of `Crystalline.tensorPowerEnvelopeThickening`, whose ring is
`Crystalline.completedPresentationEnvelope` by `Crystalline.completedEnvelopeDPRing_eq`, and not
the levels `Crystalline.levelCrystallineThickening` that [Stacks, Tag 07HP] produces morphisms out
of.

Two things are composed.  `Crystalline.exists_forall_le_levelEnvelope_hom` gives the morphism out
of the first family at *every* sufficiently large level, so a level can be chosen past the cutoffs
of the two halves of [Stacks, Tag 07KG] part (2) as well; there
`Crystalline.completedLevelFamilyIso` identifies the two families.  The two proofs that the chosen
level is past the cutoff of the first family are proofs of the same proposition, so the two levels
of the first family they name are the same object.

This is stated at the single object `Crystalline.completedCrystallineThickening s f hf`, the
completed envelope of the presentation `f` itself, and at a single level.  Neither restriction can
be lifted here, and both have to be for the levels of `...SmallSite.wholeSpaceSystem`, which are
the levels of `Crystalline.tensorPowerEnvelopeThickening` in degree zero and so belong to a
*different* presentation.  The generalisation on both counts is
`Crystalline.exists_forall_le_levelThickening_hom` of
`StacksFrontier/AlgebraicGeometry/Crystalline/LevelFamilyFinality.lean`, which applies
`Crystalline.levelFamilyIso` at an arbitrary `Crystalline.CompletedEnvelopeThickening` — three of
whose fields are its three pinning hypotheses on the nose — and so needs no comparison of the two
presentations.

This does not by itself discharge `hdet`: that a morphism of crystals is determined by its
restrictions to the levels needs, beyond a morphism `B ⟶ T_e` for every `B`, the crystal
property, which is `...SmallSite.moduleRestrictionSheafMap_eq_of_hom` of
`StacksFrontier/AlgebraicGeometry/Crystalline/LevelCrystalDeterminacy.lean`. -/
@[stacks 07HP "for the finite levels of the completed envelope"]
theorem exists_levelThickening_hom (hf : Function.Surjective f)
    (hP : ∃ σ : Type u, Nonempty (MvPolynomial σ s.A ≃ₐ[s.A] P))
    (B : DividedPowerThickening.{u, u, u} s) :
    ∃ (e : ℕ) (h : IsPAdicLevel ((completedCrystallineThickening s f hf).2.1).ring.ideal
        ((completedCrystallineThickening s f hf).2.1).ring.dividedPowers s.p e),
      Nonempty (levelThickeningObj (completedCrystallineThickening s f hf).2.1 e h ⟶ B) := by
  classical
  refine ⟨max (completedLevelFamilyIso f hf).1
      (exists_forall_le_levelEnvelope_hom s hP f hf B).choose, ?_, ?_⟩
  · exact ((completedLevelFamilyIso f hf).2 _ (le_max_left _ _)).1
  · exact ⟨((completedLevelFamilyIso f hf).2 _ (le_max_left _ _)).2.2.hom ≫
      ((exists_forall_le_levelEnvelope_hom s hP f hf B).choose_spec _
        (le_max_right _ _)).choose_spec.some⟩

end ThickeningIso

end Crystalline

end

end
