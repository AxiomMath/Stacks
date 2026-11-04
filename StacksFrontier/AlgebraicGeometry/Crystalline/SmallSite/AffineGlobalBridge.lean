module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineSite
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Limits
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineSubsite
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ChaoticSubsite
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine
public import StacksFrontier.AlgebraicGeometry.Thickenings.Conormal

/-!
# The affine-to-global bridge for the crystalline site

Fix a global crystalline situation `(p, (S, I, γ), X)` in the sense of [Stacks, Tag 07MF], with
`X` affine.  The small crystalline site `Cris(X/S)` then contains the *chaotic subsite* `𝒞` of
[Stacks, Tag 07JK], the full subcategory of the divided power thickenings `(U, T, δ)` of the
whole of `X`.  On the other side of the library sits the purely ring-theoretic affine crystalline
category `CRIS(C/A)` of [Stacks, Tag 07HM], attached to an `AffineCrystallineSituation`
([Stacks, Tag 07MD]), and it is where most of the engine of [Stacks, Tag 07JN] — the envelopes
`D(n)`, the coproduct decomposition of [Stacks, Tag 07L4], the generator of [Stacks, Tag 07KI],
the homotopy of [Stacks, Tag 07LA] — is proved.

Before this file no module of the library mentioned both `Crystalline.AffineCrystallineSituation`
and `Crystalline.GlobalCrystallineSituation`, so nothing proved on the affine side was reachable
from `Cris(X/S)`.
This file builds the bridge: the affine situation of a global one, and the functor from the
chaotic subsite to the affine crystalline category given by taking global sections of the ambient
divided power scheme.

The functor is **contravariant**, `𝒞ᵒᵖ ⥤ CRIS(C/A)`.  A morphism of `𝒞` is a morphism of the
ambient divided power *schemes*, while a morphism of `CRIS(C/A)` is a morphism of the ambient
divided power *rings*; global sections reverses the direction.  This is the duality under which
the coproducts `D(n) = ∐_{n+1} D` of [Stacks, Tag 07L4] on the affine side correspond to the
*products* `T(n) = T ×_S ⋯ ×_S T` that the chaotic-site computation of [Stacks, Tag 07JM]
consumes.

## Main definitions

Everything lives in the namespaces `Crystalline`, `Crystalline.SchemeThickening` and
`Crystalline.GlobalCrystallineSituation`.

* `GlobalCrystallineSituation.baseSectionsRing` — the divided power ring `(Γ(S, ⊤), I(⊤), γ)` of
  global sections of the base.
* `GlobalCrystallineSituation.affineSituation` — **the affine crystalline situation of
  [Stacks, Tag 07MD] attached to a global one**: the divided power ring is
  `baseSectionsRing` and the algebra over it is `Γ(X, ⊤)`.
* `SchemeThickening.sectionsRing`, `SchemeThickening.sectionsIdeal` — the divided power ring and
  ideal of global sections of the ambient scheme of a divided power thickening of schemes.
* `SchemeThickening.sectionsQuotientHom`, `SchemeThickening.sectionsQuotientEquiv` — restriction
  to the thickened scheme on the quotient `Γ(T, ⊤)/I_T(⊤)`, and the fact that it is an
  isomorphism onto `Γ(U, ⊤)` when `U` is affine.
* `GlobalCrystallineSituation.wholeThickeningToAffine` and
  `GlobalCrystallineSituation.wholeHomToAffine` — the object and morphism parts of the bridge.
* `GlobalCrystallineSituation.wholeSiteToAffine` — **the bridge**, the functor
  `𝒞ᵒᵖ ⥤ CRIS(Γ(X, ⊤)/Γ(S, ⊤))`.
* `GlobalCrystallineSituation.affinePullback` — transport along the bridge: a covariant
  assignment on `CRIS(Γ(X, ⊤)/Γ(S, ⊤))` becomes a presheaf on `𝒞`.
* `GlobalCrystallineSituation.SmallSite.wholeToAffineSubsite` — the inclusion
  `𝒞 ⥤ AffineCris(X/S)` of the chaotic subsite into the subsite of affine objects.

## Main results

* `SchemeThickening.isAffine_target` — the ambient divided power scheme of a thickening of an
  affine scheme is affine, by [Stacks, Tag 06AD].
* `SchemeThickening.sectionsIdeal_eq_ker` — for such a thickening, the divided power ideal of
  global sections is the kernel of restriction to the thickened scheme.
* `SchemeThickening.isNilpotent_of_isNilpotent_appTop` — a global section of the ambient scheme is
  nilpotent as soon as its restriction is, the divided power ideal of a thickening of an affine
  scheme being nil.
* `GlobalCrystallineSituation.wholeSectionsToQuotient_commutes` and
  `GlobalCrystallineSituation.wholeQuotientMap_comp_wholeSectionsToQuotient` — the two
  compatibilities that make the bridge well defined: the square of [Stacks, Tag 07HM] for an
  object, and naturality of the structural maps for a morphism.
* `GlobalCrystallineSituation.wholeHomToAffine_injective` and
  `GlobalCrystallineSituation.faithful_wholeSiteToAffine` — **the bridge is faithful**: a morphism
  of `CRIS(X/S)` between objects with affine thickened schemes is determined by the morphism of
  divided power rings of global sections it induces.
* `GlobalCrystallineSituation.isCrystalline_wholeThickeningToAffine` — the bridge lands in the
  *little* affine crystalline category `Cris(Γ(X, ⊤)/Γ(S, ⊤))`: the structural map
  `Γ(X, ⊤) → Γ(T, ⊤)/I_T(⊤)` is bijective.
* `GlobalCrystallineSituation.SmallSite.isAffineObject_of_isOverWholeSpace` — an object of `𝒞`
  over the whole of an affine `X` is an affine object of `Cris(X/S)`.  This is the converse of
  `SmallSite.isAffineObject_of_isAffine`, whose docstring records it as unavailable; it follows
  from [Stacks, Tag 06AD].
* `GlobalCrystallineSituation.SmallSite.fullyFaithfulWholeToAffineSubsite` — the inclusion
  `𝒞 ⥤ AffineCris(X/S)` is fully faithful.

## What is and is not proved

**No tag attribute is placed in this file**: the bridge is infrastructure, not a numbered
statement of the source.

The bridge is a *faithful functor*, not an equivalence, and that is the limit of what is proved
here.  In particular **none of [Stacks, Tag 07JM], [Stacks, Tag 07JL], [Stacks, Tag 07L4],
[Stacks, Tag 07KI], [Stacks, Tag 07LA] is transported to `Cris(X/S)` by this file.**  Each of
those is a statement about `CRIS(C/A)` or its pro-completion, and pulling one back to `𝒞` needs
the bridge to be an equivalence.  What is missing for that, precisely:

1. **Fullness.**  Given objects `(X, T, δ)`, `(X, T', δ')` of `𝒞` and a morphism of divided power
   rings `Γ(T', ⊤) ⟶ Γ(T, ⊤)` over `Γ(S, ⊤)` compatible with the maps from `Γ(X, ⊤)`, one must
   produce a morphism `T ⟶ T'` of divided power schemes.  The underlying morphism of schemes is
   the `Spec` of the ring map, both schemes being affine, and compatibility with the divided
   powers over an *affine* open follows from the case of `⊤` by
   `Crystalline.DividedPowerScheme.map_ideal_top` and
   `DividedPowers.IsDPMorphism.of_comp`, as in
   `Crystalline.FCrystalSituation.specSigmaScheme_isDPMorphism_affine`.  The missing step is the
   passage from affine opens to all opens: the library has it only as the bespoke argument of
   `Crystalline.FCrystalSituation.specSigmaScheme_isDPMorphism` and as the private
   `isDPMorphism_app_of_affine` of
   `StacksFrontier/AlgebraicGeometry/Crystalline/FibreProduct.lean`, neither of which applies to an
   arbitrary morphism.
2. **Essential surjectivity.**  Given an object `(B, J, δ)` of `Cris(Γ(X, ⊤)/Γ(S, ⊤))`, one must
   produce an object of `𝒞` with ambient scheme `Spec B`.  This needs `Spec` of a divided power
   ring *as a divided power scheme*, which the library has only as the private
   `specDividedPowerScheme` of `StacksFrontier/AlgebraicGeometry/Crystalline/FibreProduct.lean`, on
   top of the private chain `specDividedPowerIdeal`, `specDividedPowerStructure`,
   `idealSheafAsSubmodule` and `dividedPowerStructureOfAffineSections`.

Two side conditions are carried as hypotheses rather than derived, and both are genuine:

* `IsAffine S.X`.  [Stacks, Tag 07JK] assumes `X` and `S` affine; affineness of `X` is what makes
  the thickened scheme of an object of `𝒞` affine, hence the ambient scheme affine, hence the
  restriction map on global sections surjective.  Affineness of `S` is *not* needed for the
  bridge: `baseSectionsRing` is formed from `Γ(S, ⊤)` whatever `S` is.
* `hp : IsNilpotent (S.p : Γ(X, ⊤))`.  The data of a `GlobalCrystallineSituation` only ask `p` to
  be nilpotent in every local ring of `X`, which for general `X` is weaker than nilpotence in
  `Γ(X, ⊤)`; an `AffineCrystallineSituation` asks for the latter.  For affine `X` the two agree,
  by a shorter route than one through `nilpotent_iff_mem_prime`: a global
  section of a *quasi-compact* scheme that is nilpotent in every local ring is nilpotent, since its
  basic open is both its unit locus and empty.  That is
  `AlgebraicGeometry.Scheme.isNilpotent_of_forall_isNilpotent_germ` and, for this situation,
  `Crystalline.GlobalCrystallineSituation.isNilpotent_prime_sections`, both in
  `StacksFrontier/AlgebraicGeometry/Crystalline/BigSite/BinaryProductPatch.lean`.  So `hp` is now
  **derivable** for affine `X` and need not be passed; it remains an explicit argument here only
  because removing it would change the signature of every declaration in this file and the four
  that build on it.

Also not proved, and needed before the bridge can be used for cohomology: that
`Crystalline.GlobalCrystallineSituation.Thickening` has no field asking `p` to be locally
nilpotent on the ambient scheme `T`, as [Stacks, Tag 07I6] does.  Here that nilpotence is
*derived* for objects of `CRIS(X/S)` whose thickened scheme is affine, by
`isNilpotent_prime_sections`; for a general object it is unavailable, so the bridge is restricted
to `𝒞`.

## References

* [Stacks Project, Tag 07MD](https://stacks.math.columbia.edu/tag/07MD)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
* [Stacks Project, Tag 07HM](https://stacks.math.columbia.edu/tag/07HM)
* [Stacks Project, Tag 07I6](https://stacks.math.columbia.edu/tag/07I6)
* [Stacks Project, Tag 07IG](https://stacks.math.columbia.edu/tag/07IG)
* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe w v u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u})

/-- The divided power ring of global sections of the divided power base scheme. -/
abbrev baseSectionsRing : DividedPowerRing.{u} :=
  S.S.dividedPowers.toDividedPowerRing (op ⊤)

/-- The ring map `Γ(S, ⊤) → Γ(X, ⊤)` induced by the structure morphism `X ⟶ S`. -/
abbrev baseSectionsToSections : Γ(S.S.scheme, ⊤) →+* Γ(S.X, ⊤) :=
  (sourceToBase S).appTop.hom

/-- The structure morphism `X ⟶ S` kills the divided power ideal `I` on global sections,
because it factors through the closed fibre `S₀ = V(I)`. -/
theorem baseSectionsToSections_eq_zero_of_mem (s : Γ(S.S.scheme, ⊤))
    (hs : s ∈ S.S.ideal.obj (op ⊤)) : baseSectionsToSections S s = 0 :=
  comp_app_eq_zero S.toClosedFiber (DividedPowerScheme.closedFiberι S.S) ⊤ s
    ((DividedPowerScheme.closedFiberPresentation S.S).app_eq_zero_of_mem ⊤ s hs)

/-- The `Γ(S, ⊤)`-algebra structure on `Γ(X, ⊤)` given by the structure morphism `X ⟶ S`. -/
abbrev sectionsAlgebra : Algebra ↥(baseSectionsRing S) Γ(S.X, ⊤) :=
  (baseSectionsToSections S).toAlgebra

/-- **The affine crystalline situation of [Stacks, Tag 07MD] attached to a global crystalline
situation** `(p, (S, I, γ), X)`: the divided power ring is the ring of global sections
`(Γ(S, ⊤), I(⊤), γ)` of the base, and the algebra over it is the ring of global sections
`Γ(X, ⊤)`.  The two hypotheses of [Stacks, Tag 07MD] hold: the structure morphism `X ⟶ S`
factors through the closed fibre `S₀ = V(I)`, so `I` dies in `Γ(X, ⊤)`; and the nilpotence of
`p` in `Γ(X, ⊤)` is the hypothesis `hp`.

The data of the global situation only ask `p` to be nilpotent in every *local ring* of `X`, which
is strictly weaker than nilpotence in `Γ(X, ⊤)` for a general `X`; `hp` is what the affine
situation needs, and it is implied by the local condition when `X` is affine. -/
def affineSituation (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) :
    AffineCrystallineSituation.{u, u} where
  p := S.p
  prime := S.prime
  A := baseSectionsRing S
  C := Γ(S.X, ⊤)
  algebraAtPrime := S.algebraAtPrime
  algebraC := sectionsAlgebra S
  ideal_map_eq_bot := by
    refine Ideal.map_eq_bot_iff_le_ker _ |>.mpr fun s hs ↦ ?_
    exact baseSectionsToSections_eq_zero_of_mem S s hs
  prime_nilpotent := hp

/-- The prime of the affine situation is the prime of the global situation. -/
@[simp]
theorem affineSituation_p (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) :
    (affineSituation S hp).p = S.p := rfl

/-- The base ring of the affine situation is the divided power ring of global sections of `S`. -/
@[simp]
theorem affineSituation_A (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) :
    (affineSituation S hp).A = baseSectionsRing S := rfl

/-- The algebra of the affine situation is the ring of global sections `Γ(X, ⊤)`. -/
@[simp]
theorem affineSituation_C (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) :
    (affineSituation S hp).C = Γ(S.X, ⊤) := rfl

/-- The structure map of the affine situation is the map on global sections induced by the
structure morphism `X ⟶ S`. -/
theorem affineSituation_algebraMap (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) :
    algebraMap ↥(affineSituation S hp).A (affineSituation S hp).C =
      baseSectionsToSections S := rfl

end Crystalline.GlobalCrystallineSituation

namespace Crystalline.SchemeThickening

variable (D : SchemeThickening.{u})

/-- The divided power ring of global sections of the ambient scheme of a divided power
thickening. -/
abbrev sectionsRing : DividedPowerRing.{u} :=
  D.target.dividedPowers.toDividedPowerRing (op ⊤)

/-- The divided power ideal of global sections of the ambient scheme of a divided power
thickening, presented as an ideal of the ring of sections rather than as a submodule, so that the
quotient below is the quotient *ring*. -/
abbrev sectionsIdeal : Ideal ↑Γ(D.target.scheme, ⊤) :=
  D.target.ideal.obj (op ⊤)

/-- **A divided power thickening of an affine scheme has affine ambient scheme**, by
[Stacks, Tag 06AD]. -/
theorem isAffine_target [IsAffine D.source] : IsAffine D.target.scheme :=
  Stacks.Thickenings.isAffine_of_isThickening D.isThickening

/-- **The immersion of a divided power thickening of an affine scheme is surjective on global
sections.**  It is a closed immersion with affine target, so this is Mathlib's
`AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine`. -/
theorem surjective_immersion_appTop [IsAffine D.source] :
    Function.Surjective D.immersion.appTop.hom :=
  have := D.isAffine_target
  (IsClosedImmersion.isAffine_surjective_of_isAffine D.immersion).2

/-- **For a divided power thickening of an affine scheme, the divided power ideal of global
sections is exactly the kernel of the restriction to the thickened scheme.**  One inclusion is
the defining condition `SchemeThickening.ideal_eq_ker` on the affine open `⊤`, and the kernel
ideal sheaf of a quasi-compact morphism is computed by `Scheme.Hom.ker_apply`. -/
theorem sectionsIdeal_eq_ker [IsAffine D.source] :
    sectionsIdeal D = RingHom.ker D.immersion.appTop.hom := by
  have := D.isAffine_target
  rw [show sectionsIdeal D = D.target.ideal.obj (op (⊤ : D.target.scheme.Opens)) from rfl,
    D.ideal_eq_ker ⟨⊤, isAffineOpen_top _⟩]
  exact Scheme.Hom.ker_apply _ ⟨⊤, isAffineOpen_top _⟩

/-- A global section of the ambient scheme of a divided power thickening of an affine scheme lies
in the divided power ideal exactly when it dies on the thickened scheme. -/
theorem mem_sectionsIdeal_iff [IsAffine D.source] (a : ↑Γ(D.target.scheme, ⊤)) :
    a ∈ sectionsIdeal D ↔ D.immersion.appTop.hom a = 0 := by
  rw [D.sectionsIdeal_eq_ker, RingHom.mem_ker]

/-- Restriction to the thickened scheme, read on the quotient by the divided power ideal. -/
def sectionsQuotientHom [IsAffine D.source] :
    (↑Γ(D.target.scheme, ⊤) ⧸ sectionsIdeal D) →+* Γ(D.source, ⊤) :=
  Ideal.Quotient.lift _ D.immersion.appTop.hom fun a ha ↦ (D.mem_sectionsIdeal_iff a).mp ha

/-- The class of a global section `x` of the ambient scheme is sent by
`SchemeThickening.sectionsQuotientHom` to the restriction of `x` to the thickened scheme. -/
@[simp]
theorem sectionsQuotientHom_mk [IsAffine D.source] (x : ↑Γ(D.target.scheme, ⊤)) :
    D.sectionsQuotientHom (Ideal.Quotient.mk (sectionsIdeal D) x) =
      D.immersion.appTop.hom x := rfl

/-- For a divided power thickening of an affine scheme, restriction to the thickened scheme
induces a bijection from the quotient of the global sections of the ambient scheme by the divided
power ideal onto the global sections of the thickened scheme. -/
theorem bijective_sectionsQuotientHom [IsAffine D.source] :
    Function.Bijective D.sectionsQuotientHom := by
  refine ⟨?_, fun y ↦ ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (D.mem_sectionsIdeal_iff a).mpr (by rwa [← D.sectionsQuotientHom_mk a])
  · obtain ⟨a, ha⟩ := D.surjective_immersion_appTop y
    exact ⟨Ideal.Quotient.mk _ a, ha⟩

/-- **The global sections of a divided power thickening of an affine scheme, modulo the divided
power ideal, are the global sections of the thickened scheme.**  The immersion is a closed
immersion of affine schemes, so it is surjective on global sections, and its kernel is the
divided power ideal by `SchemeThickening.sectionsIdeal_eq_ker`. -/
def sectionsQuotientEquiv [IsAffine D.source] :
    (↑Γ(D.target.scheme, ⊤) ⧸ sectionsIdeal D) ≃+* Γ(D.source, ⊤) :=
  RingEquiv.ofBijective _ D.bijective_sectionsQuotientHom

/-- The class of a global section `x` of the ambient scheme is sent by
`SchemeThickening.sectionsQuotientEquiv` to the restriction of `x` to the thickened scheme. -/
@[simp]
theorem sectionsQuotientEquiv_mk [IsAffine D.source] (x : ↑Γ(D.target.scheme, ⊤)) :
    D.sectionsQuotientEquiv (Ideal.Quotient.mk (sectionsIdeal D) x) =
      D.immersion.appTop.hom x := rfl

/-- **A global section of the ambient scheme of a divided power thickening of an affine scheme is
nilpotent as soon as its restriction to the thickened scheme is.**  The divided power ideal is the
kernel of the restriction, and the ideal of a thickening of an affine scheme is nil. -/
theorem isNilpotent_of_isNilpotent_appTop [IsAffine D.source] {a : ↑Γ(D.target.scheme, ⊤)}
    (ha : IsNilpotent (D.immersion.appTop.hom a)) : IsNilpotent a := by
  have := D.isAffine_target
  obtain ⟨n, hn⟩ := ha
  exact IsNilpotent.of_pow (m := n)
    (Stacks.Thickenings.IsThickening.isNilpotent_of_mem_ker_appTop D.isThickening
      (RingHom.mem_ker.mpr (by rwa [map_pow])))

end Crystalline.SchemeThickening

namespace Crystalline

namespace GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

/-- The prime is nilpotent on the thickened scheme of an object of `CRIS(X/S)` as soon as it is
nilpotent on `Γ(X, ⊤)`: the thickened scheme maps to `X`. -/
theorem isNilpotent_prime_source (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) (B : Thickening S) :
    IsNilpotent (S.p : Γ(B.thickening.source, ⊤)) := by
  have h := hp.map B.toX.appTop.hom
  rwa [map_natCast] at h

/-- **For an object of `CRIS(X/S)` over the whole of an affine `X`, the thickened scheme is
affine**, since its structure map to `X` is an isomorphism. -/
instance instIsAffineThickeningSource [IsAffine S.X] (B : Thickening S) [IsIso B.toX] :
    IsAffine B.thickening.source :=
  IsAffine.of_isIso B.toX

/-- The structural map `Γ(X, ⊤) → Γ(T, ⊤)/I_T(⊤)` of the object of `CRIS(Γ(X, ⊤)/Γ(S, ⊤))`
attached to an object `(U, T, δ)` of `CRIS(X/S)` with `U` affine: restriction `Γ(X, ⊤) → Γ(U, ⊤)`
followed by the inverse of the restriction isomorphism `Γ(T, ⊤)/I_T(⊤) ≅ Γ(U, ⊤)`. -/
def wholeSectionsToQuotient (B : Thickening S) [IsAffine B.thickening.source] :
    Γ(S.X, ⊤) →+*
      (↑Γ(B.thickening.target.scheme, ⊤) ⧸ SchemeThickening.sectionsIdeal B.thickening) :=
  B.thickening.sectionsQuotientEquiv.symm.toRingHom.comp B.toX.appTop.hom

/-- After the restriction isomorphism `Γ(T, ⊤)/I_T(⊤) ≅ Γ(U, ⊤)`, the structural map
`wholeSectionsToQuotient` is the restriction `Γ(X, ⊤) → Γ(U, ⊤)` along `U ⟶ X`. -/
@[simp]
theorem sectionsQuotientEquiv_wholeSectionsToQuotient (B : Thickening S)
    [IsAffine B.thickening.source] (y : Γ(S.X, ⊤)) :
    B.thickening.sectionsQuotientEquiv (wholeSectionsToQuotient B y) = B.toX.appTop.hom y :=
  B.thickening.sectionsQuotientEquiv.apply_symm_apply _

/-- **The square of [Stacks, Tag 07HM] commutes for the global sections of an object of
`CRIS(X/S)` with affine thickened scheme.**  After the restriction isomorphism
`Γ(T, ⊤)/I_T(⊤) ≅ Γ(U, ⊤)` both ways around it are the two ways around the commuting square
`U ↪ T ⟶ S`, `U ⟶ X ⟶ S` of the object. -/
theorem wholeSectionsToQuotient_commutes (B : Thickening S)
    [IsAffine B.thickening.source] :
    (Ideal.Quotient.mk (SchemeThickening.sectionsIdeal B.thickening)).comp
        B.toBase.hom.appTop.hom =
      (wholeSectionsToQuotient B).comp (baseSectionsToSections S) := by
  refine RingHom.ext fun x ↦ B.thickening.sectionsQuotientEquiv.injective ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, sectionsQuotientEquiv_wholeSectionsToQuotient,
    SchemeThickening.sectionsQuotientEquiv_mk]
  exact Stacks.Thickenings.appTop_comm_of_comm B.over_base x

/-- **The prime is nilpotent on global sections of the ambient scheme** of an object of
`CRIS(X/S)` with affine thickened scheme: it is nilpotent on the thickened scheme, and the
divided power ideal of a thickening of an affine scheme is nil. -/
theorem isNilpotent_prime_sections (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
    (B : Thickening S) [IsAffine B.thickening.source] :
    IsNilpotent (S.p : ↑Γ(B.thickening.target.scheme, ⊤)) :=
  B.thickening.isNilpotent_of_isNilpotent_appTop
    (by simpa using isNilpotent_prime_source hp B)

/-- **The object of the big affine crystalline category `CRIS(Γ(X, ⊤)/Γ(S, ⊤))` attached to an
object of `CRIS(X/S)` whose thickened scheme is affine.**  Its divided power ring is the ring of
global sections `(Γ(T, ⊤), I_T(⊤), δ)` of the ambient scheme, the map from the base is the map on
global sections of `T ⟶ S`, and the structural map is `wholeSectionsToQuotient`.

The thickened scheme `U` being affine, so is the ambient scheme `T`, by [Stacks, Tag 06AD]; that
is what `Crystalline.SchemeThickening.sectionsQuotientEquiv` needs.  The object is crystalline in
the sense of `Crystalline.DividedPowerThickening.IsCrystalline` only when `U` is the whole of `X`,
which is `isCrystalline_wholeThickeningToAffine`. -/
def wholeThickeningToAffine (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
    (B : Thickening S) [IsAffine B.thickening.source] :
    DividedPowerThickening.{u, u, u} (affineSituation S hp) where
  ring := B.thickening.sectionsRing
  fromBase := globalSectionsDPMorphism B.toBase
  prime_nilpotent := isNilpotent_prime_sections hp B
  toQuotient := wholeSectionsToQuotient B
  commutes := wholeSectionsToQuotient_commutes B

section Morphisms

variable {B B' : Thickening S} [IsAffine B.thickening.source] [IsAffine B'.thickening.source]

/-- A morphism of `CRIS(X/S)` carries the divided power ideal of global sections of the target
into that of the source: both are the kernel of restriction to the thickened scheme, and the
square of thickenings commutes. -/
theorem targetHom_appTop_mem_sectionsIdeal (f : B ⟶ B')
    {a : ↑Γ(B'.thickening.target.scheme, ⊤)}
    (ha : a ∈ SchemeThickening.sectionsIdeal B'.thickening) :
    f.targetHom.hom.appTop.hom a ∈ SchemeThickening.sectionsIdeal B.thickening := by
  rw [SchemeThickening.mem_sectionsIdeal_iff,
    Stacks.Thickenings.appTop_comm_of_comm f.immersion_naturality a,
    (SchemeThickening.mem_sectionsIdeal_iff _ a).mp ha, map_zero]

/-- The map induced by a morphism of `CRIS(X/S)` between objects with affine thickened schemes on
the quotients of the rings of global sections by the divided power ideals. -/
def wholeQuotientMap (f : B ⟶ B') :
    (↑Γ(B'.thickening.target.scheme, ⊤) ⧸ SchemeThickening.sectionsIdeal B'.thickening) →+*
      (↑Γ(B.thickening.target.scheme, ⊤) ⧸ SchemeThickening.sectionsIdeal B.thickening) :=
  Ideal.quotientMap _ f.targetHom.hom.appTop.hom fun _ ha ↦
    Ideal.mem_comap.mpr (targetHom_appTop_mem_sectionsIdeal f ha)

/-- After the restriction isomorphisms `Γ(T, ⊤)/I_T(⊤) ≅ Γ(U, ⊤)`, the map `wholeQuotientMap f`
is the map on global sections of the morphism `U ⟶ U'` of thickened schemes. -/
@[simp]
theorem sectionsQuotientEquiv_wholeQuotientMap (f : B ⟶ B')
    (q : ↑Γ(B'.thickening.target.scheme, ⊤) ⧸ SchemeThickening.sectionsIdeal B'.thickening) :
    B.thickening.sectionsQuotientEquiv (wholeQuotientMap f q) =
      f.sourceHom.appTop.hom (B'.thickening.sectionsQuotientEquiv q) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [wholeQuotientMap, Ideal.quotientMap_mk, SchemeThickening.sectionsQuotientEquiv_mk,
    SchemeThickening.sectionsQuotientEquiv_mk]
  exact Stacks.Thickenings.appTop_comm_of_comm f.immersion_naturality a

/-- **The structural maps `Γ(X, ⊤) → Γ(T, ⊤)/I_T(⊤)` are natural in the object of `CRIS(X/S)`**,
for objects with affine thickened schemes.  After the restriction isomorphisms this is the
triangle `U ⟶ U' ⟶ X` of the morphism. -/
theorem wholeQuotientMap_comp_wholeSectionsToQuotient (f : B ⟶ B') :
    (wholeQuotientMap f).comp (wholeSectionsToQuotient B') = wholeSectionsToQuotient B := by
  refine RingHom.ext fun y ↦ B.thickening.sectionsQuotientEquiv.injective ?_
  rw [RingHom.comp_apply, sectionsQuotientEquiv_wholeQuotientMap,
    sectionsQuotientEquiv_wholeSectionsToQuotient, sectionsQuotientEquiv_wholeSectionsToQuotient,
    Stacks.Thickenings.appTop_comp_apply, f.toX_naturality]

/-- **The morphism of `CRIS(Γ(X, ⊤)/Γ(S, ⊤))` attached to a morphism of `CRIS(X/S)` between
objects with affine thickened schemes.**  It is the map on global sections of the ambient divided
power schemes, so the assignment is *contravariant*: this is the duality between the geometric
crystalline category and the ring-theoretic one of [Stacks, Tag 07HM]. -/
def wholeHomToAffine (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) (f : B ⟶ B') :
    wholeThickeningToAffine hp B' ⟶ wholeThickeningToAffine hp B where
  hom := globalSectionsDPMorphism f.targetHom
  fromBase_comp :=
    (globalSectionsDPMorphism_comp f.targetHom B'.toBase).trans
      (congrArg (fun h : B.thickening.target ⟶ S.S ↦ globalSectionsDPMorphism h)
        f.base_naturality)
  toQuotient_comp := wholeQuotientMap_comp_wholeSectionsToQuotient f

/-- The underlying divided power morphism of `wholeHomToAffine hp f` is the map on global sections
of the morphism of ambient divided power schemes of `f`. -/
@[simp]
theorem wholeHomToAffine_hom (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) (f : B ⟶ B') :
    (wholeHomToAffine hp f).hom = globalSectionsDPMorphism f.targetHom := rfl

end Morphisms

/-- The inclusion of the chaotic subsite `𝒞` of thickenings of the whole space into the big
crystalline category `CRIS(X/S)`, through the small crystalline site. -/
abbrev wholeToBig (S : GlobalCrystallineSituation.{u}) :
    SmallSite.WholeSpaceThickening S ⥤ Thickening S :=
  SmallSite.wholeι S ⋙ CrystallineThickening.ι S

/-- **The affine-to-global bridge.**  The chaotic subsite `𝒞 ⊆ Cris(X/S)` of divided power
thickenings of the whole of an affine `X`, of [Stacks, Tag 07JK], maps to the affine crystalline
category `CRIS(Γ(X, ⊤)/Γ(S, ⊤))` of [Stacks, Tag 07HM] by taking global sections of the ambient
divided power scheme.

The functor is contravariant — its source is `𝒞ᵒᵖ` — because a morphism of thickenings is a
morphism of the ambient *schemes* while a morphism of `CRIS(C/A)` is a morphism of the ambient
*rings*.  This is the duality that turns the coproducts `D(n) = ∐ D` of [Stacks, Tag 07L4] on the
affine side into the products of `𝒞` that the chaotic-site computation of [Stacks, Tag 07JM]
consumes. -/
def wholeSiteToAffine [IsAffine S.X] (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) :
    (SmallSite.WholeSpaceThickening S)ᵒᵖ ⥤
      DividedPowerThickening.{u, u, u} (affineSituation S hp) where
  obj A :=
    have : IsIso ((wholeToBig S).obj A.unop).toX := A.unop.property
    wholeThickeningToAffine hp ((wholeToBig S).obj A.unop)
  map {A B} f :=
    have : IsIso ((wholeToBig S).obj A.unop).toX := A.unop.property
    have : IsIso ((wholeToBig S).obj B.unop).toX := B.unop.property
    wholeHomToAffine hp ((wholeToBig S).map f.unop)
  map_id A := by
    have : IsIso ((wholeToBig S).obj A.unop).toX := A.unop.property
    exact DividedPowerThickening.Hom.ext (globalSectionsDPMorphism_id _)
  map_comp {A B C} f g := by
    have : IsIso ((wholeToBig S).obj A.unop).toX := A.unop.property
    have : IsIso ((wholeToBig S).obj B.unop).toX := B.unop.property
    have : IsIso ((wholeToBig S).obj C.unop).toX := C.unop.property
    exact DividedPowerThickening.Hom.ext (globalSectionsDPMorphism_comp _ _).symm

/-- The bridge takes an object of `𝒞` to the divided power ring of global sections of its ambient
divided power scheme. -/
theorem wholeSiteToAffine_obj_ring [IsAffine S.X] (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
    (A : (SmallSite.WholeSpaceThickening S)ᵒᵖ) :
    ((wholeSiteToAffine hp).obj A).ring =
      ((wholeToBig S).obj A.unop).thickening.sectionsRing := rfl

/-- **The bridge lands in the little affine crystalline category `Cris(Γ(X, ⊤)/Γ(S, ⊤))`**: the
structural map `Γ(X, ⊤) → Γ(T, ⊤)/I_T(⊤)` of the image of an object of `𝒞` is bijective, because
it is the composite of the isomorphism `Γ(X, ⊤) ≅ Γ(U, ⊤)` with the inverse of the restriction
isomorphism `Γ(T, ⊤)/I_T(⊤) ≅ Γ(U, ⊤)`. -/
theorem isCrystalline_wholeThickeningToAffine [IsAffine S.X]
    (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) (B : Thickening S) [IsIso B.toX] :
    DividedPowerThickening.IsCrystalline (wholeThickeningToAffine hp B) := by
  have hiso : IsIso (Scheme.Hom.appTop B.toX) := by
    have h : IsIso (Scheme.Γ.map B.toX.op) := inferInstance
    rwa [Scheme.Γ_map_op] at h
  exact (B.thickening.sectionsQuotientEquiv.symm.bijective).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.Hom.appTop B.toX))

/-- **A morphism of `CRIS(X/S)` between objects with affine thickened schemes is determined by the
morphism of divided power rings it induces on global sections.**  The ambient divided power
schemes are affine, so their morphism is determined by its effect on global sections
(`AlgebraicGeometry.ext_of_isAffine`); the morphism of thickened schemes is then determined
because the immersion of the target is a monomorphism, being a closed immersion. -/
theorem wholeHomToAffine_injective (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
    {B B' : Thickening S} [IsAffine B.thickening.source] [IsAffine B'.thickening.source]
    {f g : B ⟶ B'}
    (h : wholeHomToAffine hp f = wholeHomToAffine hp g) : f = g := by
  have hT : f.targetHom = g.targetHom := by
    have h0 : globalSectionsDPMorphism f.targetHom = globalSectionsDPMorphism g.targetHom :=
      congrArg DividedPowerThickening.Hom.hom h
    have h1 : f.targetHom.hom.appTop = g.targetHom.hom.appTop :=
      CommRingCat.hom_ext (congrArg DividedPowers.DPMorphism.toRingHom h0)
    have := B'.thickening.isAffine_target
    exact DividedPowerScheme.Hom.ext (ext_of_isAffine h1)
  have hS : f.sourceHom = g.sourceHom := by
    have e : f.sourceHom ≫ B'.thickening.immersion = g.sourceHom ≫ B'.thickening.immersion := by
      rw [← f.immersion_naturality, ← g.immersion_naturality, hT]
    exact (cancel_mono B'.thickening.immersion).mp e
  exact Thickening.Hom.ext hS hT

/-- **The bridge is faithful.**  A morphism of the chaotic subsite is determined by the morphism
of divided power rings of global sections that it induces. -/
instance faithful_wholeSiteToAffine [IsAffine S.X] (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) :
    (wholeSiteToAffine hp).Faithful where
  map_injective {A B} {f g} h := by
    have : IsIso ((wholeToBig S).obj A.unop).toX := A.unop.property
    have : IsIso ((wholeToBig S).obj B.unop).toX := B.unop.property
    exact Quiver.Hom.unop_inj ((wholeToBig S).map_injective (wholeHomToAffine_injective hp h))

/-- **Transport along the bridge.**  A covariant assignment on the affine crystalline category
`CRIS(Γ(X, ⊤)/Γ(S, ⊤))` becomes a presheaf on the chaotic subsite `𝒞`, by composing with the
bridge.  This is the shape in which an affine construction indexed by the objects of `CRIS(C/A)`
— a system of modules over the envelopes, say — reaches `Cris(X/S)`. -/
abbrev affinePullback [IsAffine S.X] (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) {A : Type v}
    [Category.{w} A] (F : DividedPowerThickening.{u, u, u} (affineSituation S hp) ⥤ A) :
    (SmallSite.WholeSpaceThickening S)ᵒᵖ ⥤ A :=
  wholeSiteToAffine hp ⋙ F

/-! ### The chaotic subsite sits inside the affine subsite -/

/-- **An object of the chaotic subsite `𝒞` over the whole of an affine `X` is an affine object of
`Cris(X/S)`**, in the sense of `Crystalline.GlobalCrystallineSituation.SmallSite.IsAffineObject`:
its thickened scheme is isomorphic to `X`, hence affine, and its ambient divided power scheme is
then affine by [Stacks, Tag 06AD].

This is the step-3 input of [Stacks, Tag 07JK] that identifies `𝒞` as a subcategory of
`AffineCris(X/S)` rather than merely of `Cris(X/S)`.  It is the converse of
`SmallSite.isAffineObject_of_isAffine`, whose docstring records it as unavailable; it is available
through `Stacks.Thickenings.isAffine_of_isThickening`. -/
theorem SmallSite.isAffineObject_of_isOverWholeSpace [IsAffine S.X] (A : CrystallineThickening S)
    (hA : SmallSite.IsOverWholeSpace S A) : SmallSite.IsAffineObject S A :=
  have : IsIso A.obj.toX := hA
  have : IsAffine A.obj.thickening.source := IsAffine.of_isIso A.obj.toX
  ⟨this, A.obj.thickening.isAffine_target⟩

/-- **The inclusion `𝒞 ⥤ AffineCris(X/S)`** of the chaotic subsite of thickenings of the whole of
an affine `X` into the subsite of affine objects.  It is the inclusion `wholeι` of
[Stacks, Tag 07JK] lifted through `SmallSite.isAffineObject_of_isOverWholeSpace`, so composing it
with `affineι` gives `wholeι` back, definitionally. -/
abbrev SmallSite.wholeToAffineSubsite [IsAffine S.X] :
    SmallSite.WholeSpaceThickening S ⥤ SmallSite.AffineCrystallineThickening S :=
  (SmallSite.IsAffineObject S).lift (SmallSite.wholeι S) fun A ↦
    SmallSite.isAffineObject_of_isOverWholeSpace A.obj A.property

/-- The inclusion `𝒞 ⥤ AffineCris(X/S)` followed by `AffineCris(X/S) ⥤ Cris(X/S)` is the
inclusion `𝒞 ⥤ Cris(X/S)`. -/
def SmallSite.wholeToAffineSubsiteCompAffineι [IsAffine S.X] :
    SmallSite.wholeToAffineSubsite (S := S) ⋙ SmallSite.affineι S ≅ SmallSite.wholeι S :=
  (SmallSite.IsAffineObject S).liftCompιIso _ _

/-- The inclusion `𝒞 ⥤ AffineCris(X/S)` is fully faithful, being a lift of the fully faithful
inclusion `𝒞 ⥤ Cris(X/S)` through a full subcategory. -/
def SmallSite.fullyFaithfulWholeToAffineSubsite [IsAffine S.X] :
    (SmallSite.wholeToAffineSubsite (S := S)).FullyFaithful :=
  .ofFullyFaithful _

end GlobalCrystallineSituation

end Crystalline

end

end
