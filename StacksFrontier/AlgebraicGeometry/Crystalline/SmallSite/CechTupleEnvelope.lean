module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineCrystallineSite.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.BinaryProductPatch
public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineSite.Coproduct
public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeFunctoriality
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechTuplePresentation

/-!
# The envelopes `D_α` of the Čech intersections

[Stacks, Tag 07MM] forms, for every tuple `α = (λ_0, …, λ_n)` of members of its affine open
covering, the `p`-adically completed divided power envelope `D_α` of the kernel of
`P_α = P_{λ_0} ⊗_A ⋯ ⊗_A P_{λ_n} → C_α`.  This file **constructs that ring**, as an object of the
completed affine crystalline site `Cris^∧(C_α/A)`.

Two things are needed and are supplied here.  The first is an affine crystalline situation at the
Čech intersection, `...SmallSite.interSituation`: the divided power base is the ring of global
sections `(Γ(S, ⊤), I(⊤), γ)` of the base of the global situation and the algebra over it is
`C_α = Γ(U_α)`.  It is built directly, not through
`Crystalline.GlobalCrystallineSituation.restrict`, which replaces the base `S` by `S.S.restrict W`
and therefore does not leave the ring `A` alone.  Its two hypotheses hold: `I` dies in `Γ(X, ⊤)`
and hence in `C_α`, because the structure morphism factors through the closed fibre; and `p` is
nilpotent in `C_α` by
`Crystalline.GlobalCrystallineSituation.isNilpotent_prime_sections_of_isAffineOpen`, the Čech
intersection being affine.

The second is the surjective presentation of `C_α` over that base, which is
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CechTuplePresentation.lean`, read as a map of
`A`-algebras.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `interSituation` — **the affine crystalline situation `(A, I, γ) → C_α` at a Čech
  intersection**.
* `CechPresentation.tupleAlgHom` — the presentation `P_α → C_α` as a map of `A`-algebras.
* `CechPresentation.tupleEnvelope` — **the ring `D_α` of [Stacks, Tag 07MM]**, as an object of
  `Cris^∧(C_α/A)`.
* `CechPresentation.tupleDividedPowerEnvelope` — the same envelope before `p`-adic completion,
  which is the object the universal property speaks about.
* `CechPresentation.tupleEnvelopeMap` — **the transition morphism `D_{α ∘ φ} ⟶ D_α`** along a
  Čech face, on the uncompleted envelopes.
* `CechPresentation.tupleCompletedEnvelopeRing` — the divided power ring `(D_α, J̄_α, γ̄_α)` of
  the remark, which by `CechPresentation.tupleEnvelope_ring` is the ring of
  `CechPresentation.tupleEnvelope`.
* `CechPresentation.tupleCompletedEnvelopeMap` — **the transition morphism on those completed
  rings**, the one the remark uses.

## Main results

* `CechPresentation.surjective_tupleAlgHom` — the presentation is surjective, which is what the
  envelope's construction requires.
* `CechPresentation.ker_tupleAlgHom` — the ideal the envelope is taken at is `J_α`, which is what
  makes `CechPresentation.tupleEnvelope` the remark's `D_α`.
* `CechPresentation.tupleEnvelopeMap_id` and `CechPresentation.tupleEnvelopeMap_comp`, and their
  completed forms `CechPresentation.tupleCompletedEnvelopeMap_id` and
  `CechPresentation.tupleCompletedEnvelopeMap_comp` — the transition morphisms are **strictly
  functorial** in the simplex category, which is the `map_id` and `map_comp` a
  `...SmallSite.CechSystem` asks for.

## What is and is not proved

**[Stacks, Tag 07MM] is not proved and no tag attribute is placed in this file.**  What is built
is the family of rings `D_α`, one in each `Cris^∧(C_α/A)`, together with the transition morphisms
`D_{α ∘ φ} ⟶ D_α` — on the uncompleted envelopes and on the completed ones — and their strict
functoriality in the simplex category.

The transitions are produced by `Crystalline.envelopeIdealMap`, which reads the universal
property of the envelope ([Stacks, Tag 07H8], `Crystalline.DividedPowerEnvelope.homEquiv`) with
the envelope of *another* ideal in *another* ring as its target.  That the property allows this is
the content of
`StacksFrontier/AlgebraicGeometry/Crystalline/EnvelopeFunctoriality.lean`: it is stated for a divided
power ring `A`, a ring `B` and an ideal `J ⊆ B`, and never mentions an affine crystalline
situation, so the restriction to one situation was only in the wrappers
`Crystalline.polynomialEnvelopeMap` and `Crystalline.completedEnvelope_isCoproduct`
([Stacks, Tag 07L4]).  Here `interSituation c α` and `interSituation c (α ∘ φ)` have different
`C` but the *same* divided power base `A = Γ(S, ⊤)`, so `Crystalline.envelopeIdealMap` applies
directly; `Crystalline.polynomialEnvelopeMapOver` is the version for situations whose bases
differ too.

What stands between what is here and a `...SmallSite.CechSystem` is one step, and it is a step
about the *site*, not about envelopes.  A `...SmallSite.CechSystem` asks, for each tuple, for a
functor `ℕ ⥤ Cris(X/S)` into the **global small site**, and the transitions above are divided
power morphisms of rings; neither is a morphism in either `Cris^∧(C_α/A)`, those two categories
being different — the remark's transition `T(α)_e ⟶ T(α ∘ φ)_e` lies over the inclusion
`U_α ⊆ U_{α ∘ φ}` and so exists only after transport to `Cris(X/S)`.  Concretely what is owed is

* the level towers `T(α)_e = Spec(D_α/p^e D_α)` as objects of `Cris(X/S)`.  On the affine side the
  levels exist, `Crystalline.levelFunctor`; carrying them to the global small site asks for the
  analogue at `U_α` of `Crystalline.GlobalCrystallineSituation.wholeSiteEquivLittleAffine`, which
  is stated for a situation whose `X` is affine and compares `Cris(Γ(X, ⊤)/Γ(S, ⊤))` with the
  thickenings of the *whole* of that `X`.

## References

* [Stacks Project, Tag 07MM](https://stacks.math.columbia.edu/tag/07MM)
* [Stacks Project, Tag 07MD](https://stacks.math.columbia.edu/tag/07MD)
* [Stacks Project, Tag 07KI](https://stacks.math.columbia.edu/tag/07KI)
* [Stacks Project, Tag 07L4](https://stacks.math.columbia.edu/tag/07L4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} {Λ : Type u}

/-! ### The affine crystalline situation at a Čech intersection -/

/-- **The affine crystalline situation of [Stacks, Tag 07MD] at a Čech intersection**: the divided
power ring is the ring of global sections `(Γ(S, ⊤), I(⊤), γ)` of the base of the global
situation, and the algebra over it is `C_α = Γ(U_α)`, through the structural map
`...SmallSite.baseToSections`.

Both hypotheses of [Stacks, Tag 07MD] hold.  The divided power ideal `I` has zero image in `C_α`
because the structure morphism `X ⟶ S` factors through the closed fibre `S₀ = V(I)`, which is
`Crystalline.GlobalCrystallineSituation.baseSectionsToSections_eq_zero_of_mem`; and `p` is
nilpotent in `C_α` by
`Crystalline.GlobalCrystallineSituation.isNilpotent_prime_sections_of_isAffineOpen`, the Čech
intersection being affine for a separated `X`. -/
def interSituation [Scheme.IsSeparated S.X] (c : CechCovering S Λ) {n : ℕ}
    (α : Fin (n + 1) → Λ) : AffineCrystallineSituation.{u, u} where
  p := S.p
  prime := S.prime
  A := baseSectionsRing S
  C := Γ(S.X, c.inter α)
  algebraAtPrime := S.algebraAtPrime
  algebraC := (baseToSections S (c.inter α)).toAlgebra
  ideal_map_eq_bot := by
    refine Ideal.map_eq_bot_iff_le_ker _ |>.mpr fun s hs ↦ ?_
    show sectionsRestrict (le_top : c.inter α ≤ ⊤) (baseSectionsToSections S s) = 0
    rw [baseSectionsToSections_eq_zero_of_mem S s hs, map_zero]
  prime_nilpotent := by
    have h := isNilpotent_prime_sections_of_isAffineOpen S (c.inter α) (c.isAffineOpen_inter α)
    have h' := h.map (c.inter α).topIso.hom.hom
    rwa [map_natCast] at h'

/-- The divided power ring of the situation at a Čech intersection is `baseSectionsRing S`. -/
@[simp]
theorem interSituation_A [Scheme.IsSeparated S.X] (c : CechCovering S Λ) {n : ℕ}
    (α : Fin (n + 1) → Λ) : (interSituation c α).A = baseSectionsRing S := rfl

/-- The algebra of the situation at a Čech intersection is `Γ(S.X, c.inter α)`. -/
@[simp]
theorem interSituation_C [Scheme.IsSeparated S.X] (c : CechCovering S Λ) {n : ℕ}
    (α : Fin (n + 1) → Λ) : (interSituation c α).C = Γ(S.X, c.inter α) := rfl

/-- The structural map of the situation at a Čech intersection is `...SmallSite.baseToSections`. -/
theorem interSituation_algebraMap [Scheme.IsSeparated S.X] (c : CechCovering S Λ) {n : ℕ}
    (α : Fin (n + 1) → Λ) :
    algebraMap ↥(interSituation c α).A (interSituation c α).C = baseToSections S (c.inter α) :=
  rfl

/-! ### The presentation as a map of algebras, and the envelope -/

section Envelope

variable [Scheme.IsSeparated S.X] {c : CechCovering S Λ}
  (P : CechPresentation c Γ(S.S.scheme, ⊤))
  (hP : ∀ U : S.X.Opens, P.base U = baseToSections S U)

/-- **The presentation `P_α → C_α` of [Stacks, Tag 07MM] as a map of `A`-algebras**, which is the
shape the divided power envelope takes it in. -/
def CechPresentation.tupleAlgHom {n : ℕ} (α : Fin (n + 1) → Λ) :
    MvPolynomial (P.tupleIndex α) ↥(interSituation c α).A →ₐ[↥(interSituation c α).A]
      (interSituation c α).C :=
  { P.tupleMap α with
    commutes' := fun r =>
      (P.tupleMap_C α r).trans (RingHom.congr_fun (hP (c.inter α)) r) }

/-- The map of algebras `CechPresentation.tupleAlgHom` agrees with `CechPresentation.tupleMap`. -/
@[simp]
theorem CechPresentation.tupleAlgHom_apply {n : ℕ} (α : Fin (n + 1) → Λ)
    (q : MvPolynomial (P.tupleIndex α) ↥(interSituation c α).A) :
    P.tupleAlgHom hP α q = P.tupleMap α q := rfl

/-- **The presentation of a Čech intersection is surjective**, in the algebra form the envelope
asks for.  This is `...SmallSite.CechPresentation.surjective_tupleMap`. -/
theorem CechPresentation.surjective_tupleAlgHom {n : ℕ} (α : Fin (n + 1) → Λ) :
    Function.Surjective (P.tupleAlgHom hP α) :=
  P.surjective_tupleMap α

/-- **The ideal the envelope below is taken at is `J_α`**, the kernel of `P_α → C_α`.  This is
what makes `...CechPresentation.tupleEnvelope` the ring `D_α` of [Stacks, Tag 07MM] rather than
the envelope of some other ideal: `Crystalline.polynomialDividedPowerEnvelope` is the envelope of
`RingHom.ker` of its presentation. -/
theorem CechPresentation.ker_tupleAlgHom {n : ℕ} (α : Fin (n + 1) → Λ) :
    RingHom.ker (P.tupleAlgHom hP α).toRingHom = P.tupleIdeal α := rfl

/-- **The ring `D_α` of [Stacks, Tag 07MM]**: the `p`-adically completed divided power envelope of
`J_α = ker(P_α → C_α)`, as an object of the completed affine crystalline site `Cris^∧(C_α/A)` at
the Čech intersection.

This is `Crystalline.completedEnvelopeThickening` ([Stacks, Tag 07L4]) at the presentation
`...CechPresentation.tupleAlgHom`, which is `Crystalline.completedPolynomialEnvelopeThickening`
([Stacks, Tag 07KI]) carrying in addition the identification of its underlying divided power ring
with the completion — the identification `...CechPresentation.tupleEnvelope_ring` below needs.
**It is not yet an object of `Cris(X/S)`**; see the "What is and is not proved" section of the
module docstring. -/
def CechPresentation.tupleEnvelope {n : ℕ} (α : Fin (n + 1) → Λ) :
    CompletedCrystallineThickening.{u, u, u} (interSituation c α) :=
  (completedEnvelopeThickening (interSituation c α) (P.tupleAlgHom hP α)
    (P.surjective_tupleAlgHom hP α)).thickening

/-! ### The transition morphisms `D_{α ∘ φ} ⟶ D_α` -/

/-- **The divided power envelope of `J_α`, before `p`-adic completion.**  The ring `D_α` of
[Stacks, Tag 07MM] is its completion, `...CechPresentation.tupleEnvelope`; the transition
morphisms along the Čech faces are built here on this uncompleted envelope, because it is the
object the universal property [Stacks, Tag 07H8] speaks about. -/
def CechPresentation.tupleDividedPowerEnvelope {n : ℕ} (α : Fin (n + 1) → Λ) :
    DividedPowerEnvelope (interSituation c α).A
      (algebraMap ↥(interSituation c α).A
        (MvPolynomial (P.tupleIndex α) ↥(interSituation c α).A))
      (RingHom.ker (P.tupleAlgHom hP α).toRingHom)
      (ideal_map_le_ker_presentation (interSituation c α) (P.tupleAlgHom hP α)) :=
  polynomialDividedPowerEnvelope (interSituation c α) (P.tupleAlgHom hP α)

/-- **The transition map `P_{α ∘ φ} → P_α` is a map over the base `A = Γ(S, ⊤)`**, because it
renames variables and so fixes the constants.  This is the second hypothesis — beside
`...CechPresentation.tupleIdeal_map_le` — under which the universal property of the envelope
produces the transition morphism. -/
theorem CechPresentation.tupleRename_comp_algebraMap {m n : SimplexCategory} (φ : m ⟶ n)
    (α : Fin (n.len + 1) → Λ) :
    (P.tupleRename φ α).comp
        (algebraMap ↥(interSituation c α).A
          (MvPolynomial (P.tupleIndex fun i => α (φ.toOrderHom i))
            ↥(interSituation c α).A)) =
      algebraMap ↥(interSituation c α).A
        (MvPolynomial (P.tupleIndex α) ↥(interSituation c α).A) := by
  apply RingHom.ext
  intro r
  simp only [RingHom.comp_apply, MvPolynomial.algebraMap_eq]
  exact P.tupleRename_C φ α r

/-- **The transition morphism `D_{α ∘ φ} ⟶ D_α` of [Stacks, Tag 07MM]**, on the uncompleted
divided power envelopes: the divided power morphism over `A = Γ(S, ⊤)` which on the image of the
polynomial algebra is the inclusion of tensor factors `P_{α ∘ φ} → P_α`.

Its two inputs are `...CechPresentation.tupleIdeal_map_le`, that the inclusion carries `J_{α ∘ φ}`
into `J_α`, and `...CechPresentation.tupleRename_comp_algebraMap`, that it is a map over `A`.
Both envelopes are taken over the *same* divided power base `A`, only the target `C_α = Γ(U_α)`
moving with the tuple, so the construction is `Crystalline.envelopeIdealMap`. -/
def CechPresentation.tupleEnvelopeMap {m n : SimplexCategory} (φ : m ⟶ n)
    (α : Fin (n.len + 1) → Λ) :
    {q : DividedPowers.DPMorphism
        (P.tupleDividedPowerEnvelope hP fun i => α (φ.toOrderHom i)).object.dividedPowers
        (P.tupleDividedPowerEnvelope hP α).object.dividedPowers //
      q.comp (P.tupleDividedPowerEnvelope hP fun i => α (φ.toOrderHom i)).structureMap =
        (P.tupleDividedPowerEnvelope hP α).structureMap} :=
  envelopeIdealMap (P.tupleDividedPowerEnvelope hP fun i => α (φ.toOrderHom i))
    (P.tupleDividedPowerEnvelope hP α) (P.tupleRename φ α) (P.tupleIdeal_map_le φ α)
    (P.tupleRename_comp_algebraMap φ α)

/-- **The transition morphism is the inclusion of tensor factors on the image of `P_{α ∘ φ}`.**
With `Crystalline.eq_envelopeIdealMap` this determines it, and that is what makes the family
strictly functorial below. -/
theorem CechPresentation.tupleEnvelopeMap_algebraMap {m n : SimplexCategory} (φ : m ⟶ n)
    (α : Fin (n.len + 1) → Λ)
    (x : MvPolynomial (P.tupleIndex fun i => α (φ.toOrderHom i)) ↥(interSituation c α).A) :
    (P.tupleEnvelopeMap hP φ α).1.toRingHom
        ((P.tupleDividedPowerEnvelope hP fun i =>
          α (φ.toOrderHom i)).algebraMap.toRingHom x) =
      (P.tupleDividedPowerEnvelope hP α).algebraMap.toRingHom (P.tupleRename φ α x) :=
  envelopeIdealMap_algebraMap (P.tupleDividedPowerEnvelope hP fun i => α (φ.toOrderHom i))
    (P.tupleDividedPowerEnvelope hP α) (P.tupleRename φ α) (P.tupleIdeal_map_le φ α)
    (P.tupleRename_comp_algebraMap φ α) x

/-- The transition morphism is a morphism over the base `A`, read on elements. -/
theorem CechPresentation.tupleEnvelopeMap_structureMap {m n : SimplexCategory} (φ : m ⟶ n)
    (α : Fin (n.len + 1) → Λ) (z : ↥(interSituation c α).A) :
    (P.tupleEnvelopeMap hP φ α).1.toRingHom
        ((P.tupleDividedPowerEnvelope hP fun i =>
          α (φ.toOrderHom i)).structureMap.toRingHom z) =
      (P.tupleDividedPowerEnvelope hP α).structureMap.toRingHom z :=
  envelopeIdealMap_structureMap (P.tupleDividedPowerEnvelope hP fun i => α (φ.toOrderHom i))
    (P.tupleDividedPowerEnvelope hP α) (P.tupleRename φ α) (P.tupleIdeal_map_le φ α)
    (P.tupleRename_comp_algebraMap φ α) z

/-- **The transition morphism along an identity is the identity.**  This is `map_id` of a
`...SmallSite.CechSystem`, on the envelopes: an *equation*, not a coherence isomorphism, because
`...CechPresentation.tupleRename_id` is one and the envelope's universal property is a genuine
`Equiv`. -/
theorem CechPresentation.tupleEnvelopeMap_id (n : SimplexCategory) (α : Fin (n.len + 1) → Λ) :
    (P.tupleEnvelopeMap hP (𝟙 n) α).1 =
      DividedPowers.DPMorphism.id (P.tupleDividedPowerEnvelope hP α).object.dividedPowers := by
  refine (eq_envelopeIdealMap (P.tupleDividedPowerEnvelope hP α)
    (P.tupleDividedPowerEnvelope hP α) (P.tupleRename (𝟙 n) α) (P.tupleIdeal_map_le (𝟙 n) α)
    (P.tupleRename_comp_algebraMap (𝟙 n) α) _ ?_ ?_).symm
  · apply DividedPowers.DPMorphism.ext
    funext z
    rfl
  · intro x
    show (P.tupleDividedPowerEnvelope hP α).algebraMap.toRingHom x =
      (P.tupleDividedPowerEnvelope hP α).algebraMap.toRingHom (P.tupleRename (𝟙 n) α x)
    rw [RingHom.congr_fun (P.tupleRename_id n α) x]
    rfl

/-- **The transition morphisms compose**, contravariantly in the simplex category.  This is
`map_comp` of a `...SmallSite.CechSystem`, on the envelopes. -/
theorem CechPresentation.tupleEnvelopeMap_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (α : Fin (n.len + 1) → Λ) :
    (P.tupleEnvelopeMap hP (ψ ≫ φ) α).1 =
      (P.tupleEnvelopeMap hP φ α).1.comp
        (P.tupleEnvelopeMap hP ψ fun j => α (φ.toOrderHom j)).1 := by
  refine (eq_envelopeIdealMap
    (P.tupleDividedPowerEnvelope hP fun i => α ((ψ ≫ φ).toOrderHom i))
    (P.tupleDividedPowerEnvelope hP α) (P.tupleRename (ψ ≫ φ) α)
    (P.tupleIdeal_map_le (ψ ≫ φ) α) (P.tupleRename_comp_algebraMap (ψ ≫ φ) α) _ ?_ ?_).symm
  · apply DividedPowers.DPMorphism.ext
    funext z
    exact (congrArg (P.tupleEnvelopeMap hP φ α).1.toRingHom
      (P.tupleEnvelopeMap_structureMap hP ψ (fun j => α (φ.toOrderHom j)) z)).trans
      (P.tupleEnvelopeMap_structureMap hP φ α z)
  · intro x
    refine (congrArg (P.tupleEnvelopeMap hP φ α).1.toRingHom
      (P.tupleEnvelopeMap_algebraMap hP ψ (fun j => α (φ.toOrderHom j)) x)).trans
      ((P.tupleEnvelopeMap_algebraMap hP φ α _).trans ?_)
    exact congrArg _ (RingHom.congr_fun (P.tupleRename_comp ψ φ α) x).symm

/-! ### The transitions of the completed envelopes -/

/-- **The divided power ring `(D_α, J̄_α, γ̄_α)` of [Stacks, Tag 07MM]**: the `p`-adic completion
of `...CechPresentation.tupleDividedPowerEnvelope`, with its completed divided power ideal and
the extension of the divided powers to it.  This is the underlying divided power ring of
`...CechPresentation.tupleEnvelope`, by `Crystalline.CompletedEnvelopeThickening.ring_eq`. -/
def CechPresentation.tupleCompletedEnvelopeRing {n : ℕ} (α : Fin (n + 1) → Λ) :
    DividedPowerRing.{u} :=
  completedEnvelopeDPRing (interSituation c α) (P.tupleAlgHom hP α)
    (P.surjective_tupleAlgHom hP α)
    (completedEnvelopeThickening (interSituation c α) (P.tupleAlgHom hP α)
      (P.surjective_tupleAlgHom hP α)).hp

/-- **The ring of `...CechPresentation.tupleEnvelope` is that completion**, so the morphisms below
really are morphisms of the objects of `Cris^∧(C_α/A)` built above.  This is
`Crystalline.CompletedEnvelopeThickening.ring_eq` at the presentation of a Čech intersection. -/
theorem CechPresentation.tupleEnvelope_ring {n : ℕ} (α : Fin (n + 1) → Λ) :
    (P.tupleEnvelope hP α).ring = P.tupleCompletedEnvelopeRing hP α :=
  (completedEnvelopeThickening (interSituation c α) (P.tupleAlgHom hP α)
    (P.surjective_tupleAlgHom hP α)).ring_eq

/-- **The transition morphism `D_{α ∘ φ} ⟶ D_α` on the completed envelopes**, which is the one
[Stacks, Tag 07MM] uses: the `p`-adic completion of
`...CechPresentation.tupleEnvelopeMap`, a divided power morphism for the completed divided powers
by `Crystalline.adicCompletionRingMap_isDPMorphism`. -/
def CechPresentation.tupleCompletedEnvelopeMap {m n : SimplexCategory} (φ : m ⟶ n)
    (α : Fin (n.len + 1) → Λ) :
    DividedPowers.DPMorphism
      (P.tupleCompletedEnvelopeRing hP fun i => α (φ.toOrderHom i)).dividedPowers
      (P.tupleCompletedEnvelopeRing hP α).dividedPowers :=
  DividedPowers.DPMorphism.mk'
    (adicCompletionRingMap_isDPMorphism
      (P.tupleDividedPowerEnvelope hP fun i => α (φ.toOrderHom i)).object.dividedPowers
      (P.tupleDividedPowerEnvelope hP α).object.dividedPowers S.p _ _
      (P.tupleEnvelopeMap hP φ α).1)

/-- **The completed transition morphism along an identity is the identity.** -/
theorem CechPresentation.tupleCompletedEnvelopeMap_id (n : SimplexCategory)
    (α : Fin (n.len + 1) → Λ) :
    P.tupleCompletedEnvelopeMap hP (𝟙 n) α =
      DividedPowers.DPMorphism.id (P.tupleCompletedEnvelopeRing hP α).dividedPowers := by
  have hq : (P.tupleEnvelopeMap hP (𝟙 n) α).1.toRingHom =
      RingHom.id (P.tupleDividedPowerEnvelope hP α).object :=
    congrArg DividedPowers.DPMorphism.toRingHom (P.tupleEnvelopeMap_id hP n α)
  have h := (congrArg (fun s => adicCompletionRingMap s (map_pAdicIdeal_le S.p s)) hq).trans
    (adicCompletionRingMap_id (R := (P.tupleDividedPowerEnvelope hP α).object) S.p)
  exact DividedPowers.DPMorphism.ext (congrArg DFunLike.coe h)

/-- **The completed transition morphisms compose**, contravariantly in the simplex category. -/
theorem CechPresentation.tupleCompletedEnvelopeMap_comp {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n) (α : Fin (n.len + 1) → Λ) :
    P.tupleCompletedEnvelopeMap hP (ψ ≫ φ) α =
      (P.tupleCompletedEnvelopeMap hP φ α).comp
        (P.tupleCompletedEnvelopeMap hP ψ fun j => α (φ.toOrderHom j)) := by
  have hq : (P.tupleEnvelopeMap hP (ψ ≫ φ) α).1.toRingHom =
      ((P.tupleEnvelopeMap hP φ α).1.toRingHom).comp
        ((P.tupleEnvelopeMap hP ψ fun j => α (φ.toOrderHom j)).1.toRingHom) :=
    congrArg DividedPowers.DPMorphism.toRingHom (P.tupleEnvelopeMap_comp hP ψ φ α)
  have h := (congrArg (fun s => adicCompletionRingMap s (map_pAdicIdeal_le S.p s)) hq).trans
    (adicCompletionRingMap_comp S.p
      (P.tupleEnvelopeMap hP ψ fun j => α (φ.toOrderHom j)).1.toRingHom
      (P.tupleEnvelopeMap hP φ α).1.toRingHom)
  exact DividedPowers.DPMorphism.ext (congrArg DFunLike.coe h)

end Envelope

end Crystalline.GlobalCrystallineSituation.SmallSite

end
