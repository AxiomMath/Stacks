module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Smooth.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerEnvelope
public import StacksFrontier.RingTheory.DividedPowers.Nilpotent
public import StacksFrontier.RingTheory.Smooth.Lifting

/-!
# The strong lifting property and maps out of a divided power envelope

In Situation [Stacks, Tag 07MD] let `A → P' → C` be ring maps with `P' → C` surjective with
kernel `J'`, and let `D_{P', γ}(J')` be the divided power envelope of `J'` relative to
`(A, I, γ)`.  This module proves the lifting step on which the retract construction of
[Stacks, Tag 07L5] rests: if `(B, K, δ)` is a divided power `A`-algebra in which `p` is
nilpotent, if `L ⊆ K` is an ideal of `B`, and if an `A`-algebra map `P' → B ⧸ L` is given whose
further reduction to `B ⧸ K` is the structural map coming from `P' → C`, then that map lifts to
a homomorphism of divided power `A`-algebras `D_{P', γ}(J') → (B, K, δ)`, compatible with the
maps to `C`.

Two ingredients do the work.  The divided power ideal `K` is locally nilpotent, because `p` is
nilpotent in `B` — this is [Stacks, Tag 07GR] — hence so is the sub-ideal `L`; and `A → P'`
lifts along `B → B ⧸ L` because it has the strong lifting property of [Stacks, Tag 07K4].  The
lifted ring map carries `J'` into `K`, because its reduction to `B ⧸ K` kills `J'`, so the
universal property of the envelope turns it into a divided power morphism.

Smoothness of `A → P'` is used *only* through the strong lifting property.  The statement is
therefore proved with that property as a hypothesis, as
`Crystalline.exists_dpMorphism_envelope_of_hasStrongLiftingProperty`, and the smooth case is
deduced from it, as `Crystalline.exists_dpMorphism_envelope_of_smooth`.

## Main definitions

* `Algebra.HasStrongLiftingProperty` — the strong lifting property of [Stacks, Tag 07K4]: every
  map to a quotient by a locally nilpotent ideal lifts.  The test algebra is taken in the same
  universe as the algebra itself, which is the universe in which the property is applied below.

## Main results

* `Algebra.HasStrongLiftingProperty.of_smooth` — a smooth algebra has the strong lifting
  property; this is [Stacks, Tag 07K4] itself, restated as the property.
* `Algebra.HasStrongLiftingProperty.exists_lift_of_surjective` — the property in the form in
  which the source uses it: a lift exists along any surjection with locally nilpotent kernel,
  not only along a literal quotient map.
* `Algebra.HasStrongLiftingProperty.exists_lift_of_sq_eq_bot` — the infinitesimal lifting
  property of [Stacks, Tag 00TN] is a special case of the strong lifting property, a square zero
  ideal being locally nilpotent.
* `Crystalline.locallyNilpotent_dpIdeal` — the divided power ideal of a divided power ring in
  which `p` is nilpotent is locally nilpotent, by [Stacks, Tag 07GR].
* `Crystalline.exists_dpMorphism_envelope_of_hasStrongLiftingProperty` — the lifting step, with
  the strong lifting property as hypothesis.
* `Crystalline.exists_dpMorphism_envelope_of_smooth` — the lifting step for a smooth
  presentation, which is how [Stacks, Tag 07L5] uses it.

## Relation to [Stacks, Tag 07L5] and [Stacks, Tag 07L6]

[Stacks, Tag 07L5] has two assertions.  The first is the *retract*: for a smooth presentation
`A → P' → C` with kernel `J'` and `D'` the `p`-adic completion of `D_{P', γ}(J')`, there are a
polynomial presentation `A → P → C` and homomorphisms of divided power `A`-algebras
`a : D → D'`, `b : D' → D` compatible with the maps to `C` and satisfying `a ∘ b = id_{D'}`.
The second is that `a` and `b` induce an equivalence between the categories of pairs `(M, ∇)`
satisfying [Stacks, Tag 07JB], [Stacks, Tag 07JC], [Stacks, Tag 07JD] and [Stacks, Tag 07JE]
over `D` and over `D'`.  Both are proved in
`StacksFrontier/AlgebraicGeometry/Crystalline/EnvelopeRetractEquivalence.lean`.

Of the first assertion, what is proved *here* is the step the source writes as "the kernel of
`D_e → D'_e` is locally nilpotent, hence by [Stacks, Tag 07K4] we can find a lift
`β_e : P' → D_e` of the map `P' → D'_e`", together with the step that follows it, "by the
universal property of the divided power envelope we obtain a map `D_{P', γ}(J') → D`".  That is
`exists_dpMorphism_envelope_of_smooth`, stated for an arbitrary divided power `A`-algebra `B` in
which `p` is nilpotent and an arbitrary ideal `L` of `B` contained in its divided power ideal,
so that `B = D_e` and `L = ker(D_e → D'_e)` is one instance of it.  The *compatible* choice of
the `β_e` is carried out in `EnvelopeRetract.lean`: the lifts are chosen successively along the
surjections `D_{e + i + 1} → D_{e + i} ×_{D'_{e + i}} D'_{e + i + 1}`, whose kernels are square
zero.  A square zero ideal is locally nilpotent, so each of those lifts is again an instance of
the strong lifting property — that is `Algebra.HasStrongLiftingProperty.exists_lift_of_sq_eq_bot`
— and nothing in the construction needs smoothness beyond it.

[Stacks, Remark 60.17.6, Tag 07L6] rests on exactly that observation: "The equivalence of
Proposition [Stacks, Tag 07JH] holds if we start with a surjection `P → C` where `P/A` satisfies
the strong lifting property of Algebra, Lemma [Stacks, Tag 07K4].  To prove this we can argue as
in the proof of Lemma [Stacks, Tag 07L5]."  The remark is proved, by that argument, as
`...SmallSite.exists_presentation_retract_crystalPairEquivalence_of_hasStrongLiftingProperty` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CrystalStrongLiftingPairs.lean`: the retract
for a presentation with the strong lifting property is
`Crystalline.exists_completedEnvelopeRetract_of_hasStrongLiftingProperty`, and since `P` need not
be of finite type the polynomial algebra mapping onto it has in general infinitely many
variables, for which the equivalence of pairs along the retract is
`Crystalline.CoordinateDual.retractPairEquivalence`.  The lifting step of this file, with the
strong lifting property as a hypothesis, is
`exists_dpMorphism_envelope_of_hasStrongLiftingProperty`.

## Implementation notes

The strong lifting property is a `Prop`-valued definition rather than a class: it is a property
of a ring map used as a hypothesis, and making it a class would make `of_smooth` an instance
competing with smoothness itself during synthesis.  The test algebra ranges over one universe,
the universe of the algebra; this is the universe in which the divided power rings of this
chapter live, and a universe-restricted hypothesis only strengthens the theorems that assume it.

The map out of the envelope is produced from the `homEquiv` field of
`Crystalline.DividedPowerEnvelope` and characterized through its `homEquiv_apply` field, which
is the only route available: the envelope is specified by its universal property and not
constructed, and the convenience lemmas describing the induced maps are `private` to the file
defining it.

## References

* [Stacks Project, Tag 07GR](https://stacks.math.columbia.edu/tag/07GR)
* [Stacks Project, Tag 07K4](https://stacks.math.columbia.edu/tag/07K4)
* [Stacks Project, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
* [Stacks Project, Tag 07L6](https://stacks.math.columbia.edu/tag/07L6)
-/

@[expose] public section

universe u v

namespace Algebra

/-- **The strong lifting property of [Stacks, Tag 07K4].**  An `R`-algebra `S` has it when for
every `R`-algebra `B` and every locally nilpotent ideal `L ⊆ B`, each `R`-algebra map
`S → B ⧸ L` lifts to an `R`-algebra map `S → B`.

Smooth algebras have this property, which is the content of [Stacks, Tag 07K4]; the point of
isolating it is that the lifting arguments of the crystalline chapter use smoothness only
through it. -/
def HasStrongLiftingProperty (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] : Prop :=
  ∀ (B : Type v) [CommRing B] [Algebra R B] (L : Ideal B), L.IsLocallyNilpotent →
    ∀ g : S →ₐ[R] B ⧸ L, ∃ f : S →ₐ[R] B, (Ideal.Quotient.mkₐ R L).comp f = g

namespace HasStrongLiftingProperty

/-- A smooth algebra has the strong lifting property.  This is [Stacks, Tag 07K4], restated as
the property. -/
theorem of_smooth (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] : HasStrongLiftingProperty R S :=
  fun B _ _ L hL g => main_theorem07K4 R S B L hL g

/-- The strong lifting property in the shape in which the crystalline chapter uses it: a lift
exists along any surjection with locally nilpotent kernel, not only along a quotient map. -/
theorem exists_lift_of_surjective {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (h : HasStrongLiftingProperty R S) {B B' : Type v} [CommRing B] [CommRing B']
    [Algebra R B] [Algebra R B'] (φ : B →ₐ[R] B') (hφ : Function.Surjective φ)
    (hker : (RingHom.ker (φ : B →+* B')).IsLocallyNilpotent) (g : S →ₐ[R] B') :
    ∃ f : S →ₐ[R] B, φ.comp f = g := by
  classical
  obtain ⟨f, hf⟩ := h B (RingHom.ker (φ : B →+* B')) hker
    ((Ideal.quotientKerAlgEquivOfSurjective hφ).symm.toAlgHom.comp g)
  refine ⟨f, ?_⟩
  ext s
  have h1 : Ideal.Quotient.mk (RingHom.ker (φ : B →+* B')) (f s) =
      (Ideal.quotientKerAlgEquivOfSurjective hφ).symm (g s) := AlgHom.congr_fun hf s
  have h2 : Ideal.quotientKerAlgEquivOfSurjective hφ
      (Ideal.Quotient.mk (RingHom.ker (φ : B →+* B')) (f s)) = φ (f s) :=
    Ideal.quotientKerAlgEquivOfSurjective_mk hφ (f s)
  rw [h1] at h2
  simpa using h2.symm

/-- The infinitesimal lifting property of [Stacks, Tag 00TN] is a special case of the strong
lifting property, because a square zero ideal is locally nilpotent.

This is what licenses the argument of [Stacks, Remark 60.17.6, Tag 07L6]: the proof of
[Stacks, Tag 07L5] cites [Stacks, Tag 00TN] for its successive lifts along square zero kernels,
and those lifts are therefore themselves instances of [Stacks, Tag 07K4], not a second use of
smoothness. -/
theorem exists_lift_of_sq_eq_bot {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (h : HasStrongLiftingProperty R S) {B : Type v} [CommRing B] [Algebra R B]
    (L : Ideal B) (hL : L ^ 2 = ⊥) (g : S →ₐ[R] B ⧸ L) :
    ∃ f : S →ₐ[R] B, (Ideal.Quotient.mkₐ R L).comp f = g :=
  h B L (fun x hx => Ideal.Nilpotent.locallyNilpotent (I := L) ⟨2, hL⟩ x hx) g

end HasStrongLiftingProperty

end Algebra

namespace Crystalline

/-- The divided power ideal of a divided power ring in which `p` is nilpotent is locally
nilpotent.  This is one direction of [Stacks, Tag 07GR]. -/
theorem locallyNilpotent_dpIdeal {p : ℕ} (hp : p.Prime) (B : DividedPowerRing.{u})
    (hpB : IsNilpotent (p : B)) : B.ideal.IsLocallyNilpotent := by
  have hq : IsNilpotent ((p : ℕ) : B ⧸ B.ideal) := by
    obtain ⟨n, hn⟩ := hpB
    refine ⟨n, ?_⟩
    rw [← map_natCast (Ideal.Quotient.mk B.ideal) p, ← map_pow, hn, map_zero]
  intro x hx
  exact (DividedPowers.locallyNilpotent_iff_isNilpotent_natCast hp B.dividedPowers hq).mpr
    hpB x hx

/-- **The lifting step of the construction in the proof of [Stacks, Tag 07L5], with smoothness
replaced by the strong lifting property of [Stacks, Tag 07K4].**

Let `(A, I, γ)` be a divided power ring, let `P'` be an `A`-algebra with the strong lifting
property, let `π : P' → C` be a ring map whose kernel contains the image of `I`, and let `D` be
the divided power envelope of `ker π`.  Let `(B, K, δ)` be a divided power ring, `aB : A → B` a
divided power morphism, and suppose `p` is nilpotent in `B` for a prime `p`.  Given an ideal
`L ⊆ K` and a ring map `g : P' → B ⧸ L` which restricts to `aB` on `A` and whose further
reduction to `B ⧸ K` is induced by `π`, there is a divided power morphism `b : D → (B, K, δ)`
over `A` whose restriction along `P' → D`, read modulo `L`, is `g`, and which is compatible with
the maps to `C`: its restriction read modulo `K` is induced by `π`.

Taking `B = D_e` and `L = ker(D_e → D'_e)` this is the step of the source's proof which produces
`β_e : P' → D_e` lifting `P' → D'_e` and then the map `D_{P', γ}(J') → D_e`; it is the step on
which the argument of [Stacks, Remark 60.17.6, Tag 07L6] rests, proved as
`...SmallSite.exists_presentation_retract_crystalPairEquivalence_of_hasStrongLiftingProperty`. -/
theorem exists_dpMorphism_envelope_of_hasStrongLiftingProperty {p : ℕ} (hp : p.Prime)
    (A : DividedPowerRing.{u}) {P' : Type u} [CommRing P'] [Algebra A P']
    {C : Type v} [CommRing C] (π : P' →+* C)
    {hJ : A.ideal.map (algebraMap A P') ≤ RingHom.ker π}
    (D : DividedPowerEnvelope A (algebraMap A P') (RingHom.ker π) hJ)
    (hlift : Algebra.HasStrongLiftingProperty A P')
    (B : DividedPowerRing.{u}) (hpB : IsNilpotent (p : B))
    (aB : DividedPowers.DPMorphism A.dividedPowers B.dividedPowers)
    {L : Ideal B} (hL : L ≤ B.ideal) (c : C →+* B ⧸ B.ideal) (g : P' →+* B ⧸ L)
    (hgA : g.comp (algebraMap A P') = (Ideal.Quotient.mk L).comp aB.toRingHom)
    (hgC : (Ideal.Quotient.factor hL).comp g = c.comp π) :
    ∃ b : DividedPowers.DPMorphism D.object.dividedPowers B.dividedPowers,
      b.comp D.structureMap = aB ∧
        (Ideal.Quotient.mk L).comp (b.toRingHom.comp D.algebraMap.toRingHom) = g ∧
        (Ideal.Quotient.mk B.ideal).comp (b.toRingHom.comp D.algebraMap.toRingHom) =
          c.comp π := by
  classical
  -- The divided power ideal of `B` is locally nilpotent by [Stacks, Tag 07GR], hence so is `L`.
  have hBnil := locallyNilpotent_dpIdeal hp B hpB
  have hLnil : L.IsLocallyNilpotent := fun x hx => hBnil x (hL hx)
  -- Lift `g` along `B → B ⧸ L` using the strong lifting property.
  let _ : Algebra (A : Type u) (B : Type u) := aB.toRingHom.toAlgebra
  let gA : P' →ₐ[(A : Type u)] (B : Type u) ⧸ L :=
    { g with commutes' := fun r => RingHom.congr_fun hgA r }
  obtain ⟨β, hβ⟩ := hlift (B : Type u) L hLnil gA
  have hβg : (Ideal.Quotient.mk L).comp β.toRingHom = g :=
    RingHom.ext fun x => AlgHom.congr_fun hβ x
  -- Reduction modulo `L` of an element lying over `g x` is, modulo `B.ideal`, `c (π x)`.
  have hred : ∀ (y : B) (x : P'), Ideal.Quotient.mk L y = g x →
      Ideal.Quotient.mk B.ideal y = c (π x) := fun y x hy => by
    rw [← Ideal.Quotient.factor_mk hL, hy]
    exact RingHom.congr_fun hgC x
  -- The lift carries `ker π` into the divided power ideal of `B`.
  have hβJ : ∀ x ∈ RingHom.ker π, β x ∈ B.ideal := fun x hx => by
    rw [← Ideal.Quotient.eq_zero_iff_mem,
      hred (β x) x (RingHom.congr_fun hβg x), RingHom.mem_ker.mp hx, map_zero]
  have hmap : Ideal.map β.toRingHom (RingHom.ker π) ≤ B.ideal :=
    Ideal.map_le_iff_le_comap.mpr fun x hx => hβJ x hx
  -- Feed the lift to the universal property of the envelope.
  let pr : IdealPair.Hom (RingHom.ker π) B.ideal :=
    IdealPair.Hom.ofRingHom β.toRingHom hmap
  have hpr : IdealPair.Hom.comp pr
      (IdealPair.Hom.ofRingHom (algebraMap (A : Type u) P') hJ) =
      IdealPair.Hom.ofDPMorphism aB :=
    IdealPair.Hom.ext_toRingHom _ _ (RingHom.ext β.commutes)
  let bData := (D.homEquiv B aB).symm ⟨pr, hpr⟩
  have halg : bData.1.toRingHom.comp D.algebraMap.toRingHom = β.toRingHom := by
    have hpair : pr = IdealPair.Hom.comp (IdealPair.Hom.ofDPMorphism bData.1) D.algebraMap :=
      (congrArg Subtype.val ((D.homEquiv B aB).apply_symm_apply ⟨pr, hpr⟩)).symm.trans
        (D.homEquiv_apply B aB bData)
    have hr := congrArg IdealPair.Hom.toRingHom hpair.symm
    change bData.1.toRingHom.comp D.algebraMap.toRingHom = pr.toRingHom at hr
    simpa only [pr, IdealPair.Hom.ofRingHom] using hr
  have key : (Ideal.Quotient.mk L).comp (bData.1.toRingHom.comp D.algebraMap.toRingHom) = g := by
    rw [halg, hβg]
  -- Compatibility with the maps to `C` is the further reduction of `key` modulo `B.ideal`.
  refine ⟨bData.1, bData.2, key, ?_⟩
  exact RingHom.ext fun x => hred _ x (RingHom.congr_fun key x)

/-- **The lifting step of the construction in the proof of [Stacks, Tag 07L5].**

For a smooth `A`-algebra `P'` and a ring map `π : P' → C` whose kernel contains the image of the
divided power ideal, every divided power ring `(B, K, δ)` over `A` in which `p` is nilpotent
receives a divided power morphism from the envelope `D` of `ker π`, compatible with the maps to
`C` and lifting any ring map `P' → B ⧸ L` over `A` which is compatible with `π` modulo `K`, for
any ideal `L ⊆ K`.

Smoothness enters only through
`Algebra.HasStrongLiftingProperty.of_smooth`: this is the smooth instance of
`exists_dpMorphism_envelope_of_hasStrongLiftingProperty`.

The retract of [Stacks, Tag 07L5] is proved, at every finite level of the `p`-adic tower, by
`Crystalline.exists_compatible_levelRetract` of
`StacksFrontier/AlgebraicGeometry/Crystalline/EnvelopeRetract.lean`, which subsumes this lifting
step. -/
theorem exists_dpMorphism_envelope_of_smooth {p : ℕ} (hp : p.Prime)
    (A : DividedPowerRing.{u}) {P' : Type u} [CommRing P'] [Algebra A P']
    [Algebra.Smooth (A : Type u) P'] {C : Type v} [CommRing C] (π : P' →+* C)
    {hJ : A.ideal.map (algebraMap A P') ≤ RingHom.ker π}
    (D : DividedPowerEnvelope A (algebraMap A P') (RingHom.ker π) hJ)
    (B : DividedPowerRing.{u}) (hpB : IsNilpotent (p : B))
    (aB : DividedPowers.DPMorphism A.dividedPowers B.dividedPowers)
    {L : Ideal B} (hL : L ≤ B.ideal) (c : C →+* B ⧸ B.ideal) (g : P' →+* B ⧸ L)
    (hgA : g.comp (algebraMap A P') = (Ideal.Quotient.mk L).comp aB.toRingHom)
    (hgC : (Ideal.Quotient.factor hL).comp g = c.comp π) :
    ∃ b : DividedPowers.DPMorphism D.object.dividedPowers B.dividedPowers,
      b.comp D.structureMap = aB ∧
        (Ideal.Quotient.mk L).comp (b.toRingHom.comp D.algebraMap.toRingHom) = g ∧
        (Ideal.Quotient.mk B.ideal).comp (b.toRingHom.comp D.algebraMap.toRingHom) =
          c.comp π :=
  exists_dpMorphism_envelope_of_hasStrongLiftingProperty hp A π D
    (Algebra.HasStrongLiftingProperty.of_smooth _ _) B hpB aB hL c g hgA hgC

end Crystalline

end
