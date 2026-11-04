module

public import StacksFrontier.RingTheory.Dualizing.FlatLocalGorenstein
public import StacksFrontier.RingTheory.Dualizing.GorensteinFieldExtension
public import StacksFrontier.RingTheory.Dualizing.GorensteinFormalFibres
public import StacksFrontier.RingTheory.Dualizing.GorensteinLocalization
public import StacksFrontier.RingTheory.Flat.NormalFibres
public import StacksFrontier.RingTheory.FormalFibres.RingMapProperty

/-!
# Gorensteinness as a property of formal fibres

[Stacks, Tag 0BJN] asserts that the five properties (A), (B), (C), (D), (E) of
[Stacks, Tag 0BIR] hold for the property `P(k → R) = `"`R` is a Gorenstein ring". For a property
`P` of ring maps from a field to a Noetherian ring these read:

* (A) if `P(k → R)` and `k'/k` is a finitely generated field extension, then
  `P(k' → R ⊗_k k')`;
* (B) `P(k → R)` holds if and only if `P(k → R_𝔭)` holds for every prime `𝔭` of `R`;
* (C) for flat maps `A → B → C` of Noetherian rings with `B → C` regular, if the fibres of
  `A → B` have `P` then so do the fibres of `A → C`;
* (D) for flat maps `A → B → C` of Noetherian rings with `B → C` faithfully flat, if the fibres
  of `A → C` have `P` then so do the fibres of `A → B`;
* (E) if `k'/k` is separable algebraic and `k → k' → R`, then `P(k → R)` implies `P(k' → R)`.

This file proves (B), (C), (D) and (E) for Gorensteinness and conjoins them with clause (A),
`Dualizing.isGorensteinRing_tensorProduct_of_essFiniteType_fieldExtension`.

## Main results

* `Dualizing.isGorensteinLocalRing_of_isGorensteinRing` — a Noetherian local ring that is
  Gorenstein as a ring is a Gorenstein local ring.
* `Dualizing.isGorensteinRing_iff_forall_isGorensteinRing_localization` — Gorensteinness is
  detected by the localizations at primes.
* `Dualizing.isGorensteinRing_of_faithfullyFlat` — Gorensteinness descends along a faithfully
  flat map of Noetherian rings.
* `Dualizing.nonempty_ringEquiv_localization_fiber` — the localization of the fibre ring
  `κ(𝔭) ⊗_R S` at a prime contracting to `𝔮` is the closed fibre of `R_𝔭 → S_𝔮`.
* `Dualizing.isGorensteinRing_of_flat_of_isGorensteinRing_fiber` — the Gorenstein analogue of
  [Stacks, Tag 0339]: Gorensteinness ascends along a flat map with Gorenstein fibres.
* `Dualizing.gorensteinProperty_localization` — **[Stacks, Tag 0BJN]**, clause (B).
* `Dualizing.gorensteinProperty_regularAscent` — **[Stacks, Tag 0BJN]**, clause (C).
* `Dualizing.gorensteinProperty_faithfullyFlatDescent` — **[Stacks, Tag 0BJN]**, clause (D).
* `Dualizing.gorensteinProperty_groundFieldExtension` — **[Stacks, Tag 0BJN]**, clause (E).
* `Dualizing.gorensteinProperty_satisfies_formalFiberAxioms` — clauses (A)--(E) conjoined, for a
  `RingMapProperty` identified with Gorensteinness of the target.
* `Dualizing.gorensteinTarget_satisfies_formalFiberAxioms` — **the whole of
  [Stacks, Tag 0BJN]**: the same five clauses at the concrete property
  `Dualizing.gorensteinTarget`, with no identification hypothesis.

## References

* [Stacks Project, Tag 0BJN](https://stacks.math.columbia.edu/tag/0BJN)
* [Stacks Project, Tag 0BIR](https://stacks.math.columbia.edu/tag/0BIR)
* [Stacks Project, Tag 0BJL](https://stacks.math.columbia.edu/tag/0BJL)
* [Stacks Project, Tag 0BJ9](https://stacks.math.columbia.edu/tag/0BJ9)
* [Stacks Project, Tag 0339](https://stacks.math.columbia.edu/tag/0339)
* [Stacks Project, Tag 0AWX](https://stacks.math.columbia.edu/tag/0AWX)
* [Stacks Project, Tag 0DW4](https://stacks.math.columbia.edu/tag/0DW4)
-/

@[expose] public section

open CategoryTheory IsLocalRing

open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **A Noetherian local ring which is Gorenstein as a ring is a Gorenstein local ring.** -/
public theorem isGorensteinLocalRing_of_isGorensteinRing (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (h : IsGorensteinRing R) : IsGorensteinLocalRing R := by
  let e : R ≃ₐ[R] (Localization.AtPrime (maximalIdeal R)) :=
    IsLocalization.atUnits R (maximalIdeal R).primeCompl (fun x ↦ by simpa using! fun a ↦ a)
  exact isGorensteinLocalRing_of_ringEquiv e.toRingEquiv (h (maximalIdeal R))

/-- **Gorensteinness is detected by the localizations at primes.** A Noetherian ring is
Gorenstein if and only if each of its localizations at a prime ideal is a Gorenstein ring. -/
public theorem isGorensteinRing_iff_forall_isGorensteinRing_localization (R : Type u)
    [CommRing R] [IsNoetherianRing R] :
    (∀ p : PrimeSpectrum R, IsGorensteinRing (Localization.AtPrime p.asIdeal)) ↔
      IsGorensteinRing R := by
  refine ⟨fun h p hp => ?_, fun h p => ?_⟩
  · exact isGorensteinLocalRing_of_isGorensteinRing (Localization.AtPrime p) (h ⟨p, hp⟩)
  · exact isGorensteinRing_of_isLocalization h p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal)

/-- For a flat map `R → S` of rings with `S` Noetherian and a prime `q` of `S`, the localization
`S_q` is Noetherian and `R_{q ∩ R} → S_q` is a flat local homomorphism. -/
private theorem noetherian_localHom_flat_localization (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing S] [Module.Flat R S] (q : Ideal S) [q.IsPrime] :
    IsNoetherianRing (Localization.AtPrime q) ∧
      IsLocalHom (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q)) ∧
      Module.Flat (Localization.AtPrime (q.under R)) (Localization.AtPrime q) :=
  ⟨IsLocalization.isNoetherianRing q.primeCompl _ inferInstance,
    Localization.isLocalHom_localRingHom _ _ _ _,
    (Module.flat_iff_of_isLocalization (Localization.AtPrime (q.under R))
      (q.under R).primeCompl _).mpr (Module.Flat.trans R S (Localization.AtPrime q))⟩

/-- **Gorensteinness descends along a faithfully flat map of Noetherian rings.** If `R → S` is
faithfully flat and `S` is Gorenstein, then `R` is Gorenstein. -/
public theorem isGorensteinRing_of_faithfullyFlat {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    (hS : IsGorensteinRing S) : IsGorensteinRing R := by
  intro q hq
  obtain ⟨Q, hQ⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := S) ⟨q, hq⟩
  have hQeq : Q.asIdeal.under R = q := congrArg PrimeSpectrum.asIdeal hQ
  subst hQeq
  obtain ⟨_, _, _⟩ := noetherian_localHom_flat_localization R S Q.asIdeal
  exact ((isGorensteinLocalRing_iff_of_flat (Localization.AtPrime (Q.asIdeal.under R))
    (Localization.AtPrime Q.asIdeal)).mp (hS Q.asIdeal)).1

/-- **The closed fibre of `R_𝔭 → S_𝔮` is a localization of the fibre ring `κ(𝔭) ⊗_R S`.** If `Q`
is a prime of `κ(𝔭) ⊗_R S` contracting to the prime `𝔮` of `S`, then `(κ(𝔭) ⊗_R S)_Q` is
isomorphic to `S_𝔮 ⧸ 𝔭 S_𝔮`. -/
public theorem nonempty_ringEquiv_localization_fiber {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (p : Ideal R) [p.IsPrime] (Q : Ideal (p.Fiber S)) [Q.IsPrime]
    (q : Ideal S) [q.IsPrime]
    (hq : Q.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S) = q) :
    Nonempty (Localization.AtPrime Q ≃+*
      Localization.AtPrime q ⧸
        (p.map (algebraMap R S)).map (algebraMap S (Localization.AtPrime q))) := by
  subst hq
  exact ⟨(Ideal.Fiber.algEquivAux₂ p Q).toRingEquiv⟩

/-- **Gorensteinness ascends along a flat map with Gorenstein fibres**, the Gorenstein analogue
of [Stacks, Tag 0339]: if `R → S` is a flat map of Noetherian rings, `R` is Gorenstein and every
fibre ring `κ(𝔭) ⊗_R S` is Gorenstein, then `S` is Gorenstein. -/
public theorem isGorensteinRing_of_flat_of_isGorensteinRing_fiber {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    (hR : IsGorensteinRing R)
    (hfib : ∀ (p : Ideal R) [p.IsPrime],
      letI : IsNoetherianRing (p.Fiber S) :=
        Stacks.Flatness.NormalFibreAscent.isNoetherianRing_fiber p
      IsGorensteinRing (p.Fiber S)) :
    IsGorensteinRing S := by
  intro q hq
  let : q.IsPrime := hq
  have hlo : q.LiesOver (q.under R) := ⟨rfl⟩
  obtain ⟨_, _, _⟩ := noetherian_localHom_flat_localization R S q
  set Q : Ideal ((q.under R).Fiber S) :=
    ((PrimeSpectrum.primesOverOrderIsoFiber R S (q.under R))
      ⟨q, inferInstance, inferInstance⟩).asIdeal with hQdef
  have : Q.IsPrime := inferInstance
  have hrq : Q.comap
      (Algebra.TensorProduct.includeRight : S →ₐ[R] (q.under R).Fiber S) = q := by
    rw [hQdef, ← PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply, OrderIso.symm_apply_apply]
  obtain ⟨E⟩ := nonempty_ringEquiv_localization_fiber (q.under R) Q q hrq
  have hIeq : (maximalIdeal (Localization.AtPrime (q.under R))).map
      (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q)) =
      ((q.under R).map (algebraMap R S)).map (algebraMap S (Localization.AtPrime q)) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hItop : (maximalIdeal (Localization.AtPrime (q.under R))).map
      (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q)) ≠ ⊤ :=
    (IsLocalRing.map_maximalIdeal_lt_top _).ne
  have : Nontrivial (Localization.AtPrime q ⧸
      (maximalIdeal (Localization.AtPrime (q.under R))).map
        (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q))) :=
    Ideal.Quotient.nontrivial_iff.mpr hItop
  have : IsLocalRing (Localization.AtPrime q ⧸
      (maximalIdeal (Localization.AtPrime (q.under R))).map
        (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q))) :=
    .of_surjective' _ Ideal.Quotient.mk_surjective
  let : IsNoetherianRing ((q.under R).Fiber S) :=
    Stacks.Flatness.NormalFibreAscent.isNoetherianRing_fiber (q.under R)
  let : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  refine (isGorensteinLocalRing_iff_of_flat (Localization.AtPrime (q.under R))
    (Localization.AtPrime q)).mpr ⟨hR (q.under R), ?_⟩
  exact isGorensteinLocalRing_of_ringEquiv ((Ideal.quotEquivOfEq hIeq).trans E.symm)
    (hfib (q.under R) Q)

/-- The fibre of `E → E ⊗_B C` at a prime `Q` of `E` lying over the prime `𝔮` of `B` is the
iterated fibre `κ(Q) ⊗_{κ(𝔮)} (κ(𝔮) ⊗_B C)`. -/
private noncomputable def iteratedFiberRingEquiv
    {B E C : Type*} [CommRing B] [CommRing E] [CommRing C]
    [Algebra B E] [Algebra B C] (q : Ideal B) [q.IsPrime]
    (Q : Ideal E) [Q.IsPrime] [Q.LiesOver q]
    [Algebra q.ResidueField Q.ResidueField]
    [IsScalarTower B q.ResidueField Q.ResidueField] :
    Q.Fiber (E ⊗[B] C) ≃+*
      Q.ResidueField ⊗[q.ResidueField] q.Fiber C :=
  (Algebra.TensorProduct.cancelBaseChange B E Q.ResidueField
      Q.ResidueField C).toRingEquiv.trans
    (Algebra.TensorProduct.cancelBaseChange B q.ResidueField Q.ResidueField
      Q.ResidueField C).symm.toRingEquiv

/-- **Stacks Project, Tag 0BJN, clause (B).** The property of a map from a field to a Noetherian
ring that its target is Gorenstein can be checked after localizing at every prime. -/
@[stacks 0BJN "(B)"]
public theorem gorensteinProperty_localization (P : RingMapProperty.{u, u})
    (hP : ∀ (k R : Type u) [Field k] [CommRing R] [Algebra k R] [IsNoetherianRing R],
      P (algebraMap k R) ↔ IsGorensteinRing R) :
    ∀ (k R : Type u) [Field k] [CommRing R] [Algebra k R] [IsNoetherianRing R],
      (∀ p : PrimeSpectrum R, P (algebraMap k (Localization.AtPrime p.asIdeal))) ↔
        P (algebraMap k R) := by
  intro k R _ _ _ _
  rw [hP, ← isGorensteinRing_iff_forall_isGorensteinRing_localization R]
  exact forall_congr' fun p => hP k (Localization.AtPrime p.asIdeal)

/-- **Stacks Project, Tag 0BJN, clause (C).** For flat maps `A → B → C` of Noetherian rings with
`B → C` regular, if every fibre of `A → B` is Gorenstein then so is every fibre of `A → C`. -/
@[stacks 0BJN "(C)"]
public theorem gorensteinProperty_regularAscent (P : RingMapProperty.{u, u})
    (hP : ∀ (k R : Type u) [Field k] [CommRing R] [Algebra k R] [IsNoetherianRing R],
      P (algebraMap k R) ↔ IsGorensteinRing R) :
    ∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [Module.Flat B C],
      (∀ p : PrimeSpectrum A, P (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B))) →
      (∀ q : PrimeSpectrum B,
        Algebra.IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber C)) →
      ∀ p : PrimeSpectrum A, P (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber C)) := by
  intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hAB hreg p
  let : IsNoetherianRing (p.asIdeal.Fiber B) :=
    Stacks.Flatness.NormalFibreAscent.isNoetherianRing_fiber p.asIdeal
  let D := (p.asIdeal.Fiber B) ⊗[B] C
  let e : D ≃ₐ[p.asIdeal.ResidueField] p.asIdeal.Fiber C :=
    Algebra.IsPushout.cancelBaseChangeAlg A p.asIdeal.ResidueField B (p.asIdeal.Fiber B) C
  let : IsNoetherianRing (p.asIdeal.Fiber C) :=
    Stacks.Flatness.NormalFibreAscent.isNoetherianRing_fiber p.asIdeal
  let : IsNoetherianRing D := isNoetherianRing_of_ringEquiv _ e.symm.toRingEquiv
  have : Module.Flat (p.asIdeal.Fiber B) D := inferInstance
  rw [hP]
  refine isGorensteinRing_of_ringEquiv (R := D) e.toRingEquiv ?_
  refine isGorensteinRing_of_flat_of_isGorensteinRing_fiber (R := p.asIdeal.Fiber B) (S := D)
    ((hP _ _).mp (hAB p)) ?_
  intro Q _
  let q : Ideal B := Q.comap (algebraMap B (p.asIdeal.Fiber B))
  let : q.IsPrime := inferInstance
  let : Q.LiesOver q := ⟨rfl⟩
  let : IsScalarTower q.ResidueField q.ResidueField Q.ResidueField :=
    ⟨fun x y z => mul_smul x y z⟩
  have : Algebra.IsGeometricallyRegular q.ResidueField (q.Fiber C) := hreg ⟨q, inferInstance⟩
  have hκ : Function.Bijective (algebraMap q.ResidueField Q.ResidueField) :=
    p.asIdeal.surjectiveOnStalks_residueField.baseChange'.residueFieldMap_bijective q Q rfl
  let κe : q.ResidueField ≃ₐ[q.ResidueField] Q.ResidueField :=
    AlgEquiv.ofBijective (Algebra.ofId q.ResidueField Q.ResidueField) hκ
  let Ee : (Q.ResidueField ⊗[q.ResidueField] q.Fiber C) ≃+*
      (q.ResidueField ⊗[q.ResidueField] q.Fiber C) :=
    (Algebra.TensorProduct.congr κe.symm (AlgEquiv.refl : q.Fiber C ≃ₐ[q.ResidueField]
      q.Fiber C)).toRingEquiv
  have : IsRegularRing (q.ResidueField ⊗[q.ResidueField] q.Fiber C) := inferInstance
  let : IsRegularRing (Q.ResidueField ⊗[q.ResidueField] q.Fiber C) :=
    IsRegularRing.of_ringEquiv
      (R := q.ResidueField ⊗[q.ResidueField] q.Fiber C) Ee.symm
  let Eiter : Q.Fiber D ≃+* (Q.ResidueField ⊗[q.ResidueField] q.Fiber C) :=
    iteratedFiberRingEquiv q Q
  let : CommRing (Q.Fiber D) := by
    change CommRing (Q.ResidueField ⊗[p.asIdeal.Fiber B] D)
    exact Algebra.TensorProduct.instCommRing
      (R := p.asIdeal.Fiber B) (A := Q.ResidueField) (B := D)
  exact isGorensteinRing_of_ringEquiv Eiter.symm
    (IsRegularRing.isGorensteinRing (Q.ResidueField ⊗[q.ResidueField] q.Fiber C))

/-- **Stacks Project, Tag 0BJN, clause (D).** For flat maps `A → B → C` of Noetherian rings with
`B → C` faithfully flat, if every fibre of `A → C` is Gorenstein then so is every fibre of
`A → B`. -/
@[stacks 0BJN "(D)"]
public theorem gorensteinProperty_faithfullyFlatDescent (P : RingMapProperty.{u, u})
    (hP : ∀ (k R : Type u) [Field k] [CommRing R] [Algebra k R] [IsNoetherianRing R],
      P (algebraMap k R) ↔ IsGorensteinRing R) :
    ∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [Module.FaithfullyFlat B C],
      (∀ p : PrimeSpectrum A, P (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber C))) →
        ∀ p : PrimeSpectrum A, P (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B)) := by
  intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hAC p
  let D := (p.asIdeal.Fiber B) ⊗[B] C
  let e : D ≃ₐ[p.asIdeal.ResidueField] p.asIdeal.Fiber C :=
    Algebra.IsPushout.cancelBaseChangeAlg A p.asIdeal.ResidueField B (p.asIdeal.Fiber B) C
  let : IsNoetherianRing (p.asIdeal.Fiber C) :=
    Stacks.Flatness.NormalFibreAscent.isNoetherianRing_fiber p.asIdeal
  let : IsNoetherianRing (p.asIdeal.Fiber B) :=
    Stacks.Flatness.NormalFibreAscent.isNoetherianRing_fiber p.asIdeal
  let : IsNoetherianRing D := isNoetherianRing_of_ringEquiv _ e.symm.toRingEquiv
  have : Module.FaithfullyFlat (p.asIdeal.Fiber B) D := inferInstance
  rw [hP]
  refine isGorensteinRing_of_faithfullyFlat (S := D) ?_
  exact isGorensteinRing_of_ringEquiv e.symm.toRingEquiv ((hP _ _).mp (hAC p))

/-- **Stacks Project, Tag 0BJN, clause (E).** Gorensteinness of the target is unchanged when the
ground field is replaced by a separable algebraic extension of it inside the target: the
condition does not refer to the ground field. -/
@[stacks 0BJN "(E)"]
public theorem gorensteinProperty_groundFieldExtension (P : RingMapProperty.{u, u})
    (hP : ∀ (k R : Type u) [Field k] [CommRing R] [Algebra k R] [IsNoetherianRing R],
      P (algebraMap k R) ↔ IsGorensteinRing R) :
    ∀ (k K R : Type u) [Field k] [Field K] [CommRing R]
      [Algebra k K] [Algebra k R] [Algebra K R] [IsScalarTower k K R]
      [IsNoetherianRing R] [Algebra.IsAlgebraic k K] [Algebra.IsSeparable k K],
      P (algebraMap k R) → P (algebraMap K R) := by
  intro k K R _ _ _ _ _ _ _ _ _ _ h
  exact (hP K R).mpr ((hP k R).mp h)

/-- **The five clauses of [Stacks, Tag 0BJN], for any property identified with Gorensteinness of
the target.** A property `P` of maps from a field to a Noetherian ring which is, by `hP`,
Gorensteinness of the target satisfies properties (A)--(E) of [Stacks, Tag 0BIR]: it is
preserved by finitely generated field extension of the ground field, is detected by the
localizations at the primes of the target, passes through a composition of flat maps whose
second map is regular, descends through a faithfully flat second map, and is unchanged upon
replacing the ground field by a separable algebraic extension of it inside the target. This is
the analogue of `cohenMacaulayProperty_satisfies_formalFiberAxioms` ([Stacks, Tag 0BJ9]) for
Gorensteinness. -/
public theorem gorensteinProperty_satisfies_formalFiberAxioms (P : RingMapProperty.{u, u})
    (hP : ∀ (k R : Type u) [Field k] [CommRing R] [Algebra k R] [IsNoetherianRing R],
      P (algebraMap k R) ↔ IsGorensteinRing R) :
    (∀ (k K R : Type u) [Field k] [Field K] [CommRing R] [Algebra k K]
      [Algebra k R] [IsNoetherianRing R] [Algebra.EssFiniteType k K],
      P (algebraMap k R) →
        P (Algebra.TensorProduct.includeRight (R := k) (A := R) (B := K)).toRingHom) ∧
    (∀ (k R : Type u) [Field k] [CommRing R] [Algebra k R] [IsNoetherianRing R],
      (∀ p : PrimeSpectrum R, P (algebraMap k (Localization.AtPrime p.asIdeal))) ↔
        P (algebraMap k R)) ∧
    (∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [Module.Flat B C],
      (∀ p : PrimeSpectrum A, P (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B))) →
      (∀ q : PrimeSpectrum B,
        Algebra.IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber C)) →
      ∀ p : PrimeSpectrum A, P (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber C))) ∧
    (∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [Module.FaithfullyFlat B C],
      (∀ p : PrimeSpectrum A, P (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber C))) →
        ∀ p : PrimeSpectrum A, P (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B))) ∧
    (∀ (k K R : Type u) [Field k] [Field K] [CommRing R]
      [Algebra k K] [Algebra k R] [Algebra K R] [IsScalarTower k K R]
      [IsNoetherianRing R] [Algebra.IsAlgebraic k K] [Algebra.IsSeparable k K],
      P (algebraMap k R) → P (algebraMap K R)) := by
  refine ⟨?_, gorensteinProperty_localization P hP, gorensteinProperty_regularAscent P hP,
    gorensteinProperty_faithfullyFlatDescent P hP,
    gorensteinProperty_groundFieldExtension P hP⟩
  intro k K R _ _ _ _ _ _ _ h
  let : Algebra.EssFiniteType R (R ⊗[k] K) := Algebra.EssFiniteType.baseChange k K R
  let : IsNoetherianRing (R ⊗[k] K) := Algebra.EssFiniteType.isNoetherianRing R (R ⊗[k] K)
  rw [hP] at h
  change P (algebraMap K (R ⊗[k] K))
  rw [hP]
  exact isGorensteinRing_tensorProduct_of_essFiniteType_fieldExtension h

/-- On a map from a field to a Noetherian ring, `Dualizing.gorensteinTarget` is Gorensteinness of
the target. -/
private theorem gorensteinTarget_algebraMap_iff :
    ∀ (k R : Type u) [Field k] [CommRing R] [Algebra k R] [IsNoetherianRing R],
      gorensteinTarget.{u} (algebraMap k R) ↔ IsGorensteinRing R := by
  intro k R _ _ _ _
  exact ⟨fun h => h.2, fun h => ⟨inferInstance, h⟩⟩

/-- **Stacks Project, Tag 0BJN.** Gorensteinness of the target of a map from a field to a
Noetherian ring satisfies properties (A)--(E) of [Stacks, Tag 0BIR]: it is preserved by finitely
generated field extension of the ground field, is detected by the localizations at the primes of
the target, passes through a composition of flat maps whose second map is regular, descends
through a faithfully flat second map, and is unchanged upon replacing the ground field by a
separable algebraic extension of it inside the target. Gorensteinness of the target is the
property `Dualizing.gorensteinTarget`. -/
@[stacks 0BJN "all five clauses conjoined, stated through the `RingMapProperty` interface at the \
concrete property `Dualizing.gorensteinTarget`, whose value on a map is Gorensteinness of the \
target together with the Noetherian structure that Gorensteinness presupposes"]
public theorem gorensteinTarget_satisfies_formalFiberAxioms :
    (∀ (k K R : Type u) [Field k] [Field K] [CommRing R] [Algebra k K]
      [Algebra k R] [IsNoetherianRing R] [Algebra.EssFiniteType k K],
      gorensteinTarget.{u} (algebraMap k R) →
        gorensteinTarget.{u}
          (Algebra.TensorProduct.includeRight (R := k) (A := R) (B := K)).toRingHom) ∧
    (∀ (k R : Type u) [Field k] [CommRing R] [Algebra k R] [IsNoetherianRing R],
      (∀ p : PrimeSpectrum R,
          gorensteinTarget.{u} (algebraMap k (Localization.AtPrime p.asIdeal))) ↔
        gorensteinTarget.{u} (algebraMap k R)) ∧
    (∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [Module.Flat B C],
      (∀ p : PrimeSpectrum A,
        gorensteinTarget.{u} (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B))) →
      (∀ q : PrimeSpectrum B,
        Algebra.IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber C)) →
      ∀ p : PrimeSpectrum A,
        gorensteinTarget.{u} (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber C))) ∧
    (∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [Module.FaithfullyFlat B C],
      (∀ p : PrimeSpectrum A,
        gorensteinTarget.{u} (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber C))) →
        ∀ p : PrimeSpectrum A,
          gorensteinTarget.{u} (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B))) ∧
    (∀ (k K R : Type u) [Field k] [Field K] [CommRing R]
      [Algebra k K] [Algebra k R] [Algebra K R] [IsScalarTower k K R]
      [IsNoetherianRing R] [Algebra.IsAlgebraic k K] [Algebra.IsSeparable k K],
      gorensteinTarget.{u} (algebraMap k R) → gorensteinTarget.{u} (algebraMap K R)) :=
  gorensteinProperty_satisfies_formalFiberAxioms gorensteinTarget.{u}
    gorensteinTarget_algebraMap_iff

end Dualizing

end
