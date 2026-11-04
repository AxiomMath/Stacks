module

public import StacksFrontier.RingTheory.Smoothing.ArtinianApproximationGeneral
public import StacksFrontier.RingTheory.Smoothing.SmoothFactorizationFromParameters
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 07FJ

The proof of Stacks 07FJ is a twenty-six item argument. Items (1)–(17) are carried out in
`StacksFrontier.RingTheory.Smoothing.PositiveCharacteristicResolution`, items (19)–(21) in
`StacksFrontier.RingTheory.Smoothing.TwistedQuotientResolution`, items (22) and (23) in
`StacksFrontier.RingTheory.Smoothing.TwistedQuotientLocalResolution`, and items (24)–(26) in
`StacksFrontier.RingTheory.Smoothing.SmoothFactorizationFromParameters`. This file composes the last
two, which closes the second half of the argument, and then composes the two halves, which
proves the lemma.

Concretely, `Stacks.Smoothing.TwistedQuotientSmoothFactorization` — items (24)–(26), Stacks 07G8,
07G9 and 07GA, stated over the whole telescope of item (18) — is proved from
`Stacks.Smoothing.exists_smoothFactorizationData_improved`, and feeding it to
`Stacks.Smoothing.twistedQuotientLocallyResolvable_of_smoothFactorization` discharges
`Stacks.Smoothing.TwistedQuotientLocallyResolvable` — items (22)–(26). The remaining item of the
argument, item (9), is Stacks 07FT, proved as
`Stacks.Smoothing.hasArtinianApproximationData` in
`StacksFrontier/RingTheory/Smoothing/ArtinianApproximationGeneral.lean`; the λ-choice of Stacks
07FH on which it turns is not justified by the source's text, and **the repair is due to Brian
Nugent** (see that file and
`StacksFrontier/RingTheory/Smoothing/InseparableResidueField.lean`).

## Main results

* `Stacks.Smoothing.injective_of_flat_of_isLocalHom`: a flat local homomorphism of local rings is
  injective.
* `Stacks.Smoothing.twistedQuotientSmoothFactorization`: items (24)–(26) of the proof of Stacks
  07FJ, over the telescope of item (18).
* `Stacks.Smoothing.twistedQuotientLocallyResolvable`: items (22)–(26) of the proof of Stacks
  07FJ.
* `Stacks.Smoothing.canBeResolvedInPositiveCharacteristic`: Stacks 07FJ.

## Implementation notes

The composition is short because the two halves were written to meet: the conclusion of
`TwistedQuotientSmoothFactorization` is `Stacks.Smoothing.ExistsTwistedSmoothFactorization`,
which is literally the existential shape that `exists_smoothFactorizationData_improved`
produces. What the proof has to supply is the translation of the telescope's data into the data
of items (24)–(26) read **in `D'`** rather than in `Λ`:

* the `Λ₀`-algebra structure on `D'` is `cc ∘ aD`, and it is essentially smooth by
  `Stacks.Smoothing.isEssentiallySmooth_comp`; unfolding essential finite presentation gives the
  finitely presented `B₀` and the submonoid `M` of which `D'` is a localization, which is the
  ind-smoothness input of item (25);
* the parameters `π_i` enter `D'` as `cc (aD π̄_i)`, where `π̄_i` is the image of `π_i` in `Λ₀`;
* the units `δ_i` and the coefficients `λ_{ij}` enter `D'` as the lifts along `b'` whose
  existence is the telescope's `hδD'` and `hlamD'`, and a lift of `δ_i` is a unit because `b'` is
  a local homomorphism of local rings;
* the map `A → D'` is `cc` composed with the corestriction of `A → Λ → Λ̄` to `D`, which is where
  the telescope's `hAD` is used.

The one hypothesis of items (24)–(26) that the telescope does not state in `D'` is the defining
relation `(δ_iπ_i)^{2N} = Σ_j a_jλ_{ij}` of item (18): the telescope states it in `Λ`, and the
chosen lifts satisfy it only after applying `b'`. It is recovered because `b'` is **injective**:
it is a flat local homomorphism between the local rings `D'` and `Λ̄`, hence faithfully flat
(`Module.FaithfullyFlat.of_flat_of_isLocalHom`), hence injective. That is
`injective_of_flat_of_isLocalHom`, and it is the only mathematical step the composition adds.

## References

* [Stacks Project, Tag 07FJ](https://stacks.math.columbia.edu/tag/07FJ)
* [Stacks Project, Tag 07FT](https://stacks.math.columbia.edu/tag/07FT)
* [Stacks Project, Tag 07G8](https://stacks.math.columbia.edu/tag/07G8)
* [Stacks Project, Tag 07G9](https://stacks.math.columbia.edu/tag/07G9)
* [Stacks Project, Tag 07GA](https://stacks.math.columbia.edu/tag/07GA)
-/

@[expose] public section

namespace Stacks.Smoothing

universe u

/-! ### Injectivity of a flat local homomorphism -/

/-- A flat local homomorphism of local rings is injective: it is faithfully flat by
`Module.FaithfullyFlat.of_flat_of_isLocalHom`, and a faithfully flat ring map is injective.

This is what lets a relation between elements of an Artinian local ring `Λ̄` be read back in a
local ring `D'` mapping to it flatly and locally, which is how the defining relation of item
(18) of the proof of Stacks 07FJ becomes available in `D'`. -/
@[ega "0 6.6.1" "a⇒b: injectivity of φ"]
theorem injective_of_flat_of_isLocalHom {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (f : R →+* S) [IsLocalHom f] (hf : f.Flat) : Function.Injective f := by
  let := f.toAlgebra
  have : Module.Flat R S := hf
  have : IsLocalHom (algebraMap R S) := by rwa [RingHom.algebraMap_toAlgebra]
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj := FaithfulSMul.algebraMap_injective R S
  rwa [RingHom.algebraMap_toAlgebra] at hinj

/-! ### Items (24)-(26) over the telescope of item (18) -/

/-- **Items (24), (25) and (26) of the proof of Stacks 07FJ** — Stacks 07G8, 07G9 and 07GA —
over the whole telescope of item (18), that is
`Stacks.Smoothing.TwistedQuotientSmoothFactorization`.

The mathematics is `Stacks.Smoothing.exists_smoothFactorizationData_improved`; what is done here
is the translation of the telescope's data into its hypotheses. See the module docstring for the
list; the only step that is not a rewriting is the defining relation of item (18) read in `D'`,
which uses injectivity of `b'` through `Stacks.Smoothing.injective_of_flat_of_isLocalHom`. -/
theorem twistedQuotientSmoothFactorization : TwistedQuotientSmoothFactorization.{u} := by
  intro k A Λ _ _ _ _ _ _ _ _ _ _ q _ t d m N n c a C _ _ _ _ _ grt φ gl u D aD π δ lam
    D' _ _ _ cc b' _hN _hc _hd1 _hn _hNn _hnbound _hq _ha _hqN _hd _hCalg _hgrt _hmapφ hgφ
    _hgflat hu hDsub hAD _ _ _ _ _ _ hess _hDflat _hdimP _hπmem
    _hπspan _hπΛspan _ _ hess' hflat' hcomp' hδq hrel hlamD' hδD' _hstdC _hcompat
  -- `u` is `φ` on the image of `k[y_1, …, y_m]`
  have hubar := primePowerQuotient_map_algebraMap q φ gl u hgφ hu
  -- `D'` as a `Λ₀`-algebra, through `Λ₀ → D → D'`
  let instΛ₀D' : Algebra (primePowerQuotient (Ideal.comap φ.toRingHom q) n) D' :=
    (cc.comp aD).toAlgebra
  let instkD' : Algebra k D' :=
    ((algebraMap (primePowerQuotient (Ideal.comap φ.toRingHom q) n) D').comp
      (algebraMap k (primePowerQuotient (Ideal.comap φ.toRingHom q) n))).toAlgebra
  have halgΛ₀D' : ∀ z, algebraMap (primePowerQuotient (Ideal.comap φ.toRingHom q) n) D' z =
    cc (aD z) := fun _ => rfl
  have hsubtype_aD : ∀ z, (D.subtype (aD z) : primePowerQuotient q n) = u z :=
    RingHom.congr_fun hDsub
  have hb'cc : ∀ x : D, b' (cc x) = (D.subtype x : primePowerQuotient q n) :=
    RingHom.congr_fun hcomp'
  have hb'Λ₀ : ∀ z, b' (algebraMap (primePowerQuotient (Ideal.comap φ.toRingHom q) n) D' z) =
      u z := by
    intro z
    rw [halgΛ₀D', hb'cc, hsubtype_aD]
  -- `Λ₀ → D'` is essentially smooth, which is the ind-smoothness input of item (25)
  obtain ⟨hefp, hD⟩ : (cc.comp aD).IsEssentiallySmooth := isEssentiallySmooth_comp hess hess'
  obtain ⟨B₀, _, _, _, M, _, _, _⟩ := hefp
  -- the map `A → D'` of item (9), through the image of `A` in `D`
  let fAD : A →+* D := RingHom.codRestrict
    ((algebraMap Λ (primePowerQuotient q n)).comp (algebraMap A Λ)) D hAD
  have hb'φB : ∀ x : A, b' (cc (fAD x)) =
      algebraMap Λ (primePowerQuotient q n) (algebraMap A Λ x) := by
    intro x
    rw [hb'cc]
    rfl
  have hφBk : ∀ r : k, cc (fAD (algebraMap k A r)) = algebraMap k D' r := by
    intro r
    have hDval : fAD (algebraMap k A r) =
        aD (algebraMap k (primePowerQuotient (Ideal.comap φ.toRingHom q) n) r) := by
      refine Subtype.ext ?_
      change algebraMap Λ (primePowerQuotient q n) (algebraMap A Λ (algebraMap k A r)) =
        (D.subtype (aD (algebraMap k
          (primePowerQuotient (Ideal.comap φ.toRingHom q) n) r)) : primePowerQuotient q n)
      rw [hsubtype_aD, ← IsScalarTower.algebraMap_apply k A Λ,
        IsScalarTower.algebraMap_apply k (MvPolynomial (Fin m) k)
          (primePowerQuotient (Ideal.comap φ.toRingHom q) n), hubar, φ.commutes]
    rw [hDval]
    rfl
  let φB : A →ₐ[k] D' := { toRingHom := cc.comp fAD, commutes' := hφBk }
  -- the parameters, the units and the coefficients of item (18), read in `D'`
  let πD : Fin d → D' := fun i =>
    algebraMap (primePowerQuotient (Ideal.comap φ.toRingHom q) n) D'
      (algebraMap (MvPolynomial (Fin m) k)
        (primePowerQuotient (Ideal.comap φ.toRingHom q) n) (π i))
  have hb'πD : ∀ i, b' (πD i) = algebraMap Λ (primePowerQuotient q n) (φ (π i)) := by
    intro i
    rw [hb'Λ₀, hubar]
  choose δD hδDb using hδD'
  choose lamD hlamDb using hlamD'
  have hunitL : ∀ i, IsUnit (algebraMap Λ (primePowerQuotient q n) (δ i)) := by
    intro i
    rw [IsScalarTower.algebraMap_apply Λ (Localization.AtPrime q) (primePowerQuotient q n)]
    exact IsUnit.map (algebraMap (Localization.AtPrime q) (primePowerQuotient q n))
      (IsLocalization.map_units (Localization.AtPrime q) (⟨δ i, hδq i⟩ : q.primeCompl))
  have hδDunit : ∀ i, IsUnit (δD i) := fun i =>
    IsUnit.of_map b' (δD i) (by rw [hδDb i]; exact hunitL i)
  -- the defining relation of item (18), read in `D'` through injectivity of `b'`
  have hrelD : ∀ i, (δD i * πD i) ^ (2 * N) = ∑ j, φB (a j) * lamD i j := by
    intro i
    refine injective_of_flat_of_isLocalHom b' hflat' ?_
    have himg := congrArg (algebraMap Λ (primePowerQuotient q n)) (hrel i)
    rw [map_pow, map_mul, map_sum] at himg
    rw [map_pow, map_mul, hδDb i, hb'πD i, himg, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, hlamDb i j]
    exact congrArg (· * algebraMap Λ (primePowerQuotient q n) (lam i j)) (hb'φB (a j)).symm
  -- the three structure maps the conclusion is about
  let instkxR₀ : Algebra (MvPolynomial (Fin d) k)
      (MvPolynomial (Fin d) (primePowerQuotient (Ideal.comap φ.toRingHom q) n)) :=
    (MvPolynomial.eval₂Hom ((MvPolynomial.C (σ := Fin d)).comp
        (algebraMap k (primePowerQuotient (Ideal.comap φ.toRingHom q) n)))
      (fun i => MvPolynomial.C (algebraMap (MvPolynomial (Fin m) k)
          (primePowerQuotient (Ideal.comap φ.toRingHom q) n) (π i)) *
        MvPolynomial.X i)).toAlgebra
  let instR₀Lbar : Algebra (MvPolynomial (Fin d)
      (primePowerQuotient (Ideal.comap φ.toRingHom q) n)) (primePowerQuotient q n) :=
    (MvPolynomial.eval₂Hom u
      (fun i => algebraMap Λ (primePowerQuotient q n) (δ i))).toAlgebra
  let instCLbar : Algebra C (primePowerQuotient q n) :=
    ((algebraMap Λ (primePowerQuotient q n)).comp
      (improvedAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel grt)).toAlgebra
  -- the evaluation of `D'[t_1, …, t_d]` in `Λ̄`, and the two squares it sits in
  let τ : Fin d → primePowerQuotient q n := fun i =>
    algebraMap Λ (primePowerQuotient q n) (δ i)
  have hcD : ∀ y : primePowerQuotient (Ideal.comap φ.toRingHom q) n,
      b' (algebraMap (primePowerQuotient (Ideal.comap φ.toRingHom q) n) D' y) =
        algebraMap (MvPolynomial (Fin d) (primePowerQuotient (Ideal.comap φ.toRingHom q) n))
          (primePowerQuotient q n) (MvPolynomial.C y) := by
    intro y
    rw [hb'Λ₀]
    change _ = MvPolynomial.eval₂Hom u
      (fun i => algebraMap Λ (primePowerQuotient q n) (δ i)) (MvPolynomial.C y)
    rw [MvPolynomial.eval₂Hom_C]
  have hτ : ∀ i, τ i = algebraMap (MvPolynomial (Fin d)
      (primePowerQuotient (Ideal.comap φ.toRingHom q) n)) (primePowerQuotient q n)
      (MvPolynomial.X i) := by
    intro i
    change _ = MvPolynomial.eval₂Hom u
      (fun i => algebraMap Λ (primePowerQuotient q n) (δ i)) (MvPolynomial.X i)
    rw [MvPolynomial.eval₂Hom_X']
  have hsqC : ∀ r : k, MvPolynomial.map
      (algebraMap (primePowerQuotient (Ideal.comap φ.toRingHom q) n) D')
      (algebraMap (MvPolynomial (Fin d) k) (MvPolynomial (Fin d)
        (primePowerQuotient (Ideal.comap φ.toRingHom q) n)) (MvPolynomial.C r)) =
      MvPolynomial.C (algebraMap k D' r) := by
    intro r
    change MvPolynomial.map
      (algebraMap (primePowerQuotient (Ideal.comap φ.toRingHom q) n) D')
      (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C r)) = _
    rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, MvPolynomial.map_C]
    rfl
  have hsqX : ∀ i, MvPolynomial.map
      (algebraMap (primePowerQuotient (Ideal.comap φ.toRingHom q) n) D')
      (algebraMap (MvPolynomial (Fin d) k) (MvPolynomial (Fin d)
        (primePowerQuotient (Ideal.comap φ.toRingHom q) n)) (MvPolynomial.X i)) =
      MvPolynomial.C (πD i) * MvPolynomial.X i := by
    intro i
    change MvPolynomial.map
      (algebraMap (primePowerQuotient (Ideal.comap φ.toRingHom q) n) D')
      (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X i)) = _
    rw [MvPolynomial.eval₂Hom_X', map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
  -- the evaluation of `B` in `Λ̄`, pinned down on the generators
  let fB : parameterPowerAlgebra A d N a →+* primePowerQuotient q n :=
    (algebraMap Λ (primePowerQuotient q n)).comp
      (parameterPowerAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel).toRingHom
  have hfB : ∀ x, fB x = algebraMap Λ (primePowerQuotient q n)
      (parameterPowerAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel x) := fun _ => rfl
  have hfBA : ∀ x : A, fB (algebraMap A (parameterPowerAlgebra A d N a) x) = b' (φB x) := by
    intro x
    rw [hfB, AlgHom.commutes]
    exact (hb'φB x).symm
  have hfBX : ∀ i, fB (Ideal.Quotient.mk (parameterPowerIdeal d N a)
      (MvPolynomial.X (Sum.inl i))) = b' (πD i) * τ i := by
    intro i
    rw [hb'πD i, hfB, parameterPowerAlgebraToTarget_X_inl, map_mul]
    exact mul_comm _ _
  have hfBZ : ∀ i j, fB (Ideal.Quotient.mk (parameterPowerIdeal d N a)
        (MvPolynomial.X (Sum.inr (i, j)))) * b' (δD i) ^ (2 * N) =
      b' (lamD i j) * τ i ^ (2 * N) := by
    intro i j
    rw [hδDb i, hlamDb i j, hfB, parameterPowerAlgebraToTarget_X_inr]
  have hcL : ∀ cv : C, algebraMap C (primePowerQuotient q n) cv = fB (grt cv) := fun _ => rfl
  exact exists_smoothFactorizationData_improved k a grt M hD φB πD δD lamD hδDunit hrelD b' τ
    hcD hτ hsqC hsqX fB hfBA hfBX hfBZ (algebraMap C (primePowerQuotient q n)) hcL

/-! ### Items (22)-(26), and Stacks 07FJ -/

/-- **Items (22)–(26) of the proof of Stacks 07FJ** — Stacks 07G6, 07G7, 07G8, 07G9 and 07GA:
the twisted quotient chain of item (18) is resolvable after localizing at `𝔮`.

This is `Stacks.Smoothing.twistedQuotientLocallyResolvable_of_smoothFactorization`, which is
items (22) and (23), applied to `Stacks.Smoothing.twistedQuotientSmoothFactorization`, which is
items (24)–(26). -/
theorem twistedQuotientLocallyResolvable : TwistedQuotientLocallyResolvable.{u} :=
  twistedQuotientLocallyResolvable_of_smoothFactorization twistedQuotientSmoothFactorization

/-- **Stacks 07FJ.** Let `k → A → Λ ⊃ 𝔮` be as in Situation 07F7 with `k` of characteristic
`p > 0`, `A` of finite presentation over `k`, `Λ` Noetherian and geometrically regular over `k`,
and `𝔮` minimal over `𝔥_A`. Then the chain can be resolved at `𝔮`.

This is `Stacks.Smoothing.canBeResolvedInPositiveCharacteristic_of_locallyResolvable` with both
of its hypotheses discharged: item (9), Stacks 07FT, by
`Stacks.Smoothing.hasArtinianApproximationData`, and items (22)–(26) by
`Stacks.Smoothing.twistedQuotientLocallyResolvable` above. Every one of the twenty-six items of
the source's proof is therefore proved. -/
@[stacks 07FJ "the lemma in full generality, with NO carried hypotheses: the whole of \
Situation 07F7 over a field of characteristic `p > 0`, with `𝔮` minimal over `𝔥_A`, and the \
conclusion `CanBeResolved k A Λ 𝔮`. Its two inputs are both proved in this library. The first \
is item (9), Stacks 07FT, `hasArtinianApproximationData`; the second is items (22)-(26), Stacks \
07G6-07GA, `twistedQuotientLocallyResolvable`. The λ-choice in the source's proof of Stacks \
07FH, on which 07FT turns, is not justified by the source's text and is false for a general \
member of the directed family of 07FG; the repair is due to BRIAN NUGENT, and is implemented in \
`exists_global_stage_primePowerQuotient`."]
theorem canBeResolvedInPositiveCharacteristic : CanBeResolvedInPositiveCharacteristic.{u} :=
  canBeResolvedInPositiveCharacteristic_of_locallyResolvable hasArtinianApproximationData
    twistedQuotientLocallyResolvable

end Stacks.Smoothing

end
