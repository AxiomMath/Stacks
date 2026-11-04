module

public import StacksFrontier.RingTheory.Smoothing.InseparableResidueField.PrescribedResidueField

/-!
# Inseparable residue fields: clauses (2) and (3) of Stacks 07FH

Clauses (2) and (3) of Stacks 07FH for a finitely generated residue field, clause (2) in the
generality of the tag, the obstruction to the adapted-section strategy for a perfect residue
field, and the first preliminaries of Nugent's repair of the λ-choice.

This is the sixth part of `StacksFrontier.RingTheory.Smoothing.InseparableResidueField`.

## Main results

* `Stacks.Smoothing.exists_mvPolynomial_factorization_mem_isEssentiallySmooth_flat`: clauses (2)
  and (3) when `κ(𝔮)` is finitely generated over `k`.
* `Stacks.Smoothing.exists_mvPolynomial_factorization_isEssentiallySmooth_flat`: clause (2).
* `Stacks.Smoothing.finite_and_isSeparable_of_formallySmooth_of_perfectRing` and
  `Stacks.Smoothing.not_formallySmooth_of_perfectRing_of_not_isIntegral`: the obstruction to the
  adapted-section strategy.
-/

@[expose] public section

namespace Stacks.Smoothing

open IsLocalRing MvPolynomial
open scoped TensorProduct

universe u v

/-- A ring isomorphic to a local Artinian ring is local and Artinian. -/
private theorem isLocalRing_and_isArtinianRing_of_ringEquiv {R S : Type*} [CommRing R]
    [CommRing S] [Nontrivial S] [IsLocalRing R] [IsArtinianRing R] (e : R ≃+* S) :
    IsLocalRing S ∧ IsArtinianRing S :=
  ⟨.of_surjective' e.toRingHom e.surjective, e.isArtinianRing⟩

/-- **Stacks 07FH, clauses (2) and (3)**, under the extra hypothesis that the residue field
`κ(𝔮)` is a finitely generated field extension of `k`. Let `k` be a field of characteristic
`p > 0`, let `Λ` be a Noetherian geometrically regular `k`-algebra, let `𝔮` be a prime of `Λ`,
let `n ≥ 1` and let `E` be a finite subset of `Λ̄ = Λ_𝔮/𝔮^nΛ_𝔮`. Then there are `m ≥ 0` and a
`k`-algebra map `φ : k[y_1, …, y_m] → Λ` such that, with `𝔭 = φ^{-1}(𝔮)`:

* `𝔭 Λ_𝔮 = 𝔮 Λ_𝔮` and the induced local map `g : k[y_1, …, y_m]_𝔭 → Λ_𝔮` is flat — clause (1)
  of the tag, repeated here so that the map on the prime-power quotients is pinned down;
* the map `u : k[y_1, …, y_m]_𝔭/𝔭^n → Λ̄` induced by `g` factors through a local Artinian
  subring `D` of `Λ̄` as an essentially smooth map `a` followed by the inclusion of `D`, which
  is flat;
* `E ⊆ D`.

"Essentially smooth" is `RingHom.IsEssentiallySmooth`: essentially of finite presentation
(Tag 00QM (2)) and formally smooth. The Stacks Project never defines the term; see
`StacksFrontier/RingTheory/Smoothing/EssentiallySmooth.lean`.

Under the hypothesis on `κ(𝔮)` no approximation is needed and `D = Λ̄` works: the content of the
statement is that `u` itself is essentially smooth.

**The `@[stacks 07FH]` attribute is deliberately NOT attached to this theorem.** A declaration
whose statement carries a hypothesis the tag does not ask for is not a formalization of that
tag, so registering it would overclaim; the attribute sits on
`exists_mvPolynomial_factorization_mem_isEssentiallySmooth_flat_of_charP`, which proves all
three clauses in the generality of the tag. What this theorem adds is only that under
`Algebra.EssFiniteType k κ(𝔮)` no approximation is needed at all: clause (3) is `E ⊆ D`, read as
`∀ e ∈ E, e ∈ D` for the subring `D ⊆ Λ_𝔮/𝔮^nΛ_𝔮` of clause (2) — the source's
`E ⊆ D mod 𝔮^nΛ_𝔮`, `E` being a finite subset of `Λ_𝔮/𝔮^nΛ_𝔮` already — and it holds here
because `D` is all of `Λ_𝔮/𝔮^nΛ_𝔮`, the residue field needing no approximation.

WHY THE JOINT CLAUSES ARE HARDER THAN EITHER ALONE, which is what made the general case
difficult. Clause (2) alone is unconditional
(`exists_mvPolynomial_factorization_isEssentiallySmooth_flat`, with `D = range u`), and clause
(3) alone is supplied by Stacks 07FG (`exists_directedOn_flat_essFiniteType_of_charP` covers
`Λ_𝔮/𝔮^nΛ_𝔮`, so some member `A` of the directed family contains the finitely many elements of
`E`). What is missing for a GIVEN such `A` is clause (2): essential smoothness of
`k[y]_𝔭/𝔭^n → A`, which by the source's route needs `λ_1, …, λ_t ∈ Λ` whose images lie in `A`
and whose residue differentials form a basis of `Ω_{F/k}` for `F = A/𝔪_A`. Write
`S_F = {w ∈ Λ : q(w) ∈ A}`; by the characteristic-`p` criterion (`d x_1, …, d x_n` span
`Ω_{F/k}` iff `F = k(x_1, …, x_n)·F^p`) the λ-choice is available for `A` exactly when
`F = k(w̄ : w ∈ S_F)·F^p`, equivalently when `F` is finite separable over `k(w̄ : w ∈ S_F)`.
`S_F` always contains the `Q`-th powers `w^Q` for `Q = p^j ≥ n` — see the module docstring, and
note their differentials are NOT zero in `Ω_{F/k}` — but those residues lie in `k·K^p`, over
which `K` is purely inseparable, so `Q`-th powers alone cannot generate a coefficient field
containing a prescribed element of `K ∖ k·K^p`, which clause (3) can force into `F`. **Nugent's
repair resolves exactly this**: it carries, for each field generator `f` of `F`, the PAIR of
global elements `s^P` and `a·s^{P-1}` with `σ(f)·q(s) = q(a)` an exact relation in
`Λ_𝔮/𝔮^nΛ_𝔮`, whose images are `σ(α^P)` and `σ(f·α^P)` and whose residues have ratio `f`; a
pair of `P`-th-power type therefore generates what neither member does. See
`exists_finset_global_adjoin_residue_eq_section` and
`exists_global_stage_primePowerQuotient`. Two routes that do NOT work, and are refuted in the
library: enlarging the generating family of `𝔪_Λ̄` instead — `exists_stage` proves flatness of
`Λ̄` over a stage for an ARBITRARY family generating `𝔪_Λ̄`, asking only (`hrx`) that the
`b`-coordinates of its members lie in `F`, but every enlargement of the family forces a matching
enlargement of `F`, so it relocates the fixed-point problem rather than removing it; and the
*adapted-section* strategy, which would obtain `q(Λ') ⊆ σ(F)` for a finitely generated
`Λ' ⊆ Λ` by lifting the canonical section of `F` along `Λ̄ ↠ K` whenever `K/F` is separable, for
by `not_formallySmooth_of_perfectRing_of_not_isIntegral`, when `κ(𝔮)` is a perfect field no
finitely generated `F` containing an element transcendental over `k` has `K/F` formally smooth,
and clause (3) can force such an element into `F`. -/
theorem exists_mvPolynomial_factorization_mem_isEssentiallySmooth_flat
    {k Λ : Type u} [Field k] [CommRing Λ] [Algebra k Λ] [IsNoetherianRing Λ]
    [Algebra.IsGeometricallyRegular k Λ] (𝔮 : Ideal Λ) [𝔮.IsPrime] (p : ℕ) [Fact p.Prime]
    [CharP k p] [Algebra.EssFiniteType k (ResidueField (Localization.AtPrime 𝔮))]
    {n : ℕ} (hn : 1 ≤ n) (E : Finset (primePowerQuotient 𝔮 n)) :
    ∃ (m : ℕ) (φ : MvPolynomial (Fin m) k →ₐ[k] Λ)
      (g : Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮) →+* Localization.AtPrime 𝔮)
      (u : primePowerQuotient (Ideal.comap φ.toRingHom 𝔮) n →+* primePowerQuotient 𝔮 n)
      (D : Subring (primePowerQuotient 𝔮 n))
      (a : primePowerQuotient (Ideal.comap φ.toRingHom 𝔮) n →+* D),
      Ideal.map ((algebraMap Λ (Localization.AtPrime 𝔮)).comp φ.toRingHom)
          (Ideal.comap φ.toRingHom 𝔮)
        = Ideal.map (algebraMap Λ (Localization.AtPrime 𝔮)) 𝔮 ∧
      (∀ f, g (algebraMap (MvPolynomial (Fin m) k)
            (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)) f)
          = algebraMap Λ (Localization.AtPrime 𝔮) (φ f)) ∧
      g.Flat ∧
      (∀ y, u (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) k)
              (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)))
              (Ideal.comap φ.toRingHom 𝔮 ^ n)) y)
          = Ideal.Quotient.mk (Ideal.map (algebraMap Λ (Localization.AtPrime 𝔮)) (𝔮 ^ n))
            (g y)) ∧
      (∀ z, (a z : primePowerQuotient 𝔮 n) = u z) ∧
      (∀ e ∈ E, e ∈ D) ∧
      ∃ (_ : IsLocalRing D) (_ : IsArtinianRing D),
        a.IsEssentiallySmooth ∧ D.subtype.Flat := by
  obtain ⟨m, φ, g, u, hmap, hg, hgflat, hu, hess⟩ :=
    exists_mvPolynomial_isEssentiallySmooth_primePowerQuotient (k := k) 𝔮 p hn
  have hlocQ : IsLocalRing (primePowerQuotient 𝔮 n) := isLocalRing_primePowerQuotient 𝔮 hn
  have hartQ : IsArtinianRing (primePowerQuotient 𝔮 n) := isArtinianRing_primePowerQuotient 𝔮
  have hbij : Function.Bijective (⊤ : Subring (primePowerQuotient 𝔮 n)).subtype :=
    ⟨Subtype.val_injective, fun x => ⟨⟨x, Subring.mem_top x⟩, rfl⟩⟩
  have hTop := isLocalRing_and_isArtinianRing_of_ringEquiv
    (Subring.topEquiv (R := primePowerQuotient 𝔮 n)).symm
  exact ⟨m, φ, g, u, ⊤,
    (Subring.topEquiv (R := primePowerQuotient 𝔮 n)).symm.toRingHom.comp u, hmap, hg, hgflat,
    hu, fun _ => rfl, fun e _ => Subring.mem_top e, hTop.1, hTop.2,
    hess.comp_ringEquiv (Subring.topEquiv (R := primePowerQuotient 𝔮 n)).symm,
    RingHom.Flat.of_bijective hbij⟩

/-! ### Clause (2) of Stacks 07FH, in the generality of the tag

Clause (2) asks only for *some* factorization `k[y]_𝔭/𝔭^n → D → Λ̄` through a local Artinian
subring `D ⊆ Λ̄` with the first arrow essentially smooth and the second flat. The source draws `D`
from the directed family of Stacks 07FG, because it needs clause (3) as well, namely `E ⊆ D` for
a prescribed finite `E ⊆ Λ̄`; but for clause (2) on its own no approximation is needed at the
other end either. Clause (1) already produces `φ` with `𝔭 Λ_𝔮 = 𝔮 Λ_𝔮` and `k[y]_𝔭 → Λ_𝔮` flat;
base change along `k[y]_𝔭 → k[y]_𝔭/𝔭^n` makes `u : k[y]_𝔭/𝔭^n → Λ̄` flat, and `u` is a local
homomorphism of local rings, hence faithfully flat, hence **injective**. So `D = range u` is a
local Artinian subring of `Λ̄` over which `Λ̄` is flat and to which `u` restricts as an
isomorphism — in particular essentially smooth. -/

/-- A flat local homomorphism of local rings is injective: flat and local implies faithfully
flat (`Module.FaithfullyFlat.of_flat_of_isLocalHom`), and a faithfully flat algebra has
injective structure map. -/
@[ega "0 6.5.1" "special case", ega "0 6.6.1" "a⇒b: injectivity of φ", sga "1 IV 2.6" "(iii)"]
private theorem injective_of_flat_isLocalHom {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] {f : R →+* S} (hf : f.Flat) (hloc : IsLocalHom f) :
    Function.Injective f := by
  let := f.toAlgebra
  have hmap : (algebraMap R S) = f := RingHom.algebraMap_toAlgebra f
  have : Module.Flat R S := RingHom.flat_algebraMap_iff.mp (by rw [hmap]; exact hf)
  have : IsLocalHom (algebraMap R S) := by rw [hmap]; exact hloc
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have h := FaithfulSMul.algebraMap_injective R S
  rwa [hmap] at h

/-- For a flat local homomorphism `A → L` of local rings with `𝔪_A L = 𝔪_L`, the induced map
`A/𝔪_A^n → L/𝔪_L^n` is flat — by base change along `A → A/𝔪_A^n` — and injective, being again a
flat local homomorphism of local rings. This is the part of
`isEssentiallySmooth_quotient_of_flat` that needs no finiteness of the residue extension. -/
private theorem exists_quotient_flat_injective {A L : Type u} [CommRing A] [IsLocalRing A]
    [CommRing L] [IsLocalRing L] [Algebra A L] [Module.Flat A L]
    (hmax : Ideal.map (algebraMap A L) (maximalIdeal A) = maximalIdeal L)
    {n : ℕ} (hn : 1 ≤ n) {I : Ideal A} {J : Ideal L}
    (hI : I = maximalIdeal A ^ n) (hJ : J = maximalIdeal L ^ n) :
    ∃ u : (A ⧸ I) →+* (L ⧸ J),
      (∀ a, u (Ideal.Quotient.mk I a) = Ideal.Quotient.mk J (algebraMap A L a)) ∧
      u.Flat ∧ Function.Injective u := by
  classical
  have hlocR : IsLocalRing (A ⧸ I) := isLocalRing_quotient_of_eq_pow hn hI
  have hlocQ : IsLocalRing (L ⧸ J) := isLocalRing_quotient_of_eq_pow hn hJ
  have hIJ : Ideal.map (algebraMap A L) I = J := by rw [hI, hJ, Ideal.map_pow, hmax]
  have hker : ∀ a ∈ I, (Ideal.Quotient.mk J) (algebraMap A L a) = 0 := by
    intro a haI
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hIJ]
    exact Ideal.mem_map_of_mem _ haI
  set u : (A ⧸ I) →+* (L ⧸ J) :=
    Ideal.Quotient.lift I ((Ideal.Quotient.mk J).comp (algebraMap A L)) hker with hudef
  have hu : ∀ a, u (Ideal.Quotient.mk I a) = Ideal.Quotient.mk J (algebraMap A L a) := fun a =>
    Ideal.Quotient.lift_mk _ _ _
  have hucomp : u.comp (Ideal.Quotient.mk I) = (Ideal.Quotient.mk J).comp (algebraMap A L) :=
    RingHom.ext hu
  have hflatQ : Module.Flat (A ⧸ I) (L ⧸ Ideal.map (algebraMap A L) I) :=
    Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor L I).toLinearEquiv
  have hflatu : u.Flat := by
    have hcomp : u = ((Ideal.quotEquivOfEq hIJ :
          (L ⧸ Ideal.map (algebraMap A L) I) ≃+* (L ⧸ J)) :
        (L ⧸ Ideal.map (algebraMap A L) I) →+* (L ⧸ J)).comp
          (algebraMap (A ⧸ I) (L ⧸ Ideal.map (algebraMap A L) I)) := by
      refine RingHom.ext fun z => ?_
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      rw [hu a]
      rfl
    rw [hcomp, RingHom.Flat.comp_iff_of_bijective_left
      (Ideal.quotEquivOfEq hIJ).bijective, RingHom.flat_algebraMap_iff]
    exact hflatQ
  have hmaxu : Ideal.map u (maximalIdeal (A ⧸ I)) = maximalIdeal (L ⧸ J) := by
    rw [maximalIdeal_quotient_of_eq_pow, maximalIdeal_quotient_of_eq_pow, Ideal.map_map, hucomp,
      ← Ideal.map_map, hmax]
  have hlocu : IsLocalHom u := by
    refine ⟨fun a ha => ?_⟩
    by_contra hcon
    have hmem : a ∈ maximalIdeal (A ⧸ I) := (mem_maximalIdeal a).mpr (mem_nonunits_iff.mpr hcon)
    exact ((mem_maximalIdeal _).mp (hmaxu ▸ Ideal.mem_map_of_mem _ hmem)) ha
  exact ⟨u, hu, hflatu, injective_of_flat_isLocalHom hflatu hlocu⟩

/-- A bijective ring homomorphism is essentially smooth. -/
private theorem isEssentiallySmooth_of_bijective {R S : Type u} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : Function.Bijective f) : f.IsEssentiallySmooth := by
  have hid : (algebraMap R R).IsEssentiallySmooth := RingHom.IsEssentiallySmooth.of_etale
  have h := hid.comp_ringEquiv (RingEquiv.ofBijective f hf)
  have hcoe : ((RingEquiv.ofBijective f hf : R ≃+* S) : R →+* S).comp (algebraMap R R) = f :=
    RingHom.ext fun _ => rfl
  rwa [hcoe] at h

/-- **Stacks 07FH, clause (2)**, in the generality of the tag. Let `k` be a field, let `Λ` be a
Noetherian geometrically regular `k`-algebra, let `𝔮` be a prime of `Λ` and let `n ≥ 1`. Then
there are `m ≥ 0` and a `k`-algebra map `φ : k[y_1, …, y_m] → Λ` such that, with
`𝔭 = φ^{-1}(𝔮)`, one has `𝔭 Λ_𝔮 = 𝔮 Λ_𝔮` with `g : k[y_1, …, y_m]_𝔭 → Λ_𝔮` flat, and the map
`k[y_1, …, y_m]_𝔭/𝔭^n → Λ_𝔮/𝔮^nΛ_𝔮` induced by `g` factors through a local Artinian subring `D`
of `Λ_𝔮/𝔮^nΛ_𝔮` by an essentially smooth map followed by the inclusion of `D`, which is flat.

"Essentially smooth" is `RingHom.IsEssentiallySmooth`: essentially of finite presentation
(Tag 00QM (2)) and formally smooth. The Stacks Project never defines the term; see
`StacksFrontier/RingTheory/Smoothing/EssentiallySmooth.lean`. -/
@[stacks 07FH "clause (2), UNCONDITIONALLY: no hypothesis on `κ(𝔮)` beyond the tag's own (`Λ`
Noetherian and geometrically regular over `k`); the characteristic hypothesis is not needed
either. `essentially smooth` is `RingHom.IsEssentiallySmooth` (essentially of finite
presentation, Tag 00QM (2), plus formally smooth); the Stacks Project uses the term here and in
the two following lemmas without ever defining it, and this repository supplies the definition
those proofs need, in `StacksFrontier.RingTheory.Smoothing.EssentiallySmooth`. WHAT IS PROVED: `m`
and `φ : k[y_1, …, y_m] → Λ` with `𝔭 = φ^{-1}(𝔮)`, the ideal identity `𝔭Λ_𝔮 = 𝔮Λ_𝔮`, flatness
of `g : k[y]_𝔭 → Λ_𝔮`, a local Artinian subring `D` of `Λ̄ = Λ_𝔮/𝔮^nΛ_𝔮` and a factorization of
the induced map `u : k[y]_𝔭/𝔭^n → Λ̄` as an essentially smooth map into `D` followed by the
inclusion `D → Λ̄`, which is flat. HOW: clause (2) on its own needs no approximating subring at
either end. Clause (1), `exists_mvPolynomial_flat_localization`, is unconditional and supplies
`φ` with `𝔭Λ_𝔮 = 𝔮Λ_𝔮` and `k[y]_𝔭 → Λ_𝔮` flat; hence `𝔭^n Λ_𝔮 = 𝔮^n Λ_𝔮`, so `u` is the base
change of a flat map along `k[y]_𝔭 → k[y]_𝔭/𝔭^n` and is flat, and `u` is a local homomorphism of
local rings, hence faithfully flat (`Module.FaithfullyFlat.of_flat_of_isLocalHom`), hence
INJECTIVE. So `D = range u` is a local Artinian subring of `Λ̄`, `u` restricts to an isomorphism
onto it — essentially smooth, a bijective ring map being so — and `D → Λ̄` is flat because `u`
is. The source instead draws `D` from the directed family of Stacks 07FG, because it proves
clause (3) at the same time: the approximating subring is needed for `E ⊆ D`, and that is where
the source's unjustified λ-choice sits. WHAT REMAINS: clause (2) alone places no element inside
`D`, so it is Stacks 07FT's joint use of clauses (2) AND (3) that carries the difficulty; see
`exists_mvPolynomial_factorization_mem_isEssentiallySmooth_flat`, which is still conditional."]
theorem exists_mvPolynomial_factorization_isEssentiallySmooth_flat
    {k Λ : Type u} [Field k] [CommRing Λ] [Algebra k Λ] [IsNoetherianRing Λ]
    [Algebra.IsGeometricallyRegular k Λ] (𝔮 : Ideal Λ) [𝔮.IsPrime]
    {n : ℕ} (hn : 1 ≤ n) :
    ∃ (m : ℕ) (φ : MvPolynomial (Fin m) k →ₐ[k] Λ)
      (g : Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮) →+* Localization.AtPrime 𝔮)
      (u : primePowerQuotient (Ideal.comap φ.toRingHom 𝔮) n →+* primePowerQuotient 𝔮 n)
      (D : Subring (primePowerQuotient 𝔮 n))
      (a : primePowerQuotient (Ideal.comap φ.toRingHom 𝔮) n →+* D),
      Ideal.map ((algebraMap Λ (Localization.AtPrime 𝔮)).comp φ.toRingHom)
          (Ideal.comap φ.toRingHom 𝔮)
        = Ideal.map (algebraMap Λ (Localization.AtPrime 𝔮)) 𝔮 ∧
      (∀ f, g (algebraMap (MvPolynomial (Fin m) k)
            (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)) f)
          = algebraMap Λ (Localization.AtPrime 𝔮) (φ f)) ∧
      g.Flat ∧
      (∀ y, u (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) k)
              (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)))
              (Ideal.comap φ.toRingHom 𝔮 ^ n)) y)
          = Ideal.Quotient.mk (Ideal.map (algebraMap Λ (Localization.AtPrime 𝔮)) (𝔮 ^ n))
            (g y)) ∧
      (∀ z, (a z : primePowerQuotient 𝔮 n) = u z) ∧
      ∃ (_ : IsLocalRing D) (_ : IsArtinianRing D),
        a.IsEssentiallySmooth ∧ D.subtype.Flat := by
  classical
  obtain ⟨m, φ, g, hmapeq, hg, hgflat⟩ := exists_mvPolynomial_flat_localization (k := k) 𝔮
  set P := MvPolynomial (Fin m) k with hPdef
  set L := Localization.AtPrime 𝔮 with hLdef
  set 𝔭 : Ideal P := Ideal.comap φ.toRingHom 𝔮 with h𝔭def
  set A := Localization.AtPrime 𝔭 with hAdef
  -- the tower `P → A → L`, with `A → L` the flat map `g` of clause (1)
  let instPL : Algebra P L := ((algebraMap Λ L).comp φ.toRingHom).toAlgebra
  have hPL : (algebraMap P L) = (algebraMap Λ L).comp φ.toRingHom :=
    RingHom.algebraMap_toAlgebra _
  let instAL : Algebra A L := g.toAlgebra
  have hAL : (algebraMap A L) = g := RingHom.algebraMap_toAlgebra _
  have htow : IsScalarTower P A L := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    rw [hAL, hg x, hPL]
    rfl
  have hflatAL : Module.Flat A L :=
    RingHom.flat_algebraMap_iff.mp (by rw [hAL]; exact hgflat)
  -- `𝔪_A L = 𝔪_L`, which is the ideal identity of clause (1) read in `L`
  have hmax : Ideal.map (algebraMap A L) (maximalIdeal A) = maximalIdeal L := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔭 A, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq P A L, hPL, hmapeq,
      IsLocalization.AtPrime.map_eq_maximalIdeal 𝔮 L]
  -- the induced map on the `n`-th prime power quotients is flat and injective
  obtain ⟨u, hu, huflat, huinj⟩ := exists_quotient_flat_injective (A := A) (L := L) hmax hn
    (map_pow_eq_maximalIdeal_pow 𝔭 n) (map_pow_eq_maximalIdeal_pow 𝔮 n)
  have hlocP : IsLocalRing (primePowerQuotient 𝔭 n) := isLocalRing_primePowerQuotient 𝔭 hn
  have hlocQ : IsLocalRing (primePowerQuotient 𝔮 n) := isLocalRing_primePowerQuotient 𝔮 hn
  have hartP : IsArtinianRing (primePowerQuotient 𝔭 n) := isArtinianRing_primePowerQuotient 𝔭
  -- `D` is the image of `u`, over which `u` restricts to an isomorphism
  have hbij : Function.Bijective u.rangeRestrict :=
    ⟨fun x y h => huinj (congrArg (Subring.subtype u.range) h), u.rangeRestrict_surjective⟩
  have := hbij.surjective.nontrivial
  have hD := isLocalRing_and_isArtinianRing_of_ringEquiv (RingEquiv.ofBijective _ hbij)
  have hsubflat : (u.range).subtype.Flat := by
    have hcomp : u = (u.range).subtype.comp u.rangeRestrict := rfl
    rw [hcomp, RingHom.Flat.comp_iff_of_bijective_right hbij] at huflat
    exact huflat
  refine ⟨m, φ, g, u, u.range, u.rangeRestrict, hmapeq, fun f => ?_, hgflat, fun y => ?_,
    fun _ => rfl, hD.1, hD.2, isEssentiallySmooth_of_bijective hbij, hsubflat⟩
  · exact hg f
  · rw [hu y, hAL]

/-! ### The separable coefficient field that the adapted-section route asks for

One strategy for the joint clauses (2) and (3) is the *adapted section*. Choose a finitely
generated `k`-subalgebra `Λ' ⊆ Λ` with `Λ' ∩ 𝔮 = 0`. Every nonzero element of `Λ'` is outside
`𝔮`, hence maps to a unit of `Λ̄ = Λ_𝔮/𝔮^nΛ_𝔮`, so the restriction of `q : Λ → Λ̄` to `Λ'`
extends, with no choice involved, to a ring section `τ : F → Λ̄` of the residue map over the
subfield `F ⊆ K = κ(𝔮)` generated by the residues of `Λ'`. If `τ` lifts along the nilpotent
surjection `Λ̄ ↠ K` to a ring section `σ : K → Λ̄`, then `q(Λ') ⊆ σ(F)` lies in *every* stage
`Ψ_σ(F'[λ])` with `F' ⊇ F`, so clause (3) and the λ-choice can be met at once: for `y ∈ Λ'` the
higher `b`-coordinates of `q(y)` are `0 ∈ F` rather than new elements of `K`, which is what
defeats the fixed-point problem in `exists_coefficientStage_basis_kaehlerDifferential`.

The lifting of `τ` is the whole of that strategy, and the condition under which it is automatic
is that `K/F` be formally smooth — which for field extensions is separability of `K/F`, Lemma
[stacks, 0322]. **That condition is not available in general**, and the two theorems in this
section are the obstruction: when `K` is a *perfect* field, `Algebra.FormallySmooth F K` forces
`F` to be finite over `k`, so an `F` which is required to contain a transcendental element cannot
be reached — and clause (3) does require exactly that, the `b`-coordinates of the prescribed
`E ⊆ Λ̄` being arbitrary elements of `K`.

The non-example this yields. Let `p` be prime, `k = 𝐅_p`, let `K` be the perfect closure of
`𝐅_p(t)` — a perfect field containing the transcendental `t` — let `Λ = K[x]`, `𝔮 = (x)`, `n = 2`,
so `Λ̄ = K[x]/(x²)` and `κ(𝔮) = K`, and let `E = {t}`. Then `Λ` is Noetherian and, `k` being
perfect, geometrically regular over `k`; and the finiteness hypothesis which Stacks 07FG trades
on holds in the strongest possible way, `H₁(L_{K/𝐅_p})` vanishing because `𝐅_p` is perfect, so
that `K/𝐅_p` is separable and hence formally smooth (Lemma [stacks, 0322]). Yet any stage
containing `E` has `t` in its coefficient field, since the residue of an element of a stage lies
in that field (`residue_mem_of_mem_coefficientStage`), and by
`not_formallySmooth_of_perfectRing_of_not_isIntegral` no finitely generated `F` with `t ∈ F` has
`K/F` formally smooth. So `dim_K H₁(L_{K/k}) < ∞` does **not** by itself produce a finitely
generated coefficient field over which `K` is separable.

What is refuted is the separability criterion for the lift, not the adapted section itself: in
this very non-example a section `σ : K → Λ̄` restricting to `τ` does exist, `Λ̄ = K[x]/(x²)` being
split over `K`. A proof of the joint clauses along these lines has to produce the lift of `τ`
some other way, from the geometry of `Λ` rather than from a property of the extension `K/F`. -/

/-- A field `K` of characteristic `p` which is perfect has no nonzero differentials over any
base field: `Ω[K⁄k]` is spanned by the differentials of elements of `K`, and every element of `K`
is a `p`-th power, whose differential is `p` times something and so vanishes. -/
@[ega "0 21.4.4" "Sufficiency, partial", ega "0 21.5.3" "partial", ega "0 22.2.7" "partial"]
private theorem subsingleton_kaehlerDifferential_of_perfectRing (k K : Type*) [Field k] [Field K]
    [Algebra k K] (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectRing K p] :
    Subsingleton (Ω[K⁄k]) := by
  have hzero : ∀ x : K, KaehlerDifferential.D k K x = 0 := by
    intro x
    obtain ⟨y, hy⟩ := (PerfectRing.bijective_frobenius (R := K) (p := p)).surjective x
    subst hy
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero K p, zero_smul]
  have hb : Submodule.span K (Set.range (KaehlerDifferential.D k K)) = ⊥ :=
    Submodule.span_eq_bot.mpr (by rintro _ ⟨x, rfl⟩; exact hzero x)
  rw [KaehlerDifferential.span_range_derivation] at hb
  exact subsingleton_of_forall_eq 0 fun z => (Submodule.eq_bot_iff _).mp hb z Submodule.mem_top

/-- **The obstruction to a separable coefficient field.** Let `k ⊆ F ⊆ K` be fields with `K` of
characteristic `p` and *perfect*, and let `F/k` be finitely generated. If `K` is formally smooth
over `F` — which for a field extension is separability of `K/F`, Lemma [stacks, 0322] — then
`F/k` is already finite and separable.

Since `K` is perfect, `Ω[K⁄k] = 0`; the Jacobi–Zariski sequence
`H₁(L_{K/F}) → K ⊗_F Ω[F⁄k] → Ω[K⁄k]` (Lemma [stacks, 00S2],
`Algebra.H1Cotangent.exact_δ_mapBaseChange`) therefore exhibits `K ⊗_F Ω[F⁄k]` as the image of
`H₁(L_{K/F})`, which vanishes by formal smoothness. As `K` is a faithfully flat `F`-module this
gives `Ω[F⁄k] = 0`, and a finitely generated field extension with vanishing differentials is
finite separable (`finite_and_isSeparable_of_subsingleton_kaehlerDifferential`, Lemma
[stacks, 07E1]).

The hypotheses are: `K` perfect of characteristic `p` (`PerfectRing K p`, `CharP K p`), `F/k`
finitely generated (`Algebra.EssFiniteType k F`), and `Algebra.FormallySmooth F K`. -/
theorem finite_and_isSeparable_of_formallySmooth_of_perfectRing (k F K : Type*) [Field k]
    [Field F] [Field K] [Algebra k F] [Algebra F K] [Algebra k K] [IsScalarTower k F K] (p : ℕ)
    [Fact p.Prime] [CharP K p] [PerfectRing K p] [Algebra.EssFiniteType k F]
    (hsm : Algebra.FormallySmooth F K) :
    Module.Finite k F ∧ Algebra.IsSeparable k F := by
  have h1 : Subsingleton (Ω[K⁄k]) := subsingleton_kaehlerDifferential_of_perfectRing k K p
  have h2 : Subsingleton (Algebra.H1Cotangent F K) := hsm.subsingleton_h1Cotangent
  have hker : LinearMap.ker (KaehlerDifferential.mapBaseChange k F K) = ⊤ := by
    rw [LinearMap.ker_eq_top]
    exact LinearMap.ext fun _ => Subsingleton.elim _ _
  have hrange : LinearMap.range (Algebra.H1Cotangent.δ k F K) = ⊤ := by
    rw [← (Algebra.H1Cotangent.exact_δ_mapBaseChange k F K).linearMap_ker_eq]
    exact hker
  have hbot : LinearMap.range (Algebra.H1Cotangent.δ k F K) = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr ?_
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z 0, map_zero]
  have hsub : Subsingleton (K ⊗[F] Ω[F⁄k]) :=
    subsingleton_of_forall_eq 0 fun z =>
      (Submodule.eq_bot_iff _).mp (hrange ▸ hbot) z Submodule.mem_top
  exact finite_and_isSeparable_of_subsingleton_kaehlerDifferential k F
    ((Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right F K).mp hsub)

/-- **No formally smooth descent of a perfect field past a transcendental element.** If `K` is a
perfect field of characteristic `p`, if `k ⊆ F ⊆ K` with `F/k` finitely generated and if some
element of `F` is not integral over `k`, then `K` is not formally smooth over `F`; in particular
`K/F` is not separable (Lemma [stacks, 0322]).

This is the contrapositive of `finite_and_isSeparable_of_formallySmooth_of_perfectRing`: a finite
extension is integral. -/
theorem not_formallySmooth_of_perfectRing_of_not_isIntegral (k F K : Type*) [Field k] [Field F]
    [Field K] [Algebra k F] [Algebra F K] [Algebra k K] [IsScalarTower k F K] (p : ℕ)
    [Fact p.Prime] [CharP K p] [PerfectRing K p] [Algebra.EssFiniteType k F] {y : F}
    (hy : ¬ IsIntegral k y) : ¬ Algebra.FormallySmooth F K := by
  intro hsm
  have hfin : Module.Finite k F :=
    (finite_and_isSeparable_of_formallySmooth_of_perfectRing k F K p hsm).1
  exact hy (IsIntegral.of_finite k y)


/-! ### Nugent's repair of the λ-choice: preliminaries

This section and the three that follow implement the repair of the λ-choice of Stacks 07FH
described in the implementation notes above and due to **Brian Nugent**. The pieces assembled
here are: finiteness of `H₁(L_{κ(𝔮)⁄k})` for a geometrically regular algebra, which is the
hypothesis under which the whole of the 07FG material above operates; the identification of the
residue field of a quotient of a local ring by a power of its maximal ideal; descent of flatness
along a free extension; and the Frobenius identity `q(w^P) = σ(w̄^P)` on which the repair turns.
-/

/-- **Finiteness of `H₁(L_{κ⁄k})` for a geometrically regular local algebra.** For a Noetherian
local `k`-algebra `A` which is geometrically regular over a field `k` of characteristic `p > 0`,
the `κ(A)`-vector space `H₁(L_{κ(A)⁄k})` is finite dimensional.

This is the hypothesis under which Stacks 07FG is proved. It comes out of the characterization of
geometric regularity in `geometricallyRegular_tfae` (the equivalence of
`Algebra.IsGeometricallyRegular k A` with regularity of `A` together with injectivity of
`H₁(L_{κ(A)⁄k}) → H₁(L_{κ(A)⁄A})`) together with the finite dimensionality of
`H₁(L_{κ(A)⁄A})`, which is the cotangent space of `A`. -/
theorem finite_h1Cotangent_of_isGeometricallyRegular (p : ℕ) [Fact p.Prime]
    (k : Type u) (A : Type v) [Field k] [CharP k p] [CommRing A] [Algebra k A]
    [IsNoetherianRing A] [IsLocalRing A] [Algebra.IsGeometricallyRegular k A] :
    Module.Finite (ResidueField A) (Algebra.H1Cotangent k (ResidueField A)) := by
  obtain ⟨-, hinj⟩ := ((geometricallyRegular_tfae p k A).out 1 3).mp ‹_›
  have hfin : Module.Finite (ResidueField A) (Algebra.H1Cotangent A (ResidueField A)) :=
    finite_h1Cotangent_residueField A
  exact Module.Finite.of_injective _ hinj

/-- **Descent of flatness along a free extension of a local ring.** Let `R → A → B` be ring maps
with `A` local, `B` a free `A`-module and `B` flat over `R`. If the maximal ideal of `A` does not
generate `B`, then `A` is flat over `R`.

Some `A`-basis coordinate of `1 ∈ B` is then a unit, so `A → B` is a split injection of
`A`-modules, hence of `R`-modules, and `Module.Flat.of_retract` applies. This is the step by which
the approximating subalgebra of Stacks 07FG inherits flatness over `k[y]_𝔭/𝔭^n` from the flatness
of `Λ_𝔮/𝔮^nΛ_𝔮` over it. -/
theorem flat_of_free_of_map_maximalIdeal_ne_top {R A B : Type*} [CommRing R] [CommRing A]
    [IsLocalRing A] [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] [Module.Free A B] [Module.Flat R B]
    (h : Ideal.map (algebraMap A B) (maximalIdeal A) ≠ ⊤) : Module.Flat R A := by
  classical
  set b := Module.Free.chooseBasis A B with hbdef
  obtain ⟨i, hi⟩ : ∃ i, IsUnit (b.repr 1 i) := by
    by_contra hcon
    simp only [not_exists] at hcon
    refine h (eq_top_iff.mpr fun z _ => ?_)
    have h1 : (1 : B) ∈ Ideal.map (algebraMap A B) (maximalIdeal A) := by
      rw [← b.linearCombination_repr 1, Finsupp.linearCombination_apply]
      refine Submodule.sum_mem _ fun j _ => ?_
      show (b.repr 1) j • b j ∈ _
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_right _ _
        (Ideal.mem_map_of_mem _ ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr (hcon j))))
    simpa using Ideal.mul_mem_left _ z h1
  set ρ : B →ₗ[A] A := (↑hi.unit⁻¹ : A) • b.coord i with hρdef
  have hρ1 : ρ 1 = 1 := by
    rw [hρdef]
    show (↑hi.unit⁻¹ : A) * b.coord i 1 = 1
    rw [Module.Basis.coord_apply]
    exact hi.val_inv_mul
  have hretr : (ρ.restrictScalars R).comp
      ((Algebra.linearMap A B).restrictScalars R) = LinearMap.id := by
    refine LinearMap.ext fun a => ?_
    show ρ (algebraMap A B a) = a
    rw [show algebraMap A B a = a • (1 : B) by rw [Algebra.smul_def, mul_one], map_smul, hρ1,
      smul_eq_mul, mul_one]
  exact Module.Flat.of_retract _ _ hretr



/-- The central claim of Stacks 07FG with the generating family of `𝔪` prescribed. The source's
induction (`exists_section_mem_coefficientStage`) runs with that family as a parameter, so no
choice of it is forced; `nonempty_coefficientSectionData_of_finite_h1Cotangent` is the case where
the family is chosen along with everything else. -/
private theorem exists_section_mem_coefficientStage_of_gen {k Λ : Type u} [Field k] [CommRing Λ]
    [Algebra k Λ] [IsArtinianRing Λ] [IsLocalRing Λ] (p : ℕ) [Fact p.Prime] [CharP k p]
    [Module.Finite (ResidueField Λ) (Algebra.H1Cotangent k (ResidueField Λ))]
    {d : ℕ} (gen : Fin d → Λ) (hgen : Ideal.span (Set.range gen) = maximalIdeal Λ) :
    ∃ (σ : ResidueField Λ →+* Λ) (F : IntermediateField k (ResidueField Λ)),
      (∀ c, residue Λ (σ c) = c) ∧ F.FG ∧
        ∀ a : k, algebraMap k Λ a ∈ coefficientStage σ F gen := by
  have hnil : IsNilpotent (maximalIdeal Λ) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal Λ).mp inferInstance
  obtain ⟨n, hn⟩ := hnil
  rw [Ideal.zero_eq_bot] at hn
  have hkerres : RingHom.ker (residue Λ) = maximalIdeal Λ := IsLocalRing.ker_residue
  obtain ⟨σ, hσ, F, hFfg, hF⟩ :=
    exists_section_mem_coefficientStage (p := p) (k := k) (K := ResidueField Λ) n Λ
      (residue Λ) residue_surjective (fun _ => rfl) (by rw [hkerres]; exact hn) d gen
      (by rw [hkerres]; exact hgen)
  exact ⟨σ, F, hσ, hFfg, hF⟩

/-- **Stacks 07FG with the generating family of `𝔪` and the residue field both prescribed.** Let
`k` be a field of characteristic `p > 0`, let `(Λ, 𝔪, K)` be an Artinian local `k`-algebra with
`dim_K H₁(L_{K/k}) < ∞`, let `gen` be any finite family generating `𝔪` and let `S` be a finite
subset of `Λ`. Then there are a ring-theoretic section `σ : K → Λ` of the residue map and a
finitely generated `F₀ ⊆ K` such that, for *every* finitely generated `F` with `F₀ ⊆ F ⊆ K`, the
stage `Ψ_σ(F[gen])` is an Artinian local `k`-subalgebra of `Λ` containing `S`, over which `Λ` is
free, which is essentially of finite type over `k`, whose maximal ideal generates `𝔪`, and whose
residue field is `F`.

This differs from `exists_subalgebra_residueField_image_eq_of_charP` in two ways, both needed by
Nugent's repair of the λ-choice: the generating family of `𝔪` is given in advance rather than
chosen (in the repair it is `q(μ_1), …, q(μ_r)` for *global* `μ_j ∈ 𝔮 ⊆ Λ`, which is what dodges
the gap), and the residue field is identified with `F` by an explicit isomorphism rather than only
as a set of residues. Freeness, which `exists_stage` proves, is retained in place of flatness
because `flat_of_free_of_map_maximalIdeal_ne_top` needs it. -/
theorem exists_stage_of_gen {k Λ : Type u} [Field k] [CommRing Λ] [Algebra k Λ]
    [IsArtinianRing Λ] [IsLocalRing Λ] (p : ℕ) [Fact p.Prime] [CharP k p]
    [Module.Finite (ResidueField Λ) (Algebra.H1Cotangent k (ResidueField Λ))]
    {d : ℕ} (gen : Fin d → Λ) (hgen : Ideal.span (Set.range gen) = maximalIdeal Λ)
    (S : Finset Λ) :
    ∃ (σ : ResidueField Λ →+* Λ) (F₀ : IntermediateField k (ResidueField Λ)),
      (∀ c, residue Λ (σ c) = c) ∧ F₀.FG ∧
      ∀ F : IntermediateField k (ResidueField Λ), F₀ ≤ F → F.FG →
        ∃ (A : Subalgebra k Λ) (_ : IsArtinianRing A) (_ : IsLocalRing A)
          (e : ResidueField A ≃+* F),
          A.toSubring = coefficientStage σ F gen ∧
          (∀ y ∈ S, y ∈ A) ∧ Module.Free A Λ ∧ Algebra.EssFiniteType k A ∧
          Ideal.map A.val.toRingHom (maximalIdeal A) = maximalIdeal Λ ∧
          ∀ y : A, ((e (residue A y) : ResidueField Λ)) = residue Λ (y : Λ) := by
  classical
  obtain ⟨σ, Fbase, hσ, hbasefg, hbase⟩ :=
    exists_section_mem_coefficientStage_of_gen (k := k) (Λ := Λ) p gen hgen
  set C : CoefficientSectionData k Λ := ⟨σ, hσ, d, gen, hgen, Fbase, hbasefg, hbase⟩ with hCdef
  let : Algebra (ResidueField Λ) Λ := C.σ.toAlgebra
  have hsec : ∀ c, residue Λ (algebraMap (ResidueField Λ) Λ c) = c := C.residue_σ
  have hnil : IsNilpotent (maximalIdeal Λ) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal Λ).mp inferInstance
  have hxm : ∀ i, C.gen i ∈ maximalIdeal Λ := fun i =>
    C.span_range_gen ▸ Ideal.subset_span (Set.mem_range_self i)
  have hsurj := eval₂Hom_surjective_of_isSection C.σ C.residue_σ C.gen C.span_range_gen hnil
  have hfinΛ : Module.Finite (ResidueField Λ) Λ := by
    have hid : (residue Λ).comp C.σ = RingHom.id _ := RingHom.ext C.residue_σ
    have h : C.σ.Finite := (finite_iff_residue_finite C.σ).mpr (by rw [hid]; exact .id _)
    exact h
  obtain ⟨m, b⟩ := (⟨_, Module.finBasis (ResidueField Λ) Λ⟩ :
    Σ m : ℕ, Module.Basis (Fin m) (ResidueField Λ) Λ)
  set T : Finset (ResidueField Λ) :=
    (Finset.univ.image fun i : Fin m => b.repr 1 i) ∪
    (Finset.univ.image fun q : Fin C.numGen × Fin m => b.repr (C.gen q.1) q.2) ∪
    (Finset.univ.image fun t : Fin m × Fin m × Fin m => b.repr (b t.1 * b t.2.1) t.2.2) with hT
  obtain ⟨F', hF'base, hF'fg, hF'b⟩ := exists_fg_subset_coefficientStage C.σ C.gen hsurj
    C.base C.base_fg (Finset.univ.image b ∪ S)
  set F₁ := F' ⊔ IntermediateField.adjoin k (T : Set (ResidueField Λ)) with hF₁
  have hF₁fg : F₁.FG := IntermediateField.fg_sup hF'fg (IntermediateField.fg_adjoin_finset T)
  have hbaseF₁ : C.base ≤ F₁ := hF'base.trans le_sup_left
  have hTF₁ : (T : Set (ResidueField Λ)) ⊆ (F₁ : Set (ResidueField Λ)) := fun y hy =>
    (le_sup_right : IntermediateField.adjoin k _ ≤ F₁)
      (IntermediateField.subset_adjoin k _ hy)
  have hbF₁ : ∀ i, b i ∈ coefficientStage C.σ F₁ C.gen := fun i =>
    coefficientStage_mono C.σ C.gen (le_sup_left : F' ≤ F₁)
      (hF'b (b i) (Finset.mem_union_left _ (Finset.mem_image_of_mem b (Finset.mem_univ i))))
  have hSF₁ : ∀ y ∈ S, y ∈ coefficientStage C.σ F₁ C.gen := fun y hy =>
    coefficientStage_mono C.σ C.gen (le_sup_left : F' ≤ F₁)
      (hF'b y (Finset.mem_union_right _ hy))
  refine ⟨σ, F₁, hσ, hF₁fg, fun F hF hfg => ?_⟩
  let A : Subalgebra k Λ :=
    { toSubsemiring := (coefficientStage C.σ F C.gen).toSubsemiring
      algebraMap_mem' := fun a => coefficientStage_mono C.σ C.gen (hbaseF₁.trans hF)
        (C.range_algebraMap_mem a) }
  have hA : A.toSubring = coefficientStage C.σ F C.gen := rfl
  have hAmem : ∀ y : Λ, y ∈ A ↔ y ∈ coefficientStage C.σ F C.gen := fun y => Iff.rfl
  obtain ⟨hart, hloc, hfree, heft, hmax⟩ := exists_stage hsec hnil b C.gen C.span_range_gen F hfg
    (fun i => coefficientStage_mono C.σ C.gen hF (hbF₁ i))
    (fun i => hF (hTF₁ (by simp [hT])))
    (fun j i => hF (hTF₁ (by simp [hT])))
    (fun i j l => hF (hTF₁ (by simp [hT])))
    A hA
  -- the residue field of the stage is exactly the coefficient field
  set ρ : A →+* F := RingHom.codRestrict ((residue Λ).comp A.val.toRingHom) F
    (fun y => residue_mem_of_mem_coefficientStage C.σ C.residue_σ C.gen hxm F
      ((hAmem _).1 y.2)) with hρdef
  have hρcoe : ∀ y : A, ((ρ y : F) : ResidueField Λ) = residue Λ (y : Λ) := fun _ => rfl
  have hρsurj : Function.Surjective ρ := by
    intro c
    refine ⟨⟨C.σ (c : ResidueField Λ),
      (hAmem _).2 (mem_coefficientStage_of_mem C.σ C.gen F c)⟩, ?_⟩
    exact Subtype.ext (C.residue_σ _)
  have hρker : ∀ y ∈ maximalIdeal A, ρ y = 0 := by
    intro y hy
    have h0 : residue Λ (y : Λ) = 0 := by
      rw [residue_eq_zero_iff]
      exact hmax ▸ Ideal.mem_map_of_mem A.val.toRingHom hy
    refine Subtype.ext ?_
    rw [hρcoe y, h0, ZeroMemClass.coe_zero]
  set ρbar : ResidueField A →+* F := Ideal.Quotient.lift (maximalIdeal A) ρ hρker with hρbardef
  have hρbar : ∀ y : A, ρbar (residue A y) = ρ y := fun y => Ideal.Quotient.lift_mk _ _ _
  have hρbarsurj : Function.Surjective ρbar := fun c => by
    obtain ⟨y, hy⟩ := hρsurj c
    exact ⟨residue A y, by rw [hρbar, hy]⟩
  exact ⟨A, hart, hloc, RingEquiv.ofBijective ρbar ⟨ρbar.injective, hρbarsurj⟩, hA,
    fun y hy => coefficientStage_mono C.σ C.gen hF (hSF₁ y hy), hfree, heft, hmax,
    fun y => (congrArg Subtype.val (hρbar y)).trans (hρcoe y)⟩

end Stacks.Smoothing
