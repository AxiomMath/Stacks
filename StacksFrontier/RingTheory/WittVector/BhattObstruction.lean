module

public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Regular.Flat
public import StacksFrontier.RingTheory.Cech.PuncturedVanishing
public import StacksFrontier.RingTheory.WittVector.ArtinSchreierWitt
public import StacksFrontier.RingTheory.WittVector.CechKilling
public import StacksFrontier.RingTheory.WittVector.FrobeniusSubOneSurjective

/-!
# An Artin–Schreier–Witt obstruction to maps into free algebras

Let `p` be a prime and `R` a henselian local domain of characteristic `p` with separably closed
residue field, and let `x 0, x 1, x 2` be a weakly regular sequence of nonzero elements of `R`.
Let `S` be a domain integral over `R` and `w` a finite family of elements of `S` whose radical
contains the `x i`, so that the opens `D(w j)` cover the punctured spectrum of `S` over
`Spec R ∖ V(x 0, x 1, x 2)`. An Artin–Schreier–Witt Čech cocycle on this covering consists of Witt
vectors `a j` over the fraction field of `S` with coefficients in `S[1/w j]` and `b i j` with
coefficients in `S[1/(w i * w j)]`, with `b i j + b j k = b i k` and
`F (b i j) - b i j = a i - a j`.

If the zeroth coefficient of some `a j₀` is not of the form `h ^ p - h` in the fraction field of
`S`, then there is no `R`-algebra map from `S` to a nontrivial finite free `R`-algebra `T`.

## Main results

* `WittVector.map_frobenius`: the Witt vector Frobenius commutes with maps of coefficient rings.
* `Stacks.ArtinSchreier.map_mem_awaySubring`: `awaySubring` is compatible with ring maps.
* `Stacks.ArtinSchreier.isEmpty_algHom_of_artinSchreierWitt_cocycle`: the obstruction above.
-/

@[expose] public section

open IsLocalRing RingTheory.Sequence Stacks.RingTheory.PuncturedVanishing WittVector
open scoped nonZeroDivisors

namespace WittVector

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝕎" => WittVector p

/-- The Witt vector Frobenius commutes with the map induced by a ring map. -/
theorem map_frobenius {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (x : 𝕎 A) :
    map f (frobenius x) = frobenius (map f x) := by
  ext n
  rw [map_coeff, coeff_frobenius, coeff_frobenius, MvPolynomial.map_aeval,
    MvPolynomial.aeval_eq_eval₂Hom, RingHom.ext_int (f.comp (algebraMap ℤ A)) (algebraMap ℤ B)]
  exact congrArg (fun g ↦ MvPolynomial.eval₂Hom (algebraMap ℤ B) g (frobeniusPoly p n))
    (funext fun i ↦ (map_coeff f x i).symm)

end WittVector

namespace Stacks.ArtinSchreier

/-- A ring map `f : Ω → Ω'` compatible with a ring map `g : T → T'` sends `awaySubring Ω s` into
`awaySubring Ω' (g s)`. -/
theorem map_mem_awaySubring {T T' Ω Ω' : Type*} [CommRing T] [CommRing T'] [CommRing Ω]
    [CommRing Ω'] [Algebra T Ω] [Algebra T' Ω'] (g : T →+* T') (f : Ω →+* Ω')
    (hfg : ∀ t, f (algebraMap T Ω t) = algebraMap T' Ω' (g t)) {s : T} {ω : Ω}
    (hω : ω ∈ awaySubring Ω s) : f ω ∈ awaySubring Ω' (g s) := by
  obtain ⟨n, t, ht⟩ := hω
  exact ⟨n, g t, by rw [← map_pow g, ← hfg, ← hfg, ← map_mul, ht]⟩

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝕎" => WittVector p

/-- **An Artin–Schreier–Witt obstruction.** Let `R` be a henselian local domain of characteristic
`p` with separably closed residue field, `x 0, x 1, x 2` a weakly regular sequence of nonzero
elements of `R`, `S` a domain integral over `R` and `w` a finite family of elements of `S` whose
radical contains the `x i`. Let `a j` and `b i j` be Witt vectors over the fraction field of `S`
with coefficients in `S[1/w j]` and `S[1/(w i * w j)]` respectively, forming an
Artin–Schreier–Witt Čech cocycle: `b i j + b j k = b i k` and `F (b i j) - b i j = a i - a j`. If
the zeroth coefficient of `a j₀` is not of the form `h ^ p - h` in the fraction field of `S`, then
there is no `R`-algebra map from `S` to a nontrivial finite free `R`-algebra. -/
theorem isEmpty_algHom_of_artinSchreierWitt_cocycle (R : Type*) [CommRing R] [IsDomain R]
    [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [CharP R p] {x : Fin 3 → R}
    (hreg : IsWeaklyRegular R [x 0, x 1, x 2]) (hx : ∀ i, x i ≠ 0) (S : Type*) [CommRing S]
    [IsDomain S] [Algebra R S] [Algebra.IsIntegral R S] {ι : Type*} [Finite ι] (w : ι → S)
    (hxw : ∀ i, algebraMap R S (x i) ∈ (Ideal.span (Set.range w)).radical)
    (a : ι → 𝕎 (FractionRing S)) (b : ι → ι → 𝕎 (FractionRing S))
    (ha : ∀ j n, (a j).coeff n ∈ awaySubring (FractionRing S) (w j))
    (hb : ∀ i j n, (b i j).coeff n ∈ awaySubring (FractionRing S) (w i * w j))
    (hcoc : ∀ i j k, b i j + b j k = b i k)
    (hab : ∀ i j, frobenius (b i j) - b i j = a i - a j) (j₀ : ι)
    (h₀ : ∀ h : FractionRing S, h ^ p - h ≠ (a j₀).coeff 0) (T : Type*) [CommRing T]
    [Nontrivial T] [Algebra R T] [Module.Free R T] [Module.Finite R T] :
    IsEmpty (S →ₐ[R] T) := by
  refine ⟨fun φ ↦ ?_⟩
  have hRT : ∀ r : R, r ≠ 0 → algebraMap R T r ∈ T⁰ := fun r hr ↦
    mem_nonZeroDivisors_iff_right.2 fun t h ↦
      (isRegular_iff_ne_zero.2 hr).smul_eq_zero_iff_right.1 (by rw [Algebra.smul_def, mul_comm, h])
  have hST : ∀ s : S, s ≠ 0 → φ s ∈ T⁰ := fun s hs ↦ by
    obtain ⟨r, hr, s', hs'⟩ :=
      (Algebra.IsIntegral.isIntegral (R := R) s).isAlgebraic.exists_nonzero_dvd
        (mem_nonZeroDivisors_of_ne_zero hs)
    have h := hRT r hr
    rw [← φ.commutes, hs', map_mul] at h
    exact (mul_mem_nonZeroDivisors.1 h).1
  set Ω := FractionRing T
  have hinj : Function.Injective (algebraMap T Ω) := IsFractionRing.injective T Ω
  have : Nontrivial Ω := hinj.nontrivial
  have : CharP Ω p := .of_ringHom_of_ne_zero (algebraMap R Ω) p hp.out.ne_zero
  let ψ : FractionRing S →+* Ω := IsLocalization.lift (M := S⁰)
    (g := (algebraMap T Ω).comp φ.toRingHom) fun s ↦
      IsLocalization.map_units Ω (⟨φ s, hST s (nonZeroDivisors.ne_zero s.2)⟩ : T⁰)
  have hψ : ∀ s, ψ (algebraMap S (FractionRing S) s) = algebraMap T Ω (φ s) := fun s ↦
    IsLocalization.lift_eq _ s
  have hmem : ∀ (s : S) (ω : FractionRing S), ω ∈ awaySubring (FractionRing S) s →
      ψ ω ∈ awaySubring Ω (φ s) := fun s ω h ↦ map_mem_awaySubring φ.toRingHom ψ hψ h
  set xT : Fin 3 → T := fun i ↦ algebraMap R T (x i)
  have hregT : IsWeaklyRegular T [xT 0, xT 1, xT 2] := hreg.of_flat (S := T)
  have hxu : ∀ i, IsUnit (algebraMap T Ω (xT i)) := fun i ↦
    IsLocalization.map_units Ω (⟨xT i, hRT _ (hx i)⟩ : T⁰)
  set y : ι → T := fun j ↦ φ (w j)
  have hrad : ∀ i, xT i ∈ (Ideal.span (Set.range y)).radical := fun i ↦ by
    obtain ⟨n, hn⟩ := hxw i
    have h := Ideal.mem_map_of_mem φ hn
    rw [Ideal.map_span, ← Set.range_comp, map_pow, φ.commutes] at h
    exact ⟨n, h⟩
  have hsurj : ∀ z ∈ coeffSubring p (algebraMap T Ω).range,
      ∃ e ∈ coeffSubring p (algebraMap T Ω).range, frobenius e - e = z := by
    intro z hz
    choose t ht using fun n ↦ RingHom.mem_range.1 (mem_coeffSubring_iff.1 hz n)
    obtain ⟨e, he⟩ := exists_frobenius_sub_self_eq_of_henselianLocalRing (p := p) R (T := T)
      (mk p t)
    refine ⟨map (algebraMap T Ω) e, mem_coeffSubring_iff.2 fun n ↦
      RingHom.mem_range.2 ⟨e.coeff n, (map_coeff _ _ _).symm⟩, ?_⟩
    rw [← map_frobenius, ← map_sub, he]
    ext n
    rw [map_coeff, coeff_mk, ht]
  obtain ⟨θ, -, hθ⟩ := exists_frobenius_sub_self_eq_of_cech (p := p)
    (A := (algebraMap T Ω).range) (Aᵢ := fun j ↦ awaySubring Ω (y j))
    (B := fun i j ↦ awaySubring Ω (y i * y j))
    (fun i j ↦ awaySubring_le_awaySubring_mul _ _)
    (fun i j ↦ awaySubring_mono_of_dvd (dvd_mul_left _ _))
    (fun c hc ↦ mem_range_of_forall_mem_awaySubring hinj hxu hregT hrad hc)
    (fun b hb hcoc ↦ exists_cech_coboundary_of_forall_mem_radical hinj hxu hregT hrad b hb hcoc)
    hsurj (fun j ↦ by rintro _ ⟨t, rfl⟩; exact algebraMap_mem_awaySubring _ t)
    (fun j ↦ map ψ (a j)) (fun i j ↦ map ψ (b i j))
    (fun j n ↦ by rw [map_coeff]; exact hmem _ _ (ha j n))
    (fun i j n ↦ by rw [map_coeff]; simpa only [map_mul] using hmem _ _ (hb i j n))
    (fun i j k ↦ by rw [← map_add, hcoc])
    (fun i j ↦ by rw [← map_frobenius, ← map_sub, ← map_sub, hab]) j₀
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal T
  obtain ⟨𝔮, h𝔮, -⟩ := Ideal.exists_minimalPrimes_le (J := 𝔪) bot_le
  have : 𝔮.IsPrime := h𝔮.1.1
  have hdisj : ∀ t ∈ T⁰, t ∉ 𝔮 := fun t ht h ↦
    Set.disjoint_left.1 (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes h𝔮) h ht
  let D := T ⧸ 𝔮
  let L := FractionRing D
  let : Algebra S D := ((Ideal.Quotient.mk 𝔮).comp φ.toRingHom).toAlgebra
  have hSD : Function.Injective (algebraMap S D) := by
    refine (injective_iff_map_eq_zero _).2 fun s hs ↦ by_contra fun h0 ↦ ?_
    have hs' : Ideal.Quotient.mk 𝔮 (φ s) = 0 := hs
    exact hdisj _ (hST s h0) (Ideal.Quotient.eq_zero_iff_mem.1 hs')
  have : IsScalarTower R S D := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change Ideal.Quotient.mk 𝔮 (algebraMap R T r) = Ideal.Quotient.mk 𝔮 (φ (algebraMap R S r))
    rw [φ.commutes]
  have : Module.Finite R D :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R 𝔮).toLinearMap Ideal.Quotient.mk_surjective
  have : Module.Finite S D := Module.Finite.of_restrictScalars_finite R S D
  have : FaithfulSMul S D := (faithfulSMul_iff_algebraMap_injective S D).2 hSD
  have : FaithfulSMul S L := (faithfulSMul_iff_algebraMap_injective S L).2 <| by
    rw [IsScalarTower.algebraMap_eq S D L]
    exact (IsFractionRing.injective D L).comp hSD
  let : Algebra (FractionRing S) L := FractionRing.liftAlgebra S L
  have : FiniteDimensional (FractionRing S) L := inferInstance
  have : CharP (FractionRing S) p :=
    .of_ringHom_of_ne_zero (algebraMap R (FractionRing S)) p hp.out.ne_zero
  let ρ : Ω →+* L := IsLocalization.lift (M := T⁰)
    (g := (algebraMap D L).comp (Ideal.Quotient.mk 𝔮)) fun t ↦
      isUnit_iff_ne_zero.2 <| (map_ne_zero_iff _ (IsFractionRing.injective D L)).2 fun h ↦
        hdisj t t.2 (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hρψ : ρ.comp ψ = algebraMap (FractionRing S) L := by
    refine IsLocalization.ringHom_ext S⁰ (RingHom.ext fun s ↦ ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply, hψ, IsLocalization.lift_eq, RingHom.comp_apply,
      RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply S D L]
    rfl
  refine frobenius_sub_self_ne_map_of_coeff_zero_not_mem (K := FractionRing S) (L := L) (a j₀) h₀
    (map ρ θ) ?_
  rw [← map_frobenius, ← map_sub, hθ]
  ext n
  rw [map_coeff, map_coeff, map_coeff, ← hρψ]
  rfl

end Stacks.ArtinSchreier
