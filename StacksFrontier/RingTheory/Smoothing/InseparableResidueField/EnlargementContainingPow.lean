module

public import StacksFrontier.RingTheory.GeometricallyRegular.Defs
public import StacksFrontier.RingTheory.Smoothing.EssentiallySmoothEnlargement
public import StacksFrontier.RingTheory.Smoothing.InseparableResidueField.FibreFlatness

/-!
# Enlarging the factorization of Lemma 07FH to absorb a power of an element

Stacks 07FI in the setting of Stacks 07FH, verbatim: `k` a field of characteristic `p > 0`, `Λ`
a Noetherian geometrically regular `k`-algebra, `𝔮 ⊆ Λ` a prime, `n ≥ 1`, a `k`-algebra map
`φ : k[y₁, …, y_m] → Λ` with `𝔭 = φ⁻¹(𝔮)` satisfying clause (1) of 07FH, a factorization
`k[y₁, …, y_m]_𝔭/𝔭ⁿ → D → Λ_𝔮/𝔮ⁿΛ_𝔮` through a local Artinian ring `D` as in clause (2), and a
finite subset `E ⊆ Λ_𝔮/𝔮ⁿΛ_𝔮` contained in `D` as in clause (3). For every `λ ∈ Λ ∖ 𝔮` the
factorization is enlarged to `k[y₁, …, y_m]_𝔭/𝔭ⁿ → D → D' → Λ_𝔮/𝔮ⁿΛ_𝔮` with `D → D'` an
essentially smooth map of local Artinian rings, `D' → Λ_𝔮/𝔮ⁿΛ_𝔮` flat, and `λ^q ∈ D'` for some
`q > 0`.

## Main results

* `Stacks.Smoothing.exists_essentiallySmooth_enlargement_containing_pow_of_factorization`:
  Stacks 07FI.

## Implementation notes

The ring-theoretic content is
`Stacks.Smoothing.exists_essentiallySmooth_enlargement_containing_pow`, which needs of the
setup only that `Λ_𝔮/𝔮ⁿΛ_𝔮` be local Artinian and that `D → Λ_𝔮/𝔮ⁿΛ_𝔮` be a flat local map
from a local Artinian ring. Here those are derived from the setup of 07FH: `Λ_𝔮/𝔮ⁿΛ_𝔮` is
local because `n ≥ 1` and Artinian because `Λ` is Noetherian, and `D → Λ_𝔮/𝔮ⁿΛ_𝔮` is a local
homomorphism because the maximal ideal of the Artinian local ring `D` is nilpotent. The
remaining data of 07FH (clause (1), the left-hand map and its essential smoothness, the set `E`,
geometric regularity and `λ ∉ 𝔮`) are hypotheses of the statement, as in the source, and are not
needed by the proof.

In the source `D'` is a subring of `Λ_𝔮/𝔮ⁿΛ_𝔮`; here it is a ring with an injective flat local
map `b' : D' → Λ_𝔮/𝔮ⁿΛ_𝔮`, and "`λ^q ∈ D'`" is the statement that the image of `λ^q` lies in the
range of `b'`.

## References

* [Stacks Project, Tag 07FI](https://stacks.math.columbia.edu/tag/07FI)
* [Stacks Project, Tag 07FH](https://stacks.math.columbia.edu/tag/07FH)
-/

@[expose] public section

universe u

namespace Stacks.Smoothing

open IsLocalRing

/-- A ring homomorphism from an Artinian local ring to a nontrivial ring is local: the maximal
ideal of the source is nilpotent, so it maps to nilpotent elements, which are not units. -/
private theorem isLocalHom_of_isArtinianRing {D T : Type*} [CommRing D] [IsLocalRing D]
    [IsArtinianRing D] [CommRing T] [Nontrivial T] (b : D →+* T) : IsLocalHom b := by
  refine ⟨fun x hx => ?_⟩
  by_contra hxu
  have hxm : x ∈ (⊥ : Ideal D).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact (mem_maximalIdeal x).mpr (mem_nonunits_iff.mpr hxu)
  have hnil : IsNilpotent (⊥ : Ideal D).jacobson := IsArtinianRing.isNilpotent_jacobson_bot
  obtain ⟨N, hN⟩ := hnil
  have hxN : x ^ N = 0 := by
    have h := Ideal.pow_mem_pow hxm N
    rwa [hN, Submodule.zero_eq_bot, Ideal.mem_bot] at h
  have hu : IsUnit (b x ^ N) := hx.pow N
  rw [← map_pow, hxN, map_zero] at hu
  exact not_isUnit_zero hu

/-- **Stacks 07FI.** Let `k` be a field of characteristic `p > 0`, let `Λ` be a Noetherian
geometrically regular `k`-algebra, let `𝔮 ⊆ Λ` be a prime and let `n ≥ 1`. Let
`φ : k[y₁, …, y_m] → Λ` be a `k`-algebra map, `𝔭 = φ⁻¹(𝔮)`, and suppose, as in Lemma 07FH,

1. `𝔭Λ_𝔮 = 𝔮Λ_𝔮` and `g : k[y₁, …, y_m]_𝔭 → Λ_𝔮` is flat;
2. the induced map `u : k[y₁, …, y_m]_𝔭/𝔭ⁿ → Λ_𝔮/𝔮ⁿΛ_𝔮` factors as `b ∘ a` through a local
   Artinian ring `D`, with `a` essentially smooth and `b` flat;
3. a finite subset `E ⊆ Λ_𝔮/𝔮ⁿΛ_𝔮` is contained in `D`.

Then for every `λ ∈ Λ ∖ 𝔮` there are an integer `q > 0` and a factorization
`k[y₁, …, y_m]_𝔭/𝔭ⁿ → D → D' → Λ_𝔮/𝔮ⁿΛ_𝔮` of `u`, with `D'` local Artinian, `c : D → D'` an
essentially smooth local homomorphism, `b' : D' → Λ_𝔮/𝔮ⁿΛ_𝔮` flat, local and injective (so
that `D'` is a subring of `Λ_𝔮/𝔮ⁿΛ_𝔮`), `b' ∘ c = b`, and `λ^q ∈ D'`. -/
@[stacks 07FI "in the full setup of Lemma 07FH: `Λ` Noetherian and geometrically regular over \
`k` of characteristic `p > 0`, `n ≥ 1`, `φ : k[y₁,…,y_m] → Λ` with clause (1) (`𝔭Λ_𝔮 = 𝔮Λ_𝔮`, \
`k[y]_𝔭 → Λ_𝔮` flat), the factorization `k[y]_𝔭/𝔭ⁿ → D → Λ_𝔮/𝔮ⁿΛ_𝔮` of clause (2) through a \
local Artinian `D` (first arrow essentially smooth, second flat) and the finite `E ⊆ D` of \
clause (3), and `λ ∉ 𝔮`. `D'` is a ring with an injective flat local map to `Λ_𝔮/𝔮ⁿΛ_𝔮`, and \
`λ^q ∈ D'` means the image of `λ^q` lies in its range. Essentially smooth is \
`RingHom.IsEssentiallySmooth` (essentially of finite presentation, Tag 00QM (2), and formally \
smooth)"]
theorem exists_essentiallySmooth_enlargement_containing_pow_of_factorization
    {k Λ : Type u} [Field k] (p : ℕ) [CharP k p] (hp : 0 < p)
    [CommRing Λ] [Algebra k Λ] [IsNoetherianRing Λ] [Algebra.IsGeometricallyRegular k Λ]
    (𝔮 : Ideal Λ) [𝔮.IsPrime] {n : ℕ} (hn : 1 ≤ n)
    {m : ℕ} (φ : MvPolynomial (Fin m) k →ₐ[k] Λ)
    (g : Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮) →+* Localization.AtPrime 𝔮)
    (_hmap : Ideal.map ((algebraMap Λ (Localization.AtPrime 𝔮)).comp φ.toRingHom)
        (Ideal.comap φ.toRingHom 𝔮) = Ideal.map (algebraMap Λ (Localization.AtPrime 𝔮)) 𝔮)
    (_hg : ∀ f, g (algebraMap (MvPolynomial (Fin m) k)
        (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)) f)
          = algebraMap Λ (Localization.AtPrime 𝔮) (φ f))
    (_hgflat : g.Flat)
    (u : primePowerQuotient (Ideal.comap φ.toRingHom 𝔮) n →+* primePowerQuotient 𝔮 n)
    (_hu : ∀ y, u (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) k)
          (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮))) (Ideal.comap φ.toRingHom 𝔮 ^ n)) y)
        = Ideal.Quotient.mk (Ideal.map (algebraMap Λ (Localization.AtPrime 𝔮)) (𝔮 ^ n)) (g y))
    {D : Type u} [CommRing D] [IsLocalRing D] [IsArtinianRing D]
    (a : primePowerQuotient (Ideal.comap φ.toRingHom 𝔮) n →+* D)
    (b : D →+* primePowerQuotient 𝔮 n)
    (_ha : a.IsEssentiallySmooth) (hb : b.Flat) (hab : b.comp a = u)
    (E : Finset (primePowerQuotient 𝔮 n)) (_hE : ∀ x ∈ E, x ∈ b.range)
    (lam : Λ) (_hlam : lam ∉ 𝔮) :
    ∃ (q : ℕ) (D' : Type u) (_ : CommRing D') (_ : IsLocalRing D') (_ : IsArtinianRing D')
      (c : D →+* D') (b' : D' →+* primePowerQuotient 𝔮 n) (_ : IsLocalHom c)
      (_ : IsLocalHom b'),
      0 < q ∧ c.IsEssentiallySmooth ∧ b'.Flat ∧ b'.comp c = b ∧ (b'.comp c).comp a = u ∧
        Function.Injective b' ∧
        algebraMap Λ (primePowerQuotient 𝔮 n) (lam ^ q) ∈ b'.range := by
  have : IsLocalRing (primePowerQuotient 𝔮 n) := isLocalRing_primePowerQuotient 𝔮 hn
  have : IsArtinianRing (primePowerQuotient 𝔮 n) := isArtinianRing_primePowerQuotient 𝔮
  have : IsLocalHom b := isLocalHom_of_isArtinianRing b
  obtain ⟨q, D', hcr, hlr, har, c, b', hcl, hbl, hq, hc, hb', hcomp, w, hw⟩ :=
    exists_essentiallySmooth_enlargement_containing_pow k p hp Λ 𝔮 n b hb lam
  have hinj : Function.Injective b' := by
    let := b'.toAlgebra
    have hmap : algebraMap D' (primePowerQuotient 𝔮 n) = b' := RingHom.algebraMap_toAlgebra b'
    have : Module.Flat D' (primePowerQuotient 𝔮 n) :=
      RingHom.flat_algebraMap_iff.mp (by rw [hmap]; exact hb')
    have : IsLocalHom (algebraMap D' (primePowerQuotient 𝔮 n)) := by rw [hmap]; exact hbl
    have : Module.FaithfullyFlat D' (primePowerQuotient 𝔮 n) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    have h := FaithfulSMul.algebraMap_injective D' (primePowerQuotient 𝔮 n)
    rwa [hmap] at h
  exact ⟨q, D', hcr, hlr, har, c, b', hcl, hbl, hq, hc, hb', hcomp, by rw [hcomp, hab], hinj,
    RingHom.mem_range.mpr ⟨w, hw⟩⟩

end Stacks.Smoothing

end
