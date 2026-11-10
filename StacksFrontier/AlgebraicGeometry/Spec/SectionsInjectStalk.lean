module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.RingTheory.AssociatedPrime.PrimeComplNonZeroDivisor

/-!
# Sections of `M^~` inject into the stalk at a point dominating all associated points

Let `R` be a Noetherian ring, `M` an `R`-module, and `q` a prime of `R` with the property that

  every associated prime of `M` is contained in `q`.                                     (H)

Geometrically (H) says that every associated point of the quasi-coherent sheaf `M^~` on `Spec R`
specializes to the point `q`.  The main result of this file is that under (H) the germ map

  `Γ(W, M^~) ⟶ (M^~)_q`

is injective for **every** open neighbourhood `W` of `q` — no affineness of `W` is required.
This is the step in the proof of Stacks 05U7 phrased there as: *a section of the kernel would be
supported at a closed subset of `X_s` not meeting `x`, which is a contradiction to our choice of
`X`*.

## The argument

Injectivity is local, so by the sheaf axiom it suffices to show that a section `t` over `W` with
vanishing germ at `q` restricts to zero on each basic open `D(a) ⊆ W`.  Vanishing of the germ
gives a basic open `D(g) ∋ q` on which `t` already restricts to zero, and `g ∉ q`.  On `D(a)` the
sections are the localization `M_a`, and the restriction of `t` to `D(g) ∩ D(a) = D(g * a)`
vanishes; writing `t|_{D(a)}` as a fraction `m / a ^ n` this says that a power of `g * a` kills
`m`, hence that a power of `g` kills `t|_{D(a)}`.  Since the associated primes of `M` all lie in
`q`, an element outside `q` acts injectively on every localization of `M` — this is
`Module.smul_injective_localizedModule_powers_of_associatedPrimes_le` — and therefore
`t|_{D(a)} = 0`.

Note that `a` is an arbitrary element of `R`: the basic opens `D(a)` covering `W` need not
contain `q`, which is why the input lemma has to allow localizing away from an element lying
inside `q`.

## Main results

* `AlgebraicGeometry.tilde.eq_zero_of_germ_eq_zero`: a section of `M^~` over an open
  neighbourhood of `q` whose germ at `q` vanishes is zero.
* `AlgebraicGeometry.tilde.germ_injective`: the germ map `Γ(W, M^~) ⟶ (M^~)_q` is injective.
* `AlgebraicGeometry.tilde.injective_germ_trans_linearEquiv`: the same statement with the stalk
  identified with an arbitrary localization of `M` at the complement of `q`, for instance
  `LocalizedModule q.asIdeal.primeCompl M`.

## References

* [Stacks Project, Tag 05U7](https://stacks.math.columbia.edu/tag/05U7)
-/

@[expose] public noncomputable section

universe u

open TopCat AlgebraicGeometry TopologicalSpace CategoryTheory Opposite PrimeSpectrum

namespace Module

variable {C : Type*} [CommRing C] {N : Type*} [AddCommGroup N] [Module C N]

/-- **An element outside `q` acts injectively on a localization away from an arbitrary element.**
If `C` is Noetherian and every associated prime of `N` is contained in the prime `q`, then for
any `a : C` and any module `N'` exhibited as the localization of `N` at the powers of `a`, every
`r ∉ q` acts injectively on `N'`.

This is `Module.smul_injective_localizedModule_powers_of_associatedPrimes_le` transported along
the canonical isomorphism to an arbitrary realization of the localization.  As there, `a` is
unrestricted; in particular it may lie in `q`. -/
theorem smul_injective_away_of_associatedPrimes_le [IsNoetherianRing C]
    (q : Ideal C) [q.IsPrime] (h : ∀ P ∈ associatedPrimes C N, P ≤ q) (a : C)
    {N' : Type*} [AddCommGroup N'] [Module C N'] (f : N →ₗ[C] N')
    [IsLocalizedModule (Submonoid.powers a) f]
    {r : C} (hr : r ∈ q.primeCompl) {z : N'} (hz : r • z = 0) : z = 0 := by
  have e := IsLocalizedModule.iso (Submonoid.powers a) f
  have h0 : r • e.symm z = 0 := by rw [← map_smul, hz, map_zero]
  have h1 := Module.smul_injective_localizedModule_powers_of_associatedPrimes_le q h a hr h0
  have h2 := congrArg e h1
  simpa using h2

end Module

namespace AlgebraicGeometry

/-- The basic open subset `D(f)` of `Spec R`, with its type spelled as `(Spec R).Opens`.

This is definitionally `PrimeSpectrum.basicOpen f`.  The two spellings differ only in how the
ambient topological space is presented, but the instances for sections of a module over `Spec R`
are stated for opens of the scheme, so they only fire on this one. -/
abbrev specBasicOpen {R : CommRingCat.{u}} (f : R) : (Spec R).Opens := PrimeSpectrum.basicOpen f

namespace tilde

variable {R : CommRingCat.{u}} [IsNoetherianRing R] (M : ModuleCat.{u} R)

/-- **The local step.** Let every associated prime of `M` be contained in the prime `q`, let
`g ∉ q`, and let `V ≤ U` be opens of `Spec R` on which the sections of `M^~` are the
localizations of `M` away from `a` and away from `g * a` respectively — the case of interest is
`U = D(a)` and `V = D(g * a) = D(g) ⊓ D(a)`.  Then a section over `U` restricting to zero on `V`
is itself zero.

The element `a` is arbitrary: `U` need not be a neighbourhood of `q`. -/
theorem eq_zero_of_restrict_eq_zero (q : PrimeSpectrum R)
    (hM : ∀ P ∈ associatedPrimes R M, P ≤ q.asIdeal)
    {g a : R} (hg : g ∈ q.asIdeal.primeCompl)
    (U V : (Spec R).Opens) (hUV : V ≤ U)
    [IsLocalizedModule (Submonoid.powers a) (toOpen M U).hom]
    [IsLocalizedModule (Submonoid.powers (g * a)) (toOpen M V).hom]
    (u : (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (op U))
    (hu : (modulesSpecToSheaf.obj (tilde M)).presheaf.map (homOfLE hUV).op u = 0) :
    u = 0 := by
  -- Write `u` as a fraction `m / a ^ n`.
  obtain ⟨⟨m, ⟨b, hb⟩⟩, hm⟩ :=
    IsLocalizedModule.surj (Submonoid.powers a) (toOpen M U).hom u
  obtain ⟨n, rfl⟩ := hb
  have hm' : (a ^ n) • u = toOpen M U m := hm
  -- The numerator `m` dies in the sections over `V`, ...
  have hres : toOpen M V m = 0 := by
    have h1 : (modulesSpecToSheaf.obj (tilde M)).presheaf.map (homOfLE hUV).op
        (toOpen M U m) = 0 := by
      rw [← hm', map_smul, hu, smul_zero]
    exact h1
  -- ... so a power of `g * a` kills it, ...
  obtain ⟨⟨c, k, rfl⟩, hk⟩ :=
    (IsLocalizedModule.eq_zero_iff (Submonoid.powers (g * a)) (toOpen M V).hom).mp hres
  have hk' : ((g * a) ^ k) • m = 0 := hk
  -- ... hence a power of `g` kills `u`, since `a` already acts invertibly over `U`.
  have key : (a ^ (n + k) * g ^ k) • u = 0 := by
    have h1 : ((g * a) ^ k * a ^ n) • u = 0 := by
      rw [mul_smul, hm', ← map_smul, hk', _root_.map_zero]
    rw [show a ^ (n + k) * g ^ k = (g * a) ^ k * a ^ n by ring]
    exact h1
  have hgk : (g ^ k) • u = 0 := by
    refine IsLocalizedModule.smul_injective (S := Submonoid.powers a) (toOpen M U).hom
      ⟨a ^ (n + k), n + k, rfl⟩ ?_
    change (a ^ (n + k)) • ((g ^ k) • u) = (a ^ (n + k)) • (0 : _)
    rw [smul_zero, ← mul_smul]
    exact key
  -- An element outside `q` is injective on the localization `Γ(U, M^~)` of `M`.
  exact Module.smul_injective_away_of_associatedPrimes_le q.asIdeal hM a (toOpen M U).hom
    (pow_mem hg k) hgk

/-- **A section of `M^~` with vanishing germ at `q` vanishes.** Let `R` be Noetherian, let every
associated prime of the `R`-module `M` be contained in the prime `q`, and let `W` be any open
neighbourhood of `q` in `Spec R`.  A section of `M^~` over `W` whose germ at `q` is zero is
zero. -/
theorem eq_zero_of_germ_eq_zero (q : PrimeSpectrum R)
    (hM : ∀ P ∈ associatedPrimes R M, P ≤ q.asIdeal) (W : (Spec R).Opens) (hq : q ∈ W)
    (t : Γ(tilde M, W)) (ht : (tilde M).presheaf.germ W q hq t = 0) : t = 0 := by
  -- The germ vanishes, so `t` restricts to zero on some neighbourhood `W'` of `q`, ...
  obtain ⟨W', hqW', iU, iV, e⟩ :=
    (tilde M).presheaf.germ_eq q hq hq t 0 (by rw [ht, _root_.map_zero])
  have hzero : (tilde M).presheaf.map iU.op t = 0 := by
    rw [e]; exact _root_.map_zero _
  -- ... hence on a basic open `D(g)` with `g ∉ q`.
  obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hqg, hgW'⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hqW' W'.2
  have hgW'' : specBasicOpen g ≤ W' := hgW'
  have hgW : specBasicOpen g ≤ W := hgW''.trans (leOfHom iU)
  have hres : (tilde M).presheaf.map (homOfLE hgW).op t = 0 := by
    have h2 : (tilde M).presheaf.map (homOfLE hgW'').op ((tilde M).presheaf.map iU.op t) = 0 := by
      rw [hzero]; exact _root_.map_zero _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp] at h2
    exact h2
  -- By the sheaf axiom it is enough to kill `t` on each basic open `D(a) ⊆ W`.
  refine TopCat.Presheaf.IsSheaf.section_ext (tilde M).isSheaf (U := op W) (s := t) (t := 0) ?_
  intro y hy
  obtain ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, hya, haW⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hy W.2
  have haW' : specBasicOpen a ≤ W := haW
  refine ⟨specBasicOpen a, haW', hya, ?_⟩
  rw [show (tilde M).presheaf.map (homOfLE haW').op 0 = 0 from _root_.map_zero _]
  have hle : specBasicOpen (g * a) ≤ specBasicOpen g := PrimeSpectrum.basicOpen_mul_le_left g a
  have hle' : specBasicOpen (g * a) ≤ specBasicOpen a := PrimeSpectrum.basicOpen_mul_le_right g a
  -- Restricting to `D(g * a)` factors through `D(g)`, where `t` is already zero.
  have e1 : (tilde M).presheaf.map (homOfLE hle').op
        ((tilde M).presheaf.map (homOfLE haW').op t)
      = (tilde M).presheaf.map (homOfLE hle).op
        ((tilde M).presheaf.map (homOfLE hgW).op t) := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp]
    rfl
  refine eq_zero_of_restrict_eq_zero M q hM (g := g) (a := a)
    ((PrimeSpectrum.mem_basicOpen g q).mp hqg)
    (specBasicOpen a) (specBasicOpen (g * a)) hle' _ ?_
  change (tilde M).presheaf.map (homOfLE hle').op ((tilde M).presheaf.map (homOfLE haW').op t) = 0
  rw [e1, hres]
  exact _root_.map_zero _

/-- **Sections of `M^~` over a neighbourhood of `q` inject into the stalk at `q`.** Let `R` be
Noetherian and let every associated prime of the `R`-module `M` be contained in the prime `q`.
Then for every open neighbourhood `W` of `q` in `Spec R` — in particular for every affine open
neighbourhood — the germ map `Γ(W, M^~) ⟶ (M^~)_q` is injective. -/
theorem germ_injective (q : PrimeSpectrum R)
    (hM : ∀ P ∈ associatedPrimes R M, P ≤ q.asIdeal) (W : (Spec R).Opens) (hq : q ∈ W) :
    Function.Injective ((tilde M).presheaf.germ W q hq) := by
  intro s t hst
  have h0 : (tilde M).presheaf.germ W q hq (s - t) = 0 := by
    rw [_root_.map_sub, hst, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_germ_eq_zero M q hM W hq _ h0)

/-- **The same statement with the stalk identified with `M_q`.** If `f : M →ₗ[R] N'` exhibits
`N'` as the localization of `M` at the complement of `q` — for instance
`LocalizedModule.mkLinearMap q.asIdeal.primeCompl M` — then the induced map `Γ(W, M^~) → N'` is
injective for every open neighbourhood `W` of `q`. -/
theorem injective_germ_trans_linearEquiv (q : PrimeSpectrum R)
    (hM : ∀ P ∈ associatedPrimes R M, P ≤ q.asIdeal) (W : (Spec R).Opens) (hq : q ∈ W)
    {N' : Type u} [AddCommGroup N'] [Module R N'] (f : M →ₗ[R] N')
    [IsLocalizedModule q.asIdeal.primeCompl f] :
    Function.Injective fun t : Γ(tilde M, W) =>
      IsLocalizedModule.linearEquiv q.asIdeal.primeCompl (toStalk M q).hom f
        ((tilde M).presheaf.germ W q hq t) :=
  (IsLocalizedModule.linearEquiv q.asIdeal.primeCompl (toStalk M q).hom f).injective.comp
    (germ_injective M q hM W hq)

end tilde

end AlgebraicGeometry

end
