module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Ideal.Operations
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CanonicalSectionsMap

/-!
# A Čech correction divisible by a power of the syntomic equation is invisible to a quadratic
obstruction variation

Let `f, g` be a comaximal pair in a commutative ring `B`, so that `Spec B = D(f) ∪ D(g)`. For a
`B`-module `M` the Čech sequence of the two-element cover is exact,

  `0 → M → M_f ⊕ M_g → M_{fg} → 0`,

and its surjectivity on the right is what lets two objects given on `D(f)` and on `D(g)` be
matched on the overlap: a comparison class `ξ ∈ M_{fg}` is written `ξ = a|_{fg} + b|_{fg}` and the
two members are corrected by `a` and by `b`.

This file proves two things about that splitting.

* **The share carried by `D(g)` can be made divisible by any prescribed power of `f`**
  (`Deformation.Examples.CoprimeCover.exists_eq_add_pow_smul`). Comaximality gives
  `1 = u f^N + v g^k` for any `N`, and clearing the denominators of `ξ = m/(f^k g^k)` against
  *that* partition of unity
  rather than against `1 = u f^k + v g^k` leaves the `D(g)`-component inside `f^N · M_g`.
* **A map `∂ = δ + sq` with `δ` additive and `sq` homogeneous of degree two vanishes identically on
  `f^n · M_g` as soon as `f^n` annihilates the target**
  (`Deformation.Examples.CoprimeCover.obstructionVariation_pow_smul_eq_zero`). Both terms acquire a
  factor `f^n` — the quadratic one acquires `f^{2n}` — and a single `f^n` already kills them.

Together (`Deformation.Examples.CoprimeCover.exists_eq_add_obstructionVariation_eq_zero`): *if the
target of `∂` is annihilated by `f^n`, then every comparison class on the overlap admits a Čech
splitting whose `D(g)`-share is annihilated by `∂`.* Non-additivity of `∂` is no obstacle, because
the conclusion is not that `∂` is linear on the available corrections but that it is **zero** on
them.

## Why this is the shape the converse of Stacks 0DZ7 asks for

`StacksFrontier/Deformation/Examples/Linear/FlatAlgebraLiftCoprimeCover.lean` reduces the converse of
Stacks 0DZ7 at a principal multiplicative set to an auxiliary-free gluing principle: for a
comaximal pair `f, g` in a finite type flat `A`-algebra `B` with `A → B_h` syntomic for every
`h ∈ (f)`, and a surjection `A' → A` of Noetherian rings with nilpotent kernel, a flat `A'`-lift of
`B_g` produces one of `B`. It is proved there at a square-zero kernel; past square zero the
difficulty recorded there is that correcting the given lift on `D(g)` changes it, and the
obstruction of the corrected lift is the variation `∂ = δ + sq` of the original's — a Bockstein
plus a cup-square, not an additive map
(`StacksFrontier/Deformation/ObstructionVariationQuadratic.lean`).

The two facts above say that this difficulty is removable, provided one knows that the obstruction
module is annihilated by a power of `f`. In the geometry it is: the obstruction to lifting an
`A_k`-algebra one step along the filtration of the kernel lies in a module which is *finitely
generated* over `B` (the algebra is of finite type over a Noetherian ring) and which *vanishes
after inverting `f`* (over `D(f)` the algebra is syntomic, hence a local complete intersection,
hence has vanishing obstruction module in every coefficient module — the vanishing that Stacks
07M8 rests on, and 07M8 is `Deformation.hasFlatAlgebraLift_of_syntomic`). Those two properties
already
produce the annihilator, and that implication is carried out here
(`Deformation.Examples.CoprimeCover.exists_forall_pow_smul_eq_zero_of_forall_eq_zero`): vanishing
in the localization is annihilation by *some* power of `f`, and finite generation makes one power
do for every element — the uniformity step being
`Stacks.LocalCohomology.exists_pow_smul_eq_zero_of_fg_torsion`
(`StacksFrontier/AlgebraicGeometry/LocalCohomology/CanonicalSectionsMap.lean:129`), which this file
reuses rather than reproves. So the syntomic member of the cover does not merely make its own side
unobstructed: it bounds the whole obstruction module by a power of its own equation, and
corrections divisible by that power are invisible.

## Main results

* `Deformation.Examples.CoprimeCover.exists_eq_add_pow_smul` — the Čech splitting of a two-element
  comaximal cover, with the `D(g)`-share divisible by a prescribed power of `f`.
* `Deformation.Examples.CoprimeCover.eq_zero_of_isCoprime_of_isLocalizedModule` — an element
  vanishing on both members of the cover is zero, so a glued obstruction is detected member by
  member.
* `Deformation.Examples.CoprimeCover.exists_forall_pow_smul_eq_zero_of_forall_eq_zero` — a finitely
  generated module vanishing over `D(f)` is annihilated by one power of `f`.
* `Deformation.Examples.CoprimeCover.pow_smul_eq_zero_of_isLocalizedModule` — an annihilator of a
  module annihilates its localizations.
* `Deformation.Examples.CoprimeCover.apply_pow_smul_eq_zero` — an additive variation vanishes on
  the divisible corrections. This is the form used to carry a correction up one step of the
  filtration: the obstruction to lifting the correction class itself is a Bockstein, hence
  additive.
* `Deformation.Examples.CoprimeCover.obstructionVariation_pow_smul_eq_zero` — `δ + sq` vanishes on
  the divisible corrections.
* `Deformation.Examples.CoprimeCover.exists_eq_add_obstructionVariation_eq_zero` — the two
  combined: a Čech splitting whose `D(g)`-share has vanishing obstruction variation.
* `Deformation.Examples.CoprimeCover.exists_eq_add_obstructionVariation_eq_zero_of_fg` — the same
  with the annihilator not assumed but derived from finite generation and vanishing over `D(f)`.

## Implementation notes

**How these lemmas would close the gluing principle, and what is missing.** Write
`I = ker(A' → A)`, `A_k = A'/Iᵏ`, `K_k = Iᵏ/Iᵏ⁺¹`, and for a coefficient module `N` write `T¹(N)`,
`T²(N)` for the deformation and obstruction modules of `B` over `A`. Let `C'` be the given flat
`A'`-lift of `B_g`. The induction maintains, at each `k`, a flat lift `B_k` of `B` over `A_k`
together with a flat `A'`-lift `D'` of `B_g` whose reduction to `A_k` is `(B_k)_g`; at `k = 1` take
`B_1 = B` and `D' = C'`. One step:

* `(B_k)_f` is syntomic over `A_k`, so it lifts to `A_{k+1}`, and freely: every translate of such a
  lift by `T¹(K_k)_f` is again one.
* `(B_k)_g` lifts to `A_{k+1}` as the reduction of `D'`.
* The two restrict to two lifts of `(B_k)_{fg}`, differing by a comparison class
  `ξ ∈ T¹(K_k)_{fg}`. Split it with `exists_eq_add_pow_smul` at `N = n`, where `f^n` annihilates
  `T²(K_{k+1})` by `exists_forall_pow_smul_eq_zero_of_forall_eq_zero`; correct the two members by
  the two shares and glue.
* The share landing on `D(g)` is divisible by `f^n`, so by
  `obstructionVariation_pow_smul_eq_zero` the corrected lift there has the same obstruction as the
  uncorrected one, namely zero; and by `apply_pow_smul_eq_zero` the Bockstein obstruction to
  carrying the correction itself up the remaining stages vanishes too, which is what turns the
  corrected `A_{k+1}`-lift of `B_g` back into the reduction of an `A'`-lift and so restores the
  invariant.
* The obstruction of the glued `B_{k+1}` then vanishes over `D(f)` because the whole obstruction
  module does, and over `D(g)` by the previous item, hence vanishes by
  `eq_zero_of_isCoprime_of_isLocalizedModule`.

Every step of that argument other than the deformation theory itself is proved in this file. What
is **not** here is the deformation theory: that `A_{k+1}`-lifts of an `A_k`-algebra form a torsor
under `Ext¹(NL, · ⊗ K_k)` when one exists, that the obstruction to a further lift is a class in
`Ext²(NL, · ⊗ K_{k+1})`, that it varies along the torsor by a Bockstein plus a cup-square, that
`Ext²` vanishes for a local complete intersection, and that all of this is natural under
localization. That is the interface recorded as absent in the implementation notes of
`StacksFrontier/Deformation/ObstructionVariationQuadratic.lean` — "no `Ext` API in this repository
presents it" — and it is absent still.

So the gluing principle itself is **not** proved, Stacks 0DZ7 is **not** closed, and no Stacks
attribute is claimed. What this file settles is the local-global algebra the argument runs on, and
in particular that the obstacle recorded in the implementation notes of
`StacksFrontier/Deformation/Examples/Linear/FlatAlgebraLiftCoprimeCover.lean` — that non-additivity of
the obstruction variation prevents the Čech correction from being arranged — is not an obstacle:
the correction on the non-syntomic member can be made one on which the variation is identically
zero.

## References

* [Stacks Project, Tag 0DZ7](https://stacks.math.columbia.edu/tag/0DZ7)
* [Stacks Project, Tag 07M8](https://stacks.math.columbia.edu/tag/07M8)
-/

@[expose] public noncomputable section

universe u

namespace Deformation.Examples.CoprimeCover

/-! ### Comaximality -/

/-- A comaximal pair of elements, in the form the gluing principle of
`StacksFrontier/Deformation/Examples/Linear/FlatAlgebraLiftCoprimeCover.lean` states it, is a coprime
pair. -/
theorem isCoprime_of_sup_span_singleton_eq_top {B : Type u} [CommRing B] {f g : B}
    (hfg : Ideal.span {f} ⊔ Ideal.span {g} = ⊤) : IsCoprime f g :=
  (Ideal.isCoprime_span_singleton_iff f g).mp (Ideal.isCoprime_iff_sup_eq.mpr hfg)

/-! ### Vanishing on both members of the cover -/

/-- An element of a module vanishing in the localization at the powers of `c` is killed by a power
of `c`. -/
private theorem exists_pow_smul_eq_zero_of_map_eq_zero {B : Type u} [CommRing B] (c : B)
    {M Mc : Type u} [AddCommGroup M] [Module B M] [AddCommGroup Mc] [Module B Mc]
    (lc : M →ₗ[B] Mc) [IsLocalizedModule (Submonoid.powers c) lc] {x : M} (hx : lc x = 0) :
    ∃ k : ℕ, c ^ k • x = 0 := by
  obtain ⟨⟨_, k, rfl⟩, hs⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers c) lc).mp hx
  exact ⟨k, by simpa only [Submonoid.smul_def] using hs⟩

/-- **An element of a module vanishing on both members of a two-element comaximal cover is zero.**
Vanishing in `M_f` means annihilation by a power of `f` and vanishing in `M_g` by a power of `g`;
those two powers are again comaximal, so their partition of unity writes the element as a sum of
two zeros.

This is the other local-global step the gluing needs: the obstruction of a glued lift is an element
of a module, and it vanishes as soon as it vanishes over each member of the cover — over the
syntomic member because the whole obstruction module does, and over the other because the lift
carried there extends. -/
theorem eq_zero_of_isCoprime_of_isLocalizedModule {B : Type u} [CommRing B] {f g : B}
    (hfg : IsCoprime f g) {M Mf Mg : Type u} [AddCommGroup M] [Module B M]
    [AddCommGroup Mf] [Module B Mf] [AddCommGroup Mg] [Module B Mg]
    (lf : M →ₗ[B] Mf) (lg : M →ₗ[B] Mg)
    [IsLocalizedModule (Submonoid.powers f) lf] [IsLocalizedModule (Submonoid.powers g) lg]
    (x : M) (hxf : lf x = 0) (hxg : lg x = 0) : x = 0 := by
  obtain ⟨k, hfx⟩ := exists_pow_smul_eq_zero_of_map_eq_zero f lf hxf
  obtain ⟨l, hgx⟩ := exists_pow_smul_eq_zero_of_map_eq_zero g lg hxg
  obtain ⟨u, v, huv⟩ := hfg.pow (m := k) (n := l)
  calc x = (u * f ^ k + v * g ^ l) • x := by rw [huv, one_smul]
    _ = u • (f ^ k • x) + v • (g ^ l • x) := by rw [add_smul, mul_smul, mul_smul]
    _ = 0 := by simp [hfx, hgx]

/-! ### The divisible Čech splitting -/

/-- On a localization at the powers of a product, each factor acts injectively: multiplying by the
other factor turns the hypothesis into injectivity of the product, which is a unit there. -/
theorem smul_pow_injective_of_isLocalizedModule {B : Type u} [CommRing B] (c d : B)
    {M Mcd : Type u} [AddCommGroup M] [Module B M] [AddCommGroup Mcd] [Module B Mcd]
    (lcd : M →ₗ[B] Mcd) [IsLocalizedModule (Submonoid.powers (c * d)) lcd] (k : ℕ) :
    Function.Injective fun x : Mcd => c ^ k • x := by
  have h : Function.Injective fun x : Mcd => ((c * d) ^ k) • x := by
    simpa only [Submonoid.smul_def] using
      IsLocalizedModule.smul_injective lcd (⟨(c * d) ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers (c * d))
  intro x y hxy
  refine h ?_
  change ((c * d) ^ k) • x = ((c * d) ^ k) • y
  rw [mul_pow, mul_comm (c ^ k) (d ^ k), ← smul_smul, ← smul_smul]
  exact congrArg (fun z => d ^ k • z) hxy

/-- Every element of a localization at the powers of `c` can be multiplied by `c ^ k` into the
image of any given `m`. -/
private theorem exists_pow_smul_eq_map {B : Type u} [CommRing B] (c : B)
    {M Mc : Type u} [AddCommGroup M] [Module B M] [AddCommGroup Mc] [Module B Mc]
    (lc : M →ₗ[B] Mc) [IsLocalizedModule (Submonoid.powers c) lc] (m : M) (k : ℕ) :
    ∃ a : Mc, c ^ k • a = lc m :=
  ⟨IsLocalizedModule.mk' (S := Submonoid.powers c) lc m ⟨c ^ k, k, rfl⟩, by
    simpa only [Submonoid.smul_def] using
      IsLocalizedModule.mk'_cancel' (S := Submonoid.powers c) lc m ⟨c ^ k, k, rfl⟩⟩

/-- If `c ^ k • a` and `(c * d) ^ k • ξ` both come from the same `m`, then `a` maps to `d ^ k • ξ`
in the localization at the powers of `c * d`. -/
private theorem map_eq_pow_smul_of_pow_smul_eq {B : Type u} [CommRing B] (c d : B)
    {M Mc Mcd : Type u} [AddCommGroup M] [Module B M] [AddCommGroup Mc] [Module B Mc]
    [AddCommGroup Mcd] [Module B Mcd] (lc : M →ₗ[B] Mc) (lcd : M →ₗ[B] Mcd)
    [IsLocalizedModule (Submonoid.powers (c * d)) lcd] {φ : Mc →ₗ[B] Mcd}
    (hφ : ∀ m : M, φ (lc m) = lcd m) {m : M} {a : Mc} {ξ : Mcd} {k : ℕ}
    (hξ : (c * d) ^ k • ξ = lcd m) (ha : c ^ k • a = lc m) : φ a = d ^ k • ξ := by
  refine smul_pow_injective_of_isLocalizedModule c d lcd k ?_
  change c ^ k • φ a = c ^ k • (d ^ k • ξ)
  rw [← LinearMap.map_smul, ha, hφ, smul_smul, ← mul_pow, hξ]

/-- **The Čech splitting of a two-element comaximal cover, with the share on the second member
divisible by a prescribed power of the first equation.** Let `f, g` be coprime in `B`, let `M` be a
`B`-module with localizations `M_f`, `M_g`, `M_{fg}` and let `ξ ∈ M_{fg}`. Then for every `N` there
are `a ∈ M_f` and `b ∈ M_g` with `ξ = a|_{fg} + (f^N b)|_{fg}`.

Ordinary Čech exactness is the case `N = 0`: writing `ξ = m/(f^k g^k)` and `1 = u f^k + v g^k`
gives `ξ = v·(m/g^k) + u·(m/f^k)`. The refinement is to clear the denominators against
`1 = u f^{N+k} + v g^k` instead, which is available for every `N` because `f^{N+k}` and `g^k` are
coprime as soon as `f` and `g` are; the surplus `f^N` then stays with the `M_g`-component.

The comparison maps are taken as data satisfying the only property that pins them down, namely that
they commute with the localization maps; the canonical maps are the unique such. -/
theorem exists_eq_add_pow_smul {B : Type u} [CommRing B] {f g : B} (hfg : IsCoprime f g)
    {M Mf Mg Mfg : Type u}
    [AddCommGroup M] [Module B M] [AddCommGroup Mf] [Module B Mf]
    [AddCommGroup Mg] [Module B Mg] [AddCommGroup Mfg] [Module B Mfg]
    (lf : M →ₗ[B] Mf) (lg : M →ₗ[B] Mg) (lfg : M →ₗ[B] Mfg)
    [IsLocalizedModule (Submonoid.powers f) lf]
    [IsLocalizedModule (Submonoid.powers g) lg]
    [IsLocalizedModule (Submonoid.powers (f * g)) lfg]
    {φ : Mf →ₗ[B] Mfg} (hφ : ∀ m : M, φ (lf m) = lfg m)
    {ψ : Mg →ₗ[B] Mfg} (hψ : ∀ m : M, ψ (lg m) = lfg m)
    (N : ℕ) (ξ : Mfg) :
    ∃ (a : Mf) (b : Mg), ξ = φ a + ψ (f ^ N • b) := by
  obtain ⟨⟨m, ⟨_, k, rfl⟩⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers (f * g)) lfg ξ
  have hkey : ((f * g) ^ k) • ξ = lfg m := by simpa only [Submonoid.smul_def] using hs
  obtain ⟨a₀, hfa⟩ := exists_pow_smul_eq_map f lf m k
  obtain ⟨b₀, hgb⟩ := exists_pow_smul_eq_map g lg m k
  have hA : φ a₀ = g ^ k • ξ := map_eq_pow_smul_of_pow_smul_eq f g lf lfg hφ hkey hfa
  have hB : ψ b₀ = f ^ k • ξ := by
    have : IsLocalizedModule (Submonoid.powers (g * f)) lfg := by
      rw [mul_comm g f]
      infer_instance
    exact map_eq_pow_smul_of_pow_smul_eq g f lg lfg hψ (by rw [mul_comm g f, hkey]) hgb
  obtain ⟨u, v, huv⟩ := hfg.pow (m := N + k) (n := k)
  have hscal : v * g ^ k + f ^ N * u * f ^ k = 1 := by linear_combination huv
  refine ⟨v • a₀, u • b₀, ?_⟩
  rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul, hA, hB, smul_smul, smul_smul,
    smul_smul, ← add_smul, hscal, one_smul]

/-! ### A divisible correction is invisible to the obstruction variation -/

/-- An annihilator of a module annihilates each of its localizations. -/
theorem pow_smul_eq_zero_of_isLocalizedModule {B : Type u} [CommRing B] {f g : B}
    {T Tg : Type u} [AddCommGroup T] [Module B T] [AddCommGroup Tg] [Module B Tg]
    (lT : T →ₗ[B] Tg) [IsLocalizedModule (Submonoid.powers g) lT] {n : ℕ}
    (hT : ∀ t : T, f ^ n • t = 0) (y : Tg) : f ^ n • y = 0 := by
  obtain ⟨⟨t, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers g) lT y
  have hs' : (s : B) • y = lT t := by simpa only [Submonoid.smul_def] using hs
  refine IsLocalizedModule.smul_injective lT s ?_
  change s • (f ^ n • y) = s • (0 : Tg)
  simp only [Submonoid.smul_def, smul_zero]
  rw [smul_smul, mul_comm (s : B) (f ^ n), ← smul_smul, hs', ← LinearMap.map_smul, hT, map_zero]

/-- **An additive variation vanishes on the corrections divisible by an annihilator of its
target.** This is the step that carries a correction chosen at one stage of a filtration up to the
next: the obstruction to lifting the correction class itself is a Bockstein, which is additive. -/
theorem apply_pow_smul_eq_zero {B : Type u} [CommRing B] {f : B} {Mg Tg : Type u}
    [AddCommGroup Mg] [Module B Mg] [AddCommGroup Tg] [Module B Tg] {n : ℕ}
    (hann : ∀ y : Tg, f ^ n • y = 0) (δ : Mg →ₗ[B] Tg) (b : Mg) : δ (f ^ n • b) = 0 := by
  rw [LinearMap.map_smul, hann]

/-- **The obstruction variation vanishes on the corrections divisible by an annihilator of its
target.** Let `δ` be additive and `sq` homogeneous of degree two, both into a module annihilated by
`f^n`. Then `δ b + sq b = 0` for every `b` in `f^n · M_g`.

This is the point at which the non-additivity of `∂ = δ + sq` stops mattering. `∂` is indeed not a
homomorphism — `StacksFrontier/Deformation/ObstructionVariationQuadratic.lean` proves that its zero
set is not even closed under addition — but on the divisible corrections it is not merely additive,
it is identically zero: `δ` picks up a factor `f^n` from linearity and `sq` a factor `f^{2n}` from
homogeneity, and one factor `f^n` already annihilates the target. -/
theorem obstructionVariation_pow_smul_eq_zero {B : Type u} [CommRing B] {f : B} {Mg Tg : Type u}
    [AddCommGroup Mg] [Module B Mg] [AddCommGroup Tg] [Module B Tg] {n : ℕ}
    (hann : ∀ y : Tg, f ^ n • y = 0) (δ : Mg →ₗ[B] Tg) (sq : Mg → Tg)
    (hsq : ∀ (c : B) (x : Mg), sq (c • x) = c ^ 2 • sq x) (b : Mg) :
    δ (f ^ n • b) + sq (f ^ n • b) = 0 := by
  rw [apply_pow_smul_eq_zero hann δ b, zero_add, hsq, pow_two, ← smul_smul, hann]

/-- **The Čech correction on the second member of a two-element comaximal cover can be chosen with
vanishing obstruction variation.** Let `f, g` be coprime in `B`, let `M` be a `B`-module with its
three localizations and comparison maps, let `T` be a `B`-module annihilated by `f^n` with
localization `T_g`, and let `δ + sq` be a variation map `M_g → T_g` with `δ` additive and `sq`
homogeneous of degree two. Then every comparison class `ξ` on the overlap splits as `ξ = a| + b|`
with `δ b + sq b = 0`.

Read in the deformation theory of a comaximal pair with one syntomic member: the matching of a lift
on the syntomic `D(f)` with a given lift on `D(g)` can always be arranged with a correction on
`D(g)` that does not change the obstruction there. The hypothesis `hT` is what the syntomic member
supplies — the obstruction module is finitely generated over `B` and dies on `D(f)`, hence is
annihilated by a power of `f` — and the conclusion is what the gluing needs. The
deformation-theoretic identification of `M`, `T`, `δ` and `sq` is not carried out in this
repository; see the module docstring. -/
theorem exists_eq_add_obstructionVariation_eq_zero {B : Type u} [CommRing B] {f g : B}
    (hfg : IsCoprime f g) {M Mf Mg Mfg T Tg : Type u}
    [AddCommGroup M] [Module B M] [AddCommGroup Mf] [Module B Mf]
    [AddCommGroup Mg] [Module B Mg] [AddCommGroup Mfg] [Module B Mfg]
    [AddCommGroup T] [Module B T] [AddCommGroup Tg] [Module B Tg]
    (lf : M →ₗ[B] Mf) (lg : M →ₗ[B] Mg) (lfg : M →ₗ[B] Mfg)
    [IsLocalizedModule (Submonoid.powers f) lf]
    [IsLocalizedModule (Submonoid.powers g) lg]
    [IsLocalizedModule (Submonoid.powers (f * g)) lfg]
    {φ : Mf →ₗ[B] Mfg} (hφ : ∀ m : M, φ (lf m) = lfg m)
    {ψ : Mg →ₗ[B] Mfg} (hψ : ∀ m : M, ψ (lg m) = lfg m)
    (lT : T →ₗ[B] Tg) [IsLocalizedModule (Submonoid.powers g) lT] {n : ℕ}
    (hT : ∀ t : T, f ^ n • t = 0)
    (δ : Mg →ₗ[B] Tg) (sq : Mg → Tg) (hsq : ∀ (c : B) (x : Mg), sq (c • x) = c ^ 2 • sq x)
    (ξ : Mfg) :
    ∃ (a : Mf) (b : Mg), ξ = φ a + ψ b ∧ δ b + sq b = 0 := by
  obtain ⟨a, b, hab⟩ := exists_eq_add_pow_smul hfg lf lg lfg hφ hψ n ξ
  exact ⟨a, f ^ n • b, hab,
    obstructionVariation_pow_smul_eq_zero
      (pow_smul_eq_zero_of_isLocalizedModule (g := g) lT hT) δ sq hsq b⟩

/-! ### Where the annihilator comes from -/

/-- **The annihilator the syntomic member of the cover supplies.** A finitely generated `B`-module
which vanishes after inverting `f` is annihilated by a single power of `f`: each element is killed
by some power, because that is what vanishing in the localization means, and finite generation
makes one power do for all of them.

Both hypotheses are properties of the obstruction module of the lifting problem that the tag's own
data gives: it is finitely generated over `B` because `B` is of finite type over a Noetherian ring,
and it vanishes after inverting `f` because `B_f` is syntomic over `A`, hence a local complete
intersection, hence unobstructed in every coefficient module. The conclusion is the hypothesis `hT`
of `Deformation.Examples.CoprimeCover.exists_eq_add_obstructionVariation_eq_zero`. -/
theorem exists_forall_pow_smul_eq_zero_of_forall_eq_zero {B : Type u} [CommRing B] {f : B}
    {T Tf : Type u} [AddCommGroup T] [Module B T] [AddCommGroup Tf] [Module B Tf]
    (lTf : T →ₗ[B] Tf) [IsLocalizedModule (Submonoid.powers f) lTf]
    (hfin : (⊤ : Submodule B T).FG) (hvan : ∀ t : T, lTf t = 0) :
    ∃ n : ℕ, ∀ t : T, f ^ n • t = 0 := by
  have htors : ∀ t ∈ (⊤ : Submodule B T), ∃ k : ℕ, f ^ k • t = 0 := by
    intro t _
    exact exists_pow_smul_eq_zero_of_map_eq_zero f lTf (hvan t)
  obtain ⟨n, hn⟩ := Stacks.LocalCohomology.exists_pow_smul_eq_zero_of_fg_torsion
    (⊤ : Submodule B T) hfin f htors
  exact ⟨n, fun t => hn t Submodule.mem_top⟩

/-- **The Čech correction on the non-syntomic member can be chosen unobstructed, from the two
properties of the obstruction module that the cover provides.** Same conclusion as
`Deformation.Examples.CoprimeCover.exists_eq_add_obstructionVariation_eq_zero`, with the
annihilator hypothesis replaced by the two statements it comes from: the obstruction module `T` is
finitely generated over `B`, and it vanishes after inverting `f`.

This is the whole of the local-global mechanism, with no annihilator assumed: comaximality of the
cover and vanishing of the obstruction module over the syntomic member are enough to make every
comparison class on the overlap splittable with an obstruction-free share on the other member. -/
theorem exists_eq_add_obstructionVariation_eq_zero_of_fg {B : Type u} [CommRing B] {f g : B}
    (hfg : IsCoprime f g) {M Mf Mg Mfg T Tf Tg : Type u}
    [AddCommGroup M] [Module B M] [AddCommGroup Mf] [Module B Mf]
    [AddCommGroup Mg] [Module B Mg] [AddCommGroup Mfg] [Module B Mfg]
    [AddCommGroup T] [Module B T] [AddCommGroup Tf] [Module B Tf]
    [AddCommGroup Tg] [Module B Tg]
    (lf : M →ₗ[B] Mf) (lg : M →ₗ[B] Mg) (lfg : M →ₗ[B] Mfg)
    [IsLocalizedModule (Submonoid.powers f) lf]
    [IsLocalizedModule (Submonoid.powers g) lg]
    [IsLocalizedModule (Submonoid.powers (f * g)) lfg]
    {φ : Mf →ₗ[B] Mfg} (hφ : ∀ m : M, φ (lf m) = lfg m)
    {ψ : Mg →ₗ[B] Mfg} (hψ : ∀ m : M, ψ (lg m) = lfg m)
    (lTf : T →ₗ[B] Tf) [IsLocalizedModule (Submonoid.powers f) lTf]
    (lT : T →ₗ[B] Tg) [IsLocalizedModule (Submonoid.powers g) lT]
    (hfin : (⊤ : Submodule B T).FG) (hvan : ∀ t : T, lTf t = 0)
    (δ : Mg →ₗ[B] Tg) (sq : Mg → Tg) (hsq : ∀ (c : B) (x : Mg), sq (c • x) = c ^ 2 • sq x)
    (ξ : Mfg) :
    ∃ (a : Mf) (b : Mg), ξ = φ a + ψ b ∧ δ b + sq b = 0 := by
  obtain ⟨n, hn⟩ := exists_forall_pow_smul_eq_zero_of_forall_eq_zero (f := f) lTf hfin hvan
  exact exists_eq_add_obstructionVariation_eq_zero hfg lf lg lfg hφ hψ lT hn δ sq hsq ξ

end Deformation.Examples.CoprimeCover

end
