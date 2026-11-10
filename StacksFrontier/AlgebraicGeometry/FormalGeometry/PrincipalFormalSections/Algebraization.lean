module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalSections.Comparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalSections.Krull
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.Finiteness
public import StacksFrontier.RingTheory.LocalCohomology.MappingConeH0.Cover
public import StacksFrontier.RingTheory.LocalCohomology.SectionsIso.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Algebraization of formal sections at a principal formal locus

**[Stacks, Tag 0EIH].** Let `A` be a Noetherian ring, let `f ∈ 𝔞 ⊆ A` be an element of an ideal
of `A`, and let `M` be a finite `A`-module. Assume `A` is `f`-adically complete, `f` is a
nonzerodivisor on `M`, and `H¹_𝔞(M/fM)` is a finite `A`-module. Then, with
`U = Spec(A) ∖ V(𝔞)`, the canonical map

`colim_V Γ(V, M̃) ⟶ lim_n Γ(U, (M/fⁿM)~)`

is an isomorphism, the colimit being over the opens `V ⊆ U` containing `U ∩ V(f)`.

## The proof

Write `N = lim_n Γ(U, (M/fⁿM)~)` for the target and `θ : M ⟶ N` for the canonical map, which
sends `m` to the family of constant sections `m mod fⁿM`.

**The target is a finite module on which `f` is a nonzerodivisor.** Finiteness of `H¹_𝔞(M/fM)`
makes `Γ(U, (M/fM)~)` finite, by the four-term sequence of [Stacks, Tag 0DWR]; the tower
`Γ(U, (M/fⁿM)~)` then satisfies the hypotheses of [Stacks, Tag 0BLB], whose three conclusions —
`N` finite, `f` a nonzerodivisor on `N`, and `ker(N ⟶ Γ(U, (M/fⁿM)~)) = fⁿN` — are proved in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/PrincipalFormalSections/Limit.lean`.

**`θ` is an isomorphism near the formal locus.** For `g ∈ 𝔞` the kernel and the cokernel of `θ`
are divisible by `f` up to powers of `g`: this is
`Stacks.Algebraization.FormalSections.exists_pow_smul_eq_smul_of_toLimModule_eq_zero` and
`Stacks.Algebraization.FormalSections.exists_pow_smul_eq_add_smul`, both read off the level-one
component, where the sections on the standard open `D(g)` are the localization of `M/fM` at `g`.
At a point `p` of the formal locus some `g ∈ 𝔞` avoids `p`, and `f ∈ p`, so Nakayama's lemma
kills the kernel and the cokernel at `p`. Their supports are closed because they are finite
modules, so the complement of the union of those supports is a neighbourhood `V` of the formal
locus on which `θ` — and, by the same two conditions propagated to the quotients, each
`M/fⁿM ⟶ N/fⁿN` — induces a bijection on sections.

**The two sides agree on `V`.** For `x ∈ N` the level-`n` component `xₙ`, pushed into the
sections of `(N/fⁿN)~`, is the constant section attached to `x mod fⁿN`
(`Stacks.Algebraization.FormalSections.limPush_eq_limConst`): both sides are linear in `x`, they
agree on the image of `M` by the definition of `θ`, and the cokernel of `M ⟶ N/fⁿN` is killed by
a power of each generator of `𝔞`, so they agree after multiplying by such a power, hence on the
standard open of that generator — and those standard opens cover `U`. Surjectivity of the
comparison follows: the section of `M̃` on `V` corresponding to the constant section of `Ñ`
attached to `x` has `x` as its comparison.

**Injectivity** needs no hypothesis beyond the nonzerodivisor one. A section of `M̃` on a
neighbourhood `W` of the formal locus whose comparison vanishes has all its reductions modulo
`fⁿ` equal to zero, so at every point `p` of the formal locus its value lies in every `fⁿM_p`
and therefore vanishes, by Krull's intersection theorem at `p`
(`Stacks.Algebraization.FormalSections.exists_notMem_smul_eq_zero_of_forall_mem_powSmul`). The
locus where a section vanishes is open and now contains the formal locus, so the section dies in
the colimit.

## Main definitions

* `Stacks.Algebraization.FormalSections.limModule` — the target `N`, as a module.
* `Stacks.Algebraization.FormalSections.toLimModule` — the canonical map `M ⟶ N`.
* `Stacks.Algebraization.FormalSections.LocalIso` — the two local conditions on `M ⟶ N` at a
  point: injective and surjective up to factors outside that point.
* `Stacks.Algebraization.FormalSections.limPush` and
  `Stacks.Algebraization.FormalSections.limConst` — the two maps compared by the key
  compatibility.

## Main results

* `Stacks.Algebraization.FormalSections.exists_localIso_nbhd` — a neighbourhood of the formal
  locus on which `M ⟶ N` is locally bijective.
* `Stacks.Algebraization.FormalSections.limPush_eq_limConst` — the key compatibility.
* `Stacks.Algebraization.FormalSections.isIso_formalComparison` — **[Stacks, Tag 0EIH]**.

## Implementation notes

The quotient `M/fM` is `Stacks.Algebraization.FormalSections.Quot f M 1`, the quotient of `M` by
the submodule `fM`; `Stacks.Algebraization.FormalSections.powSmul_one` identifies that submodule
with `Ideal.span {f} • ⊤`, the spelling the rest of the library uses. The hypothesis on
`H¹_𝔞(M/fM)` is stated with `Stacks.LocalCohomology.localCohomologyModule`, the library's local
cohomology, for the finitely generated ideal `𝔞`.

The membership `f ∈ 𝔞` is carried by the tagged statement, because the source carries it, but it
is not consumed: the proof uses only completeness, the nonzerodivisor hypothesis and the
finiteness of `H¹_𝔞(M/fM)`, so the conclusion holds for every `f` and every ideal `𝔞`.

## References

* [Stacks Project, Tag 0EIH](https://stacks.math.columbia.edu/tag/0EIH)
* [Stacks Project, Tag 0BLB](https://stacks.math.columbia.edu/tag/0BLB)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/
@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open PrimeSpectrum (basicOpen)
open Stacks.LocalCohomology

universe u

namespace Stacks.Algebraization.FormalSections

/-! ### Elementary facts about the open `U = Spec A ∖ V(𝔞)` -/

variable {A : Type u} [CommRing A]

/-- A prime `p` lies in `U = Spec A ∖ V(𝔞)` if and only if `𝔞 ⊄ p`. -/
theorem mem_complOpen_iff {a : Ideal A} {p : PrimeSpectrum A} :
    p ∈ complOpen A a ↔ ¬ (a : Set A) ⊆ p.asIdeal :=
  Iff.rfl

/-- For `g ∈ 𝔞`, the standard open `D(g)` is contained in `U = Spec A ∖ V(𝔞)`. -/
theorem basicOpen_le_complOpen {a : Ideal A} {g : A} (hg : g ∈ a) :
    (basicOpen g : Opens (PrimeSpectrum.Top A)) ≤ complOpen A a := by
  intro p hp
  exact fun hsub ↦ hp (hsub hg)

/-- A point `p` of `U = Spec A ∖ V(𝔞)` lies in `D(g)` for some `g ∈ 𝔞`. -/
theorem exists_mem_notMem_of_mem_complOpen {a : Ideal A} {p : PrimeSpectrum A}
    (hp : p ∈ complOpen A a) : ∃ g ∈ a, g ∉ p.asIdeal := by
  by_contra hcon
  push Not at hcon
  exact hp hcon

/-! ### The comparison module `N = lim Γ(U, (M/fⁿM)~)` and the map from `M` -/

variable {a : Ideal A} {f : A} (M : ModuleCat.{u} A)

/-- The target of the comparison map: `N = lim_n Γ(U, (M/fⁿM)~)`, as a module. -/
abbrev limModule : ModuleCat.{u} A := ModuleCat.of A (formalLimit f M (complOpen A a))

/-- The canonical map `M ⟶ N`. -/
def toLimModule : M ⟶ limModule (a := a) (f := f) M :=
  ModuleCat.ofHom (toFormalLimit f M (complOpen A a))

/-- The level-`n` component of the image of `m` in `N` is the constant section of `(M/fⁿM)~` on
`U` determined by `m mod fⁿM`. -/
@[simp]
theorem toLimModule_apply_level (m : M) (n : ℕ) :
    (toLimModule (a := a) (f := f) M m).1 n =
      moduleSectionsMk (Quot f M n) (complOpen A a) (quotMk f M n m) := rfl

/-- A multiple of `z` dies in `N / im(M ⟶ N)` exactly when it lies in the image of `M`. -/
private theorem smul_mkQ_range_eq_zero_iff (c : A) (z : formalLimit f M (complOpen A a)) :
    c • (LinearMap.range (toLimModule (a := a) (f := f) M).hom).mkQ z = 0 ↔
      ∃ m : M, c • z = toLimModule (a := a) (f := f) M m := by
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact exists_congr fun m ↦ eq_comm

variable [IsNoetherianRing A] [Module.Finite A (M : Type u)]
  (hf : IsSMulRegular (M : Type u) f)

include hf

/-! ### Divisibility of the kernel and the cokernel of `M ⟶ N` -/

omit [IsNoetherianRing A] [Module.Finite A (M : Type u)] in
/-- **The kernel of `M ⟶ N` is divisible by `f` up to powers of any `g ∈ 𝔞`.** -/
theorem exists_pow_smul_eq_smul_of_toLimModule_eq_zero {g : A} (hg : g ∈ a) (m : M)
    (hm : toLimModule (a := a) (f := f) M m = 0) :
    ∃ (k : ℕ) (m' : M), toLimModule (a := a) (f := f) M m' = 0 ∧ g ^ k • m = f • m' := by
  have hzero : moduleSectionsMk (Quot f M 1) (complOpen A a) (quotMk f M 1 m) = 0 :=
    congrFun (congrArg Subtype.val hm) 1
  have hres : moduleSectionsMk (Quot f M 1) (basicOpen g) (quotMk f M 1 m) = 0 := by
    rw [← moduleSectionsRestrict_moduleSectionsMk (M := Quot f M 1)
      (basicOpen_le_complOpen hg) (quotMk f M 1 m), hzero, map_zero]
  obtain ⟨k, hk⟩ :=
    exists_pow_smul_eq_zero_of_moduleSectionsMk_eq_zero (Quot f M 1) g (quotMk f M 1 m) hres
  have hk' : quotMk f M 1 (g ^ k • m) = 0 := by
    rwa [map_smul]
  obtain ⟨m', hm'⟩ := (quotMk_eq_zero_iff f M).1 hk'
  rw [pow_one] at hm'
  refine ⟨k, m', ?_, hm'.symm⟩
  refine isSMulRegular_formalLimit f M (complOpen A a) hf ?_
  change f • (toFormalLimit f M (complOpen A a)) m' = f • 0
  rw [smul_zero, ← map_smul, hm', map_smul]
  change g ^ k • (toLimModule (a := a) (f := f) M m) = 0
  rw [hm, smul_zero]

omit [IsNoetherianRing A] [Module.Finite A (M : Type u)] in
/-- **The cokernel of `M ⟶ N` is divisible by `f` up to powers of any `g ∈ 𝔞`.** -/
theorem exists_pow_smul_eq_add_smul {r : ℕ} (gs : Fin r → A) (hgs : Ideal.span (Set.range gs) = a)
    {g : A} (hg : g ∈ a) (z : formalLimit f M (complOpen A a)) :
    ∃ (k : ℕ) (m : M) (z' : formalLimit f M (complOpen A a)),
      g ^ k • z = toLimModule (a := a) (f := f) M m + f • z' := by
  have hgU : (basicOpen g : Opens (PrimeSpectrum.Top A)) ≤ complOpen A a :=
    basicOpen_le_complOpen hg
  obtain ⟨k₀, q, hq⟩ := exists_pow_smul_eq_moduleSectionsMk (Quot f M 1) g
    (moduleSectionsRestrict (Quot f M 1) hgU (z.1 1))
  obtain ⟨m, rfl⟩ := quotMk_surjective f M 1 q
  set w : formalLimit f M (complOpen A a) :=
    g ^ k₀ • z - toLimModule (a := a) (f := f) M m with hw
  have hwres : moduleSectionsRestrict (Quot f M 1) hgU (w.1 1) = 0 := by
    have h1 : w.1 1 = g ^ k₀ • z.1 1 -
        moduleSectionsMk (Quot f M 1) (complOpen A a) (quotMk f M 1 m) := rfl
    rw [h1, map_sub, map_smul, hq,
      moduleSectionsRestrict_moduleSectionsMk (M := Quot f M 1) hgU (quotMk f M 1 m), sub_self]
  obtain ⟨l, hl⟩ := exists_pow_smul_eq_zero_of_restrict_basicOpen_eq_zero gs
    (complementZeroLocus_eq_iSup_basicOpen gs a hgs) hgU (w.1 1) hwres
  have hlevel : ((g ^ l • w : formalLimit f M (complOpen A a))).1 1 = 0 := hl
  obtain ⟨z', hz'⟩ := exists_smul_eq_of_level_one_eq_zero f M (complOpen A a) hf
    (g ^ l • w) hlevel
  refine ⟨l + k₀, g ^ l • m, z', ?_⟩
  have hthis := hz'.1
  rw [hw, smul_sub] at hthis
  rw [show (toLimModule (a := a) (f := f) M) (g ^ l • m) =
      g ^ l • (toLimModule (a := a) (f := f) M) m from
    map_smul (toLimModule (a := a) (f := f) M).hom (g ^ l) m, hthis, pow_add, mul_smul]
  abel


omit [IsNoetherianRing A] [Module.Finite A (M : Type u)] in
/-- **Iterating the cokernel divisibility.** -/
theorem exists_pow_smul_eq_add_pow_smul {r : ℕ} (gs : Fin r → A)
    (hgs : Ideal.span (Set.range gs) = a) {g : A} (hg : g ∈ a) (n : ℕ) :
    ∀ z : formalLimit f M (complOpen A a),
      ∃ (k : ℕ) (m : M) (z' : formalLimit f M (complOpen A a)),
        g ^ k • z = toLimModule (a := a) (f := f) M m + f ^ n • z' := by
  induction n with
  | zero => exact fun z ↦ ⟨0, 0, z, by simp⟩
  | succ n ih =>
    intro z
    obtain ⟨k, m, z', hkmz⟩ := ih z
    obtain ⟨k', m', z'', hk'⟩ := exists_pow_smul_eq_add_smul M hf gs hgs hg z'
    refine ⟨k' + k, g ^ k' • m + f ^ n • m', z'', ?_⟩
    have e1 : (toLimModule (a := a) (f := f) M) (g ^ k' • m + f ^ n • m') =
        g ^ k' • (toLimModule (a := a) (f := f) M) m +
          f ^ n • (toLimModule (a := a) (f := f) M) m' := by
      rw [map_add, map_smul, map_smul]
    have hgoal : g ^ (k' + k) • z =
        g ^ k' • ((toLimModule (a := a) (f := f) M) m + f ^ n • z') := by
      rw [pow_add, mul_smul, hkmz]
    have hcomm : g ^ k' • (f ^ n • z') = f ^ n • (g ^ k' • z') := smul_comm _ _ _
    have hpow : f ^ n • (f • z'') = f ^ (n + 1) • z'' := by rw [smul_smul, ← pow_succ]
    rw [hgoal, e1, smul_add, hcomm, hk', smul_add, hpow]
    abel

/-! ### The local conditions at a point of the formal locus -/

/-- Let `g ∈ 𝔞` and let `p` be a prime with `f ∈ p` and `g ∉ p`. Every element of the kernel of
`M ⟶ N` is killed by some element outside `p`. -/
theorem exists_notMem_smul_eq_zero_of_toLimModule_eq_zero {g : A} (hg : g ∈ a)
    {p : PrimeSpectrum A} (hfp : f ∈ p.asIdeal) (hgp : g ∉ p.asIdeal) (m : M)
    (hm : toLimModule (a := a) (f := f) M m = 0) :
    ∃ c ∈ p.asIdeal.primeCompl, c • m = 0 := by
  have : p.asIdeal.IsPrime := p.2
  have hdiv : ∀ w ∈ LinearMap.ker (toLimModule (a := a) (f := f) M).hom,
      ∃ w' ∈ LinearMap.ker (toLimModule (a := a) (f := f) M).hom, ∃ g' : A,
        g' ∉ p.asIdeal ∧ f • w' = g' • w := by
    intro w hw
    obtain ⟨k, w', hw', hk⟩ := exists_pow_smul_eq_smul_of_toLimModule_eq_zero M hf hg w
      (LinearMap.mem_ker.1 hw)
    exact ⟨w', LinearMap.mem_ker.2 hw', g ^ k,
      fun hmem ↦ hgp (p.2.mem_of_pow_mem k hmem), hk.symm⟩
  obtain ⟨c, hc, hcm⟩ :=
    Stacks.AlgebraicGeometry.CodimensionOneObstruction.exists_notMem_smul_eq_zero_of_mem
      (LinearMap.ker (toLimModule (a := a) (f := f) M).hom) hfp hdiv (LinearMap.mem_ker.2 hm)
  exact ⟨c, hc, hcm⟩

omit [IsNoetherianRing A] [Module.Finite A (M : Type u)] in
/-- Let `g ∈ 𝔞` and let `p` be a prime with `f ∈ p` and `g ∉ p`. If `N` is a finite module, then
every element of `N` has a multiple by some element outside `p` in the image of `M ⟶ N`. -/
theorem exists_notMem_smul_mem_range {r : ℕ} (gs : Fin r → A)
    (hgs : Ideal.span (Set.range gs) = a) {g : A} (hg : g ∈ a) {p : PrimeSpectrum A}
    (hfp : f ∈ p.asIdeal) (hgp : g ∉ p.asIdeal)
    [Module.Finite A (formalLimit f M (complOpen A a))]
    (z : formalLimit f M (complOpen A a)) :
    ∃ c ∈ p.asIdeal.primeCompl, ∃ m : M, c • z = toLimModule (a := a) (f := f) M m := by
  have : p.asIdeal.IsPrime := p.2
  set Rng := LinearMap.range (toLimModule (a := a) (f := f) M).hom
  have hdiv : ∀ w : (formalLimit f M (complOpen A a) ⧸ Rng),
      ∃ w' : (formalLimit f M (complOpen A a) ⧸ Rng), ∃ g' : A, g' ∉ p.asIdeal ∧
        f • w' = g' • w := by
    intro w
    obtain ⟨y, rfl⟩ := Rng.mkQ_surjective w
    obtain ⟨k, m, z', hk⟩ := exists_pow_smul_eq_add_smul M hf gs hgs hg y
    refine ⟨Rng.mkQ z', g ^ k, fun hmem ↦ hgp (p.2.mem_of_pow_mem k hmem), ?_⟩
    have h2 : Rng.mkQ (g ^ k • y) =
        Rng.mkQ ((toLimModule (a := a) (f := f) M) m + f • z') := by rw [hk]
    rw [map_add, map_smul, map_smul,
      show Rng.mkQ ((toLimModule (a := a) (f := f) M) m) = 0 from
        (Submodule.Quotient.mk_eq_zero Rng).2 ⟨m, rfl⟩, zero_add] at h2
    exact h2.symm
  obtain ⟨c, hcp, hc⟩ :=
    Stacks.AlgebraicGeometry.CodimensionOneObstruction.exists_notMem_smul_eq_zero hfp hdiv
      (Rng.mkQ z)
  exact ⟨c, hcp, (smul_mkQ_range_eq_zero_iff M c z).1 hc⟩

/-! ### Propagating the local conditions to the quotients -/

end Stacks.Algebraization.FormalSections

namespace Stacks.Algebraization.FormalSections

variable {A : Type u} [CommRing A] {f : A} {M P : ModuleCat.{u} A} (u : M ⟶ P)
  {p : PrimeSpectrum A}

/-- If `u : M ⟶ P` is injective and surjective up to factors outside `p`, then the kernel of the
induced map `M/fⁿM ⟶ P/fⁿP` is killed, elementwise, by factors outside `p`. -/
theorem quotMap_ker_cond
    (hker : ∀ m : M, u m = 0 → ∃ c ∈ p.asIdeal.primeCompl, c • m = 0)
    (hcoker : ∀ z : P, ∃ c ∈ p.asIdeal.primeCompl, ∃ m : M, c • z = u m)
    (n : ℕ) (q : Quot f M n) (hq : quotMap f u n q = 0) :
    ∃ c ∈ p.asIdeal.primeCompl, c • q = 0 := by
  obtain ⟨m, rfl⟩ := quotMk_surjective f M n q
  rw [quotMap_quotMk, quotMk_eq_zero_iff] at hq
  obtain ⟨y, hy⟩ := hq
  obtain ⟨c, hc, m₁, hm₁⟩ := hcoker y
  have h1 : u ((c : A) • m - f ^ n • m₁) = 0 := by
    rw [map_sub, map_smul, map_smul, ← hm₁, ← hy, smul_comm, sub_self]
  obtain ⟨d, hd, hdm⟩ := hker _ h1
  rw [smul_sub] at hdm
  refine ⟨d * (c : A), Submonoid.mul_mem _ hd hc, ?_⟩
  rw [mul_smul, ← map_smul, ← map_smul]
  refine (quotMk_eq_zero_iff f M).2 ⟨d • m₁, ?_⟩
  rw [smul_comm]
  exact (sub_eq_zero.1 hdm).symm

/-- If `u : M ⟶ P` is surjective up to factors outside `p`, then so is the induced map
`M/fⁿM ⟶ P/fⁿP`. -/
theorem quotMap_coker_cond
    (hcoker : ∀ z : P, ∃ c ∈ p.asIdeal.primeCompl, ∃ m : M, c • z = u m)
    (n : ℕ) (w : Quot f P n) :
    ∃ c ∈ p.asIdeal.primeCompl, ∃ q : Quot f M n, c • w = quotMap f u n q := by
  obtain ⟨y, rfl⟩ := quotMk_surjective f P n w
  obtain ⟨c, hc, m, hm⟩ := hcoker y
  exact ⟨c, hc, quotMk f M n m, by rw [quotMap_quotMk, ← hm, map_smul]⟩

end Stacks.Algebraization.FormalSections

/-! ### A neighbourhood of the formal locus on which `M ⟶ N` is locally bijective -/

namespace Stacks.Algebraization.FormalSections

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {a : Ideal A} {f : A}
  (M : ModuleCat.{u} A) [Module.Finite A (M : Type u)]
  (hf : IsSMulRegular (M : Type u) f)

/-- The two local conditions on the canonical map `M ⟶ N` at a point: it is injective, and
surjective, up to factors outside that point. -/
def LocalIso (p : PrimeSpectrum A) : Prop :=
  (∀ m : M, toLimModule (a := a) (f := f) M m = 0 →
      ∃ c ∈ p.asIdeal.primeCompl, c • m = 0) ∧
    (∀ z : formalLimit f M (complOpen A a), ∃ c ∈ p.asIdeal.primeCompl, ∃ m : M,
      c • z = toLimModule (a := a) (f := f) M m)

include hf in
/-- **There is a neighbourhood of the formal locus on which `M ⟶ N` is locally bijective.** The
kernel and the cokernel of `M ⟶ N` are finite modules whose supports miss the formal locus, so
the complement of the union of those supports is such a neighbourhood. -/
theorem exists_localIso_nbhd {r : ℕ} (gs : Fin r → A) (hgs : Ideal.span (Set.range gs) = a)
    [Module.Finite A (formalLimit f M (complOpen A a))] :
    ∃ V : OpenNearVanishing A a f, ∀ p ∈ V.carrier, LocalIso (a := a) (f := f) M p := by
  classical
  set Rng := LinearMap.range (toLimModule (a := a) (f := f) M).hom
  have : IsNoetherian A (M : Type u) := isNoetherian_of_isNoetherianRing_of_finite A _
  have hKfin : Module.Finite A
      (LinearMap.ker (toLimModule (a := a) (f := f) M).hom) :=
    Module.Finite.of_fg (IsNoetherian.noetherian _)
  have hCfin : Module.Finite A (formalLimit f M (complOpen A a) ⧸ Rng) :=
    Module.Finite.quotient A Rng
  have hKmem : ∀ p : PrimeSpectrum A,
      p ∉ Module.support A (LinearMap.ker (toLimModule (a := a) (f := f) M).hom) ↔
      ∀ m : M, toLimModule (a := a) (f := f) M m = 0 →
        ∃ c ∈ p.asIdeal.primeCompl, c • m = 0 := by
    intro p
    rw [Module.notMem_support_iff']
    constructor
    · intro h m hm
      obtain ⟨c, hc, hcm⟩ := h ⟨m, LinearMap.mem_ker.2 hm⟩
      exact ⟨c, hc, congrArg Subtype.val hcm⟩
    · intro h w
      obtain ⟨c, hc, hcw⟩ := h w.1 (LinearMap.mem_ker.1 w.2)
      exact ⟨c, hc, Subtype.ext hcw⟩
  have hCmem : ∀ p : PrimeSpectrum A,
      p ∉ Module.support A (formalLimit f M (complOpen A a) ⧸ Rng) ↔
      ∀ z : formalLimit f M (complOpen A a), ∃ c ∈ p.asIdeal.primeCompl, ∃ m : M,
        c • z = toLimModule (a := a) (f := f) M m := by
    intro p
    rw [Module.notMem_support_iff']
    constructor
    · intro h z
      obtain ⟨c, hc, hcz⟩ := h (Rng.mkQ z)
      exact ⟨c, hc, (smul_mkQ_range_eq_zero_iff M c z).1 hcz⟩
    · intro h w
      obtain ⟨z, rfl⟩ := Rng.mkQ_surjective w
      obtain ⟨c, hc, m, hcm⟩ := h z
      exact ⟨c, hc, (smul_mkQ_range_eq_zero_iff M c z).2 ⟨m, hcm⟩⟩
  set Z : Set (PrimeSpectrum A) :=
    Module.support A (LinearMap.ker (toLimModule (a := a) (f := f) M).hom) ∪
      Module.support A (formalLimit f M (complOpen A a) ⧸ Rng) with hZ
  have hZclosed : IsClosed Z := by
    rw [hZ, Module.support_eq_zeroLocus, Module.support_eq_zeroLocus]
    exact (PrimeSpectrum.isClosed_zeroLocus _).union (PrimeSpectrum.isClosed_zeroLocus _)
  have hnotZ : ∀ p : PrimeSpectrum A, p ∈ complOpen A a → f ∈ p.asIdeal → p ∉ Z := by
    intro p hpU hfp hpZ
    obtain ⟨g, hg, hgp⟩ := exists_mem_notMem_of_mem_complOpen hpU
    rcases hpZ with hpZ | hpZ
    · exact ((hKmem p).2
        (fun m hm ↦ exists_notMem_smul_eq_zero_of_toLimModule_eq_zero M hf hg hfp hgp m hm)) hpZ
    · exact ((hCmem p).2
        (fun z ↦ exists_notMem_smul_mem_range M hf gs hgs hg hfp hgp z)) hpZ
  refine ⟨⟨complOpen A a ⊓ ⟨Zᶜ, hZclosed.isOpen_compl⟩, inf_le_left,
    fun p hp hpf ↦ ⟨hp, hnotZ p hp hpf⟩⟩, ?_⟩
  intro p hp
  have hpZ : p ∉ Z := hp.2
  rw [hZ] at hpZ
  exact ⟨(hKmem p).1 fun h ↦ hpZ (Or.inl h), (hCmem p).1 fun h ↦ hpZ (Or.inr h)⟩

omit [IsNoetherianRing A] [Module.Finite A (M : Type u)] in
/-- On a neighbourhood as above, the maps on the quotients are also locally bijective, so they
induce bijections on sections. -/
theorem bijective_moduleSectionsMap_quotMap {V : Opens (PrimeSpectrum.Top A)}
    (hV : ∀ p ∈ V, LocalIso (a := a) (f := f) M p) (n : ℕ) :
    Function.Bijective (moduleSectionsMap
      (quotMap f (toLimModule (a := a) (f := f) M) n) V) :=
  bijective_moduleSectionsMap _
    (fun p hp ↦ quotMap_ker_cond (toLimModule (a := a) (f := f) M) (hV p hp).1 (hV p hp).2 n)
    (fun p hp ↦ quotMap_coker_cond (toLimModule (a := a) (f := f) M) (hV p hp).2 n)

/-! ### The comparison of the quotients at the level of the limit -/

/-- The level-`n` component of an element of `N = lim Γ(U, (M/fⁿM)~)`, pushed forward along
`M ⟶ N` into the sections of `(N/fⁿN)~` on `U`. -/
def limPush (n : ℕ) : formalLimit f M (complOpen A a) →ₗ[A]
    moduleSections (Quot f (limModule (a := a) (f := f) M) n) (complOpen A a) :=
  (moduleSectionsMap (quotMap f (toLimModule (a := a) (f := f) M) n) (complOpen A a)).comp
    (levelAt f M (complOpen A a) n)

/-- The constant section of `(N/fⁿN)~` on `U` determined by the class of an element of `N`
modulo `fⁿN`. -/
def limConst (n : ℕ) : formalLimit f M (complOpen A a) →ₗ[A]
    moduleSections (Quot f (limModule (a := a) (f := f) M) n) (complOpen A a) :=
  (moduleSectionsMk (Quot f (limModule (a := a) (f := f) M) n) (complOpen A a)).comp
    (quotMk f (limModule (a := a) (f := f) M) n).hom

omit [IsNoetherianRing A] [Module.Finite A (M : Type u)] in
/-- `limPush M n x` is the image of the level-`n` component of `x` under `M/fⁿM ⟶ N/fⁿN`. -/
theorem limPush_apply (n : ℕ) (x : formalLimit f M (complOpen A a)) :
    limPush M n x =
      moduleSectionsMap (quotMap f (toLimModule (a := a) (f := f) M) n) (complOpen A a) (x.1 n) :=
  rfl

omit [IsNoetherianRing A] [Module.Finite A (M : Type u)] in
/-- `limConst M n x` is the constant section determined by `x mod fⁿN`. -/
theorem limConst_apply (n : ℕ) (x : formalLimit f M (complOpen A a)) :
    limConst M n x =
      moduleSectionsMk (Quot f (limModule (a := a) (f := f) M) n) (complOpen A a)
        (quotMk f (limModule (a := a) (f := f) M) n x) :=
  rfl

omit [IsNoetherianRing A] [Module.Finite A (M : Type u)] in
/-- The two maps agree on the image of `M`, by the very definition of `M ⟶ N`. -/
theorem limPush_toLimModule (n : ℕ) (m : M) :
    limPush M n ((toLimModule (a := a) (f := f) M) m) =
      limConst M n ((toLimModule (a := a) (f := f) M) m) := by
  rw [limPush_apply, limConst_apply, toLimModule_apply_level, moduleSectionsMap_moduleSectionsMk]
  rfl

omit [IsNoetherianRing A] [Module.Finite A (M : Type u)] in
/-- The values of `limPush M n` are killed by `fⁿ`. -/
theorem pow_smul_limPush (n : ℕ) (z : formalLimit f M (complOpen A a)) :
    f ^ n • limPush M n z = 0 :=
  pow_smul_level_eq_zero f (limModule (a := a) (f := f) M) (complOpen A a) n _

omit [IsNoetherianRing A] [Module.Finite A (M : Type u)] in
/-- The values of `limConst M n` are killed by `fⁿ`. -/
theorem pow_smul_limConst (n : ℕ) (z : formalLimit f M (complOpen A a)) :
    f ^ n • limConst M n z = 0 :=
  pow_smul_level_eq_zero f (limModule (a := a) (f := f) M) (complOpen A a) n _

omit [IsNoetherianRing A] [Module.Finite A (M : Type u)] in
include hf in
/-- **The key compatibility.** The level-`n` component of an element `x` of
`N = lim Γ(U, (M/fⁿM)~)`, pushed forward to the sections of `(N/fⁿN)~`, is the constant section
determined by the class of `x` modulo `fⁿN`.

Both sides are `A`-linear in `x`, they agree on the image of `M` by the very definition of
`M ⟶ N`, and for `g ∈ 𝔞` the cokernel of `M ⟶ N/fⁿN` is killed by a power of `g`. So the two
agree after multiplication by a power of each generator of `𝔞`, hence at every point of the
standard open of that generator, and the standard opens of the generators cover `U`. -/
theorem limPush_eq_limConst {r : ℕ} (gs : Fin r → A) (hgs : Ideal.span (Set.range gs) = a)
    (n : ℕ) (x : formalLimit f M (complOpen A a)) : limPush M n x = limConst M n x := by
  have hcov : (complOpen A a : Opens (PrimeSpectrum.Top A)) = ⨆ i, basicOpen (gs i) :=
    complementZeroLocus_eq_iSup_basicOpen gs a hgs
  refine ext_moduleSections fun pt ↦ ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcov.le pt.2)
  have hgi : gs i ∈ a := by
    rw [← hgs]
    exact Ideal.subset_span ⟨i, rfl⟩
  obtain ⟨k, m, z', hk⟩ := exists_pow_smul_eq_add_pow_smul M hf gs hgs hgi n x
  have hsm : (gs i) ^ k • limPush (a := a) (f := f) M n x =
      (gs i) ^ k • limConst (a := a) (f := f) M n x := by
    rw [← map_smul (limPush (a := a) (f := f) M n),
      ← map_smul (limConst (a := a) (f := f) M n), hk, map_add, map_add,
      map_smul (limPush (a := a) (f := f) M n), map_smul (limConst (a := a) (f := f) M n),
      pow_smul_limPush M n z', pow_smul_limConst M n z', add_zero, add_zero]
    exact limPush_toLimModule M n m
  exact smul_injective_localizedModule (Quot f (limModule (a := a) (f := f) M) n)
    (g := (gs i) ^ k) (fun hmem ↦ hi (pt.1.2.mem_of_pow_mem k hmem))
    (congrFun (congrArg Subtype.val hsm) pt)

/-! ### The theorem -/

include hf in
/-- **The comparison map is bijective**, given that the sections of `(M/fM)~` on `U` are a
finite `A`-module and that `A` is `f`-adically precomplete. -/
theorem bijective_formalComparison_of_finite {r : ℕ} (gs : Fin r → A)
    (hgs : Ideal.span (Set.range gs) = a) [IsPrecomplete (Ideal.span {f}) A]
    (hfin1 : Module.Finite A (moduleSections (Quot f M 1) (complOpen A a))) :
    Function.Bijective (formalComparison A a f M) := by
  have hfinN : Module.Finite A (formalLimit f M (complOpen A a)) :=
    finite_formalLimit f M (complOpen A a) hf hfin1
  obtain ⟨V, hV⟩ := exists_localIso_nbhd M hf gs hgs
  have hbijV : Function.Bijective (moduleSectionsMap
      (toLimModule (a := a) (f := f) M) V.carrier) :=
    bijective_moduleSectionsMap _ (fun p hp ↦ (hV p hp).1) (fun p hp ↦ (hV p hp).2)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨W, s, rfl⟩ := Module.DirectLimit.exists_of w
    rw [formalComparison_of] at hw
    have hred : ∀ n : ℕ, moduleSectionsMap (quotMk f M n) W.carrier s = 0 := by
      intro n
      have h0 : extendQuot A a f M W n (moduleSectionsMap (quotMk f M n) W.carrier s) = 0 :=
        congrFun (congrArg Subtype.val hw) n
      have h1 := congrArg (moduleSectionsRestrict (Quot f M n) W.le_complement) h0
      rw [restrict_extendQuot, map_zero] at h1
      exact h1
    have hvan : ∀ (p : PrimeSpectrum A) (hp : p ∈ complOpen A a), f ∈ p.asIdeal →
        ∀ hpW : p ∈ W.carrier, s.1 ⟨p, hpW⟩ = 0 := by
      intro p hp hfp hpW
      obtain ⟨m, t, hmt⟩ : ∃ (m : M) (t : p.asIdeal.primeCompl),
          s.1 ⟨p, hpW⟩ = LocalizedModule.mk m t := by
        induction (s.1 ⟨p, hpW⟩) using LocalizedModule.induction_on with
        | _ m t => exact ⟨m, t, rfl⟩
      have hpow : ∀ n : ℕ, ∃ c ∈ p.asIdeal.primeCompl, c • m ∈ powSmul f M n := by
        intro n
        have hz : locMap (quotMk f M n) p (LocalizedModule.mk m t) = 0 := by
          rw [← hmt]
          exact congrFun (congrArg Subtype.val (hred n)) ⟨p, hpW⟩
        rw [locMap_mk, localizedModule_mk_eq_zero_iff] at hz
        obtain ⟨c, hc⟩ := hz
        refine ⟨(c : A), c.2, ?_⟩
        rw [← map_smul] at hc
        exact (quotMk_eq_zero_iff f M).1 hc
      obtain ⟨c, hc, hcm⟩ :=
        exists_notMem_smul_eq_zero_of_forall_mem_powSmul f M p hf hfp hpow
      rw [hmt]
      exact (localizedModule_mk_eq_zero_iff m t).2 ⟨⟨c, hc⟩, hcm⟩
    have hWle : vanishingOpen M s ≤ complOpen A a :=
      (vanishingOpen_le M s).trans W.le_complement
    set W' : OpenNearVanishing A a f := ⟨vanishingOpen M s, hWle,
      fun p hp hpf ↦ mem_vanishingOpen M s (W.vanishing_le p hp hpf)
        (hvan p hp hpf (W.vanishing_le p hp hpf))⟩ with hW'
    have hWW' : W ≤ W' := vanishingOpen_le M s
    rw [← Module.DirectLimit.of_f (hij := hWW'),
      show nearRestrict A a f M W W' hWW' s = 0 from restrict_vanishingOpen_eq_zero M s,
      map_zero]
  · intro x
    obtain ⟨s, hs⟩ := hbijV.2
      (moduleSectionsMk (limModule (a := a) (f := f) M) V.carrier x)
    refine ⟨Module.DirectLimit.of A (OpenNearVanishing A a f) _ (nearRestrict A a f M) V s, ?_⟩
    rw [formalComparison_of]
    refine formalLimit_ext f M (complOpen A a) fun n ↦ ?_
    rw [nbhdComparison_apply]
    refine extendQuot_injective_aux A a f M V n ?_
    rw [restrict_extendQuot]
    refine (bijective_moduleSectionsMap_quotMap M hV n).1 ?_
    rw [← moduleSectionsMap_comp_apply, quotMk_comp_quotMap, moduleSectionsMap_comp_apply, hs,
      moduleSectionsMap_moduleSectionsMk, moduleSectionsMap_restrict, ← limPush_apply,
      limPush_eq_limConst M hf gs hgs n x, limConst_apply,
      moduleSectionsRestrict_moduleSectionsMk]

end Stacks.Algebraization.FormalSections

/-! ### Stacks 0EIH -/

namespace Stacks.Algebraization.FormalSections

/-- Let `A` be a Noetherian ring, let `f ∈ 𝔞 ⊆ A` be an element of an ideal of `A`, and let `M`
be a finite `A`-module. Assume

1. `A` is `f`-adically complete,
2. `f` is a nonzerodivisor on `M`,
3. `H¹_𝔞(M/fM)` is a finite `A`-module.

Then, with `U = Spec(A) ∖ V(𝔞)`, the canonical map

`colim_V Γ(V, M̃) ⟶ lim_n Γ(U, (M/fⁿM)~)`

is an isomorphism, the colimit being over the opens `V ⊆ U` containing `U ∩ V(f)`.

The map is `Stacks.Algebraization.FormalSections.formalComparison`: on a neighbourhood `V` of
the formal locus it reduces a section of `M̃` modulo `fⁿ` and extends the result back to `U`,
which is legitimate because `(M/fⁿM)~` vanishes on `D(f) ⊇ U ∖ V`. The quotient `M/fM` is
written `Stacks.Algebraization.FormalSections.Quot f M 1`, which is `M` modulo the submodule
`fM`; see `Stacks.Algebraization.FormalSections.powSmul_one`.

The membership `f ∈ 𝔞` is carried but not consumed: the proof below uses only the other three
hypotheses, so the conclusion holds for every `f` and every ideal `𝔞`. -/
@[stacks 0EIH]
theorem isIso_formalComparison (A : Type u) [CommRing A] [IsNoetherianRing A] (f : A)
    (a : Ideal A) (hfa : f ∈ a) (M : ModuleCat.{u} A) [Module.Finite A (M : Type u)]
    [IsAdicComplete (Ideal.span {f}) A] (hf : IsSMulRegular (M : Type u) f)
    (hH1 : Module.Finite A
      (localCohomologyModule A a (Ideal.fg_of_isNoetherianRing a) (Quot f M 1) 1)) :
    IsIso (ModuleCat.ofHom (formalComparison A a f M)) := by
  have hmem : f ∈ a := hfa
  obtain ⟨r, gs, hgs⟩ := Submodule.fg_iff_exists_fin_generating_family.1
    (Ideal.fg_of_isNoetherianRing a)
  have hQfin : Module.Finite A (Quot f M 1 : Type u) :=
    Module.Finite.of_surjective (quotMk f M 1).hom (quotMk_surjective f M 1)
  have hfin1 : Module.Finite A (moduleSections (Quot f M 1) (complOpen A a)) := by
    have hbridge : moduleSections (Quot f M 1) (complOpen A a) ≃ₗ[A]
        complementGlobalSections A a (complementTilde A a (Quot f M 1)) :=
      (moduleSectionsCongr (Quot f M 1)
        (Scheme.Opens.ι_image_top (complementZeroLocus A a)).symm).trans
        (complementGlobalSectionsEquiv a (Quot f M 1))
    have := (finite_complementGlobalSections_iff_finite_localCohomologyModule.{u, u} A a
      (Ideal.fg_of_isNoetherianRing a) (Quot f M 1)
      (complementTilde A a (Quot f M 1)) (Iso.refl _)).2 hH1
    exact Module.Finite.equiv hbridge.symm
  exact (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_formalComparison_of_finite M hf gs hgs hfin1)

end Stacks.Algebraization.FormalSections

end
