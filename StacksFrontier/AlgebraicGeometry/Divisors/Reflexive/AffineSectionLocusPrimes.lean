module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.AffineReflexivePowerTilde
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexiveHeightOnePrimes
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SectionIsomorphismLocus
public import StacksFrontier.AlgebraicGeometry.Divisors.ReflexiveEquivalence.StalkDescent
public import StacksFrontier.AlgebraicGeometry.Modules.Stalk
import all StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SectionLocusGenericPoint

/-!
# The isomorphism locus of a section of `M̃` is the set of primes cut out by that section

Let `A` be a commutative ring, let `M` be an `A`-module and let `s ∈ M`.  [Stacks, Tag 0EBN]
attaches to a global section of a module `ℱ` on a scheme `X` the open locus

`U = {x ∈ X | s : 𝒪_{X, x} → ℱ_x is an isomorphism}`,

which this library calls `AlgebraicGeometry.sectionIsomorphismLocus`, while [Stacks, Tag 0EBQ]
reads that locus on `X = Spec(A)` with `ℱ = M̃` as the set of primes `𝔭` at which
`A_𝔭 → M_𝔭`, `a ↦ a·s`, is bijective, which this library calls
`Stacks.AlgebraicGeometry.ReflexiveHeightOnePrimes.sectionIsomorphismPrimes`.  This file proves
that the two sets are *equal*, so that every statement about one is a statement about the other.

The points of `Spec(A)` **are** the primes of `A`: `↑(Spec A)` is `PrimeSpectrum A` by `rfl`,
with no `PrimeSpectrum.comap` and no homeomorphism intervening, so the equality below is an
equality of subsets of one and the same type.  The two spellings are only *definitionally*, not
syntactically, equal -- `↑(Spec A)` has to be unfolded to reach `PrimeSpectrum A` -- so the
statements below are phrased with a point of `Spec R` and the coercion is left to the elaborator;
a `rw` against a membership of the locus stated for `PrimeSpectrum R` does not fire.

## Main definitions


## Main results

* `AlgebraicGeometry.bijective_smul_iff_of_isLocalizedModule`: bijectivity of "multiplication by
  the image of `s`" on a localization of `M` does not depend on which model of the localization
  is used.
* `AlgebraicGeometry.mem_sectionIsomorphismLocus_iff_bijective_smul_germ`: membership of
  `sectionIsomorphismLocus` is bijectivity of `c ↦ c · s_x` on the stalk of `ℱ`, over the local
  ring, with the module structure a scheme carries.
* `AlgebraicGeometry.germ_tildeGlobalSection`: the germ of that section at a prime is the
  canonical image `s/1` of `s` in the localization, by `rfl`.
* `AlgebraicGeometry.mem_sectionIsomorphismLocus_tilde_iff`: **the bridge.** A prime lies in the
  locus of [Stacks, Tag 0EBN] for `M̃` and the section attached to `s` exactly when it lies in
  the set of primes of [Stacks, Tag 0EBQ].
* `AlgebraicGeometry.sectionIsomorphismLocus_tilde_eq`: the same statement as an equality of
  sets.

## Implementation notes

**Which module structure on the stalk.**  Two `𝒪_{X, x}`-module structures on the stalk of an
`𝒪_X`-module are in play in this library: Mathlib's, on the stalk of a presheaf of modules,
which `AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf` restates for `X.Modules`, and
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule`, built by hand over a ringed space.
They are not the same instance, and the localization identifications of a stalk of `M̃` --
`AlgebraicGeometry.StructureSheaf.toStalkₗ` and its `IsLocalizedModule` instance -- are stated
for Mathlib's.  So the locus is read here through
`Stacks.AlgebraicGeometry.ReflexiveModules.stalkMapOfHom`, which lives on a scheme and is linear
over the local ring for Mathlib's structure, rather than through
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL`; the small germ lemmas about the
structure sheaf as a module over itself are therefore the ones phrased for `stalkMapOfHom`
rather than `Stacks.SheafOfModules.unitStalkLinearEquiv`.  They are the private germ lemmas
of `StacksFrontier/AlgebraicGeometry/Divisors/Reflexive/SectionLocusGenericPoint.lean`, which
made the same choice for the same reason; this file takes them from there through
`import all`, and adds the two it needs beyond them.

**Why a model-independence lemma is needed at all.**  The two sides of the bridge are the same
map, "multiplication by `s`", on two different models of the localization: the module side uses
`LocalizedModule 𝔭ᶜ M` over `Localization.AtPrime 𝔭`, the scheme side the stalk of `M̃` over the
stalk of `𝒪_{Spec A}`.  `bijective_smul_iff_of_isLocalizedModule` transports bijectivity between
any two models, which is all that is needed: only bijectivity crosses the bridge, and it crosses
along the `R`-linear comparison equivalences `IsLocalizedModule.linearEquiv`, whose compatibility
with the two scalar actions is checked on the image of `A` and then propagated by the universal
property.

**No hypothesis is carried.**  Neither Noetherianity, nor normality, nor finiteness, nor
reflexivity, nor a rank hypothesis is used: the statement is an identification of two sets, and
both are defined for an arbitrary module over an arbitrary commutative ring.

## References

* [Stacks Project, Tag 0EBQ](https://stacks.math.columbia.edu/tag/0EBQ)
* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveEquivalence
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace AlgebraicGeometry

/-! ### Multiplication by a section is bijective independently of the model -/

/-- **Bijectivity of multiplication by the image of `s` does not depend on the model of the
localization.**  If `(A, N, f)` and `(A', N', f')` both present the localization of the ring
`R₀` and of the module `M` at the same submonoid `S`, then `a ↦ a · f s` is bijective exactly
when `a ↦ a · f' s` is.

The comparison maps are the `R₀`-linear equivalences of `IsLocalizedModule.linearEquiv`, and the
square they form with the two multiplication maps commutes because both composites agree on the
image of `R₀`, where each is `r ↦ r · f' s`. -/
theorem bijective_smul_iff_of_isLocalizedModule {R₀ : Type*} [CommRing R₀] (S : Submonoid R₀)
    {M : Type*} [AddCommGroup M] [Module R₀ M]
    {A : Type*} [CommRing A] [Algebra R₀ A] [IsLocalization S A]
    {N : Type*} [AddCommGroup N] [Module R₀ N] [Module A N] [IsScalarTower R₀ A N]
    (f : M →ₗ[R₀] N) [IsLocalizedModule S f]
    {A' : Type*} [CommRing A'] [Algebra R₀ A'] [IsLocalization S A']
    {N' : Type*} [AddCommGroup N'] [Module R₀ N'] [Module A' N'] [IsScalarTower R₀ A' N']
    (f' : M →ₗ[R₀] N') [IsLocalizedModule S f'] (s : M) :
    Function.Bijective (fun a : A => a • f s) ↔ Function.Bijective (fun a : A' => a • f' s) := by
  set T : A →ₗ[R₀] N := (LinearMap.toSpanSingleton A N (f s)).restrictScalars R₀
  set T' : A' →ₗ[R₀] N' := (LinearMap.toSpanSingleton A' N' (f' s)).restrictScalars R₀
  set eR : A ≃ₗ[R₀] A' :=
    IsLocalizedModule.linearEquiv S (Algebra.linearMap R₀ A) (Algebra.linearMap R₀ A') with heR
  set eM : N ≃ₗ[R₀] N' := IsLocalizedModule.linearEquiv S f f' with heM
  have hsq : eM.toLinearMap ∘ₗ T = T' ∘ₗ eR.toLinearMap := by
    refine IsLocalizedModule.ext S (Algebra.linearMap R₀ A)
      (IsLocalizedModule.map_units f') ?_
    refine LinearMap.ext fun r => ?_
    have hleft : eM (algebraMap R₀ A r • f s) = r • f' s := by
      rw [IsScalarTower.algebraMap_smul, map_smul, heM, IsLocalizedModule.linearEquiv_apply]
    have hright : eR (algebraMap R₀ A r) = algebraMap R₀ A' r := by
      rw [heR]
      exact IsLocalizedModule.linearEquiv_apply S (Algebra.linearMap R₀ A)
        (Algebra.linearMap R₀ A') r
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Algebra.linearMap_apply]
    rw [hright]
    exact hleft.trans (IsScalarTower.algebraMap_smul A' r (f' s)).symm
  have h1 : Function.Bijective (⇑eM ∘ ⇑T) ↔ Function.Bijective ⇑T :=
    Function.Bijective.of_comp_iff' eM.bijective _
  have h2 : Function.Bijective (⇑T' ∘ ⇑eR) ↔ Function.Bijective ⇑T' :=
    Function.Bijective.of_comp_iff _ eR.bijective
  have h3 : (⇑eM ∘ ⇑T) = (⇑T' ∘ ⇑eR) := funext fun a => LinearMap.congr_fun hsq a
  change Function.Bijective ⇑T ↔ Function.Bijective ⇑T'
  rw [← h1, h3, h2]

/-! ### The isomorphism locus through the germ of the section -/

/-- A germ of the local ring killing the germ of the unit section is zero: a representative
restricts to zero on a smaller open, hence has zero germ. -/
private theorem eq_zero_of_smul_unitGerm_eq_zero {X : Scheme.{u}} (x : X)
    (c : X.presheaf.stalk x) (hc : c • unitGerm X x = 0) : c = 0 := by
  obtain ⟨U, hU, r, rfl⟩ := X.presheaf.exists_germ_eq c
  rw [← germ_eq_smul_unitGerm x U hU r] at hc
  obtain ⟨W, hW, iU, iV, hres⟩ := TopCat.Presheaf.germ_eq (unitMod X).presheaf x hU hU r 0
    (hc.trans (map_zero _).symm)
  have h0 : (X.presheaf.map iU.op).hom r = 0 :=
    hres.trans (map_zero ((unitMod X).presheaf.map iV.op).hom)
  have hg := TopCat.Presheaf.germ_res_apply X.presheaf iU x hW r
  rw [h0, map_zero] at hg
  exact hg.symm

/-- The stalk of `𝒪_X` as a module over itself is free of rank one on the germ of the unit
section. -/
private theorem bijective_smul_unitGerm {X : Scheme.{u}} (x : X) :
    Function.Bijective (fun c : X.presheaf.stalk x => c • unitGerm X x) := by
  refine ⟨fun a b hab => ?_, fun y => ?_⟩
  · have h : (a - b) • unitGerm X x = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.mpr hab
    exact sub_eq_zero.mp (eq_zero_of_smul_unitGerm_eq_zero x _ h)
  · obtain ⟨U, hU, a, rfl⟩ := (unitMod X).presheaf.exists_germ_eq y
    exact ⟨X.presheaf.germ U x hU a, (germ_eq_smul_unitGerm x U hU a).symm⟩

/-- **The locus of [Stacks, Tag 0EBN] through the germ of the section.**  A point lies in
`AlgebraicGeometry.sectionIsomorphismLocus` exactly when multiplication by the germ of `s` is a
bijection from the local ring onto the stalk, the stalk being a module over the local ring by
`AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf`.

The morphism `𝒪_X ⟶ ℱ` attached to `s` carries `c · 1_x` to `c · s_x`, and `c ↦ c · 1_x` is a
bijection onto the stalk of `𝒪_X` as a module over itself. -/
theorem mem_sectionIsomorphismLocus_iff_bijective_smul_germ {X : Scheme.{u}} (F : X.Modules)
    (s : F.sections) (x : X) :
    x ∈ sectionIsomorphismLocus F s ↔ Function.Bijective
      (fun c : X.presheaf.stalk x => c • F.presheaf.germ ⊤ x trivial (s.eval (op ⊤))) := by
  have hfun : (fun c : X.presheaf.stalk x =>
        c • F.presheaf.germ ⊤ x trivial (s.eval (op ⊤)))
      = (fun m => stalkMapOfHom (F.unitHomEquiv.symm s) x m) ∘
        (fun c : X.presheaf.stalk x => c • unitGerm X x) :=
    funext fun c => ((stalkMapOfHom_smul (F.unitHomEquiv.symm s) x c (unitGerm X x)).trans
      (congrArg (c • ·) (stalkMapOfHom_unitGerm F s x))).symm
  rw [hfun, Function.Bijective.of_comp_iff _ (bijective_smul_unitGerm x)]
  exact mem_sectionIsomorphismLocus_iff F s x

/-! ### The germ of the global section attached to an element of `M` -/

variable {R : CommRingCat.{u}}

/-- The germ at a prime of the global section attached to `s` is the canonical image of `s` in
the stalk, the localization of `M` at that prime. -/
theorem germ_tildeGlobalSection (M : ModuleCat.{u} R) (s : M) (p : PrimeSpectrum R) :
    (tilde M).presheaf.germ ⊤ p trivial ((tildeGlobalSection M s).eval (op ⊤)) =
      StructureSheaf.toStalkₗ R M p s :=
  rfl

/-! ### The bridge -/

/-- **The locus of [Stacks, Tag 0EBN] on an affine scheme is the set of primes of
[Stacks, Tag 0EBQ].**  For a commutative ring `R`, an `R`-module `M` and `s ∈ M`, a prime `𝔭`
lies in the locus where the global section of `M̃` attached to `s` induces an isomorphism
`𝒪_{Spec R, 𝔭} → (M̃)_𝔭` exactly when `A_𝔭 → M_𝔭`, `a ↦ a·s`, is bijective.

Both sides are "multiplication by `s`" on a localization at `𝔭`; the stalk of `𝒪_{Spec R}` is a
localization of `R` at `𝔭` (`AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk`) and the
stalk of `M̃` is a localized module (`AlgebraicGeometry.StructureSheaf.toStalkₗ`), so
`bijective_smul_iff_of_isLocalizedModule` identifies the two bijectivity statements. -/
theorem mem_sectionIsomorphismLocus_tilde_iff (M : ModuleCat.{u} R) (s : M) (p : Spec R) :
    p ∈ sectionIsomorphismLocus (tilde M) (tildeGlobalSection M s) ↔
      p ∈ Stacks.AlgebraicGeometry.ReflexiveHeightOnePrimes.sectionIsomorphismPrimes R s := by
  let q : PrimeSpectrum R := p
  let B : Type u := (Spec R).presheaf.stalk p
  let S := q.asIdeal.primeCompl
  let : Algebra R B := StructureSheaf.stalkAlgebra R q
  let : Module B ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf q) :=
    AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf (tilde M) p
  have : IsScalarTower R B ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf q) :=
    .of_algebraMap_smul fun _ _ => rfl
  let : IsLocalization.AtPrime B q.asIdeal := StructureSheaf.IsLocalization.to_stalk R q
  have : IsScalarTower R (Localization.AtPrime q.asIdeal) (LocalizedModule S M) :=
    .of_algebraMap_smul fun r m => by
      induction m using LocalizedModule.induction_on with
      | _ a t =>
        rw [← Localization.mk_one_eq_algebraMap, LocalizedModule.mk_smul_mk,
          LocalizedModule.smul'_mk, one_mul]
  refine (mem_sectionIsomorphismLocus_iff_bijective_smul_germ (tilde M)
    (tildeGlobalSection M s) p).trans ?_
  exact bijective_smul_iff_of_isLocalizedModule S (StructureSheaf.toStalkₗ R M q)
    (LocalizedModule.mkLinearMap S M) s

/-- **The locus of [Stacks, Tag 0EBN] on an affine scheme, as a set equality.**  The open locus
cut out on `Spec R` by the global section of `M̃` attached to `s` is the set of primes at which
`a ↦ a·s` is an isomorphism `R_𝔭 → M_𝔭`. -/
theorem sectionIsomorphismLocus_tilde_eq (M : ModuleCat.{u} R) (s : M) :
    sectionIsomorphismLocus (tilde M) (tildeGlobalSection M s) =
      Stacks.AlgebraicGeometry.ReflexiveHeightOnePrimes.sectionIsomorphismPrimes R s :=
  Set.ext fun p => mem_sectionIsomorphismLocus_tilde_iff M s p

/-! ### Nonemptiness of the isomorphism locus -/

/-- **The isomorphism locus of a nonzero section of a rank one module is nonempty**: it contains
the generic point, because the rank one hypothesis keeps the zero ideal out of the support of
`M ⧸ A·s`.  This is the hypothesis the cocone of [Stacks, Tag 0EBN] is stated under. -/
theorem nonempty_sectionIsomorphismOpen_tilde [IsNoetherianRing R] [IsDomain R]
    [IsIntegrallyClosed R] (M : ModuleCat.{u} R) [Module.Finite R M] [Module.IsReflexive R M]
    [IsNormal (Spec R)] [_root_.SheafOfModules.IsCoherent (tilde M)]
    (hrank : Module.rank R M = 1) {s : M} (hs : s ≠ 0) :
    Nonempty (sectionIsomorphismOpen (Spec R) (tilde M) (tildeGlobalSection M s)).toScheme := by
  have htf : Module.IsTorsionFree R M :=
    (isTorsionFree_of_isReflexive_and_dualEval_isTorsion_and_injective_iff
      (R := R) (M := M)).1 inferInstance
  have hbot : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈
      Stacks.AlgebraicGeometry.ReflexiveHeightOnePrimes.sectionIsomorphismPrimes R s :=
    (Stacks.AlgebraicGeometry.ReflexiveHeightOnePrimes.mem_sectionIsomorphismPrimes_iff hs _).2
      (Stacks.AlgebraicGeometry.ReflexiveHeightOnePrimes.bot_notMem_support_quotient hrank hs)
  exact ⟨⟨⟨⊥, Ideal.isPrime_bot⟩, (mem_sectionIsomorphismLocus_tilde_iff M s _).2 hbot⟩⟩


end AlgebraicGeometry

end
