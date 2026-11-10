module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.Finiteness
public import StacksFrontier.RingTheory.Flat.InjectiveModMaximalIdeal

@[expose] public section

/-!
# Injectivity modulo the maximal ideal of a valuation ring

Let `A` be a valuation ring, let `A → B` be a local homomorphism of local rings which is
essentially of finite type, and let `u : N → M` be a map of finite `B`-modules with `M` flat over
`A`. Stacks 0GSG says that if `ū : N/𝔪_A N → M/𝔪_A M` is injective then `u` is injective and
`M/u(N)` is flat over `A`.

## The argument

Both conclusions come from Stacks 046Y, with the roles of the source and the target exchanged
relative to that lemma. 046Y asks for `B` essentially of finite *presentation* over `A` and for
both modules finitely presented over `B`, and none of that is assumed here; the valuation ring
supplies all three.

Write `B` as a quotient of `P = (A[x_1, …, x_n])_𝔮`, which is possible because `B` is a local
ring essentially of finite type over `A`; then `u` is a map of finite `P`-modules, and `P`, being
a localization of a polynomial algebra, is flat over `A`, so Stacks 0GSE makes `A → P`
essentially of finite presentation. The same lemma makes `M` finitely presented over `P`, `M`
being `A`-flat and finite, so the flatness half of 046Y applies verbatim and gives flatness of
`M/u(N)` over `A`.

For injectivity, 046Y needs in addition that `Ker u` be finitely generated. Here that is
immediate rather than a limit argument: `u(N)` is a submodule of the `A`-flat module `M`, hence
`A`-torsion-free, hence `A`-flat, `A` being a Bézout domain; it is finite over `P`, so Stacks
0GSE makes it finitely presented over `P`; and the kernel of the surjection `N ↠ u(N)` from a
finite module onto a finitely presented one is finitely generated.

## Main results

* `Module.Flat.injective_of_injective_mapQ_maximalIdeal_of_valuationRing`: `u` is injective.
* `Module.Flat.flat_quotient_range_of_injective_mapQ_maximalIdeal_of_valuationRing`: `M/u(N)` is
  flat over `A`.

## Implementation notes

The closed fibre `N/𝔪_A N` is the quotient `N ⧸ 𝔪_A • (⊤ : Submodule A N)` and `ū` is the
canonical `Submodule.mapQ` of `u.restrictScalars A`, exactly as in
`StacksFrontier.RingTheory.Flat.InjectiveModMaximalIdeal`; the required inclusion is
`Submodule.smul_top_le_comap_smul_top`.

`A` is not assumed local: a valuation ring is a local ring. The two conclusions are independent
statements and are kept as two declarations, proved from one common auxiliary.

## References

* [Stacks Project, Tag 0GSG](https://stacks.math.columbia.edu/tag/0GSG)
* [Stacks Project, Tag 046Y](https://stacks.math.columbia.edu/tag/046Y)
* [Stacks Project, Tag 0GSE](https://stacks.math.columbia.edu/tag/0GSE)
-/

open IsLocalRing

universe u₁ u₂ u₃ u₄

namespace Module.Flat

/-- A local ring essentially of finite type over `A` is a quotient of the localization of a
polynomial algebra over `A` at a prime ideal, compatibly with the structure maps from `A`. -/
@[ega "IV 1.3.11"]
private theorem exists_localizedPolynomial_surjection (A : Type u₁) (B : Type u₂) [CommRing A]
    [CommRing B] [IsLocalRing B] [Algebra A B] [Algebra.EssFiniteType A B] :
    ∃ (n : ℕ) (q : Ideal (MvPolynomial (Fin n) A)) (_ : q.IsPrime)
      (g : Localization.AtPrime q →+* B),
      g.comp (algebraMap A (Localization.AtPrime q)) = algebraMap A B ∧ Function.Surjective g := by
  classical
  obtain ⟨S₀, T, hft, hloc⟩ := (Algebra.essFiniteType_iff_exists_subalgebra A B).mp inferInstance
  obtain ⟨n, φ, hφ⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := S₀)).mp hft
  let ι : S₀ →+* B := S₀.subtype
  let ψ : MvPolynomial (Fin n) A →+* B := ι.comp φ.toRingHom
  let q : Ideal (MvPolynomial (Fin n) A) := (maximalIdeal B).comap ψ
  have hq : q.IsPrime := Ideal.IsPrime.comap _
  have hunits : ∀ y : q.primeCompl, IsUnit (ψ ↑y) := fun y =>
    notMem_maximalIdeal.mp y.property
  let g : Localization.AtPrime q →+* B := IsLocalization.lift hunits
  have hgcomp : g.comp (algebraMap (MvPolynomial (Fin n) A) (Localization.AtPrime q)) = ψ :=
    IsLocalization.lift_comp hunits
  refine ⟨n, q, hq, g, ?_, ?_⟩
  · rw [IsScalarTower.algebraMap_eq A (MvPolynomial (Fin n) A) (Localization.AtPrime q),
      ← RingHom.comp_assoc, hgcomp]
    ext a
    simp [ψ, ι]
  · intro b
    obtain ⟨⟨x, t⟩, rfl⟩ := IsLocalization.mk'_surjective T b
    obtain ⟨p, rfl⟩ := hφ x
    obtain ⟨d, hd⟩ := hφ t.1
    have hdq : d ∈ q.primeCompl := by
      intro hdmem
      have hu : IsUnit (ψ d) := by
        change IsUnit (ι (φ d))
        rw [hd]
        exact IsLocalization.map_units B t
      exact notMem_maximalIdeal.mpr hu hdmem
    refine ⟨IsLocalization.mk' (M := q.primeCompl) (Localization.AtPrime q) p ⟨d, hdq⟩, ?_⟩
    rw [IsLocalization.lift_mk'_spec]
    change ι (φ p) = ι (φ d) * IsLocalization.mk' B (φ p) t
    rw [hd]
    exact (IsLocalization.mk'_spec' B (φ p) t).symm

/-- **Stacks 0GSG**, both conclusions at once. See
`Module.Flat.injective_of_injective_mapQ_maximalIdeal_of_valuationRing` and
`Module.Flat.flat_quotient_range_of_injective_mapQ_maximalIdeal_of_valuationRing`. -/
private theorem injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal_of_valuationRing
    {A : Type u₁} {B : Type u₂} {N : Type u₃} {M : Type u₄}
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [Algebra A B] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [Algebra.EssFiniteType A B]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] [Module.Finite B N]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M] [Module.Finite B M]
    [Module.Flat A M]
    (u : N →ₗ[B] M)
    (hu : Function.Injective
      (Submodule.mapQ (maximalIdeal A • (⊤ : Submodule A N))
        (maximalIdeal A • (⊤ : Submodule A M)) (u.restrictScalars A)
        (Submodule.smul_top_le_comap_smul_top (maximalIdeal A) (u.restrictScalars A)))) :
    Function.Injective u ∧ Module.Flat A (M ⧸ LinearMap.range u) := by
  classical
  obtain ⟨n, q, hq, g, hgA, hg⟩ := exists_localizedPolynomial_surjection A B
  let P := Localization.AtPrime q
  let algPB : Algebra P B := g.toAlgebra
  have htwAPB : IsScalarTower A P B := IsScalarTower.of_algebraMap_smul fun a b => by
    simp only [Algebra.smul_def]
    change g (algebraMap A P a) * b = algebraMap A B a * b
    rw [← RingHom.comp_apply, hgA]
  let modPN : Module P N := Module.compHom N g
  let modPM : Module P M := Module.compHom M g
  have htwPBN : IsScalarTower P B N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have htwPBM : IsScalarTower P B M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have htwAPN : IsScalarTower A P N := IsScalarTower.of_algebraMap_smul fun a x => by
    change g (algebraMap A P a) • x = a • x
    rw [← IsScalarTower.algebraMap_smul B a x, ← RingHom.comp_apply, hgA]
  have htwAPM : IsScalarTower A P M := IsScalarTower.of_algebraMap_smul fun a x => by
    change g (algebraMap A P a) • x = a • x
    rw [← IsScalarTower.algebraMap_smul B a x, ← RingHom.comp_apply, hgA]
  have hcompLocal : IsLocalHom (g.comp (algebraMap A P)) := hgA ▸ inferInstance
  have : IsLocalHom (algebraMap A P) := isLocalHom_of_comp (algebraMap A P) g
  have : Module.Finite P B := Module.Finite.of_surjective (Algebra.linearMap P B) hg
  have : Module.Finite P N := Module.Finite.trans (R := P) B N
  have : Module.Finite P M := Module.Finite.trans (R := P) B M
  have hPess : (algebraMap A P).EssentiallyOfFinitePresentation :=
    (essentiallyOfFinitePresentation_and_finitePresentation_of_flat_of_valuationRing
      (A := A) (B := P) (M := P)).1 inferInstance
  have : Module.FinitePresentation P M :=
    (essentiallyOfFinitePresentation_and_finitePresentation_of_flat_of_valuationRing
      (A := A) (B := P) (M := M)).2 inferInstance inferInstance
  let uP : N →ₗ[P] M :=
    { toFun := u
      map_add' := u.map_add
      map_smul' := fun a x => u.map_smul (g a) x }
  have huP : Function.Injective
      (Submodule.mapQ (maximalIdeal A • (⊤ : Submodule A N))
        (maximalIdeal A • (⊤ : Submodule A M)) (uP.restrictScalars A)
        (Submodule.smul_top_le_comap_smul_top (maximalIdeal A) (uP.restrictScalars A))) := by
    have heq : uP.restrictScalars A = u.restrictScalars A := by ext; rfl
    rwa [heq]
  have hQ : Module.Flat A (M ⧸ LinearMap.range uP) :=
    flat_quotient_range_of_injective_mapQ_maximalIdeal hPess uP huP
  have : Module.Flat A (LinearMap.range uP) :=
    flat_iff_torsion_eq_bot_of_isBezout.mpr
      (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)
  have : Module.Finite P (LinearMap.range uP) := Module.Finite.range uP
  have : Module.FinitePresentation P (LinearMap.range uP) :=
    (essentiallyOfFinitePresentation_and_finitePresentation_of_flat_of_valuationRing
      (A := A) (B := P) (M := LinearMap.range uP)).2 inferInstance inferInstance
  have hker : (LinearMap.ker uP).FG := by
    rw [← LinearMap.ker_rangeRestrict uP]
    exact Module.FinitePresentation.fg_ker (R := P) (M := N)
      (N := LinearMap.range uP) uP.rangeRestrict uP.surjective_rangeRestrict
  exact ⟨injective_of_fg_ker_of_injective_mapQ_maximalIdeal uP hQ huP hker, hQ⟩

/-- **The injectivity half of Stacks 0GSG.** Let `A` be a valuation ring, let `A → B` be a local
homomorphism of local rings which is essentially of finite type, and let `u : N → M` be a map of
finite `B`-modules with `M` flat over `A`. If `ū : N/𝔪_A N → M/𝔪_A M` is injective then `u` is
injective. -/
@[stacks 0GSG "injectivity"]
theorem injective_of_injective_mapQ_maximalIdeal_of_valuationRing
    {A : Type u₁} {B : Type u₂} {N : Type u₃} {M : Type u₄}
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [Algebra A B] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [Algebra.EssFiniteType A B]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] [Module.Finite B N]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M] [Module.Finite B M]
    [Module.Flat A M]
    (u : N →ₗ[B] M)
    (hu : Function.Injective
      (Submodule.mapQ (maximalIdeal A • (⊤ : Submodule A N))
        (maximalIdeal A • (⊤ : Submodule A M)) (u.restrictScalars A)
        (Submodule.smul_top_le_comap_smul_top (maximalIdeal A) (u.restrictScalars A)))) :
    Function.Injective u :=
  (injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal_of_valuationRing u hu).1

/-- **The cokernel half of Stacks 0GSG.** Let `A` be a valuation ring, let `A → B` be a local
homomorphism of local rings which is essentially of finite type, and let `u : N → M` be a map of
finite `B`-modules with `M` flat over `A`. If `ū : N/𝔪_A N → M/𝔪_A M` is injective then `M/u(N)`
is flat over `A`. -/
@[stacks 0GSG "flatness of the cokernel"]
theorem flat_quotient_range_of_injective_mapQ_maximalIdeal_of_valuationRing
    {A : Type u₁} {B : Type u₂} {N : Type u₃} {M : Type u₄}
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [Algebra A B] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [Algebra.EssFiniteType A B]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] [Module.Finite B N]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M] [Module.Finite B M]
    [Module.Flat A M]
    (u : N →ₗ[B] M)
    (hu : Function.Injective
      (Submodule.mapQ (maximalIdeal A • (⊤ : Submodule A N))
        (maximalIdeal A • (⊤ : Submodule A M)) (u.restrictScalars A)
        (Submodule.smul_top_le_comap_smul_top (maximalIdeal A) (u.restrictScalars A)))) :
    Module.Flat A (M ⧸ LinearMap.range u) :=
  (injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal_of_valuationRing u hu).2

end Module.Flat
