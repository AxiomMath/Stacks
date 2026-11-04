module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.RingTheory.Derivation.ToSquareZero
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Smooth.Locus
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Examples.Geometric.LocalizedSplitting
public import StacksFrontier.Deformation.SquareZero.AlgebraExtensions

/-!
# Localizations of square-zero extensions

Let `k` be a field, let `B` be a `k`-algebra, and let `S` be a multiplicative subset of `B`. This
file defines when a square-zero extension of `S⁻¹B` by `S⁻¹N` is the localization of a
square-zero extension of `B` by a module `N`, shows that every extension has a localization, and
describes the relation maps induced by lifts from a presentation.

## Main definitions

* `Deformation.Examples.IsLocalizedExtension` describes the localization of a square-zero
  extension: the middle ring is localized at the inverse image of `S`, compatibly with the
  quotient map and with the identified kernel.

## Implementation notes

Projecting a field out of `Stacks.Deformation.algebraExtensionProblem` needs that definition to
be unfolded, which `implicit` transparency does not do, so instance synthesis and the `rfl`
closing `rw` decline on goals that print as `X = X`. The single local attribute below opens that
definition up for the whole file.

## References

* [Stacks Project, Tag 0DZ8](https://stacks.math.columbia.edu/tag/0DZ8)
-/

@[expose] public section

universe uk uB uN

namespace Deformation.Examples

open Stacks.Deformation

attribute [local implicit_reducible] Stacks.Deformation.algebraExtensionProblem

/-- Retractions at primes containing `s` give a global retraction modulo a multiple of `s`. -/
private theorem exists_complement_smul_id_factor
    {R M P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup P]
    [Module R M] [Module R P] (d : M →ₗ[R] P) (s : R)
    (h : ∀ q : PrimeSpectrum R, s ∈ q.asIdeal →
      ∃ a ∉ q.asIdeal, ∃ t : P →ₗ[R] M, t.comp d = a • LinearMap.id) :
    ∃ r : R, ∃ t : P →ₗ[R] M, t.comp d = (1 - r * s) • LinearMap.id := by
  let L := LinearMap.range (LinearMap.lcomp R M d)
  let e : (M →ₗ[R] M) ⧸ L := L.mkQ LinearMap.id
  let I : Ideal R := (R ∙ e).annihilator
  have haI (a : R) : a ∈ I ↔ ∃ t : P →ₗ[R] M, t.comp d = a • LinearMap.id := by
    show a ∈ (R ∙ e).annihilator ↔ _
    rw [Submodule.mem_annihilator_span_singleton]
    show a • L.mkQ LinearMap.id = 0 ↔ _
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rfl
  have htop : Ideal.span ({s} : Set R) ⊔ I = ⊤ := by
    by_contra hn
    obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ hn
    obtain ⟨a, ha, t, ht⟩ := h ⟨p, hp.isPrime⟩
      (hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self s)))
    exact ha (hle (Ideal.mem_sup_right ((haI a).2 ⟨t, ht⟩)))
  obtain ⟨r, a, ha, hra⟩ := Ideal.mem_span_singleton_sup.mp
    (show (1 : R) ∈ Ideal.span ({s} : Set R) ⊔ I by rw [htop]; trivial)
  obtain ⟨t, ht⟩ := (haI a).1 ha
  exact ⟨r, t, by rw [← hra, add_sub_cancel_left]; exact ht⟩

/-- A linear map descends from a localization modulo maps factoring through `d`. -/
private theorem exists_lift_modulo_precomp_of_isLocalizedModule
    {R M P N N' : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup P] [AddCommGroup N] [AddCommGroup N']
    [Module R M] [Module R P] [Module R N] [Module R N']
    [Module.FinitePresentation R M]
    (d : M →ₗ[R] P) (S : Submonoid R) (j : N →ₗ[R] N') [IsLocalizedModule S j]
    (hd : ∀ s : S, ∃ r : R, ∃ t : P →ₗ[R] M,
      t.comp d = (1 - r * s) • LinearMap.id)
    (g : M →ₗ[R] N') :
    ∃ f : M →ₗ[R] N, ∃ l : P →ₗ[R] N', g = j.comp f + l.comp d := by
  obtain ⟨f, s, hf⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule S j g
  obtain ⟨r, t, ht⟩ := hd s
  refine ⟨r • f, g.comp t, ?_⟩
  ext x
  have hf' : j (f x) = (s : R) • g x := DFunLike.congr_fun hf x
  have ht' : t (d x) = (1 - r * s) • x := DFunLike.congr_fun ht x
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    hf', ht', map_smul, sub_smul, one_smul, mul_smul]
  simp only [map_sub, map_smul]
  abel

/-- Factoring through `d` can be detected after localization when every denominator has a
complementary scalar multiple of the identity factoring through `d`. -/
private theorem exists_precomp_of_localized_precomp
    {R M P N N' : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup P] [AddCommGroup N] [AddCommGroup N']
    [Module R M] [Module R P] [Module R N] [Module R N']
    [Module.Finite R M] [Module.FinitePresentation R P]
    (d : M →ₗ[R] P) (S : Submonoid R) (j : N →ₗ[R] N') [IsLocalizedModule S j]
    (hd : ∀ s : S, ∃ r : R, ∃ t : P →ₗ[R] M,
      t.comp d = (1 - r * s) • LinearMap.id)
    (f : M →ₗ[R] N) (l : P →ₗ[R] N') (h : j.comp f = l.comp d) :
    ∃ t : P →ₗ[R] N, f = t.comp d := by
  obtain ⟨l₀, s, hl⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule S j l
  have he : j.comp (l₀.comp d) = j.comp ((s : R) • f) := by
    rw [← LinearMap.comp_assoc, hl, LinearMap.smul_comp, ← h, LinearMap.comp_smul]
    rfl
  obtain ⟨a, ha⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule S j
    (l₀.comp d) ((s : R) • f) he
  obtain ⟨r, t, ht⟩ := hd (a * s)
  refine ⟨(r * a) • l₀ + f.comp t, ?_⟩
  ext x
  have ha' : (a : R) • l₀ (d x) = (a : R) • ((s : R) • f x) :=
    DFunLike.congr_fun ha x
  have ht' : t (d x) = (1 - r * (a * s : S)) • x := DFunLike.congr_fun ht x
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    mul_smul, ha', ht', Submonoid.coe_mul, sub_smul, one_smul, mul_smul]
  simp only [map_sub, map_smul]
  abel

/-- Denominators avoiding the non-smooth locus act invertibly modulo the cotangent
differential. -/
private theorem exists_cotangent_complement_retraction
    {k B : Type*} [CommRing k] [CommRing B] [Algebra k B]
    [Algebra.EssFiniteType k B]
    (P : Algebra.Extension k B) [Algebra.FormallySmooth k P.Ring]
    [Module.Finite B P.Cotangent] [Module.FinitePresentation B P.CotangentSpace]
    (S : Submonoid B)
    (hS : ∀ q : PrimeSpectrum B, ¬ Algebra.IsSmoothAt k q.asIdeal →
      Disjoint (S : Set B) (q.asIdeal : Set B)) (s : S) :
    ∃ r : B, ∃ t : P.CotangentSpace →ₗ[B] P.Cotangent,
      t.comp P.cotangentComplex = (1 - r * s) • LinearMap.id := by
  apply exists_complement_smul_id_factor
  intro q hsq
  have hq : Algebra.IsSmoothAt k q.asIdeal := by
    by_contra hn
    exact Set.disjoint_left.mp (hS q hn) s.property hsq
  obtain ⟨t, ht⟩ := exists_localized_cotangent_retraction_of_isSmoothAt P q hq
  obtain ⟨a, l, hl⟩ := exists_smul_id_factor_of_localized_split P.cotangentComplex
    q.asIdeal.primeCompl t ht
  exact ⟨a, a.property, l, hl⟩

/-- The map on cokernels of precomposition induced by a coefficient map. -/
private def precompCokernelMap
    {R M P N N' : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup P] [AddCommGroup N] [AddCommGroup N']
    [Module R M] [Module R P] [Module R N] [Module R N']
    (d : M →ₗ[R] P) (j : N →ₗ[R] N') :
    ((M →ₗ[R] N) ⧸ LinearMap.range (LinearMap.lcomp R N d)) →ₗ[R]
      ((M →ₗ[R] N') ⧸ LinearMap.range (LinearMap.lcomp R N' d)) :=
  (LinearMap.range (LinearMap.lcomp R N d)).mapQ
    (LinearMap.range (LinearMap.lcomp R N' d)) (LinearMap.compRight R j)
    (by rintro _ ⟨l, rfl⟩; exact ⟨j.comp l, rfl⟩)

/-- The cokernel map of `Deformation.Examples.precompCokernelMap` on a class. -/
private theorem precompCokernelMap_mk
    {R M P N N' : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup P] [AddCommGroup N] [AddCommGroup N']
    [Module R M] [Module R P] [Module R N] [Module R N']
    (d : M →ₗ[R] P) (j : N →ₗ[R] N') (f : M →ₗ[R] N) :
    precompCokernelMap d j (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (j.comp f) := rfl

/-- Localization is a bijection on the cokernel of precomposition with `d` when every
denominator has a complementary scalar multiple of the identity factoring through `d`. -/
private theorem bijective_precompCokernelMap_of_isLocalizedModule
    {R M P N N' : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup P] [AddCommGroup N] [AddCommGroup N']
    [Module R M] [Module R P] [Module R N] [Module R N']
    [Module.FinitePresentation R M] [Module.FinitePresentation R P]
    (d : M →ₗ[R] P) (S : Submonoid R) (j : N →ₗ[R] N') [IsLocalizedModule S j]
    (hd : ∀ s : S, ∃ r : R, ∃ t : P →ₗ[R] M,
      t.comp d = (1 - r * s) • LinearMap.id) :
    Function.Bijective (precompCokernelMap d j) := by
  constructor
  · intro x y hxy
    obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (LinearMap.lcomp R N d)) x
    obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (LinearMap.lcomp R N d)) y
    obtain ⟨l, hl⟩ := (Submodule.Quotient.eq _).1 hxy
    have h : j.comp (f - g) = l.comp d := by
      rw [LinearMap.comp_sub]
      exact hl.symm
    obtain ⟨t, ht⟩ := exists_precomp_of_localized_precomp d S j hd (f - g) l h
    exact (Submodule.Quotient.eq _).2 ⟨t, ht.symm⟩
  · intro y
    obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (LinearMap.lcomp R N' d)) y
    obtain ⟨f, l, hf⟩ := exists_lift_modulo_precomp_of_isLocalizedModule d S j hd g
    refine ⟨Submodule.Quotient.mk f, ?_⟩
    rw [precompCokernelMap_mk]
    apply (Submodule.Quotient.eq _).2
    refine ⟨-l, ?_⟩
    show (-l).comp d = j.comp f - g
    rw [hf, LinearMap.neg_comp]
    abel

/-- Localization preserves the cokernel of the dual cotangent differential when the
localization denominators avoid the non-smooth locus. -/
private theorem bijective_cotangentCokernelMap_of_disjoint_nonsmoothLocus
    {k B : Type*} [CommRing k] [CommRing B] [Algebra k B]
    [Algebra.EssFiniteType k B] [IsNoetherianRing B]
    (P : Algebra.Extension k B) [Algebra.FormallySmooth k P.Ring]
    [Module.Finite B P.Cotangent] [Module.FinitePresentation B P.CotangentSpace]
    (S : Submonoid B)
    (hS : ∀ q : PrimeSpectrum B, ¬ Algebra.IsSmoothAt k q.asIdeal →
      Disjoint (S : Set B) (q.asIdeal : Set B))
    (N : Type*) [AddCommGroup N] [Module B N] :
    Function.Bijective (precompCokernelMap P.cotangentComplex
      (LocalizedModule.mkLinearMap S N)) := by
  let := Module.finitePresentation_of_finite B P.Cotangent
  exact bijective_precompCokernelMap_of_isLocalizedModule P.cotangentComplex S
    (LocalizedModule.mkLinearMap S N) (exists_cotangent_complement_retraction P S hS)

/-- The canonical map into `S⁻¹N` is a localization map after restricting scalars along a
surjection `R → B`, when `R` is localized at the inverse image of `S`. -/
private theorem localizedModuleMk_isLocalizedAtComap
    {R B : Type*} [CommSemiring R] [CommSemiring B]
    (S : Submonoid B) (f : R →+* B) (hf : Function.Surjective f)
    (N : Type*) [AddCommGroup N] [Module B N] :
    let : Module R N := Module.compHom N f
    let : Module R (LocalizedModule S N) :=
      Module.compHom _ ((algebraMap B (Localization S)).comp f)
    ∃ j : N →ₗ[R] LocalizedModule S N, IsLocalizedModule (S.comap f) j ∧
      ∀ n, j n = LocalizedModule.mkLinearMap S N n := by
  let : Module R N := Module.compHom N f
  let : Module R (LocalizedModule S N) :=
    Module.compHom _ ((algebraMap B (Localization S)).comp f)
  have hscalar (r : R) (x : LocalizedModule S N) : r • x = f r • x :=
    IsScalarTower.algebraMap_smul (R := B) (A := Localization S)
      (M := LocalizedModule S N) (f r) x
  have hscalarN (r : R) (x : N) : r • x = f r • x := rfl
  let j : N →ₗ[R] LocalizedModule S N :=
    { toFun := LocalizedModule.mkLinearMap S N
      map_add' := by simp
      map_smul' := fun r n ↦
        ((LocalizedModule.mkLinearMap (R := B) S N).map_smul (f r) n).trans
          (hscalar r (LocalizedModule.mkLinearMap S N n)).symm }
  have hj : IsLocalizedModule (S.comap f) j := by
    constructor
    · intro t
      have hu := IsLocalizedModule.map_units (LocalizedModule.mkLinearMap S N)
        ⟨f t, t.property⟩
      have hbij := (Module.End.isUnit_iff _).1 hu
      apply (Module.End.isUnit_iff (R := R) _).2
      constructor
      · intro x y hxy
        have hxy' := hxy
        simp only [Module.algebraMap_end_apply] at hxy'
        rw [hscalar t x, hscalar t y] at hxy'
        apply hbij.1
        rw [Module.algebraMap_end_apply]
        exact hxy'
      · intro y
        obtain ⟨x, hx⟩ := hbij.2 y
        refine ⟨x, ?_⟩
        have hx' : (algebraMap B (Module.End B (LocalizedModule S N)) (f t)) x = y := hx
        rw [Module.algebraMap_end_apply] at hx'
        rw [Module.algebraMap_end_apply, hscalar t x]
        exact hx'
    · intro y
      obtain ⟨⟨n, s⟩, hs⟩ := IsLocalizedModule.surj S
        (LocalizedModule.mkLinearMap S N) y
      obtain ⟨r, hr⟩ := hf s
      have hrmem : r ∈ S.comap f := by
        show f r ∈ S
        rw [hr]
        exact s.property
      refine ⟨⟨n, ⟨r, hrmem⟩⟩, ?_⟩
      have h1 : r • y = f r • y := hscalar r y
      have h2 : f r • y = (s : B) • y := congrArg (fun b : B ↦ b • y) hr
      exact h1.trans (h2.trans hs)
    · intro x y hxy
      obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq
        (S := S) (f := LocalizedModule.mkLinearMap S N) hxy
      obtain ⟨r, hr⟩ := hf s
      have hrmem : r ∈ S.comap f := by
        show f r ∈ S
        rw [hr]
        exact s.property
      refine ⟨⟨r, hrmem⟩, ?_⟩
      have h1 : r • x = f r • x := hscalarN r x
      have h2 : f r • x = (s : B) • x := congrArg (fun b : B ↦ b • x) hr
      have h3 : (s : B) • y = f r • y := congrArg (fun b : B ↦ b • y) hr.symm
      exact h1.trans (h2.trans (hs.trans (h3.trans (hscalarN r y).symm)))
  exact ⟨j, hj, fun _ ↦ rfl⟩

/-- After localizing an extension's quotient map, its kernel is the localization of the
identified original kernel. This packages the kernel equivalence as a localized module map. -/
private theorem localizedKernelMap_isLocalized
    (k : Type uk) (B : Type uB) [Field k] [CommRing B] [Algebra k B]
    (S : Submonoid B) (N : Type uN) [AddCommGroup N] [Module B N]
    (X : (algebraExtensionProblem k B N).CompatibleExtension.{max uk (max uB uN)}) :
    let P := algebraExtensionProblem k B N
    let S' : Submonoid P.B := S
    let T := S'.comap X.toB.toRingHom
    let : Module P.B N := by
      change Module B N
      infer_instance
    let : Module X.B' N := Module.compHom N X.toB.toRingHom
    ∃ e : N ≃ₗ[X.B'] RingHom.ker X.toB.toRingHom,
      IsLocalizedModule T
        ((RingHom.toKerIsLocalization (Localization T) (Localization S')
          X.toB.toRingHom (show T ≤ Submonoid.comap X.toB.toRingHom S' from le_rfl)) ∘ₗ
          e.toLinearMap) ∧ ∀ n, e n = X.kernelEquiv n := by
  let P := algebraExtensionProblem k B N
  let S' : Submonoid P.B := S
  let T := S'.comap X.toB.toRingHom
  let : Module P.B N := by
    show Module B N
    infer_instance
  let : Module P.B (RingHom.ker X.toB.toRingHom) := X.moduleKernel
  let : Module X.B' N := Module.compHom N X.toB.toRingHom
  let eLin : N →ₗ[X.B'] RingHom.ker X.toB.toRingHom :=
    { toFun := X.kernelEquiv
      map_add' := X.kernelEquiv.map_add
      map_smul' := by
        intro r n
        show X.kernelEquiv (X.toB r • (n : P.N)) = r • X.kernelEquiv n
        rw [X.kernelEquiv.map_smul]
        exact X.toB_smul_kernel r (X.kernelEquiv n) }
  let e : N ≃ₗ[X.B'] RingHom.ker X.toB.toRingHom :=
    LinearEquiv.ofBijective eLin X.kernelEquiv.bijective
  have hmap : Submonoid.map X.toB.toRingHom T = S' :=
    Submonoid.map_comap_eq_of_surjective X.surjective S'
  have hloc := RingHom.toKerIsLocalization_isLocalizedModule
      (S := Localization T) (Q := Localization S') X.toB.toRingHom hmap
  let : IsLocalizedModule T
      (RingHom.toKerIsLocalization (Localization T) (Localization S')
        X.toB.toRingHom (show T ≤ Submonoid.comap X.toB.toRingHom S' from le_rfl)) := hloc
  let : IsLocalizedModule T
      ((RingHom.toKerIsLocalization (Localization T) (Localization S')
        X.toB.toRingHom (show T ≤ Submonoid.comap X.toB.toRingHom S' from le_rfl)) ∘ₗ
        e.toLinearMap) := inferInstance
  exact ⟨e, inferInstance, fun _ ↦ rfl⟩

/-- **Stacks 0DZ8.** The extension `Y` of `S⁻¹B` is obtained from the extension `X` of `B` by
localizing its middle ring at the inverse image of `S`: there is a map of the two middle rings
which is such a localization, and which is compatible both with the quotient maps down to `B`
and `S⁻¹B` and with the identifications of the two kernels with `N` and `S⁻¹N`. -/
@[stacks 0DZ8 "the localization relation between two extensions"]
def IsLocalizedExtension
    (k : Type uk) (B : Type uB) [Field k] [CommRing B] [Algebra k B]
    (S : Submonoid B) (N : Type uN) [AddCommGroup N] [Module B N]
    (X : (algebraExtensionProblem k B N).CompatibleExtension.{max uk (max uB uN)})
    (Y : (algebraExtensionProblem k (Localization S)
      (LocalizedModule S N)).CompatibleExtension.{max uk (max uB uN)}) : Prop :=
  let : Algebra k X.B' := X.algebraA'B'
  let : Algebra k Y.B' := Y.algebraA'B'
  ∃ f : X.B' →ₐ[k] Y.B',
    (S.comap X.toB.toRingHom).IsLocalizationMap f.toRingHom ∧
      (∀ c : X.B', Y.toB (f c) = algebraMap B (Localization S) (X.toB c)) ∧
      (∀ n : N,
        f ((X.kernelEquiv n : RingHom.ker X.toB.toRingHom) : X.B') =
          ((Y.kernelEquiv (LocalizedModule.mkLinearMap S N n) :
            RingHom.ker Y.toB.toRingHom) : Y.B'))

/-- Every extension of `B` by `N` has a localization at `S`. -/
private theorem exists_localizedExtension
    (k : Type uk) (B : Type uB) [Field k] [CommRing B] [Algebra k B]
    (S : Submonoid B) (N : Type uN) [AddCommGroup N] [Module B N]
    (X : (algebraExtensionProblem k B N).CompatibleExtension.{max uk (max uB uN)}) :
    ∃ Y : (algebraExtensionProblem k (Localization S)
        (LocalizedModule S N)).CompatibleExtension.{max uk (max uB uN)},
      IsLocalizedExtension k B S N X Y := by
  classical
  let fB : X.B' →+* B := X.toB.toRingHom
  let T : Submonoid X.B' := S.comap fB
  let C := Localization T
  let L := LocalizedModule S N
  let q : C →+* Localization S := IsLocalization.map (Localization S) fB
    (show T ≤ S.comap fB from le_rfl)
  let : Algebra k X.B' := X.algebraA'B'
  let : Algebra k C := ((algebraMap X.B' C).comp (algebraMap k X.B')).toAlgebra
  let qA : C →ₐ[k] Localization S :=
    { q with
      commutes' a := by
        show q (algebraMap X.B' C (algebraMap k X.B' a)) = _
        rw [show q (algebraMap X.B' C (algebraMap k X.B' a)) =
          algebraMap B (Localization S) (fB (algebraMap k X.B' a)) by simp [q, fB]]
        rw [show fB (algebraMap k X.B' a) = algebraMap k B a from X.toB.commutes a]
        exact (IsScalarTower.algebraMap_apply k B (Localization S) a).symm }
  have hmap : T.map fB = S := Submonoid.map_comap_eq_of_surjective X.surjective S
  have hq : Function.Surjective q := by
    let : IsLocalization (T.map fB) (Localization S) := hmap.symm ▸ inferInstance
    exact IsLocalization.map_surjective_of_surjective T C (Localization S)
      (g := fB) X.surjective
  have hsq : (RingHom.ker q) ^ 2 = ⊥ := by
    rw [IsLocalization.ker_map (S := C) (Localization S) fB hmap,
      ← Ideal.map_pow, X.sq_zero, Ideal.map_bot]
  let : Module X.B' N := Module.compHom N fB
  let : Module X.B' L :=
    Module.compHom L ((algebraMap B (Localization S)).comp fB)
  obtain ⟨j, hj, hj_apply⟩ :=
    localizedModuleMk_isLocalizedAtComap S X.toB.toRingHom X.surjective N
  let := hj
  obtain ⟨e, he, he_apply⟩ := localizedKernelMap_isLocalized k B S N X
  let g : N →ₗ[X.B'] RingHom.ker q :=
    (RingHom.toKerIsLocalization C (Localization S) fB
      (show T ≤ S.comap fB from le_rfl)) ∘ₗ e.toLinearMap
  let : IsLocalizedModule T g := he
  let eR : L ≃ₗ[X.B'] RingHom.ker q := IsLocalizedModule.linearEquiv T j g
  let : Module C L := Module.compHom L q
  let : IsScalarTower X.B' C L := IsScalarTower.of_algebraMap_smul fun c n ↦ by
    show q (algebraMap X.B' C c) • n =
      algebraMap B (Localization S) (X.toB c) • n
    rw [show q (algebraMap X.B' C c) =
      algebraMap B (Localization S) (X.toB c) by
        show q (algebraMap X.B' C c) = algebraMap B (Localization S) (fB c)
        simp [q]]
  let eC := eR.extendScalarsOfIsLocalization T C
  let : Module (Localization S) (RingHom.ker q) :=
    eR.toAddEquiv.symm.module (Localization S)
  let eB : L ≃ₗ[Localization S] RingHom.ker q :=
    { eR.toAddEquiv with
      map_smul' := by
        intro b n
        show eR (b • n) = eR (b • eR.symm (eR n))
        rw [eR.symm_apply_apply] }
  have haction (c : C) (x : RingHom.ker q) : q c • x = c • x := by
    obtain ⟨n, rfl⟩ := eR.surjective x
    show eR (q c • eR.symm (eR n)) = c • eR n
    rw [eR.symm_apply_apply]
    exact eC.map_smul c n
  let Y : (algebraExtensionProblem k (Localization S) L).CompatibleExtension := by
    dsimp only [algebraExtensionProblem]
    exact
      { B' := C
        toB := qA
        surjective := hq
        sq_zero := hsq
        moduleKernel := inferInstance
        toB_smul_kernel := haction
        kernelEquiv := eB
        map_I := by
          intro i
          have hi : (i : k) = 0 := i.2
          show (eB (0 : L) : C) = algebraMap k C i
          simp [hi] }
  refine ⟨Y, ?_⟩
  let : Algebra k Y.B' := Y.algebraA'B'
  let f : X.B' →ₐ[k] Y.B' :=
    { algebraMap X.B' C with commutes' := fun _ ↦ rfl }
  refine ⟨f, ?_, ?_, ?_⟩
  · exact (isLocalization_iff_isLocalizationMap T C).mp inferInstance
  · intro c
    show q (algebraMap X.B' C c) = algebraMap B (Localization S) (X.toB c)
    show q (algebraMap X.B' C c) = algebraMap B (Localization S) (fB c)
    simp [q]
  · intro n
    show algebraMap X.B' C (X.kernelEquiv n) = (eR (LocalizedModule.mkLinearMap S N n) : C)
    rw [← hj_apply, IsLocalizedModule.linearEquiv_apply]
    show algebraMap X.B' C (X.kernelEquiv n) = algebraMap X.B' C (e n)
    rw [he_apply]

/-- Precomposing a localization map with a multiplicative equivalence of its source gives a
localization map at the inverse image of the submonoid. -/
private theorem isLocalizationMap_comp_mulEquiv
    {R R' C : Type*} [CommMonoid R] [CommMonoid R'] [CommMonoid C]
    (T : Submonoid R') (f : R' → C) (hf : T.IsLocalizationMap f) (e : R ≃* R') :
    (T.comap e.toMonoidHom).IsLocalizationMap (f ∘ e) := by
  constructor
  · intro t
    exact hf.map_units ⟨e t, t.property⟩
  · intro z
    obtain ⟨⟨a, t⟩, ht⟩ := hf.surj z
    refine ⟨⟨e.symm a, ⟨e.symm t, ?_⟩⟩, ?_⟩
    · show e (e.symm t) ∈ T
      simp
    · simpa using ht
  · intro x y hxy
    obtain ⟨t, ht⟩ := hf.exists_of_eq hxy
    refine ⟨⟨e.symm t, ?_⟩, ?_⟩
    · show e (e.symm t) ∈ T
      simp
    · apply e.injective
      simpa using ht

/-- Being the localization of an extension only depends on the isomorphism class of the
source extension. -/
private theorem isLocalizedExtension_of_iso
    (k : Type uk) (B : Type uB) [Field k] [CommRing B] [Algebra k B]
    (S : Submonoid B) (N : Type uN) [AddCommGroup N] [Module B N]
    (X X' : (algebraExtensionProblem k B N).CompatibleExtension.{max uk (max uB uN)})
    (Y : (algebraExtensionProblem k (Localization S)
      (LocalizedModule S N)).CompatibleExtension.{max uk (max uB uN)})
    (e : SquareZeroExtensionProblem.CompatibleExtension.Iso X X')
    (h : IsLocalizedExtension k B S N X' Y) : IsLocalizedExtension k B S N X Y := by
  let : Algebra k X.B' := X.algebraA'B'
  let : Algebra k X'.B' := X'.algebraA'B'
  let : Algebra k Y.B' := Y.algebraA'B'
  obtain ⟨f, hf, hfq, hfn⟩ := h
  let eA : X.B' ≃ₐ[k] X'.B' := e.toAlgEquiv
  have heq (c : X.B') : X'.toB (eA c) = X.toB c :=
    DFunLike.congr_fun e.toB_comm c
  have hT : (S.comap X'.toB.toRingHom).comap eA.toRingEquiv.toMulEquiv.toMonoidHom =
      S.comap X.toB.toRingHom := by
    ext c
    show X'.toB (eA c) ∈ S ↔ X.toB c ∈ S
    rw [heq]
  refine ⟨f.comp eA.toAlgHom, ?_, ?_, ?_⟩
  · rw [← hT]
    exact isLocalizationMap_comp_mulEquiv _ _ hf eA.toRingEquiv.toMulEquiv
  · intro c
    show Y.toB (f (eA c)) = _
    rw [hfq, heq]
  · intro n
    show f (e.toAlgEquiv (X.kernelEquiv n)) = _
    rw [e.kernelEquiv_comm, hfn]

/-- A lift from a presentation to an extension of `C` by `N` induces its relation map on the
conormal module, when `N` is a compatible `B`- and `C`-module. -/
private theorem exists_cotangentMap_of_lift_of_isScalarTower
    {k B C N : Type*} [CommRing k] [CommRing B] [CommRing C]
    [Algebra k B] [Algebra B C] [Algebra k C] [IsScalarTower k B C]
    [AddCommGroup N] [Module C N] [Module B N] [IsScalarTower B C N]
    (P : Algebra.Extension k B)
    (X : (algebraExtensionProblem k C N).CompatibleExtension) :
    letI : Algebra k X.B' := X.algebraA'B'
    ∀ (f : P.Ring →ₐ[k] X.B')
      (_ : ∀ p, X.toB (f p) = algebraMap B C (algebraMap P.Ring B p)),
    ∃ l : P.Cotangent →ₗ[B] N, ∀ p : P.ker,
      (X.kernelEquiv (l (Algebra.Extension.Cotangent.mk p)) : X.B') = f p := by
  let : Algebra k X.B' := X.algebraA'B'
  intro f hf
  let : Module P.Ring N := Module.compHom N (algebraMap P.Ring B)
  let : IsScalarTower P.Ring B N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hmem (p : P.ker) : f p ∈ RingHom.ker X.toB.toRingHom := by
    show X.toB (f p) = 0
    rw [hf, p.property, map_zero]
  let l₀ : P.ker →ₗ[P.Ring] N :=
    { toFun := fun p ↦ X.kernelEquiv.symm ⟨f p, hmem p⟩
      map_add' := by
        intro p q
        apply X.kernelEquiv.injective
        simp only [map_add, LinearEquiv.apply_symm_apply]
        exact Subtype.ext (f.map_add p q)
      map_smul' := by
        intro a p
        apply X.kernelEquiv.injective
        apply Subtype.ext
        simp only [LinearEquiv.apply_symm_apply]
        show f (a * p) = _
        rw [map_mul]
        have h := kernelEquiv_smul_toB X (f a) (X.kernelEquiv.symm ⟨f p, hmem p⟩)
        rw [LinearEquiv.apply_symm_apply] at h
        rw [← h]
        congr 2
        rw [hf]
        let m : N := X.kernelEquiv.symm ⟨f p, hmem p⟩
        show (algebraMap B C (algebraMap P.Ring B a)) • m = (algebraMap P.Ring B a) • m
        exact IsScalarTower.algebraMap_smul (R := B) (A := C) (algebraMap P.Ring B a) m }
  have hl₀ (p : P.ker) : (X.kernelEquiv (l₀ p) : X.B') = f p :=
    congrArg Subtype.val (X.kernelEquiv.apply_symm_apply ⟨f p, hmem p⟩)
  have hprod (p q : P.ker) : l₀ (p * q) = 0 := by
    apply X.kernelEquiv.injective
    apply Subtype.ext
    rw [hl₀, map_zero, Submodule.coe_zero]
    show f (p * q) = 0
    rw [map_mul]
    have h := Ideal.mul_mem_mul (hmem p) (hmem q)
    rw [← pow_two, X.sq_zero] at h
    exact h
  let l₁ := (Ideal.Cotangent.lift l₀ hprod).comp P.cotangentEquivCotangentKer.toLinearMap
  let l := l₁.extendScalarsOfSurjective P.algebraMap_surjective
  refine ⟨l, fun p ↦ ?_⟩
  show (X.kernelEquiv (Ideal.Cotangent.lift l₀ hprod
    (P.ker.toCotangent p)) : X.B') = f p
  rw [Ideal.Cotangent.lift_toCotangent]
  exact hl₀ p

/-- A lift from a presentation to an extension induces its relation map on the conormal
module. -/
private theorem exists_cotangentMap_of_lift
    {k B N : Type*} [CommRing k] [CommRing B] [Algebra k B]
    [AddCommGroup N] [Module B N]
    (P : Algebra.Extension k B)
    (X : (algebraExtensionProblem k B N).CompatibleExtension) :
    letI : Algebra k X.B' := X.algebraA'B'
    ∀ (f : P.Ring →ₐ[k] X.B')
      (_ : ∀ p, X.toB (f p) = algebraMap P.Ring B p),
    ∃ l : P.Cotangent →ₗ[B] N, ∀ p : P.ker,
      (X.kernelEquiv (l (Algebra.Extension.Cotangent.mk p)) : X.B') = f p :=
  exists_cotangentMap_of_lift_of_isScalarTower P X

/-- A lift to an extension of a localization gives a relation map with localized
coefficients. -/
private theorem exists_cotangentMap_of_lift_localized
    {k B N : Type*} [CommRing k] [CommRing B] [Algebra k B]
    [AddCommGroup N] [Module B N] (S : Submonoid B)
    (P : Algebra.Extension k B)
    (Y : (algebraExtensionProblem k (Localization S)
      (LocalizedModule S N)).CompatibleExtension) :
    letI : Algebra k Y.B' := Y.algebraA'B'
    ∀ (f : P.Ring →ₐ[k] Y.B')
      (_ : ∀ p, Y.toB (f p) =
        algebraMap B (Localization S) (algebraMap P.Ring B p)),
    ∃ l : P.Cotangent →ₗ[B] LocalizedModule S N, ∀ p : P.ker,
      (Y.kernelEquiv (l (Algebra.Extension.Cotangent.mk p)) : Y.B') = f p :=
  exists_cotangentMap_of_lift_of_isScalarTower P Y

/-- The difference of two lifts is a derivation, hence a functional on the cotangent space. -/
private theorem exists_cotangentSpaceMap_of_lift_difference
    {k B C N : Type*} [CommRing k] [CommRing B] [CommRing C]
    [Algebra k B] [Algebra B C] [Algebra k C] [IsScalarTower k B C]
    [AddCommGroup N] [Module C N] [Module B N] [IsScalarTower B C N]
    (P : Algebra.Extension k B)
    (X : (algebraExtensionProblem k C N).CompatibleExtension) :
    letI : Algebra k X.B' := X.algebraA'B'
    ∀ (f g : P.Ring →ₐ[k] X.B')
      (_ : ∀ p, X.toB (f p) = algebraMap B C (algebraMap P.Ring B p))
      (_ : ∀ p, X.toB (g p) = algebraMap B C (algebraMap P.Ring B p)),
    ∃ t : P.CotangentSpace →ₗ[B] N, ∀ p : P.Ring,
      (X.kernelEquiv (t (1 ⊗ₜ[P.Ring] KaehlerDifferential.D k P.Ring p)) : X.B') =
        f p - g p := by
  classical
  let : Algebra k X.B' := X.algebraA'B'
  intro f g hf hg
  let : Algebra P.Ring X.B' := g.toRingHom.toAlgebra
  let : IsScalarTower k P.Ring X.B' :=
    IsScalarTower.of_algebraMap_eq' (by ext a; exact (g.commutes a).symm)
  let I : Ideal X.B' := RingHom.ker X.toB.toRingHom
  have he : (Ideal.Quotient.mkₐ k I).comp f =
      IsScalarTower.toAlgHom k P.Ring (X.B' ⧸ I) := by
    ext p
    apply Ideal.Quotient.eq.mpr
    show f p - g p ∈ I
    show X.toB (f p - g p) = 0
    rw [map_sub, hf, hg, sub_self]
  let : Module P.Ring N := Module.compHom N (algebraMap P.Ring B)
  let : IsScalarTower P.Ring B N :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : Module k N := Module.compHom N (algebraMap k B)
  let : IsScalarTower k P.Ring N := IsScalarTower.of_algebraMap_smul (by
    intro a n
    show (algebraMap P.Ring B (algebraMap k P.Ring a)) • n =
      (algebraMap k B a) • n
    rw [← IsScalarTower.algebraMap_apply k P.Ring B])
  let eLin : N →ₗ[P.Ring] I :=
    { toFun := X.kernelEquiv
      map_add' := X.kernelEquiv.map_add
      map_smul' := by
        intro r n
        apply Subtype.ext
        show (X.kernelEquiv ((algebraMap P.Ring B r) • n) : X.B') =
          g r * (X.kernelEquiv n : X.B')
        rw [← IsScalarTower.algebraMap_smul (R := B) (A := C)
          (algebraMap P.Ring B r) n, ← hg, kernelEquiv_smul_toB] }
  let e : N ≃ₗ[P.Ring] I := LinearEquiv.ofBijective eLin X.kernelEquiv.bijective
  let dI : Derivation k P.Ring I := derivationToSquareZeroOfLift I X.sq_zero f he
  let dN : Derivation k P.Ring N := e.symm.toLinearMap.compDer dI
  let t : P.CotangentSpace →ₗ[B] N := dN.liftKaehlerDifferential.liftBaseChange B
  refine ⟨t, fun p ↦ ?_⟩
  have h := derivationToSquareZeroOfLift_apply I X.sq_zero f he p
  have ht : t (1 ⊗ₜ[P.Ring] KaehlerDifferential.D k P.Ring p) = dN p := by
    simp only [t, LinearMap.liftBaseChange_tmul, one_smul,
      Derivation.liftKaehlerDifferential_comp_D]
  rw [ht]
  show ((e (dN p) : I) : X.B') = f p - g p
  rw [show e (dN p) = dI p from e.apply_symm_apply (dI p)]
  exact h

end Deformation.Examples

end
