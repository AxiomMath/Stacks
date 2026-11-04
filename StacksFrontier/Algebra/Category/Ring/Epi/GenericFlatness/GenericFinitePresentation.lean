module


import StacksCore.Algebra.Module.FinitePresentation
public import StacksFrontier.RingTheory.FinitePresentation.FreeAway
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Data.Finsupp.PWO
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.Algebra.Category.Ring.Epi.GenericFlatness.FinitePresentation

/-!
# Generic freeness and generic finite presentation (051T)

This file proves `Algebra.exists_ne_zero_isFinitePresentationFreeAway` (Stacks 051T): for a finite
module `M` over a finite type algebra `S` over a domain `R`, some nonzero `f ∈ R` satisfies the
condition `Algebra.IsFinitePresentationFreeAway R S M f` of Equation 051U. The overview of Stacks
section 051Q and its implementation notes are the module docstring of
`StacksFrontier.Algebra.Category.Ring.Epi.GenericFlatness.Noetherian`.
-/

@[expose] public section

universe u v w

/-! ### Generic freeness and generic finite presentation (051T) -/

section
open TensorProduct

/-- **A finitely generated approximation of a kernel.** Let `A` be an `R`-algebra of finite type,
let `V` be a finite `A`-module and let `p ⊆ R` be a submonoid such that `p⁻¹R` is Noetherian (for
instance the nonzero divisors of a domain). Then the kernel of any `A`-linear map out of `V`
contains a finitely generated submodule `Q` with `p`-torsion quotient: every element of the kernel
becomes an element of `Q` after multiplication by an element of `p`. -/
private theorem exists_fg_le_ker_torsion {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (p : Submonoid R) [IsNoetherianRing (Localization p)]
    {V : Type v} [AddCommGroup V] [Module A V] [Module.Finite A V]
    {W : Type w} [AddCommGroup W] [Module A W] (φ : V →ₗ[A] W) :
    ∃ Q : Submodule A V, Q.FG ∧ Q ≤ LinearMap.ker φ ∧
      ∀ x ∈ LinearMap.ker φ, ∃ c ∈ p, algebraMap R A c • x ∈ Q := by
  classical
  let T : Submonoid A := Submonoid.map (algebraMap R A) p
  let A' := Localization T
  let L := LocalizedModule T V
  let l : V →ₗ[A] L := LocalizedModule.mkLinearMap T V
  let _ : Algebra (Localization p) A' :=
    (IsLocalization.map A' (algebraMap R A) (Submonoid.le_comap_map p)).toAlgebra
  have : Algebra.FiniteType (Localization p) A' :=
    RingHom.finiteType_localizationPreserves (algebraMap R A) p (Localization p) A'
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  have : IsNoetherianRing A' := Algebra.FiniteType.isNoetherianRing (Localization p) A'
  have : Module.Finite A' L := Module.Finite.of_isLocalizedModule T l
  have : IsNoetherian A' L := isNoetherian_of_isNoetherianRing_of_finite A' L
  set N : Submodule A V := LinearMap.ker φ
  obtain ⟨G, hG⟩ : (Submodule.localized' A' T l N).FG := IsNoetherian.noetherian _
  have hmem : ∀ g : {x // x ∈ G}, ∃ m ∈ N, ∃ s : T, IsLocalizedModule.mk' l m s = (g : L) := by
    intro g
    refine (Submodule.mem_localized' A' T l N g).1 ?_
    rw [← hG]
    exact Submodule.subset_span (by simp)
  choose m hmN s hms using hmem
  refine ⟨Submodule.span A (Set.range m), Submodule.fg_span (Set.finite_range m),
    Submodule.span_le.2 (Set.range_subset_iff.2 hmN), ?_⟩
  intro x hx
  have key : Submodule.localized' A' T l N ≤
      Submodule.localized' A' T l (Submodule.span A (Set.range m)) := by
    rw [← hG]
    refine Submodule.span_le.2 ?_
    intro g hg
    rw [SetLike.mem_coe, Submodule.mem_localized']
    exact ⟨m ⟨g, hg⟩, Submodule.subset_span ⟨_, rfl⟩, s ⟨g, hg⟩, hms _⟩
  have hlx : l x ∈ Submodule.localized' A' T l (Submodule.span A (Set.range m)) :=
    key ((Submodule.mem_localized' A' T l N (l x)).2 ⟨x, hx, 1, by simp⟩)
  obtain ⟨q, hq, t, ht⟩ := (Submodule.mem_localized' A' T l _ (l x)).1 hlx
  have h1 : l q = (t : A) • l x := IsLocalizedModule.mk'_eq_iff.1 ht
  have h2 : l ((t : A) • x - q) = 0 := by
    rw [map_sub, LinearMap.map_smul, h1, sub_self]
  obtain ⟨t', ht'⟩ := (IsLocalizedModule.eq_zero_iff T l).1 h2
  obtain ⟨c, hc, hceq⟩ := Submonoid.mem_map.1 (t' * t).2
  refine ⟨c, hc, ?_⟩
  have h4 : (t' : A) • ((t : A) • x - q) = 0 := ht'
  rw [smul_sub, sub_eq_zero, ← mul_smul] at h4
  rw [show algebraMap R A c = (t' : A) * (t : A) by rw [hceq]; simp, h4]
  exact Submodule.smul_mem _ _ hq

/-- **The quotient of the approximation is torsion.** If every element of the kernel of `φ` enters
the submodule `Q` after multiplication by a non-zero-divisor of `R`, then the image in `V ⧸ Q` of an
element of the kernel of `φ` is killed by a nonzero element of `R`. -/
private theorem exists_ne_zero_smul_mkQ_eq_zero {R A : Type*} [CommRing R] [Nontrivial R]
    [CommRing A] [Algebra R A] {V W : Type*} [AddCommGroup V] [Module R V] [Module A V]
    [IsScalarTower R A V] [AddCommGroup W] [Module A W] {φ : V →ₗ[A] W} {Q : Submodule A V}
    (hQ : ∀ x ∈ LinearMap.ker φ, ∃ c ∈ nonZeroDivisors R, algebraMap R A c • x ∈ Q)
    {y : V} (hy : φ y = 0) : ∃ c : R, c ≠ 0 ∧ c • Q.mkQ y = 0 := by
  obtain ⟨c, hc, hcy⟩ := hQ y hy
  refine ⟨c, nonZeroDivisors.ne_zero hc, ?_⟩
  rwa [← IsScalarTower.algebraMap_smul A c (Q.mkQ y), ← LinearMap.map_smul,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

/-- **Passing to a further localization.** Freeness of a localization of an `R`-module `N` at the
powers of `f₁` over the corresponding localization of `R` is inherited by any localization of `N`
whose localization `Rf` of `R` inverts `f₁`: the localization of `N` is the base change of `N`
along `R → Rf`, and base change along `R → Rf` factors through `R → R_{f₁}`. -/
private theorem free_of_free_localizedModule_away {R : Type u} [CommRing R] {f₁ : R}
    {q : Submonoid R} {N : Type v} [AddCommGroup N] [Module R N]
    (Rf : Type w) [CommRing Rf] [Algebra R Rf] [IsLocalization q Rf]
    {Nf : Type*} [AddCommGroup Nf] [Module R Nf] [Module Rf Nf] [IsScalarTower R Rf Nf]
    (g : N →ₗ[R] Nf) [IsLocalizedModule q g]
    (hf₁ : IsUnit (algebraMap R Rf f₁))
    (h : Module.Free (Localization.Away f₁) (LocalizedModule (Submonoid.powers f₁) N)) :
    Module.Free Rf Nf := by
  let _ : Algebra (Localization.Away f₁) Rf :=
    (IsLocalization.lift (M := Submonoid.powers f₁) (g := algebraMap R Rf)
      (fun y => by obtain ⟨n, hn⟩ := y.2; rw [← hn, map_pow]; exact hf₁.pow n)).toAlgebra
  have : IsScalarTower R (Localization.Away f₁) Rf :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq _ x).symm
  have e1 : Rf ⊗[R] N ≃ₗ[Rf] Nf := ((isLocalizedModule_iff_isBaseChange q Rf g).mp ‹_›).equiv
  have e2 : Localization.Away f₁ ⊗[R] N ≃ₗ[Localization.Away f₁]
      LocalizedModule (Submonoid.powers f₁) N :=
    ((isLocalizedModule_iff_isBaseChange (Submonoid.powers f₁) (Localization.Away f₁)
      (LocalizedModule.mkLinearMap _ N)).mp inferInstance).equiv
  have : Module.Free (Localization.Away f₁) (Localization.Away f₁ ⊗[R] N) :=
    Module.Free.of_equiv e2.symm
  exact Module.Free.of_equiv
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization.Away f₁) Rf Rf N).trans e1)

/-- Generic freeness at `f₁` passes to every multiple of `f₁`. -/
private theorem free_localizedModule_away_of_dvd {R : Type u} [CommRing R] {f₁ f : R} (hd : f₁ ∣ f)
    {N : Type v} [AddCommGroup N] [Module R N]
    (h : Module.Free (Localization.Away f₁) (LocalizedModule (Submonoid.powers f₁) N)) :
    Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) N) :=
  free_of_free_localizedModule_away (q := Submonoid.powers f) (Localization.Away f)
    (LocalizedModule.mkLinearMap _ N)
    (isUnit_of_dvd_unit (map_dvd _ hd) (IsLocalization.Away.algebraMap_isUnit f)) h

/-- Generic freeness of an `R`-module `V` at `f` is inherited by every localization of `V` at the
powers of the image of `f` in an `R`-algebra `A`. -/
private theorem free_of_isLocalizedModule_powers_algebraMap {R A : Type*} [CommRing R]
    [CommRing A] [Algebra R A] (f : R)
    {V : Type*} [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]
    {Vf : Type*} [AddCommGroup Vf] [Module R Vf] [Module A Vf] [IsScalarTower R A Vf]
    [Module (Localization.Away f) Vf] [IsScalarTower R (Localization.Away f) Vf]
    (g : V →ₗ[A] Vf) [IsLocalizedModule (Submonoid.powers (algebraMap R A f)) g]
    (h : Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) V)) :
    Module.Free (Localization.Away f) Vf :=
  have : IsLocalizedModule (Submonoid.powers f) (g.restrictScalars R) :=
    IsLocalizedModule.restrictScalars_powers f g
  free_of_free_localizedModule_away (f₁ := f) (q := Submonoid.powers f) (Localization.Away f)
    (g.restrictScalars R) (IsLocalization.Away.algebraMap_isUnit f) h

/-- **Torsion dies in a free localization.** Let `R` be a domain, let `f : R` be nonzero and let
`V` be a module over an `R`-algebra `A` whose localization at the powers of `f` is free over
`R_f`. Then an element of `V` killed by a nonzero element of `R` is already killed by a power of
the image of `f` in `A`. -/
private theorem exists_powers_algebraMap_smul_eq_zero {R : Type*} [CommRing R] [IsDomain R]
    {A : Type*} [CommRing A] [Algebra R A] {f : R} (hf : f ≠ 0)
    {V : Type*} [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]
    (hfree : Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) V))
    {x : V} (hx : ∃ c : R, c ≠ 0 ∧ c • x = 0) :
    ∃ t : Submonoid.powers (algebraMap R A f), (t : A) • x = 0 := by
  have hpow : Submonoid.powers f ≤ nonZeroDivisors R :=
    Submonoid.powers_le.2 (mem_nonZeroDivisors_of_ne_zero hf)
  have : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hpow
  obtain ⟨c, hc, hcx⟩ := hx
  have hc' : algebraMap R (Localization.Away f) c ≠ 0 := by
    rwa [ne_eq, IsLocalization.to_map_eq_zero_iff (Localization.Away f) hpow]
  have hy : algebraMap R (Localization.Away f) c •
      LocalizedModule.mkLinearMap (Submonoid.powers f) V x = 0 := by
    rw [IsScalarTower.algebraMap_smul, ← LinearMap.map_smul, hcx, map_zero]
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers f) _).mp
    ((Module.isTorsionFree_iff_smul_eq_zero.mp inferInstance _ _ hy).resolve_left hc')
  obtain ⟨k, hk⟩ := t.2
  exact ⟨⟨algebraMap R A (f ^ k), k, by rw [map_pow]⟩, by
    rwa [IsScalarTower.algebraMap_smul, show f ^ k = (t : R) from hk]⟩

/-- **A surjection with `T`-torsion kernel becomes an isomorphism after localizing at `T`.** Let
`u : W' → W` be a surjection of `A`-modules such that every element of its kernel is killed by an
element of the submonoid `T ⊆ A`. Then a localization of `W` at `T` is also a localization of `W'`
at `T`. -/
private theorem isLocalizedModule_comp_of_surjective {A : Type*} [CommRing A]
    {W' W Wf : Type*} [AddCommGroup W'] [Module A W'] [AddCommGroup W] [Module A W]
    [AddCommGroup Wf] [Module A Wf] (T : Submonoid A) (l : W →ₗ[A] Wf) [IsLocalizedModule T l]
    {u : W' →ₗ[A] W} (hu : Function.Surjective u)
    (hker : ∀ x : W', u x = 0 → ∃ t : T, (t : A) • x = 0) :
    IsLocalizedModule T (l ∘ₗ u) where
  map_units s := IsLocalizedModule.map_units l s
  surj y := by
    obtain ⟨⟨w, s⟩, hs⟩ := IsLocalizedModule.surj T l y
    obtain ⟨x, rfl⟩ := hu w
    exact ⟨⟨x, s⟩, hs⟩
  exists_of_eq {x₁ x₂} h := by
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := T) (f := l) h
    have h0 : u ((t : A) • (x₁ - x₂)) = 0 := by
      rw [map_smul, map_sub, smul_sub, sub_eq_zero]
      simpa only [Submonoid.smul_def] using ht
    obtain ⟨t', ht'⟩ := hker _ h0
    refine ⟨t' * t, ?_⟩
    have h1 : ((t' : A) * (t : A)) • x₁ - ((t' : A) * (t : A)) • x₂ = 0 := by
      rw [← smul_sub, mul_smul]
      simpa only [Submonoid.smul_def] using ht'
    simpa only [Submonoid.smul_def, Submonoid.coe_mul] using sub_eq_zero.1 h1

/-- **Restricting scalars along `A → S`.** A localization of an `S`-module at the image in `S` of
the powers of `f : R` is, as an `A`-module for an intermediate `R`-algebra `A`, a localization at
the powers of the image of `f` in `A`. -/
private theorem isLocalizedModule_powers_algebraMap_restrictScalars {R A S : Type*} [CommRing R]
    [CommRing A] [CommRing S] [Algebra R A] [Algebra A S] [Algebra R S] [IsScalarTower R A S]
    (f : R) {W Wf : Type*} [AddCommGroup W] [Module A W] [Module S W] [IsScalarTower A S W]
    [AddCommGroup Wf] [Module A Wf] [Module S Wf] [IsScalarTower A S Wf] (l : W →ₗ[S] Wf)
    (h : IsLocalizedModule (Algebra.algebraMapSubmonoid S (Submonoid.powers f)) l) :
    IsLocalizedModule (Submonoid.powers (algebraMap R A f)) (l.restrictScalars A) := by
  rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers,
    IsScalarTower.algebraMap_apply R A S] at h
  exact IsLocalizedModule.restrictScalars_powers (algebraMap R A f) l

/-- **Finite presentation over the localized base.** A localization of a finitely presented
`R`-algebra `A` at the powers of the image of `f : R` is of finite presentation over `R_f`, being
the base change `R_f ⊗_R A`. -/
private theorem finitePresentation_of_isLocalization_powers {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A] (f : R)
    (T : Type w) [CommRing T] [Algebra A T]
    [IsLocalization (Submonoid.powers (algebraMap R A f)) T]
    [Algebra R T] [IsScalarTower R A T]
    [Algebra (Localization.Away f) T] [IsScalarTower R (Localization.Away f) T] :
    Algebra.FinitePresentation (Localization.Away f) T := by
  have hlocA : IsLocalization (Submonoid.powers (algebraMap R A f))
      (Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers f))) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]; infer_instance
  have h1 : Algebra.FinitePresentation (Localization.Away f) (Localization.Away f ⊗[R] A) :=
    Algebra.FinitePresentation.baseChange _
  have h2 : Algebra.FinitePresentation (Localization.Away f)
      (Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers f))) :=
    Algebra.FinitePresentation.equiv (Localization.tensorRightAlgEquiv (Submonoid.powers f) A)
  let e := IsLocalization.algEquiv (Submonoid.powers (algebraMap R A f))
    (Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers f))) T
  have hcomp : ((e : _ →+* _).comp (algebraMap (Localization.Away f)
      (Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers f))))) =
      algebraMap (Localization.Away f) T := by
    refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun r => ?_)
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
    have hcm := e.commutes (algebraMap R A r)
    rwa [← IsScalarTower.algebraMap_apply R A
        (Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers f))),
      ← IsScalarTower.algebraMap_apply R A T] at hcm
  exact Algebra.FinitePresentation.equiv
    (AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun x => RingHom.congr_fun hcomp x)

/-- **Equation 051U from a finitely presented approximation.** Let `R` be a domain, let `A` be an
`R`-algebra of finite presentation with `A → S` surjective, let `M'` be a finitely presented
`A`-module with `u : M' → M` surjective, and assume both kernels are `R`-torsion. If `f : R` is
nonzero and the localizations of `A` and of `M'` at the powers of `f` are free over `R_f`, then `f`
satisfies the condition 051U for `R → S` and `M`.

Both halves of the argument are the same one: the localizations of `S` and of `M` at the powers of
`f` are *also* the localizations of `A` and of `M'`, because the two kernels, being `R`-torsion,
die in a localization which is free over the domain `R_f`. Finite presentation of `S_f` over `R_f`
and of `M_f` over `S_f` and freeness of `S_f` and `M_f` over `R_f` are then read off from `A` and
`M'`. -/
private theorem isFinitePresentationFreeAway_of_surjective_of_torsion
    {R A S M' M : Type*} [CommRing R] [IsDomain R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [Algebra A S] [IsScalarTower R A S]
    [Algebra.FinitePresentation R A]
    [AddCommGroup M'] [Module R M'] [Module A M'] [IsScalarTower R A M']
    [Module.FinitePresentation A M']
    [AddCommGroup M] [Module A M] [Module S M] [IsScalarTower A S M]
    (hS : Function.Surjective (algebraMap A S))
    (hStors : ∀ a : A, algebraMap A S a = 0 → ∃ c : R, c ≠ 0 ∧ c • a = 0)
    {u : M' →ₗ[A] M} (hu : Function.Surjective u)
    (hutors : ∀ x : M', u x = 0 → ∃ c : R, c ≠ 0 ∧ c • x = 0)
    {f : R} (hf : f ≠ 0)
    (hfA : Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) A))
    (hfM : Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M')) :
    Algebra.IsFinitePresentationFreeAway R S M f := by
  -- the localizations of `S` and of `M`, read at the powers of the image of `f` in `A`
  have hlS := isLocalizedModule_powers_algebraMap_restrictScalars (A := A) f
    (Algebra.linearMap S (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers f))))
    inferInstance
  have hlM := isLocalizedModule_powers_algebraMap_restrictScalars (A := A) f
    (TensorProduct.mk S (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers f))) M 1)
    ((isLocalizedModule_iff_isBaseChange _ _ _).mpr (TensorProduct.isBaseChange S M _))
  -- they are also the localizations of `A` and of `M'`, the two kernels being `R`-torsion
  have hASf : IsLocalizedModule (Submonoid.powers (algebraMap R A f))
      (Algebra.linearMap A
        (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers f)))) := by
    have h := isLocalizedModule_comp_of_surjective (Submonoid.powers (algebraMap R A f))
      ((Algebra.linearMap S
        (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers f)))).restrictScalars A)
      (u := Algebra.linearMap A S) hS
      (fun a ha => exists_powers_algebraMap_smul_eq_zero hf hfA (hStors a ha))
    have heq : (Algebra.linearMap S
        (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers f)))).restrictScalars A ∘ₗ
          Algebra.linearMap A S =
        Algebra.linearMap A
          (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers f))) :=
      LinearMap.ext fun a => (IsScalarTower.algebraMap_apply A S _ a).symm
    rwa [heq] at h
  have hMSf : IsLocalizedModule (Submonoid.powers (algebraMap R A f))
      ((TensorProduct.mk S (Localization (Algebra.algebraMapSubmonoid S
        (Submonoid.powers f))) M 1).restrictScalars A ∘ₗ u) :=
    isLocalizedModule_comp_of_surjective _ _ hu
      (fun x hx => exists_powers_algebraMap_smul_eq_zero hf hfM (hutors x hx))
  have hlocSf : IsLocalization (Submonoid.powers (algebraMap R A f))
      (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers f))) :=
    (isLocalizedModule_iff_isLocalization' _ _).mp hASf
  exact ⟨finitePresentation_of_isLocalization_powers (A := A) f _,
    Module.FinitePresentation.of_equiv
      ((isLocalizedModule_iff_isBaseChange (Submonoid.powers (algebraMap R A f)) _ _).mp
        hMSf).equiv,
    free_of_isLocalizedModule_powers_algebraMap f (Algebra.linearMap A _) hfA,
    free_of_isLocalizedModule_powers_algebraMap f
      ((TensorProduct.mk S (Localization (Algebra.algebraMapSubmonoid S
        (Submonoid.powers f))) M 1).restrictScalars A ∘ₗ u) hfM⟩

/-- **Stacks 051T for a finitely presented approximation of `S`.** Let `R` be a domain, let `A` be
an `R`-algebra of finite presentation whose structure map to `S` is surjective with `R`-torsion
kernel, and let `M` be a finite `S`-module. Then some nonzero `f ∈ R` satisfies the condition 051U
for `R → S` and `M`.

A presentation `A^t → M` is approximated from above: quotienting `A^t` by a finitely generated
submodule of the kernel gives a finitely presented `A`-module `M'` surjecting onto `M` with
`R`-torsion kernel. Lemma 051S applied to `A` and to `M'` gives nonzero `f₁, f₂ ∈ R`, and the
single element `f = f₁f₂` works for both. -/
private theorem exists_ne_zero_isFinitePresentationFreeAway_of_surjective
    {R : Type u} [CommRing R] [IsDomain R] {A : Type u} [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] {S : Type v} [CommRing S] [Algebra R S] [Algebra A S]
    [IsScalarTower R A S] {M : Type w} [AddCommGroup M] [Module S M] [Module.Finite S M]
    (hS : Function.Surjective (algebraMap A S))
    (hStors : ∀ a : A, algebraMap A S a = 0 → ∃ c : R, c ≠ 0 ∧ c • a = 0) :
    ∃ f : R, f ≠ 0 ∧ Algebra.IsFinitePresentationFreeAway R S M f := by
  have : Algebra.FiniteType R A := Algebra.FiniteType.of_finitePresentation
  let _ : Module A M := Module.compHom M (algebraMap A S)
  have : IsScalarTower A S M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Finite A S := Module.Finite.of_surjective (Algebra.linearMap A S) hS
  have : Module.Finite A M := Module.Finite.trans S M
  -- the finitely presented approximation `M' = A^t/Q` of `M`
  obtain ⟨t, φ, hφ⟩ := Module.Finite.exists_fin' A M
  obtain ⟨Q, hQfg, hQ, hQtors⟩ := exists_fg_le_ker_torsion (R := R) (nonZeroDivisors R) φ
  have : Module.FinitePresentation A ((Fin t → A) ⧸ Q) :=
    Module.finitePresentation_of_surjective Q.mkQ Q.mkQ_surjective
      (by rw [Submodule.ker_mkQ]; exact hQfg)
  have hu : Function.Surjective (Q.liftQ φ hQ) := fun m => by
    obtain ⟨x, hx⟩ := hφ m
    exact ⟨Q.mkQ x, hx⟩
  have hutors : ∀ x : (Fin t → A) ⧸ Q, Q.liftQ φ hQ x = 0 → ∃ c : R, c ≠ 0 ∧ c • x = 0 := by
    intro x hx
    obtain ⟨y, rfl⟩ := Q.mkQ_surjective x
    exact exists_ne_zero_smul_mkQ_eq_zero hQtors hx
  obtain ⟨f₁, hf₁, hfree₁⟩ :=
    Module.FinitePresentation.exists_ne_zero_free_localizedModule_away (R := R) (S := A) (M := A)
  obtain ⟨f₂, hf₂, hfree₂⟩ :=
    Module.FinitePresentation.exists_ne_zero_free_localizedModule_away (R := R) (S := A)
      (M := (Fin t → A) ⧸ Q)
  exact ⟨f₁ * f₂, mul_ne_zero hf₁ hf₂,
    isFinitePresentationFreeAway_of_surjective_of_torsion hS hStors hu hutors
      (mul_ne_zero hf₁ hf₂)
      (free_localizedModule_away_of_dvd (dvd_mul_right f₁ f₂)
        (hfree₁ (Localization.Away f₁) (LocalizedModule (Submonoid.powers f₁) A)
          (LocalizedModule.mkLinearMap _ _)))
      (free_localizedModule_away_of_dvd (dvd_mul_left f₂ f₁)
        (hfree₂ (Localization.Away f₂)
          (LocalizedModule (Submonoid.powers f₂) ((Fin t → A) ⧸ Q))
          (LocalizedModule.mkLinearMap _ _)))⟩

namespace Algebra

/-- **Stacks 051T** (generic freeness and generic finite presentation). Let `R` be a domain, let
`S` be an `R`-algebra of finite type and let `M` be a finite `S`-module. Then some nonzero `f ∈ R`
satisfies the condition `Algebra.IsFinitePresentationFreeAway R S M f` of Equation 051U: the
localizations `S_f` and `M_f` are free `R_f`-modules, `S_f` is a finitely presented `R_f`-algebra
and `M_f` is a finitely presented `S_f`-module. -/
@[stacks 051T "The four conclusions are the condition of Equation 051U, so they are cited as
`Algebra.IsFinitePresentationFreeAway` rather than written out; that definition fixes the models
of `R_f`, `S_f` and `M_f`, and `Algebra.isFinitePresentationFreeAway_iff` moves the conclusion to
any other models. See the module docstring.",
  ega "IV 6.9.2" "more general",
  sga "1 IV 6.7"
  "more general",
  ega "IV 8.9.4.1",
  sga "1 IV 6.7" "more general",
  ega "IV 11.4.6" "special case",
  ega "IV 6.11.9" "more general"]
public theorem exists_ne_zero_isFinitePresentationFreeAway
    {R S M : Type*} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    [AddCommGroup M] [Module S M] [Module.Finite S M] :
    ∃ f : R, f ≠ 0 ∧ Algebra.IsFinitePresentationFreeAway R S M f := by
  classical
  obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType R S›
  let _ : Algebra (MvPolynomial (Fin n) R) S := π.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R) S :=
    IsScalarTower.of_algebraMap_eq fun x => (π.commutes x).symm
  -- the finitely presented approximation `A = P/J` of `S`
  obtain ⟨J, hJfg, hJI, hJtors⟩ := exists_fg_le_ker_torsion (R := R) (nonZeroDivisors R)
    (Algebra.linearMap (MvPolynomial (Fin n) R) S)
  have : Algebra.FinitePresentation R (MvPolynomial (Fin n) R ⧸ J) :=
    Algebra.FinitePresentation.quotient hJfg
  let ψ : (MvPolynomial (Fin n) R ⧸ J) →ₐ[R] S :=
    Ideal.Quotient.liftₐ J π fun a ha => LinearMap.mem_ker.mp (hJI ha)
  have hψ : Function.Surjective ψ := fun s => by
    obtain ⟨p, hp⟩ := hπ s
    exact ⟨Ideal.Quotient.mk J p, hp⟩
  let _ : Algebra (MvPolynomial (Fin n) R ⧸ J) S := ψ.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R ⧸ J) S :=
    IsScalarTower.of_algebraMap_eq fun x => (ψ.commutes x).symm
  refine exists_ne_zero_isFinitePresentationFreeAway_of_surjective hψ fun a ha => ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact exists_ne_zero_smul_mkQ_eq_zero (φ := Algebra.linearMap (MvPolynomial (Fin n) R) S)
    hJtors ha

end Algebra

end

end
