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
public import StacksFrontier.Algebra.Category.Ring.Epi.GenericFlatness.Noetherian
import all StacksFrontier.Algebra.Category.Ring.Epi.GenericFlatness.Noetherian

/-!
# The generic freeness locus (051W, 051X, 051Y)

This file studies the locus `U(R → S, M)` of Equation 051V, the union of the standard opens `D(f)`
over the `f` satisfying `Algebra.IsFinitePresentationFreeAway R S M f`: the condition passes to
multiples (`Algebra.IsFinitePresentationFreeAway.of_dvd`), the locus is stable under extensions of
the module (051W), it is local on the base (051X), and its density may be checked on a dense open
(051Y). The overview of Stacks section 051Q and its implementation notes are the module docstring of
`StacksFrontier.Algebra.Category.Ring.Epi.GenericFlatness.Noetherian`.
-/

@[expose] public section

/-! ### The generic freeness locus (051W, 051X, 051Y) -/

section
open PrimeSpectrum TensorProduct

/-! #### Passing to a multiple -/

/-- The canonical model of `B_x` for an element `x` of the base ring `A` is the localization of
`B` away from the image of `x`, its submonoid being the image of the powers of `x`. -/
private theorem isLocalization_away_algebraMapSubmonoid {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (x : A) :
    IsLocalization.Away (algebraMap A B x)
      (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers x))) := by
  change IsLocalization (Submonoid.powers _) _
  rw [← Submonoid.map_powers]
  exact Localization.isLocalization

/-- **A localization of a module followed by a base change to a further localization of the ring
is a localization.** If `l : M →ₗ[S] Mf` presents `Mf` as the localization of `M` at `T` and `Sf'`
is a localization of `S` at `T'` through `Sf`, then `Sf' ⊗[Sf] Mf` is the localization of `M` at
`T'`, both maps being base changes. -/
private theorem isLocalizedModule_mk_comp {S M : Type*} [CommRing S] [AddCommGroup M]
    [Module S M] (Sf : Type*) [CommRing Sf] [Algebra S Sf] {Mf : Type*} [AddCommGroup Mf]
    [Module S Mf] [Module Sf Mf] [IsScalarTower S Sf Mf] (Sf' : Type*) [CommRing Sf']
    [Algebra S Sf'] [Algebra Sf Sf'] [IsScalarTower S Sf Sf'] (T T' : Submonoid S)
    [IsLocalization T Sf] [IsLocalization T' Sf'] (l : M →ₗ[S] Mf) [IsLocalizedModule T l] :
    IsLocalizedModule T' (((TensorProduct.mk Sf Sf' Mf 1).restrictScalars S).comp l) :=
  (isLocalizedModule_iff_isBaseChange _ _ _).mpr
    (((isLocalizedModule_iff_isBaseChange T Sf l).mp inferInstance).comp
      (TensorProduct.isBaseChange Sf Mf Sf'))

/-- A unit lies in no prime, so its standard open is everything. This is
`AlgebraicGeometry.Scheme.basicOpen_of_isUnit` on an affine scheme. -/
private theorem basicOpen_of_isUnit {R : Type*} [CommRing R] {u : R} (hu : IsUnit u) :
    basicOpen u = ⊤ := by
  ext p
  simpa using fun hmem => p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem hmem hu)

/-- **Freeness over the base survives inverting an element of the base.** If `N` is free over `A`
then `B_x ⊗[B] N` is free over `A_x` for every `x : A`: it is the localization of `N` at the
powers of `x`, hence the base change `A_x ⊗[A] N`, and freeness is stable under base change. -/
private theorem free_tensor_of_free {A B N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N] [Module.Free A N] (x : A) :
    Module.Free (Localization.Away x)
      (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers x)) ⊗[B] N) := by
  have := isLocalization_away_algebraMapSubmonoid (B := B) x
  have hmk : IsLocalizedModule (Submonoid.powers (algebraMap A B x))
      (TensorProduct.mk B
        (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers x))) N 1) :=
    (isLocalizedModule_iff_isBaseChange _ _ _).mpr (TensorProduct.isBaseChange B N _)
  exact Module.Free.of_equiv
    ((isLocalizedModule_iff_isBaseChange (Submonoid.powers x)
      (Localization (Submonoid.powers x)) _).mp
      (IsLocalizedModule.restrictScalars_powers x (TensorProduct.mk B
        (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers x))) N 1))).equiv

/-- **Everything already nice makes every element good.** If `B` is of finite presentation and
free over `A` and `N` is of finite presentation over `B` and free over `A`, then every `x : A`
satisfies the condition 051U for `A → B` and `N`: all four properties survive inverting `x`, being
stable under the base change along `A → A_x`. -/
public theorem Algebra.isFinitePresentationFreeAway_of_finitePresentation_of_free {A B N : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N] [Algebra.FinitePresentation A B] [Module.FinitePresentation B N]
    [Module.Free A B] [Module.Free A N] (x : A) :
    Algebra.IsFinitePresentationFreeAway A B N x :=
  let e : Localization (Submonoid.powers x) ⊗[A] B ≃ₐ[Localization (Submonoid.powers x)]
      Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers x)) :=
    Localization.tensorRightAlgEquiv (Submonoid.powers x) B
  ⟨Algebra.FinitePresentation.equiv e, inferInstance, Module.Free.of_equiv e.toLinearEquiv,
    free_tensor_of_free x⟩

/-- **Goodness over the base and over a localization of the base agree.** Let `R → S` be a ring
map, `M` an `S`-module, `f : R`, and let `R_f`, `S_f`, `M_f` be models of the localizations at the
powers of `f`. Then, for `a : R`, the image of `a` in `R_f` satisfies the condition 051U for
`R_f → S_f` and `M_f` exactly when `f * a` satisfies it for `R → S` and `M`: the canonical models
of `(R_f)_a`, `(S_f)_a` and `(M_f)_a` are models of `R_{fa}`, `S_{fa}` and `M_{fa}`. -/
private theorem isFinitePresentationFreeAway_algebraMap_iff {R S M : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [AddCommGroup M] [Module S M] (f a : R)
    (Rf : Type*) [CommRing Rf] [Algebra R Rf] [IsLocalization.Away f Rf]
    (Sf : Type*) [CommRing Sf] [Algebra R Sf] [Algebra S Sf] [Algebra Rf Sf]
      [IsScalarTower R S Sf] [IsScalarTower R Rf Sf]
      [IsLocalization.Away (algebraMap R S f) Sf]
    (Mf : Type*) [AddCommGroup Mf] [Module S Mf] [Module Sf Mf] [IsScalarTower S Sf Mf]
    (l : M →ₗ[S] Mf) [IsLocalizedModule (Submonoid.powers (algebraMap R S f)) l] :
    Algebra.IsFinitePresentationFreeAway Rf Sf Mf (algebraMap R Rf a) ↔
      Algebra.IsFinitePresentationFreeAway R S M (f * a) := by
  have tower : IsScalarTower R (Localization.Away (algebraMap R Rf a))
      (Localization (Algebra.algebraMapSubmonoid Sf
        (Submonoid.powers (algebraMap R Rf a)))) := .to₁₃₄ _ Rf _ _
  have ha : IsLocalization.Away (algebraMap S Sf (algebraMap R S a))
      (Localization (Algebra.algebraMapSubmonoid Sf
        (Submonoid.powers (algebraMap R Rf a)))) := by
    rw [← IsScalarTower.algebraMap_apply R S Sf, IsScalarTower.algebraMap_apply R Rf Sf]
    exact isLocalization_away_algebraMapSubmonoid _
  have hfa : IsLocalization.Away (algebraMap R S (f * a))
      (Localization (Algebra.algebraMapSubmonoid Sf
        (Submonoid.powers (algebraMap R Rf a)))) := by
    rw [map_mul]
    exact IsLocalization.Away.mul' Sf _ _ _
  have hl := isLocalizedModule_mk_comp Sf
    (Localization (Algebra.algebraMapSubmonoid Sf (Submonoid.powers (algebraMap R Rf a))))
    (Submonoid.powers (algebraMap R S f)) (Submonoid.powers (algebraMap R S (f * a))) l
  exact (Algebra.isFinitePresentationFreeAway_iff (f * a)
    (Localization.Away (algebraMap R Rf a))
    (Localization (Algebra.algebraMapSubmonoid Sf (Submonoid.powers (algebraMap R Rf a))))
    (Localization (Algebra.algebraMapSubmonoid Sf (Submonoid.powers (algebraMap R Rf a)))
      ⊗[Sf] Mf)
    (((TensorProduct.mk Sf (Localization (Algebra.algebraMapSubmonoid Sf
      (Submonoid.powers (algebraMap R Rf a)))) Mf 1).restrictScalars S).comp l)).symm

/-- **The condition 051U passes to multiples.** If `g : R` satisfies the condition 051U for
`R → S` and `M` and `g ∣ h`, then `h` satisfies it too, since `R_h` is a localization of `R_g`. -/
public theorem Algebra.IsFinitePresentationFreeAway.of_dvd {R S M : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [AddCommGroup M] [Module S M] {g h : R}
    (hg : Algebra.IsFinitePresentationFreeAway R S M g) (hgh : g ∣ h) :
    Algebra.IsFinitePresentationFreeAway R S M h := by
  obtain ⟨c, rfl⟩ := hgh
  obtain ⟨_, _, _, _⟩ := hg
  have := isLocalization_away_algebraMapSubmonoid (B := S) g
  exact (isFinitePresentationFreeAway_algebraMap_iff g c (Localization.Away g)
    (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers g)))
    (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers g)) ⊗[S] M)
    (TensorProduct.mk S
      (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers g))) M 1)).mp
    (Algebra.isFinitePresentationFreeAway_of_finitePresentation_of_free _)

/-! #### Extensions -/

/-- **The condition 051U is stable under extensions.** If `0 → M₁ → M₂ → M₃ → 0` is a short exact
sequence of `S`-modules and `f : R` satisfies the condition 051U for `M₁` and for `M₃`, then it
satisfies it for `M₂`: inverting `f` is a flat base change, hence exact, so `M₂,f` is an extension
of `M₃,f` by `M₁,f`, and both finite presentation over `S_f` and freeness over `R_f` pass to
extensions. -/
private theorem isFinitePresentationFreeAway_of_shortExact {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module S M₁] [AddCommGroup M₂]
    [Module S M₂] [AddCommGroup M₃] [Module S M₃] (i : M₁ →ₗ[S] M₂) (q : M₂ →ₗ[S] M₃)
    (hi : Function.Injective i) (hq : Function.Surjective q) (hiq : Function.Exact i q) {f : R}
    (h₁ : Algebra.IsFinitePresentationFreeAway R S M₁ f)
    (h₃ : Algebra.IsFinitePresentationFreeAway R S M₃ f) :
    Algebra.IsFinitePresentationFreeAway R S M₂ f := by
  -- the unnamed components are the finite presentation and freeness of `M₁,f` and `M₃,f`, which
  -- the two extension lemmas take as instances
  obtain ⟨hSf, _, hSfree, _⟩ := h₁
  obtain ⟨-, _, -, _⟩ := h₃
  set Sf := Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers f))
  have hi' := baseChange_injective Sf hi
  have hq' := LinearMap.baseChange_surjective Sf hq
  have hiq' := baseChange_exact Sf hiq
  exact ⟨hSf, Module.FinitePresentation.of_exact_fst _ _ hiq' hi' hq', hSfree,
    free_of_shortExact (i := (i.baseChange Sf).restrictScalars (Localization.Away f))
      (q := (q.baseChange Sf).restrictScalars (Localization.Away f)) hi' hq' hiq'⟩

/-! #### The locus of `Spec R` and the locus of `Spec (R_f)` -/

/-- Under the identification `Spec (R_f) = D(f)`, the standard open of the image of `a : R` is the
part of `D(a)` lying in `D(f)`: it is the preimage of `D(a)`, and the range of
`PrimeSpectrum.comap (algebraMap R Rf)` is `D(f)`. -/
private theorem image_comap_basicOpen_algebraMap {R : Type*} [CommRing R] (f a : R)
    (Rf : Type*) [CommRing Rf] [Algebra R Rf] [IsLocalization.Away f Rf] :
    comap (algebraMap R Rf) '' (basicOpen (algebraMap R Rf a) : Set (PrimeSpectrum Rf)) =
      (basicOpen f : Set (PrimeSpectrum R)) ∩ (basicOpen a : Set (PrimeSpectrum R)) := by
  have h : (basicOpen (algebraMap R Rf a) : Set (PrimeSpectrum Rf)) =
      comap (algebraMap R Rf) ⁻¹' (basicOpen a : Set (PrimeSpectrum R)) := by ext q; simp
  rw [h, Set.image_preimage_eq_inter_range, localization_away_comap_range Rf f, Set.inter_comm]

/-- **A good standard open of `Spec(R_f)` is a good standard open of `Spec R` inside `D(f)`.**
For `g : R_f` good for `M_f` there is an `a : R` good for `M` whose standard open, intersected
with `D(f)`, is the image of `D(g)`: writing `g = b / f ^ n` makes `D(g)` the standard open of the
image of `b`, and `a = f * b` is good because the image of `b` is. -/
private theorem exists_isFinitePresentationFreeAway_image_comap_basicOpen {R S M : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module S M] (f : R)
    (Rf : Type*) [CommRing Rf] [Algebra R Rf] [IsLocalization.Away f Rf]
    (Sf : Type*) [CommRing Sf] [Algebra R Sf] [Algebra S Sf] [Algebra Rf Sf]
      [IsScalarTower R S Sf] [IsScalarTower R Rf Sf]
      [IsLocalization.Away (algebraMap R S f) Sf]
    (Mf : Type*) [AddCommGroup Mf] [Module S Mf] [Module Sf Mf] [IsScalarTower S Sf Mf]
    (l : M →ₗ[S] Mf) [IsLocalizedModule (Submonoid.powers (algebraMap R S f)) l] {g : Rf}
    (hg : Algebra.IsFinitePresentationFreeAway Rf Sf Mf g) :
    ∃ a : R, Algebra.IsFinitePresentationFreeAway R S M a ∧
      comap (algebraMap R Rf) '' (basicOpen g : Set (PrimeSpectrum Rf)) =
        (basicOpen f : Set (PrimeSpectrum R)) ∩ (basicOpen a : Set (PrimeSpectrum R)) := by
  obtain ⟨n, b, hnb⟩ := IsLocalization.Away.surj f g
  have hb : Algebra.IsFinitePresentationFreeAway Rf Sf Mf (algebraMap R Rf b) :=
    hg.of_dvd ⟨_, hnb.symm⟩
  have hD : basicOpen (algebraMap R Rf b) = basicOpen g := by
    rw [← hnb, basicOpen_mul,
      basicOpen_of_isUnit ((IsLocalization.Away.algebraMap_isUnit f).pow n), inf_top_eq]
  refine ⟨f * b, (isFinitePresentationFreeAway_algebraMap_iff f b Rf Sf Mf l).mp hb, ?_⟩
  rw [← hD, image_comap_basicOpen_algebraMap f b Rf, basicOpen_mul]
  simp

namespace Algebra

/-- **Stacks 051W**. Let `R → S` be a ring map and let `0 → M₁ → M₂ → M₃ → 0` be a short exact
sequence of `S`-modules. Writing `U(R → S, M) = ⋃ {D(f) | Algebra.IsFinitePresentationFreeAway R S
M f}` for the locus of Equation 051V, one has
`U(R → S, M₁) ∩ U(R → S, M₃) ⊆ U(R → S, M₂)`: an extension of free modules is free and an
extension of finitely presented modules is finitely presented, so if `f₁` and `f₃` satisfy
Equation 051U for `M₁` and `M₃` then `f₁f₃` satisfies it for `M₂`. -/
@[stacks 051W "The locus `U(R → S, M)` of Equation 051V, which has no separate definition here, is
written out as the union of the standard opens `D(f)` over the `f` satisfying Equation 051U, i.e.
over `Algebra.IsFinitePresentationFreeAway R S M f`. See the module docstring."]
public theorem iUnion_basicOpen_isFinitePresentationFreeAway_inter_subset_of_shortExact
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module S M₁] [AddCommGroup M₂] [Module S M₂]
    [AddCommGroup M₃] [Module S M₃] (i : M₁ →ₗ[S] M₂) (q : M₂ →ₗ[S] M₃)
    (hi : Function.Injective i) (hq : Function.Surjective q) (hiq : Function.Exact i q) :
    (⋃ f ∈ {f : R | IsFinitePresentationFreeAway R S M₁ f},
          (basicOpen f : Set (PrimeSpectrum R))) ∩
        (⋃ f ∈ {f : R | IsFinitePresentationFreeAway R S M₃ f},
          (basicOpen f : Set (PrimeSpectrum R))) ⊆
      ⋃ f ∈ {f : R | IsFinitePresentationFreeAway R S M₂ f},
        (basicOpen f : Set (PrimeSpectrum R)) := by
  rintro p ⟨hp₁, hp₃⟩
  obtain ⟨f₁, hf₁, hpf₁⟩ := Set.mem_iUnion₂.mp hp₁
  obtain ⟨f₃, hf₃, hpf₃⟩ := Set.mem_iUnion₂.mp hp₃
  refine Set.mem_iUnion₂.mpr ⟨f₁ * f₃, isFinitePresentationFreeAway_of_shortExact i q hi hq hiq
    (hf₁.of_dvd (dvd_mul_right f₁ f₃)) (hf₃.of_dvd (dvd_mul_left f₃ f₁)), ?_⟩
  rw [basicOpen_mul]
  exact ⟨hpf₁, hpf₃⟩

/-- **Stacks 051X**. Let `R → S` be a ring map, let `M` be an `S`-module and let `f : R`. Call
`g` good for a module when it satisfies the condition `Algebra.IsFinitePresentationFreeAway` of
Equation 051U, and let `U(R → S, M) ⊆ Spec R` be the union of the standard opens `D(g)` over the
good `g` (Equation 051V). Then, under the identification of `Spec(R_f)` with `D(f)` given by
`PrimeSpectrum.comap (algebraMap R R_f)`, one has
`U(R_f → S_f, M_f) = D(f) ∩ U(R → S, M)`. Here `R_f`, `S_f` and `M_f` are arbitrary models of the
localizations at the powers of `f`. -/
@[stacks 051X "The locus `U(R → S, M)` of Equation 051V is written out as the union of the standard
opens `D(g)` over the `g` satisfying 051U, cited as `Algebra.IsFinitePresentationFreeAway`; the
identification `Spec(R_f) = D(f)` is the open embedding `PrimeSpectrum.comap (algebraMap R R_f)`,
along which the left-hand side is pushed forward. See the module docstring."]
public theorem image_comap_iUnion_basicOpen_isFinitePresentationFreeAway
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module S M] (f : R)
    (Rf : Type*) [CommRing Rf] [Algebra R Rf] [IsLocalization.Away f Rf]
    (Sf : Type*) [CommRing Sf] [Algebra R Sf] [Algebra S Sf] [Algebra Rf Sf]
      [IsScalarTower R S Sf] [IsScalarTower R Rf Sf]
      [IsLocalization.Away (algebraMap R S f) Sf]
    (Mf : Type*) [AddCommGroup Mf] [Module S Mf] [Module Sf Mf] [IsScalarTower S Sf Mf]
    (l : M →ₗ[S] Mf) [IsLocalizedModule.Away (algebraMap R S f) l] :
    comap (algebraMap R Rf) ''
        (⋃ g ∈ {g : Rf | Algebra.IsFinitePresentationFreeAway Rf Sf Mf g},
          (basicOpen g : Set (PrimeSpectrum Rf))) =
      (basicOpen f : Set (PrimeSpectrum R)) ∩
        ⋃ g ∈ {g : R | Algebra.IsFinitePresentationFreeAway R S M g},
          (basicOpen g : Set (PrimeSpectrum R)) := by
  rw [Set.image_iUnion₂, Set.inter_iUnion₂]
  refine subset_antisymm (Set.iUnion₂_subset fun g hg => ?_) (Set.iUnion₂_subset fun a ha => ?_)
  · obtain ⟨b, hb, hgb⟩ :=
      exists_isFinitePresentationFreeAway_image_comap_basicOpen f Rf Sf Mf l hg
    rw [hgb]
    exact Set.subset_biUnion_of_mem (u := fun c : R =>
      (basicOpen f : Set (PrimeSpectrum R)) ∩ (basicOpen c : Set (PrimeSpectrum R))) hb
  · rw [← image_comap_basicOpen_algebraMap f a Rf]
    exact Set.subset_biUnion_of_mem (u := fun c : Rf =>
      comap (algebraMap R Rf) '' (basicOpen c : Set (PrimeSpectrum Rf)))
      ((isFinitePresentationFreeAway_algebraMap_iff f a Rf Sf Mf l).mpr
        (ha.of_dvd (dvd_mul_left a f)))

end Algebra

/-! #### Density -/

/-- The `f`-step of Stacks 051Y, and the whole of its mathematical content: if the locus
`U(R_f → S_f, M_f)` of Equation 051V for the pair localized at `f` is dense in `Spec(R_f)`, then
`D(f)` lies in the closure of `U(R → S, M)`. Indeed `D(f)` is the range of
`comap (algebraMap R R_f)`, which is continuous, so it lies in the closure of the image of the
dense locus upstairs, and that image is `D(f) ∩ U(R → S, M)` by Stacks 051X. The models of the
localizations are arbitrary, as in Stacks 051X. -/
private theorem basicOpen_subset_closure_iUnion_basicOpen_isFinitePresentationFreeAway
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module S M] (f : R)
    (Rf : Type*) [CommRing Rf] [Algebra R Rf] [IsLocalization.Away f Rf]
    (Sf : Type*) [CommRing Sf] [Algebra R Sf] [Algebra S Sf] [Algebra Rf Sf]
      [IsScalarTower R S Sf] [IsScalarTower R Rf Sf]
      [IsLocalization.Away (algebraMap R S f) Sf]
    (Mf : Type*) [AddCommGroup Mf] [Module S Mf] [Module Sf Mf] [IsScalarTower S Sf Mf]
    (l : M →ₗ[S] Mf) [IsLocalizedModule.Away (algebraMap R S f) l]
    (H : Dense (⋃ g ∈ {g : Rf | Algebra.IsFinitePresentationFreeAway Rf Sf Mf g},
      (basicOpen g : Set (PrimeSpectrum Rf)))) :
    (basicOpen f : Set (PrimeSpectrum R)) ⊆
      closure (⋃ g ∈ {g : R | Algebra.IsFinitePresentationFreeAway R S M g},
        (basicOpen g : Set (PrimeSpectrum R))) :=
  calc (basicOpen f : Set (PrimeSpectrum R))
      = Set.range (comap (algebraMap R Rf)) := (localization_away_comap_range Rf f).symm
    _ ⊆ closure (⋃ g ∈ {g : R | Algebra.IsFinitePresentationFreeAway R S M g},
          (basicOpen g : Set (PrimeSpectrum R))) :=
        ((continuous_comap _).range_subset_closure_image_dense H).trans <| closure_mono <|
          (Algebra.image_comap_iUnion_basicOpen_isFinitePresentationFreeAway
            (R := R) (S := S) (M := M) f Rf Sf Mf l).subset.trans Set.inter_subset_right

namespace Algebra

/-- **Stacks 051Y**. Let `R → S` be a ring map and let `M` be an `S`-module. Call `f ∈ R` good when
`S_f` is of finite presentation over `R_f`, `M_f` is of finite presentation over `S_f` and `S_f`,
`M_f` are free over `R_f` (Equation 051U), and let `U(R → S, M) ⊆ Spec R` be the union of the
standard opens `D(f)` over the good `f` (Equation 051V). If the opens `D(f)`, `f ∈ s`, have dense
union in `Spec R` — that is, they cover a dense open — and if for each `f ∈ s` the locus
`U(R_f → S_f, M_f)` is dense in `Spec(R_f) = D(f)`, then `U(R → S, M)` is dense in `Spec R`. -/
@[stacks 051Y "The dense open `U` of the source is the union of the `D(f)`, `f ∈ s`, so it is not
a separate variable; the locus of Equation 051V is written out as the union of the `D(f)` over the
`f` satisfying 051U, and density in `D(f)` is stated in
`Spec(R_f)`. See the module docstring."]
public theorem dense_iUnion_basicOpen_isFinitePresentationFreeAway_of_localizationAway
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module S M]
    (s : Set R) (hs : Dense (⋃ f ∈ s, (basicOpen f : Set (PrimeSpectrum R))))
    (H : ∀ f ∈ s, Dense (⋃ g ∈ {g : Localization.Away f |
          IsFinitePresentationFreeAway (Localization.Away f)
            (Localization (algebraMapSubmonoid S (.powers f)))
            (Localization (algebraMapSubmonoid S (.powers f)) ⊗[S] M) g},
        (basicOpen g : Set (PrimeSpectrum (Localization.Away f))))) :
    Dense (⋃ f ∈ {f : R | IsFinitePresentationFreeAway R S M f},
      (basicOpen f : Set (PrimeSpectrum R))) := by
  refine Dense.of_closure (hs.mono (Set.iUnion₂_subset fun f hf => ?_))
  -- The two instances of 051X's hypothesis block that the canonical models of 051U do not supply
  -- by unification: both are `Algebra.algebraMapSubmonoid_powers` transported.
  have : IsLocalization.Away (algebraMap R S f)
      (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers f))) := by
    rw [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers]; infer_instance
  have : IsLocalizedModule.Away (algebraMap R S f) (TensorProduct.mk S
      (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers f))) M 1) := by
    rw [IsLocalizedModule.Away, ← Algebra.algebraMapSubmonoid_powers]; infer_instance
  exact basicOpen_subset_closure_iUnion_basicOpen_isFinitePresentationFreeAway f
    (Localization.Away f) (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers f)))
    (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers f)) ⊗[S] M)
    (TensorProduct.mk S _ M 1) (H f hf)

end Algebra

end

end
