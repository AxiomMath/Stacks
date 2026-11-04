module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksFrontier.RingTheory.GeometricallyIntegral.FibrewiseDense
public import StacksFrontier.RingTheory.Ideal.RelativeAssassin.Defs
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.Divisors.RelativeAssassinTwo.AffineOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.ConstructibleAssociatedPoints05KRb
public import StacksFrontier.AlgebraicGeometry.Morphisms.ConstructibleAssociatedPointsLocus
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.FiberMaximalSpectrum
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteTypePullbackScheme
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeAssassin.FiberBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Reduction

/-!
# Fibrewise containment of associated points in an open subscheme

**Stacks 05KP.** Let `f : X ⟶ Y` be a finite type morphism of schemes, `F` a finite type
quasi-coherent module on `X` and `U ⊆ X` open. If `Y` is irreducible with generic point `η` and
the associated points of `F` restricted to the fibre `X_η` all lie in `U`, then the same holds in
every fibre over a nonempty open of `Y`.

## Main results

* `Stacks.Divisors.exists_open_associatedPoints_fiber_subset`

## The argument

*The affine situation.* Over an affine open `V = Spec A` of the target with `A` a domain and an
affine open `W = Spec B` of the source above it, the containment is a statement about the
relative assassin of the `B`-module `N = Γ(F, W)` (Stacks 0CU5). Covering the part of `U ∩ W`
over the generic point by finitely many basic opens `D(g j)`, the containment over `η` says that
multiplication by the tuple `g` is injective on the generic fibre module, and generic flatness
spreads that injectivity out to a basic open `D(a) ⊆ V`.

*Globalisation.* The source is covered by finitely many affine opens above one affine open `V`
of the target; the finite intersection of the resulting basic opens contains `η`, because the
prime of `A` cut out by `η` is the zero ideal, so a nonzero section does not vanish at `η`.

*Removing reducedness.* The affine argument needs `Γ(Y, V)` to be a domain, so the target is
first replaced by its reduction, which is a universal homeomorphism onto `Y` (Stacks 054M) and
hence again irreducible, so integral. Containment of fibrewise associated points in an open is
invariant under base change of the target (Stacks 05KQ), and the open produced over the
reduction is carried back along the homeomorphism.

## References

* [Stacks Project, Tag 05KP](https://stacks.math.columbia.edu/tag/05KP)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct

universe u

namespace Stacks.Divisors

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section Algebraic

variable {A B N : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]

/-- Multiplication by a finite family of ring elements, as a single linear map to the product. -/
noncomputable def smulTuple {m : ℕ} (g : Fin m → B) : N →ₗ[B] (Fin m → N) :=
  LinearMap.pi fun j => LinearMap.lsmul B N (g j)

variable {K : Type u} [CommRing K] [Algebra A K]

/-- Each component of the right-hand tensor decomposition of a product is the tensor of the
corresponding projection. -/
theorem piRight_apply_eq_lTensor_proj {m : ℕ} (w : K ⊗[A] (Fin m → N)) (j : Fin m) :
    TensorProduct.piRight A A K (fun _ : Fin m => N) w j
      = LinearMap.lTensor K (LinearMap.proj j : (Fin m → N) →ₗ[A] N) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul c v => simp
  | add x y hx hy =>
      simp only [map_add, Pi.add_apply, hx, hy]

/-- Scalar multiplication on the second factor of a base change is the base change of scalar
multiplication. -/
theorem comm_lTensor_lsmul (b : B) (z : K ⊗[A] N) :
    (TensorProduct.comm A K N)
        (LinearMap.lTensor K ((LinearMap.lsmul B N b).restrictScalars A) z)
      = b • (TensorProduct.comm A K N) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c n => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp [hx, hy]

/-- **Base change of multiplication by a tuple.** The base change along `A → K` of
`n ↦ (g j • n)` is injective exactly when every element of `N ⊗_A K` killed by all the `g j`
vanishes. -/
theorem injective_lTensor_smulTuple_iff {m : ℕ} (g : Fin m → B) :
    Function.Injective
        (LinearMap.lTensor K ((smulTuple (N := N) g).restrictScalars A)) ↔
      ∀ ξ : N ⊗[A] K, (∀ j, g j • ξ = 0) → ξ = 0 := by
  have hproj : ∀ j : Fin m, (LinearMap.proj j : (Fin m → N) →ₗ[A] N) ∘ₗ
      ((smulTuple (N := N) g).restrictScalars A)
      = (LinearMap.lsmul B N (g j)).restrictScalars A := by
    intro j
    ext n
    rfl
  constructor
  · intro hinj ξ hξ
    have h0 : LinearMap.lTensor K ((smulTuple (N := N) g).restrictScalars A)
        ((TensorProduct.comm A N K) ξ) = 0 := by
      refine (TensorProduct.piRight A A K (fun _ : Fin m => N)).injective ?_
      funext j
      rw [piRight_apply_eq_lTensor_proj, map_zero]
      simp only [Pi.zero_apply]
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hproj j]
      refine (TensorProduct.comm A K N).injective ?_
      rw [comm_lTensor_lsmul, map_zero]
      simpa using hξ j
    have h1 := hinj (a₁ := (TensorProduct.comm A N K) ξ) (a₂ := 0) (by rw [h0, map_zero])
    exact (TensorProduct.comm A N K).injective (by rw [h1, map_zero])
  · intro h
    rw [injective_iff_map_eq_zero]
    intro z hz
    have hξ : ∀ j, g j • (TensorProduct.comm A K N) z = 0 := by
      intro j
      rw [← comm_lTensor_lsmul]
      have hj : LinearMap.lTensor K ((LinearMap.lsmul B N (g j)).restrictScalars A) z = 0 := by
        rw [← hproj j, LinearMap.lTensor_comp, LinearMap.comp_apply, hz, map_zero]
      rw [hj, map_zero]
    exact (TensorProduct.comm A K N).injective (by rw [h _ hξ, map_zero])

/-- A prime ideal cannot be the annihilator of an element of a module on which a family of
elements of that prime acts with trivial common kernel. -/
private theorem false_of_forall_mem_colon_eq {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] {ι : Type*} (g : ι → R) (hinj : ∀ ξ : M, (∀ j, g j • ξ = 0) → ξ = 0)
    {P : Ideal R} (hP : P.IsPrime) {w : M} (hw : (⊥ : Submodule R M).colon {w} = P)
    (hg : ∀ j, g j ∈ P) : False := by
  have hw0 : w = 0 := hinj w fun j =>
    Submodule.mem_bot R |>.mp (Submodule.mem_colon_singleton.mp (hw ▸ hg j))
  rw [hw0, Submodule.colon_singleton_zero] at hw
  exact hP.ne_top hw.symm

/-- **Multiplication by a tuple detects associated primes.** For a family `g` in a Noetherian
ring `R` and an `R`-module `M`, every element killed by all the `g j` vanishes exactly when
every associated prime of `M` omits one of the `g j`. -/
theorem forall_smul_eq_zero_imp_eq_zero_iff {R : Type*} [CommRing R] [IsNoetherianRing R]
    {M : Type*} [AddCommGroup M] [Module R M] {ι : Type*} (g : ι → R) :
    (∀ ξ : M, (∀ j, g j • ξ = 0) → ξ = 0) ↔
      ∀ p : Ideal R, IsAssociatedPrimeStacks R M p → ∃ j, g j ∉ p := by
  constructor
  · rintro hinj p ⟨hp, w, hw⟩
    by_contra! hcon
    exact false_of_forall_mem_colon_eq g hinj hp (Submodule.colon_span.symm.trans hw) hcon
  · intro hall ξ hξ
    by_contra hne
    have hnt : Nontrivial (Submodule.span R {ξ}) :=
      ⟨⟨⟨ξ, Submodule.mem_span_singleton_self ξ⟩, 0, by simpa using hne⟩⟩
    obtain ⟨p, hp⟩ := associatedPrimes.nonempty R (Submodule.span R {ξ})
    have hpM : p ∈ associatedPrimes R M :=
      associatedPrimes.subset_of_injective
        (f := (Submodule.span R {ξ}).subtype) Subtype.val_injective hp
    obtain ⟨j, hj⟩ := hall p ((isAssociatedPrimeStacks_iff_mem_associatedPrimes p).mpr hpM)
    obtain ⟨-, w, hwspan⟩ :=
      (isAssociatedPrimeStacks_iff_mem_associatedPrimes (M := Submodule.span R {ξ}) p).mpr hp
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp w.2
    refine hj ?_
    rw [← hwspan]
    refine Submodule.mem_colon_span_singleton.mpr (Submodule.mem_bot R |>.mpr ?_)
    refine Subtype.ext ?_
    simpa using (show g j • (w : M) = 0 by rw [← hr, smul_comm, hξ j, smul_zero])

/-- The fibre module over the contraction of a prime, computed on the fibre ring. -/
noncomputable def fiberBaseChangeEquiv (K : Type u) [CommRing K] [Algebra A K] :
    (B ⊗[A] K) ⊗[B] N ≃ₗ[B] N ⊗[A] K :=
  (TensorProduct.comm B _ N).trans (AlgebraTensorModule.cancelBaseChange A B B N K)

/-- Changing the right-hand factor of a base change commutes with the scalar action coming
from the left-hand factor. -/
theorem congrRight_smul {K' : Type u} [CommRing K'] [Algebra A K'] (ψ : K ≃ₗ[A] K') (b : B)
    (ξ : N ⊗[A] K) :
    TensorProduct.congr (LinearEquiv.refl A N) ψ (b • ξ)
      = b • TensorProduct.congr (LinearEquiv.refl A N) ψ ξ := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul n c => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp [hx, hy]

/-- A prime of the source lies in the relative assassin once its contraction is identified and
an element with that exact annihilator is exhibited on the corresponding fibre module. -/
theorem mem_relativeAssassin_of_comap_eq {q : PrimeSpectrum B} {p : PrimeSpectrum A}
    (hp : PrimeSpectrum.comap (algebraMap A B) q = p)
    (m : N ⊗[A] p.asIdeal.ResidueField)
    (hm : (⊥ : Submodule B (N ⊗[A] p.asIdeal.ResidueField)).colon {m} = q.asIdeal) :
    q ∈ Module.relativeAssassin A B N := by
  subst hp
  exact ⟨m, hm⟩

variable [IsDomain A] [Algebra.FiniteType A B]

/-- **The generic fibre controls the tuple.** If every prime in the relative assassin of `N`
lying over the generic point of the domain `A` omits one of the `g j`, then every element of
the generic fibre module killed by all the `g j` vanishes. -/
theorem forall_smul_eq_zero_of_generic_relativeAssassin {m : ℕ} (g : Fin m → B)
    (hgen : ∀ q ∈ Module.relativeAssassin A B N,
      PrimeSpectrum.comap (algebraMap A B) q = ⟨⊥, Ideal.isPrime_bot⟩ → ∃ j, g j ∉ q.asIdeal) :
    ∀ ξ : N ⊗[A] (⊥ : Ideal A).ResidueField, (∀ j, g j • ξ = 0) → ξ = 0 := by
  classical
  have hNoeth : IsNoetherianRing (B ⊗[A] (⊥ : Ideal A).ResidueField) :=
    have : IsNoetherianRing ((⊥ : Ideal A).ResidueField ⊗[A] B) :=
      Algebra.FiniteType.isNoetherianRing (⊥ : Ideal A).ResidueField _
    isNoetherianRing_of_ringEquiv _
      (Algebra.TensorProduct.comm A (⊥ : Ideal A).ResidueField B).toRingEquiv
  have key : ∀ z : (B ⊗[A] (⊥ : Ideal A).ResidueField) ⊗[B] N,
      (∀ j, algebraMap B (B ⊗[A] (⊥ : Ideal A).ResidueField) (g j) • z = 0) → z = 0 := by
    refine (forall_smul_eq_zero_imp_eq_zero_iff _).mpr ?_
    rintro P ⟨hP, z, hz⟩
    by_contra! hcon
    set C := B ⊗[A] (⊥ : Ideal A).ResidueField
    set q : PrimeSpectrum B := ⟨P.comap (algebraMap B C), Ideal.comap_isPrime _ _⟩
    have hmem : ∀ b : B, b ∈ q.asIdeal ↔ algebraMap B C b ∈ P := fun b => Iff.rfl
    have hbot : PrimeSpectrum.comap (algebraMap A B) q = ⟨⊥, Ideal.isPrime_bot⟩ := by
      refine PrimeSpectrum.ext (Ideal.ext fun a => ?_)
      simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, Submodule.mem_bot]
      refine ⟨fun ha => ?_, fun ha => by simp [ha]⟩
      by_contra ha0
      have hres : algebraMap A (⊥ : Ideal A).ResidueField a ≠ 0 := fun h0 =>
        ha0 (Ideal.mem_bot.mp (Ideal.algebraMap_residueField_eq_zero.mp h0))
      have hu : IsUnit (algebraMap A C a) := by
        rw [IsScalarTower.algebraMap_apply A (⊥ : Ideal A).ResidueField C]
        exact (isUnit_iff_ne_zero.mpr hres).map _
      refine hP.ne_top (Ideal.eq_top_of_isUnit_mem _ ?_ hu)
      rw [IsScalarTower.algebraMap_apply A B C]
      exact (hmem _).mp ha
    have hqass : q ∈ Module.relativeAssassin A B N := by
      refine mem_relativeAssassin_of_comap_eq hbot
        (fiberBaseChangeEquiv (A := A) (B := B) (N := N) _ z) (Ideal.ext fun b => ?_)
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot, hmem b, ← hz,
        Submodule.mem_colon_span_singleton, Submodule.mem_bot,
        ← (fiberBaseChangeEquiv (A := A) (B := B) (N := N)
          (⊥ : Ideal A).ResidueField).map_smul, algebraMap_smul C b z]
      exact map_eq_zero_iff _ (fiberBaseChangeEquiv (A := A) (B := B) (N := N)
        (⊥ : Ideal A).ResidueField).injective
    obtain ⟨j, hj⟩ := hgen q hqass hbot
    exact hj ((hmem (g j)).mpr (hcon j))
  intro ξ hξ
  have hz : ∀ j, algebraMap B (B ⊗[A] (⊥ : Ideal A).ResidueField) (g j) •
      (fiberBaseChangeEquiv (A := A) (B := B) (N := N) _).symm ξ = 0 := by
    intro j
    rw [algebraMap_smul, ← (fiberBaseChangeEquiv (A := A) (B := B) (N := N)
      (⊥ : Ideal A).ResidueField).symm.map_smul, hξ j, map_zero]
  simpa using congrArg (fiberBaseChangeEquiv (A := A) (B := B) (N := N)
    (⊥ : Ideal A).ResidueField) (key _ hz)

/-- **The affine core of Stacks 05KP.** Let `A` be a domain, `B` a finite type `A`-algebra and
`N` a finite `B`-module, and let `g` be a finite family in `B`. If every prime in the relative
assassin of `N` over the generic point of `A` omits one of the `g j`, then there is a nonzero
`h : A` such that the same holds for every prime of the relative assassin lying over a point of
the basic open of `h`.

Generic injectivity of `n ↦ (g j • n)` spreads out from the generic fibre by generic flatness
of the module and of the cokernel of that map. -/
theorem exists_ne_zero_forall_relativeAssassin_exists_notMem [Module.Finite B N] {m : ℕ}
    (g : Fin m → B)
    (hgen : ∀ q ∈ Module.relativeAssassin A B N,
      PrimeSpectrum.comap (algebraMap A B) q = ⟨⊥, Ideal.isPrime_bot⟩ → ∃ j, g j ∉ q.asIdeal) :
    ∃ h : A, h ≠ 0 ∧ ∀ q ∈ Module.relativeAssassin A B N,
      h ∉ (PrimeSpectrum.comap (algebraMap A B) q).asIdeal → ∃ j, g j ∉ q.asIdeal := by
  classical
  have hgenK := forall_smul_eq_zero_of_generic_relativeAssassin g hgen
  have hfield : (⊥ : Ideal A).ResidueField ≃ₐ[A] FractionRing A :=
    IsLocalization.algEquiv (nonZeroDivisors A) _ _
  have hinjK : Function.Injective (LinearMap.lTensor (FractionRing A)
      ((smulTuple (N := N) g).restrictScalars A)) := by
    refine (injective_lTensor_smulTuple_iff g).mpr fun ξ hξ => ?_
    set e := TensorProduct.congr (LinearEquiv.refl A N) hfield.symm.toLinearEquiv with he
    have hz : ∀ j, g j • e ξ = 0 := fun j => by
      rw [he, ← congrRight_smul, hξ j, map_zero]
    exact e.injective (by rw [hgenK (e ξ) hz, map_zero])
  obtain ⟨h, hh0, hall⟩ :=
    Algebra.exists_ne_zero_forall_injective_lTensor_of_forall_exists_smul_eq_zero
      (smulTuple (N := N) g)
      (fun x hx => Algebra.exists_ne_zero_smul_eq_zero_of_mem_ker _ hinjK x hx)
  refine ⟨h, hh0, fun q hq hhq => ?_⟩
  by_contra! hcon
  set p := PrimeSpectrum.comap (algebraMap A B) q
  have hres : algebraMap A p.asIdeal.ResidueField h ≠ 0 := fun h0 =>
    hhq (Ideal.algebraMap_residueField_eq_zero.mp h0)
  have hinj := hall p.asIdeal.ResidueField (isUnit_iff_ne_zero.mpr hres)
  obtain ⟨ξ, hξ⟩ := hq
  exact false_of_forall_mem_colon_eq g ((injective_lTensor_smulTuple_iff g).mp hinj) q.2 hξ hcon

end Algebraic

section Geometric

/-- **Fibrewise containment read through the relative assassin.** All associated points of the
restriction of `F` to the fibre over `y` lie in `U` exactly when every point of the relative
assassin of `F` lying over `y` lies in `U`. -/
theorem associatedPoints_fiber_subset_iff_forall_relativeAssassin {X Y : Scheme.{u}}
    (f : X ⟶ Y) (F : X.Modules) (U : X.Opens) (y : Y) :
    associatedPoints ((Scheme.Modules.pullback (f.fiberι y)).obj F) ⊆
        (f.fiberι y) ⁻¹' (U : Set X) ↔
      ∀ x ∈ relativeAssassin f F, f x = y → x ∈ U := by
  constructor
  · intro hsub x hx hxy
    obtain ⟨z, hz⟩ : x ∈ Set.range (f.fiberι y) := by rwa [f.range_fiberι]
    simpa [hz] using
      hsub ((mem_associatedPoints_fiber_iff_mem_relativeAssassin f F y z).mpr (hz ▸ hx))
  · intro h z hz
    exact h _ ((mem_associatedPoints_fiber_iff_mem_relativeAssassin f F y z).mp hz)
      (f.apply_fiberι y z)

/-- **The affine chart of Stacks 05KP.** Work over an affine open `V` of the target containing a
point `η` whose prime is the zero ideal of the domain `Γ(Y, V)`, and over an affine open `W` of
the source lying above `V`. If the points of the relative assassin over `η` which lie in `W` are
covered by basic opens contained in `U`, then there is a nonzero section `a` on `V` such that the
same containment holds in `W` over every point of the basic open of `a`.

Stacks 0CU5 turns the two fibrewise conditions into conditions on the relative assassin of the
module of sections, where the spreading out is the affine core. -/
theorem exists_ne_zero_forall_mem_of_chart {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    [F.IsQuasicoherent] {V : Y.Opens} (hV : IsAffineOpen V) {W : X.Opens} (hW : IsAffineOpen W)
    (hWV : W ≤ f ⁻¹ᵁ V) (U : X.Opens) {η : Y} (hηV : η ∈ V)
    (hfib : ∀ s : Y, IsLocallyNoetherian (f.fiber s)) (hdom : IsDomain Γ(Y, V))
    (hbot : (hV.primeIdealOf ⟨η, hηV⟩).asIdeal = ⊥)
    (hFT : (f.appLE V W hWV).hom.FiniteType)
    (hfin : Module.Finite Γ(X, W) Γ(F, W))
    (hgen : ∀ x ∈ relativeAssassin f F, f x = η → x ∈ U)
    {m : ℕ} (g : Fin m → Γ(X, W)) (hgU : ∀ j, X.basicOpen (g j) ≤ U)
    (hgcov : ∀ x ∈ W, x ∈ U → f x = η → ∃ j, x ∈ X.basicOpen (g j)) :
    ∃ a : Γ(Y, V), a ≠ 0 ∧ ∀ y ∈ Y.basicOpen a,
      ∀ x ∈ relativeAssassin f F, f x = y → x ∈ W → x ∈ U := by
  let : Algebra Γ(Y, V) Γ(X, W) := (f.appLE V W hWV).hom.toAlgebra
  let : Module Γ(Y, V) Γ(F, W) := Module.compHom Γ(F, W) (f.appLE V W hWV).hom
  let : IsScalarTower Γ(Y, V) Γ(X, W) Γ(F, W) :=
    IsScalarTower.of_compHom Γ(Y, V) Γ(X, W) Γ(F, W)
  have : Algebra.FiniteType Γ(Y, V) Γ(X, W) := hFT
  have := hdom
  have := hfin
  have hηprime : hV.primeIdealOf ⟨η, hηV⟩ = ⟨⊥, Ideal.isPrime_bot⟩ := PrimeSpectrum.ext hbot
  have hassgen : ∀ q ∈ Module.relativeAssassin Γ(Y, V) Γ(X, W) Γ(F, W),
      PrimeSpectrum.comap (algebraMap Γ(Y, V) Γ(X, W)) q = ⟨⊥, Ideal.isPrime_bot⟩ →
      ∃ j, g j ∉ q.asIdeal := by
    intro q hq hq0
    obtain ⟨⟨x, hx⟩, rfl⟩ := hW.primeIdealOf_surjective q
    have hxass : x ∈ relativeAssassin f F :=
      mem_relativeAssassin_of_mem_relativeAssassin_sections f F W V hW hV hWV hx hq
    have hfx : f x = η := by
      have h1 : hV.primeIdealOf ⟨f x, hWV hx⟩ = hV.primeIdealOf ⟨η, hηV⟩ := by
        rw [hηprime, ← IsAffineOpen.comap_primeIdealOf_appLE V hV W hW hWV hx]
        exact hq0
      exact congrArg Subtype.val (hV.primeIdealOf_injective h1)
    obtain ⟨j, hj⟩ := hgcov x hx (hgen x hxass hfx) hfx
    exact ⟨j, (mem_basicOpen_iff_notMem_primeIdealOf hW (g j) ⟨x, hx⟩).mp hj⟩
  obtain ⟨a, ha0, hall⟩ := exists_ne_zero_forall_relativeAssassin_exists_notMem g hassgen
  refine ⟨a, ha0, fun y hy x hx hxy hxW => ?_⟩
  have hq := (mem_relativeAssassin_sections_iff_of_locallyNoetherian_fibers
    f F W V hW hV hWV hfib hxW).mpr hx
  have hay : a ∉ (PrimeSpectrum.comap (algebraMap Γ(Y, V) Γ(X, W))
      (hW.primeIdealOf ⟨x, hxW⟩)).asIdeal := by
    rw [show PrimeSpectrum.comap (algebraMap Γ(Y, V) Γ(X, W)) (hW.primeIdealOf ⟨x, hxW⟩) =
      hV.primeIdealOf ⟨f x, hWV hxW⟩ from
        IsAffineOpen.comap_primeIdealOf_appLE V hV W hW hWV hxW]
    exact (mem_basicOpen_iff_notMem_primeIdealOf hV a ⟨f x, hWV hxW⟩).mp (hxy ▸ hy)
  obtain ⟨j, hj⟩ := hall _ hq hay
  exact hgU j ((mem_basicOpen_iff_notMem_primeIdealOf hW (g j) ⟨x, hxW⟩).mpr hj)

/-- On an affine open of an integral scheme, the generic point cuts out the zero ideal. -/
theorem primeIdealOf_eq_bot_of_isGenericPoint {Y : Scheme.{u}} [IsIntegral Y] {V : Y.Opens}
    (hV : IsAffineOpen V) {η : Y} (hη : IsGenericPoint η Set.univ) (hηV : η ∈ V) :
    (hV.primeIdealOf ⟨η, hηV⟩).asIdeal = ⊥ := by
  have hneV : Nonempty V := ⟨⟨η, hηV⟩⟩
  have hdom : IsDomain Γ(Y, V) := IsIntegral.component_integral V
  have hηg : η = genericPoint Y := hη.eq (genericPoint_spec Y)
  have h2 : IsGenericPoint (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Γ(Y, V)) Set.univ := by
    have hcl : closure {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Γ(Y, V))} = Set.univ := by
      rw [PrimeSpectrum.closure_singleton]
      simp
    exact hcl
  have h1 : hV.primeIdealOf ⟨η, hηV⟩ = genericPoint (Spec Γ(Y, V)) := by
    subst hηg
    exact hV.primeIdealOf_genericPoint
  rw [h1, congrArg PrimeSpectrum.asIdeal ((genericPoint_spec (Spec Γ(Y, V))).eq h2)]

/-- Over an affine open `V` of the target whose prime at `η` is zero, every affine open `W` of
the source above `V` admits a nonzero section `a` on `V` such that, over the basic open of `a`,
the points of the relative assassin of `F` in `W` lie in `U`, provided those over `η` do. -/
theorem exists_ne_zero_forall_mem_of_affine_le {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    [LocallyOfFiniteType f] [QuasiCompact f] [F.IsQuasicoherent] [F.IsFiniteType]
    (U : X.Opens) {V : Y.Opens} (hV : IsAffineOpen V) {η : Y} (hηV : η ∈ V)
    (hdom : IsDomain Γ(Y, V)) (hbot : (hV.primeIdealOf ⟨η, hηV⟩).asIdeal = ⊥)
    (hgen : ∀ x ∈ relativeAssassin f F, f x = η → x ∈ U) {W : X.Opens} (hW : IsAffineOpen W)
    (hWV : W ≤ f ⁻¹ᵁ V) :
    ∃ a : Γ(Y, V), a ≠ 0 ∧ ∀ y ∈ Y.basicOpen a,
      ∀ x ∈ relativeAssassin f F, f x = y → x ∈ W → x ∈ U := by
  have hfib : ∀ s : Y, IsLocallyNoetherian (f.fiber s) := fun s =>
    isLocallyNoetherian_fiber_of_locallyOfFiniteType f s
  have hnoeth : IsLocallyNoetherian (f.fiber η) := hfib η
  have : IsNoetherian (f.fiber η) := ⟨⟩
  set S : Set X := f.fiberι η '' ((f.fiberι η) ⁻¹' ((U : Set X) ∩ (W : Set X)))
  have hS : IsCompact S :=
    (TopologicalSpace.NoetherianSpace.isCompact _).image (f.fiberι η).continuous
  have hcov : S ⊆ ⋃ r : {r : Γ(X, W) // X.basicOpen r ≤ U}, (X.basicOpen r.1 : Set X) := by
    rintro x ⟨z, hz, rfl⟩
    obtain ⟨r, hrU, hxr⟩ := hW.exists_basicOpen_le (V := U) ⟨_, hz.1⟩ hz.2
    exact Set.mem_iUnion.mpr ⟨⟨r, hrU⟩, hxr⟩
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun r : {r : Γ(X, W) // X.basicOpen r ≤ U} => (X.basicOpen r.1 : Set X))
    (fun r => (X.basicOpen r.1).isOpen) hcov
  refine exists_ne_zero_forall_mem_of_chart f F hV hW hWV U hηV hfib hdom hbot
    (f.finiteType_appLE hV hW hWV) (moduleFinite_sections_on_affine F W hW) hgen
    (fun j : Fin t.card => ((t.equivFin.symm j : {r : Γ(X, W) // X.basicOpen r ≤ U})).1)
    (fun j => (t.equivFin.symm j : {r : Γ(X, W) // X.basicOpen r ≤ U}).2) ?_
  intro x hxW hxU hxη
  obtain ⟨z, hz⟩ : x ∈ Set.range (f.fiberι η) := by rwa [f.range_fiberι]
  have hxS : x ∈ S := ⟨z, by rw [Set.mem_preimage, hz]; exact ⟨hxU, hxW⟩, hz⟩
  obtain ⟨r, hr, hxr⟩ := Set.mem_iUnion₂.mp (ht hxS)
  exact ⟨t.equivFin ⟨r, hr⟩, by simpa using hxr⟩

/-- **Stacks 05KP for an integral target, read through the relative assassin.** If every point
of the relative assassin of `F` over the generic point of an integral target lies in `U`, then
there is an open neighbourhood of the generic point over which the same holds.

The source is covered by finitely many affine charts over one affine open of the target, each
chart contributes a nonzero section by the affine core, and the generic point lies in all the
corresponding basic opens because its prime is the zero ideal. -/
theorem exists_mem_open_forall_relativeAssassin_of_isIntegral {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) [LocallyOfFiniteType f] [QuasiCompact f] [F.IsQuasicoherent]
    [F.IsFiniteType] [IsIntegral Y] (U : X.Opens) {η : Y} (hη : IsGenericPoint η Set.univ)
    (hgen : ∀ x ∈ relativeAssassin f F, f x = η → x ∈ U) :
    ∃ V : Y.Opens, η ∈ V ∧ ∀ y ∈ V, ∀ x ∈ relativeAssassin f F, f x = y → x ∈ U := by
  classical
  obtain ⟨V₀, hV₀, hηV₀⟩ : ∃ V₀ : Y.Opens, IsAffineOpen V₀ ∧ η ∈ V₀ := by
    obtain ⟨-, ⟨V, hV, rfl⟩, hηV, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ η) isOpen_univ
    exact ⟨V, hV, hηV⟩
  have hneV : Nonempty V₀ := ⟨⟨η, hηV₀⟩⟩
  have hdom : IsDomain Γ(Y, V₀) := IsIntegral.component_integral V₀
  have hbot := primeIdealOf_eq_bot_of_isGenericPoint hV₀ hη hηV₀
  have hnz : ∀ b : Γ(Y, V₀), b ≠ 0 → η ∈ Y.basicOpen b := fun b hb0 =>
    (mem_basicOpen_iff_notMem_primeIdealOf hV₀ b ⟨η, hηV₀⟩).mpr
      (by rw [hbot]; simpa using hb0)
  have hchart : ∀ W : {W : X.affineOpens // W.1 ≤ f ⁻¹ᵁ V₀},
      ∃ a : Γ(Y, V₀), a ≠ 0 ∧ ∀ y ∈ Y.basicOpen a,
        ∀ x ∈ relativeAssassin f F, f x = y → x ∈ W.1.1 → x ∈ U := fun W =>
    exists_ne_zero_forall_mem_of_affine_le f F U hV₀ hηV₀ hdom hbot hgen W.1.2 W.2
  choose a ha0 hagood using hchart
  have hcompact : IsCompact ((f ⁻¹ᵁ V₀ : X.Opens) : Set X) :=
    f.isCompact_preimage hV₀.isCompact
  have hcov2 : ((f ⁻¹ᵁ V₀ : X.Opens) : Set X) ⊆
      ⋃ W : {W : X.affineOpens // W.1 ≤ f ⁻¹ᵁ V₀}, (W.1.1 : Set X) := by
    intro x hx
    obtain ⟨-, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx (f ⁻¹ᵁ V₀).isOpen
    exact Set.mem_iUnion.mpr ⟨⟨⟨W, hW⟩, hWV⟩, hxW⟩
  obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover
    (fun W : {W : X.affineOpens // W.1 ≤ f ⁻¹ᵁ V₀} => (W.1.1 : Set X))
    (fun W => W.1.1.isOpen) hcov2
  refine ⟨⟨(V₀ : Set Y) ∩ ⋂ W ∈ t, (Y.basicOpen (a W) : Set Y),
      V₀.isOpen.inter (isOpen_biInter_finset fun W _ => (Y.basicOpen (a W)).isOpen)⟩,
    ⟨hηV₀, Set.mem_iInter₂.mpr fun W _ => hnz _ (ha0 W)⟩, ?_⟩
  rintro y ⟨hyV₀, hyinf⟩ x hx hxy
  have hxV : x ∈ (f ⁻¹ᵁ V₀ : X.Opens) := show f x ∈ V₀ from hxy ▸ hyV₀
  obtain ⟨W, hWt, hxW⟩ := Set.mem_iUnion₂.mp (ht hxV)
  exact hagood W y (Set.mem_iInter₂.mp hyinf W hWt) x hx hxy hxW

/-- **Stacks Project, Tag 05KP.** Let `f : X ⟶ Y` be a finite type morphism of schemes, `F` a
finite type quasi-coherent module on `X` and `U ⊆ X` open. If `Y` is irreducible with generic
point `η` and all associated points of `F` restricted to the fibre over `η` lie in `U`, then
there is a nonempty open `V ⊆ Y` such that the same containment holds in the fibre over every
point of `V`.

The target is replaced by its reduction, which is integral because the closed immersion of the
reduction is a homeomorphism, and the containment is transported across that base change by
Stacks 05KQ. -/
@[stacks 05KP]
theorem exists_open_associatedPoints_fiber_subset {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) [LocallyOfFiniteType f] [QuasiCompact f] [F.IsQuasicoherent]
    [F.IsFiniteType] [IrreducibleSpace Y] (U : X.Opens) (η : Y)
    (hη : IsGenericPoint η Set.univ)
    (hηU : associatedPoints ((Scheme.Modules.pullback (f.fiberι η)).obj F) ⊆
      (f.fiberι η) ⁻¹' (U : Set X)) :
    ∃ V : Y.Opens, (V : Set Y).Nonempty ∧ ∀ y ∈ V,
      associatedPoints ((Scheme.Modules.pullback (f.fiberι y)).obj F) ⊆
        (f.fiberι y) ⁻¹' (U : Set X) := by
  classical
  let r : Y.nilradical.subscheme ⟶ Y := Y.nilradical.subschemeι
  have hr : UniversalHomeomorphism r := inferInstance
  have hb : IsHomeomorph r := hr.universally_isHomeomorph _ _ _ IsPullback.of_id_snd
  let eY : Y.nilradical.subscheme ≃ₜ Y := hb.homeomorph r
  obtain ⟨η', hrη'⟩ : ∃ η' : Y.nilradical.subscheme, r η' = η :=
    ⟨eY.symm η, eY.apply_symm_apply η⟩
  subst hrη'
  have hsymm : eY.symm (r η') = η' := eY.symm_apply_apply η'
  have hη' : IsGenericPoint η' Set.univ := by
    show closure ({η'} : Set Y.nilradical.subscheme) = Set.univ
    have h1 : closure ({η'} : Set Y.nilradical.subscheme)
        = eY.symm '' closure ({r η'} : Set Y) := by
      rw [eY.symm.image_closure, Set.image_singleton, hsymm]
    rw [h1, show closure ({r η'} : Set Y) = Set.univ from hη]
    simp
  let a : (Limits.pullback f r : Scheme.{u}) ⟶ X := Limits.pullback.fst f r
  let g : (Limits.pullback f r : Scheme.{u}) ⟶ Y.nilradical.subscheme := Limits.pullback.snd f r
  let F' : (Limits.pullback f r : Scheme.{u}).Modules := (Scheme.Modules.pullback a).obj F
  let U' : (Limits.pullback f r : Scheme.{u}).Opens := a ⁻¹ᵁ U
  have : IsReduced Y.nilradical.subscheme := isReduced_nilradical_subscheme Y
  have : IrreducibleSpace Y.nilradical.subscheme := eY.irreducibleSpace_iff.mpr inferInstance
  have : IsIntegral Y.nilradical.subscheme :=
    isIntegral_of_irreducibleSpace_of_isReduced Y.nilradical.subscheme
  have : LocallyOfFiniteType g := inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd f r))
  have : QuasiCompact g := inferInstanceAs (QuasiCompact (Limits.pullback.snd f r))
  have hU' : ∀ y' : Y.nilradical.subscheme,
      associatedPoints ((Scheme.Modules.pullback (g.fiberι y')).obj F') ⊆
          (g.fiberι y') ⁻¹' (U' : Set (Limits.pullback f r : Scheme.{u})) ↔
        associatedPoints ((Scheme.Modules.pullback (f.fiberι (r y'))).obj F) ⊆
          (f.fiberι (r y')) ⁻¹' (U : Set X) :=
    fun y' => (Stacks.RelativeAssassin.associatedPoints_fiber_subset_preimage_iff_baseChange
      f F U r y').symm
  have hgen : ∀ x ∈ relativeAssassin g F', g x = η' → x ∈ U' :=
    (associatedPoints_fiber_subset_iff_forall_relativeAssassin g F' U' η').mp
      ((hU' η').mpr hηU)
  obtain ⟨V', hη'V', hV'⟩ :=
    exists_mem_open_forall_relativeAssassin_of_isIntegral g F' U' hη' hgen
  refine ⟨⟨r '' (V' : Set Y.nilradical.subscheme), hb.isOpenMap _ V'.isOpen⟩,
    ⟨r η', ⟨η', hη'V', rfl⟩⟩, ?_⟩
  rintro y ⟨y', hy'V', rfl⟩
  exact (hU' y').mp
    ((associatedPoints_fiber_subset_iff_forall_relativeAssassin g F' U' y').mpr
      (hV' y' hy'V'))

end Geometric

end Stacks.Divisors

end
