module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.MaximalIdealInjectivity
public import StacksFrontier.Algebra.Module.FinitePresentation.Transport
public import StacksFrontier.RingTheory.CompleteIntersection.LocalRing
public import StacksFrontier.RingTheory.Flat.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.MaximalIdealResidueFibre

/-!
# Reduction to localized polynomial algebras

Fix a local ring `A`. In the injectivity-modulo-the-maximal-ideal situation of Stacks 0AT0 the
three sought conclusions — universal injectivity of `u : N → M` over `A`, finite presentation of
`N` over `B`, and flatness of `N` over `A` — need only be checked when `B` is a localization at
a prime of a polynomial algebra in finitely many variables over `A` and `N` is finitely
presented over `B`.

This is the first step of the proofs of both Stacks 0AT3 (the henselian case) and Stacks 05U9
(the general proposition), each of which opens by reducing to exactly this special case.

## Main definitions

* `AlgebraicGeometry.PolynomialLocalizationPresentation` records a presentation of `B` as the
  localization at a prime of a polynomial algebra in finitely many variables over `A`.
* `AlgebraicGeometry.SameBaseLocalRing` says that two bundled situations use the same fixed base
  ring, including its `CommRing` structure.
* `AlgebraicGeometry.InjectiveModuloMaximalIdealConclusion` packages the three conclusions.

## Main results

* `AlgebraicGeometry.universallyInjective_of_localizedPolynomial_cases` reduces universal
  injectivity to those special cases.
* `AlgebraicGeometry.finitePresentation_of_localizedPolynomial_cases` reduces finite
  presentation.
* `AlgebraicGeometry.flat_of_localizedPolynomial_cases` reduces flatness.
* `Module.Flat.of_rTensor_injective_of_flat` says that a universally injective map into a flat
  module has flat source, and
  `AlgebraicGeometry.injectiveModuloMaximalIdealConclusion_of_rTensor_injective_cases` combines
  that with the three reduction lemmas: in Situation 0AT0 all three conclusions follow from
  universal injectivity alone in those special cases, the finite-presentation conclusion being a
  hypothesis there and the flatness conclusion a consequence.
* `AlgebraicGeometry.SameBaseLocalRing.isNoetherianRing` transports a Noetherian hypothesis on
  the base ring to a special case.

## Implementation notes

The source calls the conjunction of the three conclusions "the lemma holds"; that conjunction is
used only to state the common hypothesis, and the three conclusions are proved as separate
lemmas. Universal injectivity is the universe-polymorphic `UniversallyInjectivePoly`.

Equality of base rings records equality of the carrier types together with a heterogeneous
equality of the chosen `CommRing` structures; `IsLocalRing` is a proposition, so the local-ring
structure is pinned too.

The rings and modules have independent universes. The special cases range over algebras in
`max u₁ u₂` and source modules in `max u₁ u₂ u₄`, which is where the localized polynomial
algebra over `A` and its finitely presented module constructed in the proof live, after a
`ULift`; their target module can be the original `M`. The tensor-test universe in the hypothesis
contains both the base-ring universe and the conclusion's test universe, so it has room for a
copy of `A`, which is what recovers ordinary injectivity from universal injectivity.

The proof writes `B` as the image of a surjection from `C = (MvPolynomial (Fin n) A)_q`
(`exists_polynomialLocalization_surjective`, via `Algebra.EssFiniteType.subalgebra`), presents
`N` over `C` by generators, and then replaces the kernel of that presentation by a finitely
generated submodule agreeing with it modulo `𝔪_A`
(`exists_finitelyGenerated_approximation`); this is where Noetherianity of the closed fibre
`C ⧸ 𝔪_A C` is used, and it is what makes the approximating module finitely presented. The
hypothesis applied to that module returns universal injectivity, which forces the approximation
to be an isomorphism, and the three conclusions transport back along it.

## References

* [Stacks Project, Tag 0AT0](https://stacks.math.columbia.edu/tag/0AT0)
* [Stacks Project, Tag 0AT2](https://stacks.math.columbia.edu/tag/0AT2)
-/

@[expose] public section

universe u₁ u₂ u₃ u₄ u₅

namespace AlgebraicGeometry

private theorem exists_finiteType_localizedAtPrime (A B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [IsLocalRing B] [Algebra.EssFiniteType A B] :
    ∃ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) A))
      (_ : Algebra (MvPolynomial (Fin n) A ⧸ J) B)
      (_ : IsScalarTower A (MvPolynomial (Fin n) A ⧸ J) B)
      (p : Ideal (MvPolynomial (Fin n) A ⧸ J)) (_ : p.IsPrime),
      IsLocalization.AtPrime B p := by
  classical
  let S₀ := Algebra.EssFiniteType.subalgebra A B
  obtain ⟨n, F, hF⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
      (inferInstance : Algebra.FiniteType A S₀)
  let P := MvPolynomial (Fin n) A
  let J : Ideal P := RingHom.ker F
  let T := P ⧸ J
  let e : T ≃ₐ[A] S₀ := Ideal.quotientKerAlgEquivOfSurjective hF
  let algTB : Algebra T B := ((algebraMap S₀ B).comp (e : T →+* S₀)).toAlgebra
  have he : ∀ x : T, algebraMap S₀ B (e x) = algebraMap T B x := fun _ => rfl
  have hAB : ∀ x : A, algebraMap A B x = algebraMap T B (algebraMap A T x) := by
    intro x
    rw [← he, AlgEquiv.commutes]
    exact IsScalarTower.algebraMap_apply A S₀ B x
  have : IsScalarTower A T B := IsScalarTower.of_algebraMap_eq hAB
  let p : Ideal T := (IsLocalRing.maximalIdeal B).comap (algebraMap T B)
  have hmon : p.primeCompl = Submonoid.comap (e : T →+* S₀)
      (Algebra.EssFiniteType.submonoid A B) := by
    ext x
    change algebraMap T B x ∉ IsLocalRing.maximalIdeal B ↔
      IsUnit (algebraMap S₀ B (e x))
    rw [← he x]
    exact IsLocalRing.notMem_maximalIdeal
  have hlocP : IsLocalization p.primeCompl B := by
    rw [hmon]
    exact CompleteIntersection.isLocalization_comap_of_ringEquiv e.toRingEquiv he
      (Algebra.EssFiniteType.submonoid A B)
  exact ⟨n, J, algTB, inferInstance, p, Ideal.IsPrime.comap _, hlocP⟩

private theorem exists_polynomialLocalization_surjective (A B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [IsLocalRing B] [Algebra.EssFiniteType A B] :
    ∃ (n : ℕ) (q : Ideal (MvPolynomial (Fin n) A)) (_ : q.IsPrime)
      (f : Localization.AtPrime q →ₐ[A] B), Function.Surjective f := by
  obtain ⟨n, J, algTB, twr, p, hp, hL⟩ := exists_finiteType_localizedAtPrime A B
  let P := MvPolynomial (Fin n) A
  let T := P ⧸ J
  have hgs : Function.Surjective (algebraMap P T) := Ideal.Quotient.mk_surjective
  let q : Ideal P := p.comap (algebraMap P T)
  have hmap : Submonoid.map (algebraMap P T) q.primeCompl = p.primeCompl := by
    ext x
    refine ⟨fun ⟨y, hy, hxy⟩ => hxy ▸ hy, fun hx => ?_⟩
    obtain ⟨y, rfl⟩ := hgs x
    exact ⟨y, hx, rfl⟩
  have hlocalization :
      IsLocalization (Submonoid.map (algebraMap P T) q.primeCompl) B := by rwa [hmap]
  refine ⟨n, q, Ideal.IsPrime.comap _,
    { IsLocalization.map (S := Localization.AtPrime q) B (algebraMap P T)
        (Submonoid.le_comap_map (S := q.primeCompl) (f := algebraMap P T)) with
      commutes' := ?_ }, ?_⟩
  · intro r
    change IsLocalization.map (S := Localization.AtPrime q) B (algebraMap P T)
        (Submonoid.le_comap_map (S := q.primeCompl) (f := algebraMap P T))
        (algebraMap A (Localization.AtPrime q) r) = algebraMap A B r
    rw [IsScalarTower.algebraMap_apply A P (Localization.AtPrime q) r,
      IsLocalization.map_eq, ← IsScalarTower.algebraMap_apply A P T r,
      ← IsScalarTower.algebraMap_apply A T B r]
  · exact IsLocalization.map_surjective_of_surjective q.primeCompl
      (Localization.AtPrime q) B hgs

private theorem finsupp_ideal_smul_top_eq_submodule {R : Type*} [CommRing R]
    {ι : Type*} (I : Ideal R) :
    I • (⊤ : Submodule R (ι →₀ R)) = Finsupp.submodule (fun _ => I) := by
  classical
  ext x
  refine ⟨fun hx i => ?_, fun hx => ?_⟩
  · refine Submodule.smul_induction_on hx ?_ fun _ _ => I.add_mem
    intro a ha y _
    simpa only [Finsupp.smul_apply, smul_eq_mul] using I.mul_mem_right (y i) ha
  · rw [← Finsupp.sum_single x]
    refine Submodule.sum_mem _ fun i _ => ?_
    simpa [Finsupp.smul_single] using
      Submodule.smul_mem_smul (hx i) (Submodule.mem_top (x := Finsupp.single i (1 : R)))

private theorem exists_finitelyGenerated_approximation
    {C N : Type*} [CommRing C] [AddCommGroup N] [Module C N]
    (I : Ideal C) [IsNoetherianRing (C ⧸ I)]
    (n : ℕ) (g : (Fin n →₀ C) →ₗ[C] N) :
    ∃ K' : Submodule C (Fin n →₀ C), K' ≤ LinearMap.ker g ∧ K'.FG ∧
      LinearMap.ker g ⊔ I • (⊤ : Submodule C (Fin n →₀ C)) =
        K' ⊔ I • (⊤ : Submodule C (Fin n →₀ C)) := by
  classical
  let D := C ⧸ I
  let qC : C →ₛₗ[algebraMap C D] D :=
    { toFun := fun x => algebraMap C D x
      map_add' := map_add (algebraMap C D)
      map_smul' := fun c x => by simp }
  let qF : (Fin n →₀ C) →ₛₗ[algebraMap C D] (Fin n →₀ D) :=
    Finsupp.mapRange.linearMap qC
  have : RingHomSurjective (algebraMap C D) := ⟨Ideal.Quotient.mk_surjective⟩
  have hqC : qC.ker = I := by
    ext x
    change (Ideal.Quotient.mk I) x = 0 ↔ x ∈ I
    exact Ideal.Quotient.eq_zero_iff_mem
  have hqF : qF.ker = I • (⊤ : Submodule C (Fin n →₀ C)) := by
    rw [finsupp_ideal_smul_top_eq_submodule]
    ext x
    change (Finsupp.mapRange qC (by simp) x = 0) ↔ ∀ i, x i ∈ I
    refine ⟨fun hx i => ?_, fun hx => ?_⟩
    · have hmem : x i ∈ qC.ker := LinearMap.mem_ker.mpr <| by
        simpa [Finsupp.mapRange_apply] using Finsupp.ext_iff.mp hx i
      rwa [hqC] at hmem
    · ext i
      have hmem : x i ∈ qC.ker := hqC.symm ▸ hx i
      simpa [Finsupp.mapRange_apply] using LinearMap.mem_ker.mp hmem
  let Kbar : Submodule D (Fin n →₀ D) := (LinearMap.ker g).map qF
  have : Module.Finite D Kbar :=
    Module.Finite.iff_fg.mpr (Submodule.FG.of_le_of_isNoetherian le_top)
  obtain ⟨m, v, hv⟩ := Module.Finite.exists_fin (R := D) (M := Kbar)
  let w : Fin m → (Fin n →₀ D) := fun i => v i
  have hw : Submodule.span D (Set.range w) = Kbar := by
    rw [show Set.range w = Kbar.subtype '' Set.range v from Set.range_comp _ _,
      ← Submodule.map_span, hv, Submodule.map_subtype_top]
  choose r hr using fun i => (show w i ∈ (LinearMap.ker g).map qF from (v i).property)
  let K' : Submodule C (Fin n →₀ C) := Submodule.span C (Set.range r)
  have hmap : K'.map qF = Kbar := by
    change (Submodule.span C (Set.range r)).map qF = Kbar
    rw [Submodule.map_span qF]
    have hrange : qF '' Set.range r = Set.range w := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext fun i => (hr i).2)
    rw [hrange, ← hw]
  have hsum : LinearMap.ker g ⊔ qF.ker = K' ⊔ qF.ker := by
    rw [← Submodule.comap_map_eq qF K', hmap]
    exact (Submodule.comap_map_eq qF _).symm
  refine ⟨K', Submodule.span_le.mpr <| Set.range_subset_iff.mpr fun i => (hr i).1,
    Submodule.fg_span (Set.finite_range r), ?_⟩
  simpa [hqF] using hsum

private theorem isNoetherianRing_quotient_map_maximalIdeal (A C : Type*) [CommRing A]
    [IsLocalRing A] [CommRing C] [Algebra A C] [Algebra.EssFiniteType A C] :
    IsNoetherianRing (C ⧸ Ideal.map (algebraMap A C) (IsLocalRing.maximalIdeal A)) := by
  let mA : Ideal A := IsLocalRing.maximalIdeal A
  have : mA.IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
  let : Field (A ⧸ mA) := Ideal.Quotient.field mA
  have : Algebra.EssFiniteType (A ⧸ mA) (C ⧸ Ideal.map (algebraMap A C) mA) := by
    simpa using Algebra.EssFiniteType.quotient_map A C mA
  exact Algebra.EssFiniteType.isNoetherianRing (A ⧸ mA) _

/-- Injectivity of `u.rTensor` on a `ULift` of a test module gives it on the module itself. -/
private theorem injective_rTensor_of_uLift {R : Type*} {X Y Q : Type*} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [AddCommGroup Q] [Module R Q]
    (u : X →ₗ[R] Y) (hu : Function.Injective (u.rTensor (ULift.{u₅} Q))) :
    Function.Injective (u.rTensor Q) :=
  (injective_rTensor_iff_of_equiv u (ULift.moduleEquiv : ULift.{u₅} Q ≃ₗ[R] Q)).mp hu

private theorem injective_of_injective_rTensor_uLift {R : Type u₁} {X Y : Type*} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] (u : X →ₗ[R] Y)
    (hu : Function.Injective (u.rTensor (ULift.{u₅, u₁} R))) : Function.Injective u := by
  have hfac : u = (TensorProduct.rid R Y).toLinearMap ∘ₗ (u.rTensor R) ∘ₗ
      (TensorProduct.rid R X).symm.toLinearMap := by
    ext x
    simp [LinearMap.comp_apply]
  rw [hfac]
  exact (TensorProduct.rid R Y).injective.comp <|
    (injective_rTensor_of_uLift u hu).comp (TensorProduct.rid R X).symm.injective

private theorem injective_rTensor_of_comp_linearEquiv {R X X' Y Q : Type*} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup X'] [Module R X'] [AddCommGroup Y]
    [Module R Y] [AddCommGroup Q] [Module R Q] (u : X →ₗ[R] Y) (e : X' ≃ₗ[R] X)
    (h : Function.Injective ((u ∘ₗ e.toLinearMap).rTensor Q)) :
    Function.Injective (u.rTensor Q) := by
  have hcomp : (u ∘ₗ e.toLinearMap).rTensor Q = u.rTensor Q ∘ₗ (e.rTensor Q).toLinearMap := by
    rw [LinearMap.rTensor_comp]
    rfl
  rw [hcomp] at h
  exact (Function.Injective.of_comp_iff' _ (e.rTensor Q).bijective).mp h

private theorem ker_liftQ_le_smul_top {C F N : Type*} [CommRing C] [AddCommGroup F]
    [Module C F] [AddCommGroup N] [Module C N] (I : Ideal C) (g : F →ₗ[C] N)
    (K' : Submodule C F) (hKle : K' ≤ LinearMap.ker g)
    (hKmod : LinearMap.ker g ⊔ I • (⊤ : Submodule C F) = K' ⊔ I • (⊤ : Submodule C F)) :
    LinearMap.ker (K'.liftQ g hKle) ≤ I • (⊤ : Submodule C (F ⧸ K')) := by
  rw [Submodule.ker_liftQ]
  calc
    (Submodule.map K'.mkQ (LinearMap.ker g)) ≤
        Submodule.map K'.mkQ (LinearMap.ker g ⊔ I • (⊤ : Submodule C F)) :=
      Submodule.map_mono le_sup_left
    _ = Submodule.map K'.mkQ (K' ⊔ I • (⊤ : Submodule C F)) := by rw [hKmod]
    _ = I • (⊤ : Submodule C (F ⧸ K')) := by
      rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, Submodule.map_smul'']
      simp

/-- Over a single ring, injectivity modulo `𝔪` passes to the composite with a surjection whose
kernel lies in `𝔪 • ⊤`. -/
private theorem comap_comp_smul_top_le_of_ker_le {A N' N M : Type*} [CommRing A]
    [AddCommGroup N'] [Module A N'] [AddCommGroup N] [Module A N] [AddCommGroup M] [Module A M]
    (mA : Ideal A) (f : N' →ₗ[A] N) (hf : Function.Surjective f)
    (hker : LinearMap.ker f ≤ mA • (⊤ : Submodule A N')) (u : N →ₗ[A] M)
    (hu : Submodule.comap u (mA • ⊤) ≤ mA • (⊤ : Submodule A N)) :
    Submodule.comap (u ∘ₗ f) (mA • ⊤) ≤ mA • (⊤ : Submodule A N') := by
  intro x hx
  rw [← Submodule.comap_map_eq_self hker, Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr hf]
  exact hu hx

/-- Injectivity modulo `𝔪` passes to the composite with a surjection whose kernel lies in
`𝔪 • ⊤`. -/
theorem comap_comp_restrictScalars_smul_top_le {A C N' N M : Type*} [CommRing A]
    [CommRing C] [Algebra A C] [AddCommGroup N'] [Module C N'] [Module A N']
    [IsScalarTower A C N'] [AddCommGroup N] [Module C N] [Module A N] [IsScalarTower A C N]
    [AddCommGroup M] [Module A M] (mA : Ideal A) (pi : N' →ₗ[C] N)
    (hpi : Function.Surjective pi)
    (hker : LinearMap.ker pi ≤ mA.map (algebraMap A C) • (⊤ : Submodule C N'))
    (u : N →ₗ[A] M) (hu : Submodule.comap u (mA • ⊤) ≤ mA • (⊤ : Submodule A N)) :
    Submodule.comap (u ∘ₗ pi.restrictScalars A) (mA • ⊤) ≤ mA • (⊤ : Submodule A N') := by
  have hkerA : LinearMap.ker (pi.restrictScalars A) ≤ mA • (⊤ : Submodule A N') := by
    have hrest := Ideal.smul_restrictScalars mA (⊤ : Submodule C N')
    rw [Submodule.restrictScalars_top] at hrest
    intro x hx
    rw [← hrest]
    exact hker (by simpa using hx)
  exact comap_comp_smul_top_le_of_ker_le mA _ hpi hkerA u hu

/-- Injectivity modulo `𝔪` passes to the composite with a linear equivalence. -/
theorem comap_comp_linearEquiv_smul_top_le {A N'' N' M : Type*} [CommRing A]
    [AddCommGroup N''] [Module A N''] [AddCommGroup N'] [Module A N'] [AddCommGroup M]
    [Module A M] (mA : Ideal A) (e : N'' ≃ₗ[A] N') (u : N' →ₗ[A] M)
    (hu : Submodule.comap u (mA • ⊤) ≤ mA • (⊤ : Submodule A N')) :
    Submodule.comap (u ∘ₗ e.toLinearMap) (mA • ⊤) ≤ mA • (⊤ : Submodule A N'') := by
  exact comap_comp_smul_top_le_of_ker_le mA _ e.surjective (by simp) u hu

/-- Being a Noetherian ring transports along an equality of carrier types together with a
heterogeneous equality of the ring structures. -/
private theorem transportIsNoetherianRing {X Y : Type u₁} [rx : CommRing X] [ry : CommRing Y]
    (h : X = Y) (hh : HEq rx ry) (hX : IsNoetherianRing X) : IsNoetherianRing Y := by
  subst h
  cases hh
  exact hX

/-- A presentation of `B` as the localization at a prime of a polynomial algebra in finitely
many variables over `A`. -/
structure PolynomialLocalizationPresentation (A : Type u₁) (B : Type u₂)
    [CommRing A] [CommRing B] [Algebra A B] where
  /-- The number of polynomial variables. -/
  variableCount : ℕ
  /-- The prime at which the polynomial algebra is localized. -/
  prime : Ideal (MvPolynomial (Fin variableCount) A)
  /-- The chosen ideal is prime. -/
  [prime_isPrime : prime.IsPrime]
  /-- The polynomial algebra structure on the localization. -/
  [polynomialAlgebra : Algebra (MvPolynomial (Fin variableCount) A) B]
  /-- The given `A`-algebra structure is induced by the polynomial algebra structure. -/
  [scalarTower : IsScalarTower A (MvPolynomial (Fin variableCount) A) B]
  /-- This algebra is the localization at the chosen prime. -/
  [isLocalization : IsLocalization.AtPrime B prime]

/-- Two instances of Situation 0AT0 have the same fixed local base ring.  In addition to
equality of carriers, heterogeneous equality records the chosen `CommRing` structures; the
`IsLocalRing` data is propositional. -/
def SameBaseLocalRing (S T : InjectiveModuloMaximalIdealSituation) : Prop :=
  S.A = T.A ∧ HEq S.commRingA T.commRingA

/-- A Noetherian hypothesis on the base ring transports across `SameBaseLocalRing`.

This is what makes the hypothesis of the reduction lemmas below dischargeable: the special cases
they quantify over are only tied to the given situation through `SameBaseLocalRing`, so any
property of the base ring used to settle a special case has to be carried across it. -/
theorem SameBaseLocalRing.isNoetherianRing {S T : InjectiveModuloMaximalIdealSituation}
    (h : SameBaseLocalRing S T) (hS : IsNoetherianRing S.A) : IsNoetherianRing T.A :=
  transportIsNoetherianRing (rx := S.commRingA) (ry := T.commRingA) h.1 h.2 hS

/-- The three properties meant by “the lemma holds” in Situation 0AT0. -/
def InjectiveModuloMaximalIdealConclusion
    (S : InjectiveModuloMaximalIdealSituation) : Prop :=
  UniversallyInjectivePoly.{_, u₅} S.u ∧
    Module.FinitePresentation S.B S.N ∧ Module.Flat S.A S.N

private theorem exists_finitePresentation_surjective_comap_smul_top_le {A : Type*}
    {C : Type u₁} {N M : Type*} [CommRing A] [IsLocalRing A] [CommRing C] [Algebra A C]
    [Algebra.EssFiniteType A C] [AddCommGroup N] [Module C N] [Module A N]
    [IsScalarTower A C N] [Module.Finite C N] [AddCommGroup M] [Module A M] (u : N →ₗ[A] M)
    (hu : Submodule.comap u (IsLocalRing.maximalIdeal A • ⊤) ≤
      IsLocalRing.maximalIdeal A • (⊤ : Submodule A N)) :
    ∃ (N' : Type u₁) (_ : AddCommGroup N') (_ : Module C N') (_ : Module A N')
      (_ : IsScalarTower A C N') (_ : Module.FinitePresentation C N') (pi : N' →ₗ[C] N),
      Function.Surjective pi ∧
        Submodule.comap (u ∘ₗ pi.restrictScalars A) (IsLocalRing.maximalIdeal A • ⊤) ≤
          IsLocalRing.maximalIdeal A • (⊤ : Submodule A N') := by
  classical
  obtain ⟨m, gens, hgens⟩ := Module.Finite.exists_fin (R := C) (M := N)
  let g : (Fin m →₀ C) →ₗ[C] N := Finsupp.linearCombination C gens
  have hg : Function.Surjective g := by
    rw [← LinearMap.range_eq_top]
    change (Finsupp.linearCombination C gens).range = ⊤
    rw [Finsupp.range_linearCombination, hgens]
  let I : Ideal C := Ideal.map (algebraMap A C) (IsLocalRing.maximalIdeal A)
  have : IsNoetherianRing (C ⧸ I) := isNoetherianRing_quotient_map_maximalIdeal A C
  obtain ⟨K', hKle, hKfg, hKmod⟩ := exists_finitelyGenerated_approximation I m g
  have hpi : Function.Surjective (K'.liftQ g hKle) := fun x =>
    let ⟨y, hy⟩ := hg x
    ⟨K'.mkQ y, hy⟩
  exact ⟨(Fin m →₀ C) ⧸ K', inferInstance, inferInstance, inferInstance, inferInstance,
    Module.finitePresentation_of_surjective K'.mkQ K'.mkQ_surjective (by rwa [Submodule.ker_mkQ]),
    K'.liftQ g hKle, hpi, comap_comp_restrictScalars_smul_top_le _ _ hpi
      (ker_liftQ_le_smul_top I g K' hKle hKmod) u hu⟩

private theorem rTensor_injective_of_localizedPolynomial_cases_uLift
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    (h : ∀ (T : InjectiveModuloMaximalIdealSituation.{u₁, max u₁ u₂, u₃,
        max u₁ u₂ u₄}),
      SameBaseLocalRing S T → PolynomialLocalizationPresentation T.A T.B →
        Module.FinitePresentation T.B T.N →
          InjectiveModuloMaximalIdealConclusion.{max u₁ u₅} T)
    {n : ℕ} (q : Ideal (MvPolynomial (Fin n) S.A)) [q.IsPrime]
    {C : Type (max u₁ u₂)} [CommRing C] [IsLocalRing C] [Algebra S.A C]
    [IsLocalHom (algebraMap S.A C)] [Algebra.EssFiniteType S.A C]
    [Algebra (MvPolynomial (Fin n) S.A) C] [IsScalarTower S.A (MvPolynomial (Fin n) S.A) C]
    [IsLocalization.AtPrime C q]
    {N : Type (max u₁ u₂ u₄)} [AddCommGroup N] [Module C N] [Module S.A N]
    [IsScalarTower S.A C N] [Module.FinitePresentation C N] (u : N →ₗ[S.A] S.M)
    (hu : Submodule.comap u (IsLocalRing.maximalIdeal S.A • ⊤) ≤
      IsLocalRing.maximalIdeal S.A • (⊤ : Submodule S.A N)) :
    (∀ (Q : Type (max u₁ u₅)) [AddCommGroup Q] [Module S.A Q],
      Function.Injective (u.rTensor Q)) ∧ Module.Flat S.A N := by
  let mA : Ideal S.A := IsLocalRing.maximalIdeal S.A
  have hmod : Function.Injective ((mA • (⊤ : Submodule S.A N)).mapQ (mA • ⊤) u
      (Submodule.smul_top_le_comap_smul_top mA u)) :=
    (Stacks.UniversalInjectivity.FGIdealTest.injective_mapQ_iff u
      (Submodule.smul_top_le_comap_smul_top mA u)).mpr hu
  let T : InjectiveModuloMaximalIdealSituation.{u₁, max u₁ u₂, u₃,
      max u₁ u₂ u₄} := {
    A := S.A
    B := C
    M := S.M
    N := N
    commRingA := S.commRingA
    localRingA := S.localRingA
    commRingB := inferInstance
    localRingB := inferInstance
    algebraAB := inferInstance
    localHom := inferInstance
    essentiallyFiniteType := inferInstance
    addCommGroupM := S.addCommGroupM
    moduleAM := S.moduleAM
    flatM := S.flatM
    addCommGroupN := inferInstance
    moduleBN := inferInstance
    moduleAN := inferInstance
    isScalarTower := inferInstance
    finiteN := inferInstance
    u := u
    injective_mod_maximalIdeal := hmod }
  obtain ⟨hUI, -, hflat⟩ :=
    h T ⟨rfl, HEq.rfl⟩ ⟨n, q⟩ inferInstance
  exact ⟨fun Q _ _ => hUI Q, hflat⟩

private theorem rTensor_injective_of_localizedPolynomial_cases
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    (h : ∀ (T : InjectiveModuloMaximalIdealSituation.{u₁, max u₁ u₂, u₃,
        max u₁ u₂ u₄}),
      SameBaseLocalRing S T → PolynomialLocalizationPresentation T.A T.B →
        Module.FinitePresentation T.B T.N →
          InjectiveModuloMaximalIdealConclusion.{max u₁ u₅} T)
    {n : ℕ} (q : Ideal (MvPolynomial (Fin n) S.A)) [q.IsPrime]
    (hloc : IsLocalHom (algebraMap S.A (Localization.AtPrime q)))
    {N' : Type u₁} [AddCommGroup N'] [Module (Localization.AtPrime q) N'] [Module S.A N']
    [IsScalarTower S.A (Localization.AtPrime q) N']
    [Module.FinitePresentation (Localization.AtPrime q) N'] (u' : N' →ₗ[S.A] S.M)
    (hu' : Submodule.comap u' (IsLocalRing.maximalIdeal S.A • ⊤) ≤
      IsLocalRing.maximalIdeal S.A • (⊤ : Submodule S.A N')) :
    (∀ (Q : Type (max u₁ u₅)) [AddCommGroup Q] [Module S.A Q],
      Function.Injective (u'.rTensor Q)) ∧ Module.Flat S.A N' := by
  classical
  let P := MvPolynomial (Fin n) S.A
  let C := Localization.AtPrime q
  let C' : Type (max u₁ u₂) := ULift.{max u₁ u₂, u₁} C
  let eC : C' ≃+* C := ULift.ringEquiv
  let : CommRing C' := inferInstance
  let : Algebra P C' := inferInstance
  have : IsLocalization q.primeCompl C' :=
    IsLocalization.isLocalization_of_algEquiv q.primeCompl
      (ULift.algEquiv (R := P)).symm
  have : IsLocalRing C' := IsLocalization.AtPrime.isLocalRing C' q
  let : Algebra S.A C' := inferInstance
  have : IsScalarTower S.A P C' := inferInstance
  have : Algebra.EssFiniteType P C' :=
    Algebra.EssFiniteType.of_isLocalization C' q.primeCompl
  have : Algebra.EssFiniteType S.A C' := Algebra.EssFiniteType.comp S.A P C'
  have : IsLocalHom (algebraMap S.A C') :=
    ⟨fun a ha => hloc.map_nonunit a (IsUnit.map eC.toRingHom ha)⟩
  let N'' : Type (max (max u₁ u₂) u₄) := ULift.{max (max u₁ u₂) u₄, u₁} N'
  let : Module C' N' := Module.compHom N' eC.toRingHom
  let : Module C' N'' := inferInstance
  have : IsScalarTower S.A C' N' := ⟨fun a b x => by
    rw [Algebra.smul_def]
    change (algebraMap S.A C a * b.down) • x = a • (b.down • x)
    rw [mul_smul, IsScalarTower.algebraMap_smul C]⟩
  have : IsScalarTower S.A C' N'' := ULift.isScalarTower''
  let eN : N'' ≃ₗ[C'] N' := ULift.moduleEquiv
  let eNA : N'' ≃ₗ[S.A] N' := ULift.moduleEquiv
  have : Module.FinitePresentation C' N' := fp_transport eC
  have : Module.FinitePresentation C' N'' := Module.FinitePresentation.of_equiv eN.symm
  obtain ⟨hUI, hflat⟩ := rTensor_injective_of_localizedPolynomial_cases_uLift S h q
    (C := C') (u'.comp eNA.toLinearMap)
    (comap_comp_linearEquiv_smul_top_le (IsLocalRing.maximalIdeal S.A) eNA u' hu')
  exact ⟨fun Q _ _ => injective_rTensor_of_comp_linearEquiv u' eNA (hUI Q),
    Module.Flat.of_linearEquiv eNA.symm⟩

private theorem localizedPolynomial_cases_conclusion
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    (h : ∀ (T : InjectiveModuloMaximalIdealSituation.{u₁, max u₁ u₂, u₃,
        max u₁ u₂ u₄}),
      SameBaseLocalRing S T → PolynomialLocalizationPresentation T.A T.B →
        Module.FinitePresentation T.B T.N →
          InjectiveModuloMaximalIdealConclusion.{max u₁ u₅} T) :
    InjectiveModuloMaximalIdealConclusion.{u₅} S := by
  classical
  obtain ⟨n, q, _, f, hf⟩ := exists_polynomialLocalization_surjective S.A S.B
  let P := MvPolynomial (Fin n) S.A
  let C := Localization.AtPrime q
  let : Algebra S.A C := inferInstance
  let : Algebra P C := inferInstance
  have : IsScalarTower S.A P C := inferInstance
  have : Algebra.EssFiniteType P C := Algebra.EssFiniteType.of_isLocalization C q.primeCompl
  have : Algebra.EssFiniteType S.A C := Algebra.EssFiniteType.comp S.A P C
  let : Algebra C S.B := f.toRingHom.toAlgebra
  have hfcomm : ∀ a : S.A,
      algebraMap S.A S.B a = algebraMap C S.B (algebraMap S.A C a) :=
    fun a => (f.commutes a).symm
  have : IsScalarTower S.A C S.B := IsScalarTower.of_algebraMap_eq hfcomm
  let : Module C S.N := Module.compHom S.N (algebraMap C S.B)
  have : IsScalarTower C S.B S.N := IsScalarTower.of_compHom C S.B S.N
  have : IsScalarTower S.A C S.N := IsScalarTower.of_algebraMap_smul (by
    intro a x
    change (algebraMap C S.B (algebraMap S.A C a)) • x = a • x
    rw [← hfcomm a]
    exact IsScalarTower.algebraMap_smul S.B a x)
  have : Module.Finite C S.B :=
    Module.Finite.of_surjective (Algebra.linearMap C S.B) hf
  have : Module.Finite C S.N := Module.Finite.trans S.B S.N
  have hpreS : Submodule.comap S.u (IsLocalRing.maximalIdeal S.A • ⊤) ≤
      IsLocalRing.maximalIdeal S.A • (⊤ : Submodule S.A S.N) :=
    (Stacks.UniversalInjectivity.FGIdealTest.injective_mapQ_iff S.u
      (Submodule.smul_top_le_comap_smul_top _ S.u)).mp S.injective_mod_maximalIdeal
  obtain ⟨N', _, _, _, _, _, pi, hpi, hpre⟩ :=
    exists_finitePresentation_surjective_comap_smul_top_le (C := C) S.u hpreS
  have hloc : IsLocalHom (algebraMap S.A C) := ⟨fun a ha => S.localHom.map_nonunit a (by
    rw [← f.commutes a]
    exact IsUnit.map f.toRingHom ha)⟩
  let u' : N' →ₗ[S.A] S.M := S.u ∘ₗ pi.restrictScalars S.A
  obtain ⟨hU', _⟩ := rTensor_injective_of_localizedPolynomial_cases S h q hloc u' hpre
  have hu'inj : Function.Injective u' :=
    injective_of_injective_rTensor_uLift u' (hU' (ULift.{max u₁ u₅, u₁} S.A))
  have hpiinj : Function.Injective pi := fun x y hxy => hu'inj (congrArg S.u hxy)
  let eA : N' ≃ₗ[S.A] S.N := LinearEquiv.ofBijective (pi.restrictScalars S.A) ⟨hpiinj, hpi⟩
  have : Module.FinitePresentation C S.N :=
    Module.FinitePresentation.of_equiv (LinearEquiv.ofBijective pi ⟨hpiinj, hpi⟩)
  exact ⟨fun Q _ _ => injective_rTensor_of_comp_linearEquiv S.u eA
      (injective_rTensor_of_uLift u' (hU' _)),
    Module.finitePresentation_of_compHom_comp (RingHom.id S.B) f.toRingHom hf inferInstance,
    Module.Flat.of_linearEquiv eA.symm⟩

/-- Universal injectivity in Situation 0AT0 reduces to the case of a localization of a finite
polynomial algebra with finitely presented source module. -/
@[stacks 0AT2 "universal injectivity"]
theorem universallyInjective_of_localizedPolynomial_cases
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    (h : ∀ (T : InjectiveModuloMaximalIdealSituation.{u₁, max u₁ u₂, u₃, max u₁ u₂ u₄}),
      SameBaseLocalRing S T → PolynomialLocalizationPresentation T.A T.B →
        Module.FinitePresentation T.B T.N →
          InjectiveModuloMaximalIdealConclusion.{max u₁ u₅} T) :
    UniversallyInjectivePoly.{_, u₅} S.u :=
  (localizedPolynomial_cases_conclusion S h).1

/-- Finite presentation in Situation 0AT0 reduces to the case of a localization of a finite
polynomial algebra with finitely presented source module. -/
@[stacks 0AT2 "finite presentation"]
theorem finitePresentation_of_localizedPolynomial_cases
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    (h : ∀ (T : InjectiveModuloMaximalIdealSituation.{u₁, max u₁ u₂, u₃, max u₁ u₂ u₄}),
      SameBaseLocalRing S T → PolynomialLocalizationPresentation T.A T.B →
        Module.FinitePresentation T.B T.N →
          InjectiveModuloMaximalIdealConclusion.{max u₁ u₅} T) :
    Module.FinitePresentation S.B S.N :=
  (localizedPolynomial_cases_conclusion S h).2.1

/-- Flatness in Situation 0AT0 reduces to the case of a localization of a finite polynomial
algebra with finitely presented source module. -/
@[stacks 0AT2 "flatness"]
theorem flat_of_localizedPolynomial_cases
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    (h : ∀ (T : InjectiveModuloMaximalIdealSituation.{u₁, max u₁ u₂, u₃, max u₁ u₂ u₄}),
      SameBaseLocalRing S T → PolynomialLocalizationPresentation T.A T.B →
        Module.FinitePresentation T.B T.N →
          InjectiveModuloMaximalIdealConclusion.{max u₁ u₅} T) :
    Module.Flat S.A S.N :=
  (localizedPolynomial_cases_conclusion S h).2.2

/-! ### "The lemma" is its universal-injectivity assertion

The three assertions of "the lemma" of Situation 0AT0 are not independent.  A universally
injective map into a flat module has flat source, so the flatness assertion follows from the
universal-injectivity assertion with no further input, and in the special cases quantified over
by Stacks 0AT2 the source module is finitely presented by hypothesis.  Together with the three
reduction lemmas above this leaves universal injectivity in the localized-polynomial case as the
only thing to prove.
-/

/-- A universally injective map into a flat module has flat source.  For a submodule `P' ⊆ P`
the composite `X ⊗ P' → X ⊗ P → Y ⊗ P` agrees with `X ⊗ P' → Y ⊗ P' → Y ⊗ P`; the latter is
injective because `u` is universally injective and `Y` is flat, so the first arrow of the former
is injective.

Only test modules in the universe of the base ring are needed: flatness is detected on
submodules of modules in that universe. -/
theorem _root_.Module.Flat.of_rTensor_injective_of_flat {R : Type u₁} {X : Type u₂} {Y : Type u₃}
    [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [Module.Flat R Y]
    (u : X →ₗ[R] Y)
    (hu : ∀ (Q : Type u₁) [AddCommGroup Q] [Module R Q], Function.Injective (u.rTensor Q)) :
    Module.Flat R X := by
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro P _ _ P'
  let : AddCommGroup P := Module.addCommMonoidToAddCommGroup R
  have hcomp : (u.rTensor P).comp (P'.subtype.lTensor X) =
      (P'.subtype.lTensor Y).comp (u.rTensor P') := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  have hinj : Function.Injective ((u.rTensor P).comp (P'.subtype.lTensor X)) := by
    rw [hcomp]
    exact (Module.Flat.lTensor_preserves_injective_linearMap P'.subtype
      P'.injective_subtype).comp (hu P')
  rw [LinearMap.coe_comp] at hinj
  exact hinj.of_comp

/-- In Situation 0AT0 the universal-injectivity assertion of "the lemma" already forces the
flatness assertion: `u` is a universally injective map into an `A`-flat module. -/
theorem flat_of_rTensor_injective (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    (hu : ∀ (Q : Type (max u₁ u₅)) [AddCommGroup Q] [Module S.A Q],
      Function.Injective (S.u.rTensor Q)) :
    Module.Flat S.A S.N :=
  Module.Flat.of_rTensor_injective_of_flat S.u fun _ _ _ =>
    injective_rTensor_of_uLift S.u (hu _)

/-- In Situation 0AT0 the universal-injectivity assertion of "the lemma" together with finite
presentation of `N` over `B` gives all three assertions. -/
theorem injectiveModuloMaximalIdealConclusion_of_rTensor_injective
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    (hfp : Module.FinitePresentation S.B S.N)
    (hu : ∀ (Q : Type (max u₁ u₅)) [AddCommGroup Q] [Module S.A Q],
      Function.Injective (S.u.rTensor Q)) :
    InjectiveModuloMaximalIdealConclusion.{max u₁ u₅} S :=
  ⟨fun Q _ _ => hu Q, hfp, flat_of_rTensor_injective S hu⟩

/-- **"The lemma" of Situation 0AT0 reduces to its universal-injectivity assertion.** All three
assertions in Situation 0AT0 follow from universal injectivity alone in the special cases
quantified over by Stacks 0AT2: a localization at a prime of a polynomial algebra in finitely
many variables over `A`, with `N` finitely presented over it.

This is Stacks 0AT2 composed with `AlgebraicGeometry.flat_of_rTensor_injective`.  It is the shape
in which the henselian case (Stacks 0AT3) and the general case (Stacks 0AT4) are reached: the
finite-presentation assertion is a hypothesis of the special case and the flatness assertion is a
consequence, so only universal injectivity is left. -/
theorem injectiveModuloMaximalIdealConclusion_of_rTensor_injective_cases
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    (h : ∀ (T : InjectiveModuloMaximalIdealSituation.{u₁, max u₁ u₂, u₃, max u₁ u₂ u₄}),
      SameBaseLocalRing S T → PolynomialLocalizationPresentation T.A T.B →
        Module.FinitePresentation T.B T.N →
          ∀ (Q : Type (max u₁ u₅)) [AddCommGroup Q] [Module T.A Q],
            Function.Injective (T.u.rTensor Q)) :
    InjectiveModuloMaximalIdealConclusion.{u₅} S :=
  localizedPolynomial_cases_conclusion S fun T hb hp hfp =>
    injectiveModuloMaximalIdealConclusion_of_rTensor_injective T hfp (h T hb hp hfp)

end AlgebraicGeometry

end
