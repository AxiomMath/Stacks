module

public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftSmoothGlue
public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroGlueDatumLift
public import StacksFrontier.RingTheory.Restricted.RigSmoothSmoothLocus
public import StacksFrontier.RingTheory.Smoothing.LiftingAlongSurjections

/-!
# Lifting a smooth algebraization across a square-zero thickening

Let `R → R₀` be a surjection of Noetherian rings with square-zero kernel `N`, let
`I = (f₁, …, f_k) ⊆ R`, let `S` be a finite type `R₀`-algebra which is smooth over
`Spec R₀ ∖ V(I R₀)`, and let `H` be an `I`-adically complete Noetherian `R`-algebra whose
localizations `H_{fᵢ}` are flat over `R`, with `H ⧸ N H ≅ S^∧`. Then there is a finite type
`R`-algebra `T`, smooth over `Spec R ∖ V(I)`, lifting `S` across `R → R₀` and with `I`-adic
completion `H`.

This is the smooth counterpart of `Rig.exists_squareZeroLift` (the lifting step of Stacks 0AKA),
and it is the deformation-theoretic step of the proof of Gabber–Zavyalov's theorem on the
algebraization of rig-smooth algebras (arXiv 2402.08741, Lemma "lift-rig-smooth", there proved
with the cohomology of the tangent sheaf on `Spec ∖ V(I)` and a pushout of algebraic spaces).

## The proof

`T` is glued, by `Rig.SquareZeroLift.GlueDatum.exists_lift`, from `S`, `H` and smooth lifts `W_i`
of the localizations `S_{fᵢ}` (Stacks 07M8). Unlike étale lifts, the `W_i` are not unique and the
glueing data must be chosen: maps `φ_i : W_i → H_{fᵢ}` lifting `S_{fᵢ} → (H ⧸ N H)_{fᵢ}` and chart
changes `γ_{ij} : W_j[1/fᵢ] → W_i[1/f_j]` lifting the identity, which must be compatible and
satisfy the cocycle condition. Any choice (by formal smoothness) has defects forming a cocycle of
the glueing complex of `Derivation R S (S ⊗[R] N)` for the flat map `S → S^∧`; the exactness of
that complex at its fourth term (`FormalGlueing.glueingComplex_exact_fourth`) makes it a
coboundary, and correcting the choice by the primitive removes the defects
(`Rig.SquareZeroLift.ChartData.exists_compatible`). Then `T ⧸ N T = S`, `T^∧ = H`, and
`T[1/fᵢ] = W_i` is smooth over `R`.

## Main results

* `Rig.exists_squareZeroLift_of_smoothAwayFrom`
-/

@[expose] public section

namespace Rig

open SquareZeroLift

universe u

/-- Smoothness of a finite type algebra away from `V(f)` follows from smoothness of the
localizations at the `f i`. -/
public theorem smoothAwayFrom_span_of_isLocalization_away {R : Type u} [CommRing R] {k : ℕ}
    (f : Fin k → R) (T : Type u) [CommRing T] [Algebra R T] [Algebra.FinitePresentation R T]
    (h : ∀ i, ∃ (V : Type u) (_ : CommRing V) (_ : Algebra R V) (_ : Algebra T V),
      IsScalarTower R T V ∧ IsLocalization.Away (algebraMap R T (f i)) V ∧
        Algebra.FormallySmooth R V) :
    SmoothAwayFrom R (Ideal.span (Set.range f)) T := by
  intro q hq hle
  obtain ⟨i, hi⟩ : ∃ i, algebraMap R T (f i) ∉ q := by
    by_contra! hcon
    apply hle
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact hcon i
  obtain ⟨V, _, _, _, _, _, _⟩ := h i
  have : Algebra.FormallySmooth R (Localization.Away (algebraMap R T (f i))) :=
    .of_equiv ((IsLocalization.algEquiv (Submonoid.powers (algebraMap R T (f i))) V
      (Localization.Away (algebraMap R T (f i)))).restrictScalars R)
  rw [Algebra.smoothAt_iff_isSmoothAt R T]
  exact (Algebra.basicOpen_subset_smoothLocus_iff (R := R)).mpr this
    (show (⟨q, hq⟩ : PrimeSpectrum _) ∈ PrimeSpectrum.basicOpen _ from hi)

/-- A smooth algebra over a quotient `R₀` of `R` lifts to a smooth `R`-algebra, as a lift across
`R → R₀` in the sense of `Rig.SquareZeroLift.NilLift` (Stacks 07M8). -/
theorem exists_smooth_nilLift {R : Type u} [CommRing R] {R₀ : Type u} [CommRing R₀] [Algebra R R₀]
    (hsurj : Function.Surjective (algebraMap R R₀)) (X : Type u) [CommRing X] [Algebra R₀ X]
    [Algebra R X] [IsScalarTower R R₀ X] (hX : Algebra.Smooth R₀ X) :
    ∃ L : NilLift R (RingHom.ker (algebraMap R R₀)) X, Algebra.Smooth R L.carrier := by
  obtain ⟨A, _, _, hA, e', he'⟩ := Stacks.Smoothing.exists_smooth_lift_of_surjective R R₀ X hsurj hX
  let ψ : A →ₐ[R] X :=
    { toRingHom := e'.symm.toRingHom.comp (Ideal.Quotient.mk _)
      commutes' := fun r ↦ by
        change e'.symm (Ideal.Quotient.mk _ (algebraMap R A r)) = algebraMap R X r
        rw [← he', RingEquiv.symm_apply_apply, ← IsScalarTower.algebraMap_apply] }
  refine ⟨⟨A, ψ, fun x ↦ ?_, ?_⟩, hA⟩
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (e' x)
    refine ⟨a, ?_⟩
    change e'.symm (Ideal.Quotient.mk _ a) = x
    rw [ha, RingEquiv.symm_apply_apply]
  · ext a
    change e'.symm (Ideal.Quotient.mk _ a) = 0 ↔ _
    rw [map_eq_zero_iff _ e'.symm.injective, Ideal.Quotient.eq_zero_iff_mem]

/-- If `S` is smooth over `R₀` away from `V(f)`, then its localizations at the `f i` are smooth
over `R₀`. -/
private theorem smooth_sl_of_smoothAwayFrom {R : Type u} [CommRing R] {R₀ : Type u}
    [CommRing R₀] [Algebra R R₀] {k : ℕ} (f : Fin k → R) (S : Type u) [CommRing S] [Algebra R₀ S]
    [Algebra R S] [IsScalarTower R R₀ S] [Algebra.FinitePresentation R₀ S]
    (hS : SmoothAwayFrom R₀ ((Ideal.span (Set.range f)).map (algebraMap R R₀)) S) (i : Fin k) :
    Algebra.Smooth R₀ (Sl f S {i}) := by
  rw [← Algebra.basicOpen_subset_smoothLocus_iff_smooth]
  intro p hp
  have hfi : algebraMap R S (f i) ∉ p.asIdeal := by
    intro hmem
    apply hp
    change algebraMap R S (∏ j ∈ ({i} : Finset (Fin k)), f j) ∈ p.asIdeal
    rwa [Finset.prod_singleton]
  have hsmp := hS p.asIdeal p.isPrime (by
    intro hle
    apply hfi
    have h2 := hle (Ideal.mem_map_of_mem (algebraMap R₀ S)
      (Ideal.mem_map_of_mem (algebraMap R R₀) (Ideal.subset_span ⟨i, rfl⟩)))
    rwa [← IsScalarTower.algebraMap_apply] at h2)
  rwa [Algebra.smoothAt_iff_isSmoothAt R₀ S] at hsmp

/-- **The square-zero lifting step for smooth algebraizations.** Let `R → R₀` be a surjection of
Noetherian rings with square-zero kernel `N`, let `I = (f₁, …, f_k) ⊆ R`, and let `S` be a finite
type `R₀`-algebra which is smooth over `Spec R₀ ∖ V(I R₀)`. Let `H` be a Noetherian `I`-adically
complete `R`-algebra whose localizations `H_{fᵢ}` are flat over `R`, together with an `R`-algebra
isomorphism `e : H ⧸ N H ≅ S^∧`. Then there is a finite type `R`-algebra `T`, smooth over
`Spec R ∖ V(I)`, with a surjection `p : T → S` of kernel `N T` and a map `φ : T → H` compatible
with `e`, which identifies the `I`-adic completion of `T` with `H`. -/
public theorem exists_squareZeroLift_of_smoothAwayFrom
    {R : Type u} [CommRing R] [IsNoetherianRing R] {R₀ : Type u} [CommRing R₀] [Algebra R R₀]
    (hsurj : Function.Surjective (algebraMap R R₀)) (hsq : RingHom.ker (algebraMap R R₀) ^ 2 = ⊥)
    {k : ℕ} (f : Fin k → R)
    (S : Type u) [CommRing S] [Algebra R₀ S] [Algebra R S] [IsScalarTower R R₀ S]
    [Algebra.FiniteType R₀ S]
    (hS : SmoothAwayFrom R₀ ((Ideal.span (Set.range f)).map (algebraMap R R₀)) S)
    (H : Type u) [CommRing H] [Algebra R H] [IsNoetherianRing H]
    (hH : IsAdicComplete ((Ideal.span (Set.range f)).map (algebraMap R H)) H)
    (hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i))))
    (e : (H ⧸ (RingHom.ker (algebraMap R R₀)).map (algebraMap R H)) ≃ₐ[R]
      AdicCompletion ((Ideal.span (Set.range f)).map (algebraMap R S)) S) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T),
      Algebra.FiniteType R T ∧ SmoothAwayFrom R (Ideal.span (Set.range f)) T ∧
      ∃ (p : T →ₐ[R] S) (φ : T →ₐ[R] H), Function.Surjective p ∧
        RingHom.ker p.toRingHom = (RingHom.ker (algebraMap R R₀)).map (algebraMap R T) ∧
        (∀ x : T, e (Ideal.Quotient.mk _ (φ x)) =
          algebraMap S (AdicCompletion ((Ideal.span (Set.range f)).map (algebraMap R S)) S) (p x)) ∧
        ∃ E : AdicCompletion ((Ideal.span (Set.range f)).map (algebraMap R T)) T ≃ₐ[R] H,
          ∀ x : T, E (algebraMap T _ x) = φ x := by
  classical
  let N := RingHom.ker (algebraMap R R₀)
  have hNS : N.map (algebraMap R S) = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker]
    intro x hx
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply R R₀ S, (RingHom.mem_ker).mp hx, map_zero]
  have : IsNoetherianRing R₀ := isNoetherianRing_of_surjective R R₀ _ hsurj
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R₀ S
  have : Algebra.FiniteType R R₀ := Algebra.FiniteType.of_surjective (Algebra.ofId R R₀) hsurj
  have : Algebra.FiniteType R S := Algebra.FiniteType.trans (S := R₀) inferInstance inferInstance
  have : Algebra.FinitePresentation R S := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have : Algebra.FinitePresentation R₀ S := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have hW : ∀ i : Fin k, ∃ L : NilLift R N (Sl f S {i}), Algebra.Smooth R L.carrier :=
    fun i ↦ exists_smooth_nilLift hsurj (Sl f S {i}) (smooth_sl_of_smoothAwayFrom f S hS i)
  choose W hWs using hW
  have hWf : ∀ i, Module.Flat R (W i).carrier := fun i ↦
    have := hWs i; Algebra.Smooth.flat_of_isNoetherianRing R (W i).carrier
  have hWfs : ∀ i, Algebra.FormallySmooth R (W i).carrier := fun i ↦ (hWs i).formallySmooth
  let C₀ : ChartData N f S H e W :=
    { φ := fun i ↦ Algebra.FormallySmooth.lift _ (isNilpotent_map N hsq _)
        ((chi N f S H e {i}).comp (Wc N f S W i {i} (Finset.mem_singleton_self i)).ψ)
      hφ := fun i v ↦ Algebra.FormallySmooth.mk_lift _ _ _ v
      γ := fun a b _ ↦ Algebra.FormallySmooth.lift _ (isNilpotent_map N hsq _)
        ((((Wc N f S W a {a, b} (mem_pair_left a b)).qe N).symm.toAlgHom).comp
          (Wc N f S W b {a, b} (mem_pair_right a b)).ψ)
      hγ := fun a b _ v ↦ by
        rw [← NilLift.qe_mk N, Algebra.FormallySmooth.mk_lift]
        exact AlgEquiv.apply_symm_apply _ _ }
  obtain ⟨C, hC1, hC2⟩ := C₀.exists_compatible hsq hflat
  let D := C.toGlueDatum ⟨hC1, hC2⟩ hNS
  obtain ⟨T, _, _, hT, p, φ, hp, hker, hcompat, hE, hloc⟩ := D.exists_lift hsurj hsq hH hflat
  have : Algebra.FinitePresentation R T := Algebra.FinitePresentation.of_finiteType.mp hT
  refine ⟨T, inferInstance, inferInstance, hT,
    smoothAwayFrom_span_of_isLocalization_away f T fun i ↦ ?_, p, φ, hp, hker, hcompat, hE⟩
  obtain ⟨_, hst, hlocal, -, -⟩ := hloc i
  refine ⟨(D.L {i}).carrier, inferInstance, inferInstance, inferInstance, hst, hlocal, ?_⟩
  have hne : ({i} : Finset (Fin k)).Nonempty := Finset.singleton_nonempty i
  have : Algebra.FormallySmooth R (Wc N f S W (({i} : Finset (Fin k)).min' hne) {i}
      (Finset.min'_mem _ hne)).carrier := inferInstance
  exact Algebra.FormallySmooth.of_equiv (ChartData.eqv hNS {i} hne).symm

end Rig

end
