module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveDisjointUnionTraces
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyRootsOfUnity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapDimensionZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TwistedFrobeniusTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilTraceInputProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricFrobeniusUniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisActionFibreCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleFlatTensorExact
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicPreservesHomology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Weil's formula for the twisted Frobenius of a curve over a finite field, as a trace

Let `Y` be a smooth proper curve (possibly disconnected) over a finite field `k` with `q = p^f`
elements, `σ` an automorphism of `Y` over `k`, `k̄` an algebraic closure of `k` and
`φ = σ̄ ∘ π̄` the twisted geometric Frobenius of `Y_k̄`. For a prime `ℓ ≠ p` and `n ≥ 1` the
trace of `φ^*` on `RΓ(Y_k̄, ℤ/ℓⁿ)` is the number of fixed points of `φ`:

`Tr(φ^* | RΓ(Y_k̄, ℤ/ℓⁿ)) = #Fix(φ) · Tr(id | Γ(k̄, ℤ/ℓⁿ))`.

This is the input from Weil's trace formula ([Stacks, Tag 03U1]) used in Step 9 of the proof of
[Stacks, Tag 03V3] (the trace formula for curves, Tag 03UG). The proof: `Ψ = Fr ∘ σ̄⁻¹`, with `Fr`
the action of the arithmetic Frobenius of `k̄`, is an automorphism with `Ψ ∘ φ = φ ∘ Ψ = F^f`;
`Hⁱ(Y_k̄, ℤ/ℓⁿ) ≅ Hⁱ(Y_k̄, μ_{ℓⁿ})` compatibly with `φ^*`; these are finite free over `ℤ/ℓⁿ`
and the trace of `φ^*` on them is the sum over the components sent into themselves of
`1`, `Tr(φ^* | Pic[ℓⁿ])`, `deg φ`, `0`; Weil's formula on each such component gives the
alternating sum as the number of fixed points.

## Main definitions

* `twistedFrobeniusPsi`: the automorphism `Ψ = Fr ∘ σ̄⁻¹` of `Y_k̄`.

## Main results

* `twistedFrobeniusPsi_hom_comp`, `comp_twistedFrobeniusPsi_hom`: `Ψ ∘ φ = φ ∘ Ψ = F^f`.
* `perfectDerivedTrace_selfMapCohomologyEndo_eq_natCard_of_comp_eq_absoluteFrobeniusPow`:
  over any algebraically closed `Ω` algebraic over `𝔽_p`, for `φ` with an automorphism `Ψ` such
  that `Ψ ∘ φ = φ ∘ Ψ = F^e`, `Tr(φ^* | RΓ(Y, ℤ/ℓ^m)) = #Fix(φ)`.
* `perfectDerivedTrace_id_baseSectionsComplex_constant`: `Tr(id | Γ(Ω, ℤ/N)) = 1`.
* `perfectDerivedTrace_selfMapCohomologyEndo_twistedGeometricFrobenius_eq_card_smul`:
  `Tr(φ^* | RΓ(Y_k̄, ℤ/ℓⁿ)) = #Fix(φ) · Tr(id | Γ(k̄, ℤ/ℓⁿ))` for the twisted geometric
  Frobenius `φ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

section Psi

variable {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k))) (σ : Y ⟶ Y)
  (kbar : Type u) [Field kbar] [Algebra k kbar]

omit [Fintype k] in
/-- The action `id × Spec(τ)` of a `k`-automorphism `τ` of `k̄` on `Y_k̄` is an isomorphism. -/
theorem isIso_galoisBaseChange (τ : kbar ≃ₐ[k] kbar) : IsIso (galoisBaseChange Y kbar τ) :=
  ⟨⟨galoisBaseChange Y kbar τ⁻¹,
    by rw [← galoisBaseChange_mul, mul_inv_cancel, galoisBaseChange_one],
    by rw [← galoisBaseChange_mul, inv_mul_cancel, galoisBaseChange_one]⟩⟩

omit [Fintype k] in
/-- The base change `σ̄ = σ × id` of an automorphism of `Y` is an automorphism of `Y_k̄`. -/
theorem isIso_fieldBaseChangeMap [IsIso σ.left] : IsIso (fieldBaseChangeMap σ kbar) := by
  unfold fieldBaseChangeMap
  infer_instance

variable (p q : ℕ) [Fact p.Prime] [CharP k p] [ExpChar kbar p] [PerfectRing kbar p]
  (hcard : Fintype.card k = p ^ q) [IsIso σ.left]

/-- **The automorphism `Ψ = Fr ∘ σ̄⁻¹` of `Y_k̄`** attached to an automorphism `σ` of `Y` over
the finite field `k`: the action of the arithmetic Frobenius `x ↦ x^q` of `k̄`, after the inverse
of `σ̄ = σ × id`. It inverts the twisted geometric Frobenius `σ̄ ∘ π̄` up to `F^f`. -/
def twistedFrobeniusPsi : fieldBaseChange Y kbar ≅ fieldBaseChange Y kbar :=
  haveI := isIso_galoisBaseChange Y kbar (arithmeticFrobenius k kbar p q hcard)
  haveI := isIso_fieldBaseChangeMap Y σ kbar
  asIso (galoisBaseChange Y kbar (arithmeticFrobenius k kbar p q hcard)) ≪≫
    (asIso (fieldBaseChangeMap σ kbar)).symm

/-- `Ψ ∘ (σ̄ ∘ π̄)`, i.e. `(σ̄ π̄) ∘ Ψ` read left to right, is the `f`-fold absolute Frobenius. -/
theorem twistedFrobeniusPsi_hom_comp :
    (twistedFrobeniusPsi Y σ kbar p q hcard).hom ≫ twistedGeometricFrobenius Y σ kbar p q hcard =
      absoluteFrobeniusPow (fieldBaseChange Y kbar) p
        (isInCharacteristic_fieldBaseChange Y kbar p) q := by
  have := isIso_fieldBaseChangeMap Y σ kbar
  simp only [twistedFrobeniusPsi, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    twistedGeometricFrobenius, Category.assoc, IsIso.inv_hom_id_assoc]
  exact arithmeticFrobenius_comp_geometricFrobeniusBaseChange Y kbar p q hcard

/-- `(σ̄ ∘ π̄)` followed by `Ψ` is also the `f`-fold absolute Frobenius. -/
theorem comp_twistedFrobeniusPsi_hom :
    twistedGeometricFrobenius Y σ kbar p q hcard ≫ (twistedFrobeniusPsi Y σ kbar p q hcard).hom =
      absoluteFrobeniusPow (fieldBaseChange Y kbar) p
        (isInCharacteristic_fieldBaseChange Y kbar p) q := by
  have := isIso_fieldBaseChangeMap Y σ kbar
  simp only [twistedFrobeniusPsi, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    twistedGeometricFrobenius, Category.assoc]
  rw [reassoc_of% (geometricFrobeniusBaseChange_comp_arithmeticFrobenius Y kbar p q hcard),
    absoluteFrobeniusPow_naturality (inv (fieldBaseChangeMap σ kbar)) p
      (isInCharacteristic_fieldBaseChange Y kbar p) (isInCharacteristic_fieldBaseChange Y kbar p),
    IsIso.hom_inv_id_assoc]

end Psi

section General

attribute [local instance] HasDerivedCategory.standard
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

open CategoryTheory.FilteredDerived

/-- The `n`-fold absolute Frobenius of a scheme in characteristic `p` is a universal
homeomorphism, as the absolute Frobenius is ([Stacks, Tag 0CC8]). -/
theorem universalHomeomorphism_absoluteFrobeniusPow (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (n : ℕ) :
    UniversalHomeomorphism (absoluteFrobeniusPow X p hX n) := by
  induction n with
  | zero => rw [absoluteFrobeniusPow_zero]; exact universalHomeomorphism_of_isIso _
  | succ m ih =>
    rw [absoluteFrobeniusPow_succ_eq_comp]
    exact universalHomeomorphism_comp _ _ inferInstance ih

/-- **`RΓ(S, Rf_*(f^{-1} M))` has no cohomology in negative degrees** for a sheaf `M` placed in
degree zero. -/
theorem isZero_homology_selfMapCohomology_of_neg (Λ : Type) [CommRing Λ] {Y S : Scheme.{u}}
    (f : Y ⟶ S) (M : EtaleModules.{u, 0} Λ S) (i : ℤ) (hi : i < 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} Λ f
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj M)))) :=
  have : EnoughInjectives (EtaleModules.{u, 0} Λ Y) := etaleModules_enoughInjectives Λ Y
  (Functor.isZero_rightDerivedPlus_of_neg (etaleModuleGlobalSections.{u, 0} Λ Y)
    ((etaleModuleInverseImage.{u, 0} Λ f).obj M) i hi).of_iso (selfMapCohomologySingleIso Λ f M i)

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of Ω))
  [IsProper f] [SmoothOfRelativeDimension 1 f] (φ : Y ⟶ Y) (w : φ ≫ f = f)
  (p : ℕ) [Fact p.Prime] (hY : IsInCharacteristic Y p) (e : ℕ) (Ψ : Y ≅ Y)
  (hΨ : Ψ.hom ≫ φ = absoluteFrobeniusPow Y p hY e)
  (hΨ' : φ ≫ Ψ.hom = absoluteFrobeniusPow Y p hY e) (ℓ m : ℕ) [Fact ℓ.Prime]

/-- Freeness and finiteness transfer along a linear equivalence. -/
private theorem free_and_finite_of_linearEquiv {R M N : Type*} [Semiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] (L : M ≃ₗ[R] N) [Module.Free R M]
    [Module.Finite R M] : Module.Free R N ∧ Module.Finite R N :=
  ⟨Module.Free.of_equiv L, Module.Finite.equiv L⟩

/-- **Transport of a model trace along a conjugating additive equivalence.** -/
theorem modelTrace_trans_of_comm {N : ℕ} {A B M : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup M] [Module (ZMod N) M] (R : A ≃+ B) (E : B ≃+ M) (g : A →+ A) (g' : B →+ B)
    (h : ∀ y, R (g y) = g' (R y)) : modelTrace N (R.trans E) g = modelTrace N E g' := by
  unfold modelTrace
  congr 2
  refine AddMonoidHom.ext fun x => ?_
  simp [h]

include hΨ in
/-- **A finite free model of `Hⁱ(RΓ(Y, ℤ/ℓ^m))` with the trace of `φ^*`**: through
`Hⁱ(Y, ℤ/ℓ^m) ≅ Hⁱ(Y, μ_{ℓ^m})` the trace of `φ^*` is the sum over the components sent into
themselves of `1`, `Tr(φ_i^* | Pic(C_i)[ℓ^m])`, `deg φ_i`, `0`. -/
theorem exists_homology_selfMapCohomology_model (hm : 1 ≤ m) (hℓ : (ℓ : Ω) ≠ 0) (q : ℕ) :
    ∃ (r : Fin (componentCount Y) → ℕ)
      (E : (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod (ℓ ^ m))) q).obj
          (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} (ZMod (ℓ ^ m)) f
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
              (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ m))
                (Spec (.of Ω)).smallEtaleTopology)))) ≃+
        (∀ i, Fin (r i) → ZMod (ℓ ^ m))),
      modelTrace (ℓ ^ m) E
          ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod (ℓ ^ m))) q).map
            (DerivedCategory.Plus.ι.map (selfMapCohomologyEndo.{u, 0} (ZMod (ℓ ^ m)) f φ w
              ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
                (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ m))
                  (Spec (.of Ω)).smallEtaleTopology))))).hom.toAddMonoidHom =
        componentTraceSum f φ w p hY e Ψ hΨ' ℓ m q := by
  have hN : ℓ ^ m ≠ 0 := pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero
  have : NeZero (ℓ ^ m) := ⟨hN⟩
  have : NeZero ((ℓ ^ m : ℕ) : Ω) := ⟨by rw [Nat.cast_pow]; exact pow_ne_zero _ hℓ⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω (ℓ ^ m)
  have := isMonoidal_W_etaleModules (ZMod (ℓ ^ m)) Y
  have : UniversalHomeomorphism φ := by
    have h : φ = Ψ.inv ≫ absoluteFrobeniusPow Y p hY e := by rw [← hΨ, Iso.inv_hom_id_assoc]
    rw [h]
    exact universalHomeomorphism_comp _ _ (universalHomeomorphism_of_isIso _)
      (universalHomeomorphism_absoluteFrobeniusPow Y p hY e)
  have := etaleModuleDirectImage_preservesFiniteColimits_of_universalHomeomorphism
    (ZMod (ℓ ^ m)) φ
  obtain ⟨r, E₀, hE₀⟩ :=
    exists_model_rootsOfUnityPullbackMap_eq_sum f φ w p hY e Ψ hΨ' ℓ m hm hℓ q
  let R : (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod (ℓ ^ m))) q).obj
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} (ZMod (ℓ ^ m)) f
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ m))
            (Spec (.of Ω)).smallEtaleTopology)))) ≃+
      Sheaf.H.{u + 1} (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} Y (ℓ ^ m)) q :=
    selfMapCohomologyRootsOfUnityAddEquiv f hζ hN q
  refine ⟨r, R.trans E₀, ?_⟩
  rw [← hE₀]
  refine modelTrace_trans_of_comm R E₀ _ _ fun y => ?_
  exact selfMapCohomologyRootsOfUnityAddEquiv_selfMapCohomologyEndo f φ w hζ hN q y

include w hΨ hΨ' in
/-- The cohomology modules of `RΓ(Y, ℤ/ℓ^m)` are finite free over `ℤ/ℓ^m` in degrees `≥ 0`. -/
theorem free_finite_homology_selfMapCohomology (hm : 1 ≤ m) (hℓ : (ℓ : Ω) ≠ 0) (q : ℕ) :
    Module.Free (ZMod (ℓ ^ m)) ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (ZMod (ℓ ^ m))) q).obj
        (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} (ZMod (ℓ ^ m)) f
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ m))
              (Spec (.of Ω)).smallEtaleTopology))))) ∧
      Module.Finite (ZMod (ℓ ^ m)) ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (ZMod (ℓ ^ m))) q).obj
        (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} (ZMod (ℓ ^ m)) f
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ m))
              (Spec (.of Ω)).smallEtaleTopology))))) := by
  obtain ⟨r, E, -⟩ :=
    exists_homology_selfMapCohomology_model f φ w p hY e Ψ hΨ hΨ' ℓ m hm hℓ q
  exact free_and_finite_of_linearEquiv (E.symm.toLinearEquiv (ZMod.map_smul E.symm))

include hΨ in
/-- **The trace of `φ^*` on `Hⁱ(Y, ℤ/ℓ^m)`.** -/
theorem trace_homology_selfMapCohomologyEndo (hm : 1 ≤ m) (hℓ : (ℓ : Ω) ≠ 0) (q : ℕ) :
    LinearMap.trace (ZMod (ℓ ^ m)) _
        ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod (ℓ ^ m))) q).map
          (DerivedCategory.Plus.ι.map (selfMapCohomologyEndo.{u, 0} (ZMod (ℓ ^ m)) f φ w
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
              (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ m))
                (Spec (.of Ω)).smallEtaleTopology))))).hom =
      componentTraceSum f φ w p hY e Ψ hΨ' ℓ m q := by
  obtain ⟨hF, hFin⟩ := free_finite_homology_selfMapCohomology f φ w p hY e Ψ hΨ hΨ' ℓ m hm hℓ q
  obtain ⟨r, E, hE⟩ :=
    exists_homology_selfMapCohomology_model f φ w p hY e Ψ hΨ hΨ' ℓ m hm hℓ q
  rw [← hE]
  exact AddMonoidHom.trace_toZModLinearMap_eq_of_addEquiv (n := ℓ ^ m) E
    ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod (ℓ ^ m))) q).map
      (DerivedCategory.Plus.ι.map (selfMapCohomologyEndo.{u, 0} (ZMod (ℓ ^ m)) f φ w
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ m))
            (Spec (.of Ω)).smallEtaleTopology))))).hom.toAddMonoidHom
    (E.toAddMonoidHom.comp
      (((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod (ℓ ^ m))) q).map
      (DerivedCategory.Plus.ι.map (selfMapCohomologyEndo.{u, 0} (ZMod (ℓ ^ m)) f φ w
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ m))
            (Spec (.of Ω)).smallEtaleTopology))))).hom.toAddMonoidHom.comp
      E.symm.toAddMonoidHom)) fun x => by simp

include w hΨ hΨ' in
/-- Every cohomology module of `RΓ(Y, ℤ/ℓ^m)` is finite projective over `ℤ/ℓ^m`. -/
theorem hasFiniteProjectiveHomology_selfMapCohomology (hm : 1 ≤ m) (hℓ : (ℓ : Ω) ≠ 0) :
    HasFiniteProjectiveHomology.{0, u + 1} (ZMod (ℓ ^ m))
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} (ZMod (ℓ ^ m)) f
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ m))
            (Spec (.of Ω)).smallEtaleTopology)))) := fun i => by
  rcases lt_or_ge i 0 with hi | hi
  · have hz := isZero_homology_selfMapCohomology_of_neg (ZMod (ℓ ^ m)) f
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ m))
        (Spec (.of Ω)).smallEtaleTopology) i hi
    have := ModuleCat.isZero_iff_subsingleton.mp hz
    exact ⟨inferInstance, inferInstance⟩
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    obtain ⟨hF, hFin⟩ := free_finite_homology_selfMapCohomology f φ w p hY e Ψ hΨ hΨ' ℓ m hm hℓ q
    exact ⟨inferInstance, hFin⟩

omit [IsAlgClosed Ω] in
/-- `φ^*` has trace zero in degrees `≥ 3`. -/
theorem componentTraceSum_add_three (q : ℕ) :
    componentTraceSum f φ w p hY e Ψ hΨ' ℓ m (q + 3) = 0 := by
  unfold componentTraceSum
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs <;> rfl

include hΨ in
/-- **The trace of `φ^*` on `Hⁱ(RΓ(Y, ℤ/ℓ^m))`** for `i ≥ 0`, in `ℤ/ℓ^m` modulo commutators. -/
theorem derivedHomologyTrace_selfMapCohomologyEndo_natCast (hm : 1 ≤ m) (hℓ : (ℓ : Ω) ≠ 0)
    (hH : HasFiniteProjectiveHomology.{0, u + 1} (ZMod (ℓ ^ m))
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} (ZMod (ℓ ^ m)) f
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ m))
              (Spec (.of Ω)).smallEtaleTopology))))) (q : ℕ) :
    derivedHomologyTrace (ZMod (ℓ ^ m)) _ hH
      (DerivedCategory.Plus.ι.map (selfMapCohomologyEndo.{u, 0} (ZMod (ℓ ^ m)) f φ w
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ m))
              (Spec (.of Ω)).smallEtaleTopology)))) q =
      additiveCommutatorQuotientMk (ZMod (ℓ ^ m)) (componentTraceSum f φ w p hY e Ψ hΨ' ℓ m q) := by
  obtain ⟨hF, hFin⟩ := free_finite_homology_selfMapCohomology f φ w p hY e Ψ hΨ hΨ' ℓ m hm hℓ q
  rw [← trace_homology_selfMapCohomologyEndo f φ w p hY e Ψ hΨ hΨ' ℓ m hm hℓ q]
  exact Stacks.Trace.projectiveModuleTrace_eq_mk_trace _ _ _

omit [IsAlgClosed Ω] [IsProper f] [SmoothOfRelativeDimension 1 f] [Fact (Nat.Prime ℓ)] in
/-- The trace of `φ^*` on `Hⁱ(RΓ(Y, ℤ/ℓ^m))` vanishes for `i < 0`. -/
theorem derivedHomologyTrace_selfMapCohomologyEndo_of_neg
    (hH : HasFiniteProjectiveHomology.{0, u + 1} (ZMod (ℓ ^ m))
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} (ZMod (ℓ ^ m)) f
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ m))
              (Spec (.of Ω)).smallEtaleTopology))))) (i : ℤ) (hi : i < 0) :
    derivedHomologyTrace (ZMod (ℓ ^ m)) _ hH
      (DerivedCategory.Plus.ι.map (selfMapCohomologyEndo.{u, 0} (ZMod (ℓ ^ m)) f φ w
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ m))
              (Spec (.of Ω)).smallEtaleTopology)))) i = 0 := by
  have hz := isZero_homology_selfMapCohomology_of_neg (ZMod (ℓ ^ m)) f
    (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ m))
      (Spec (.of Ω)).smallEtaleTopology) i hi
  have := ModuleCat.isZero_iff_subsingleton.mp hz
  exact projectiveModuleTrace_eq_zero_of_subsingleton _ _ _

include hΨ in
/-- **The alternating sum of the traces of `φ^*` on `Hⁱ(Y, ℤ/ℓ^m)`** is `T₀ - T₁ + T₂`, the
traces in degrees `0, 1, 2`. -/
theorem finsum_signedByDegree_derivedHomologyTrace_selfMapCohomologyEndo (hm : 1 ≤ m)
    (hℓ : (ℓ : Ω) ≠ 0) (hH : HasFiniteProjectiveHomology.{0, u + 1} (ZMod (ℓ ^ m))
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} (ZMod (ℓ ^ m)) f
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ m))
              (Spec (.of Ω)).smallEtaleTopology))))) :
    ∑ᶠ i : ℤ, signedByDegree (ZMod (ℓ ^ m)) i (derivedHomologyTrace (ZMod (ℓ ^ m)) _ hH
      (DerivedCategory.Plus.ι.map (selfMapCohomologyEndo.{u, 0} (ZMod (ℓ ^ m)) f φ w
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ m))
              (Spec (.of Ω)).smallEtaleTopology)))) i) =
      additiveCommutatorQuotientMk (ZMod (ℓ ^ m))
        (componentTraceSum f φ w p hY e Ψ hΨ' ℓ m 0 - componentTraceSum f φ w p hY e Ψ hΨ' ℓ m 1 +
          componentTraceSum f φ w p hY e Ψ hΨ' ℓ m 2) := by
  have hnat := derivedHomologyTrace_selfMapCohomologyEndo_natCast f φ w p hY e Ψ hΨ hΨ' ℓ m hm hℓ hH
  have hsupp : Function.support (fun i : ℤ => signedByDegree (ZMod (ℓ ^ m)) i
      (derivedHomologyTrace (ZMod (ℓ ^ m)) _ hH
        (DerivedCategory.Plus.ι.map (selfMapCohomologyEndo.{u, 0} (ZMod (ℓ ^ m)) f φ w
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ m))
              (Spec (.of Ω)).smallEtaleTopology)))) i)) ⊆ ((({0, 1, 2} : Finset ℤ)) : Set ℤ) := by
    intro i hi
    by_contra hne
    apply hi
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hne
    rcases lt_or_ge i 0 with hneg | hnn
    · simp only [derivedHomologyTrace_selfMapCohomologyEndo_of_neg f φ w ℓ m hH i hneg,
        signedByDegree_zero]
    · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hnn
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 3 := ⟨q - 3, by omega⟩
      simp only [hnat, componentTraceSum_add_three, map_zero, signedByDegree_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have h0 := hnat 0
  have h1 := hnat 1
  have h2 := hnat 2
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at h0 h1 h2
  rw [h0, h1, h2, map_add, map_sub]
  have e0 : Even (0 : ℤ) := ⟨0, rfl⟩
  have e2 : Even (2 : ℤ) := ⟨1, rfl⟩
  simp only [signedByDegree, ite_eq_left e0, ite_eq_left e2, ite_eq_right Int.not_even_one]
  abel

variable [CharP Ω p] (halg : letI := ZMod.algebra Ω p; Algebra.IsAlgebraic (ZMod p) Ω)

include w hΨ hΨ' halg in
/-- **Weil's formula, summed over the components**: `T₀ - T₁ + T₂ = #Fix(φ)` in `ℤ/ℓ^m`. -/
theorem componentTraceSum_alternating_eq_natCard (he : 0 < e) (hm : 1 ≤ m) (hℓ : (ℓ : Ω) ≠ 0) :
    componentTraceSum f φ w p hY e Ψ hΨ' ℓ m 0 - componentTraceSum f φ w p hY e Ψ hΨ' ℓ m 1 +
        componentTraceSum f φ w p hY e Ψ hΨ' ℓ m 2 =
      (Nat.card (fixedSections f φ) : ZMod (ℓ ^ m)) := by
  rw [natCard_fixedSections_eq_sum f φ w p hY e Ψ hΨ hΨ' halg he]
  unfold componentTraceSum
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · exact (natCard_fixedSections_componentSelfMap_eq f φ w p hY e Ψ hΨ hΨ' halg weilTraceInput he
      ℓ m hℓ hm i h).symm.trans (Int.cast_natCast _)
  · simp

include w hΨ hΨ' halg in
/-- **Weil's trace formula for a twisted Frobenius, as the trace on `RΓ(Y, ℤ/ℓ^m)`.** Let
`f : Y ⟶ Spec Ω` be proper and smooth of relative dimension one over an algebraically closed
field `Ω` of characteristic `p`, algebraic over `𝔽_p`, and `φ` an endomorphism of `Y` over `Ω`
with an automorphism `Ψ` such that `Ψ ∘ φ` and `φ ∘ Ψ` are the `e`-fold absolute Frobenius,
`e ≥ 1`. For a prime `ℓ ≠ p` and `m ≥ 1`, the trace of `φ^*` on the perfect complex
`RΓ(Y, ℤ/ℓ^m)` is the number of `Ω`-points of `Y` fixed by `φ`. -/
theorem perfectDerivedTrace_selfMapCohomologyEndo_eq_natCard_of_comp_eq_absoluteFrobeniusPow
    (he : 0 < e) (hm : 1 ≤ m) (hℓ : (ℓ : Ω) ≠ 0)
    (hp : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} (ZMod (ℓ ^ m)) f
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ m))
              (Spec (.of Ω)).smallEtaleTopology))))) :
    perfectDerivedTrace (ZMod (ℓ ^ m)) ⟨_, hp⟩
      (DerivedCategory.Plus.ι.map (selfMapCohomologyEndo.{u, 0} (ZMod (ℓ ^ m)) f φ w
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ m))
              (Spec (.of Ω)).smallEtaleTopology)))) =
      additiveCommutatorQuotientMk (ZMod (ℓ ^ m)) (Nat.card (fixedSections f φ)) :=
  perfectDerivedTrace_selfMapCohomologyEndo_eq_card _ f φ w _ hp
    (hasFiniteProjectiveHomology_selfMapCohomology f φ w p hY e Ψ hΨ hΨ' ℓ m hm hℓ)
    (by rw [finsum_signedByDegree_derivedHomologyTrace_selfMapCohomologyEndo f φ w p hY e Ψ hΨ hΨ'
      ℓ m hm hℓ, componentTraceSum_alternating_eq_natCard f φ w p hY e Ψ hΨ hΨ' ℓ m halg he hm hℓ])

end General

section BaseSections

attribute [local instance] HasDerivedCategory.standard

open CategoryTheory.FilteredDerived Opposite

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

/-- **The sections of the constant sheaf `ℤ/N` over `Spec Ω`** are `ℤ/N`, for `Ω` algebraically
closed with `N` invertible in `Ω`: through a primitive `N`-th root of unity, they are the
`N`-th roots of unity of `Ω`. -/
theorem nonempty_constantSections_addEquiv (N : ℕ) [NeZero N] (hN : (N : Ω) ≠ 0) :
    Nonempty (((Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N)
      (Spec (.of Ω)).smallEtaleTopology).obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))))) ≃+
        ZMod N) := by
  have : NeZero (N : Ω) := ⟨hN⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω N
  let J := ((sheafToPresheaf _ _).mapIso
    (Stacks.Kummer.etaleModuleConstantUnderlyingIso (𝟙 (Spec (.of Ω))) hζ (NeZero.ne N))).app
      (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))))
  exact ⟨J.addCommGroupIsoToAddEquiv.trans
    ((Stacks.EtaleCohomology.rootsOfUnityGlobalSectionsAddEquiv.{u, 0} (Spec (.of Ω)) N).trans
      ((MulEquiv.subgroupCongr
        (rootsOfUnity_eq_zpowers_globalPrimitiveRoot (𝟙 (Spec (.of Ω))) hζ)).toAdditive.trans
          (isPrimitiveRoot_globalPrimitiveRoot (𝟙 (Spec (.of Ω))) hζ).zmodEquivZPowers.symm))⟩

/-- **`Tr(id | Γ(Spec Ω, ℤ/N)) = 1`**: the complex of sections of the constant sheaf `ℤ/N` over
`Spec Ω` is `ℤ/N` in degree zero. -/
theorem perfectDerivedTrace_id_baseSectionsComplex_constant (N : ℕ) [Fact (1 < N)]
    (hN : (N : Ω) ≠ 0)
    (hΓ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj (baseSectionsComplex (ZMod N)
      ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N)
          (Spec (.of Ω)).smallEtaleTopology)).obj))) :
    perfectDerivedTrace (ZMod N) ⟨_, hΓ⟩ (𝟙 _) = additiveCommutatorQuotientMk (ZMod N) 1 := by
  have : NeZero N := ⟨by have := (Fact.out : 1 < N); omega⟩
  let F := Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N)
    (Spec (.of Ω)).smallEtaleTopology
  let G := sheafToPresheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} (ZMod N)) ⋙
    (CategoryTheory.evaluation (Spec (.of Ω)).Etaleᵒᵖ (ModuleCat.{u + 1} (ZMod N))).obj
      (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))))
  let eB : baseSectionsComplex (ZMod N) ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F).obj ≅
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (G.obj F) :=
    (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).app F
  let eH : ∀ i, (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod N)) i).obj
      (DerivedCategory.Q.obj (baseSectionsComplex (ZMod N)
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F).obj)) ≅
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (G.obj F)).homology i := fun i =>
    (DerivedCategory.homologyFunctorFactors _ i).app _ ≪≫
      (HomologicalComplex.homologyFunctor _ _ i).mapIso eB
  have hz : ∀ i, i ≠ 0 → Subsingleton ((DerivedCategory.homologyFunctor
      (ModuleCat.{u + 1} (ZMod N)) i).obj (DerivedCategory.Q.obj (baseSectionsComplex (ZMod N)
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F).obj))) := fun i hi =>
    ModuleCat.isZero_iff_subsingleton.mp
      ((HomologicalComplex.isZero_single_obj_homology _ _ _ i hi).of_iso (eH i))
  obtain ⟨E₀⟩ := nonempty_constantSections_addEquiv N hN
  let L₀ : (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod N)) 0).obj
      (DerivedCategory.Q.obj (baseSectionsComplex (ZMod N)
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F).obj)) ≃ₗ[ZMod N] ZMod N :=
    (eH 0 ≪≫ HomologicalComplex.singleObjHomologySelfIso _ _ _).toLinearEquiv.trans
      (E₀.toLinearEquiv (ZMod.map_smul E₀))
  obtain ⟨_, _⟩ := free_and_finite_of_linearEquiv L₀.symm
  have hH : HasFiniteProjectiveHomology.{0, u + 1} (ZMod N) (DerivedCategory.Q.obj
      (baseSectionsComplex (ZMod N) ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F).obj)) :=
    fun i => by
      by_cases hi : i = 0
      · subst hi
        exact ⟨inferInstance, inferInstance⟩
      · have := hz i hi
        exact ⟨inferInstance, inferInstance⟩
  rw [perfectDerivedTrace_eq_homologyTrace (ZMod N) ⟨_, hΓ⟩ (𝟙 _) hH,
    finsum_eq_single _ 0 fun i hi => ?_]
  · have h0 : derivedHomologyTrace (ZMod N) _ hH (𝟙 _) 0 =
        additiveCommutatorQuotientMk (ZMod N) (LinearMap.trace (ZMod N) _
          ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod N)) 0).map (𝟙 _)).hom) :=
      Stacks.Trace.projectiveModuleTrace_eq_mk_trace _ _ _
    rw [h0, CategoryTheory.Functor.map_id, ModuleCat.hom_id, LinearMap.trace_id,
      L₀.finrank_eq, Module.finrank_self, Nat.cast_one]
    have e0 : Even (0 : ℤ) := ⟨0, rfl⟩
    simp only [signedByDegree, ite_eq_left e0]
  · have := hz i hi
    have h : derivedHomologyTrace (ZMod N) _ hH (𝟙 _) i = 0 :=
      projectiveModuleTrace_eq_zero_of_subsingleton _ _ _
    rw [h, signedByDegree_zero]

end BaseSections

section FiniteField

attribute [local instance] HasDerivedCategory.standard

open CategoryTheory.FilteredDerived

/-- An algebraic extension of a finite field of characteristic `p` is algebraic over `𝔽_p`. -/
theorem isAlgebraic_zmod_of_finite (k : Type u) [Field k] [Finite k] (kbar : Type u) [Field kbar]
    [Algebra k kbar] [Algebra.IsAlgebraic k kbar] (p : ℕ) [Fact p.Prime] [CharP k p]
    [CharP kbar p] :
    letI := ZMod.algebra kbar p; Algebra.IsAlgebraic (ZMod p) kbar := by
  let := ZMod.algebra kbar p
  let := ZMod.algebra k p
  have : IsScalarTower (ZMod p) k kbar :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [← RingHom.comp_apply, RingHom.ext_zmod (algebraMap (ZMod p) kbar)
        ((algebraMap k kbar).comp (algebraMap (ZMod p) k))]
  have : Algebra.IsAlgebraic (ZMod p) k := Algebra.IsAlgebraic.of_finite (ZMod p) k
  exact Algebra.IsAlgebraic.trans (ZMod p) k kbar

variable {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k))) [IsProper Y.hom]
  [SmoothOfRelativeDimension 1 Y.hom] (σ : Y ⟶ Y) [IsIso σ.left]
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] [Algebra.IsAlgebraic k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)


/-- **Weil's trace formula for the twisted Frobenius of a curve over a finite field**, the input
of Step 9 of the proof of [Stacks, Tag 03V3] (the trace formula for curves, Tag 03UG, from
Weil's formula, Tag 03U1). Let `Y` be a proper smooth curve over the finite field `k` with
`q = p^f` elements (not necessarily connected), `σ` an automorphism of `Y` over `k`, `k̄` an
algebraic closure of `k` and `φ = σ̄ ∘ π̄` the twisted geometric Frobenius of `Y_k̄`. For a
prime `ℓ ≠ p` and `n ≥ 1` the trace of `φ^*` on `RΓ(Y_k̄, ℤ/ℓⁿ)` is the number of fixed
`k̄`-points of `φ` times the trace of the identity of `Γ(k̄, ℤ/ℓⁿ)`:

`Tr(φ^* | RΓ(Y_k̄, ℤ/ℓⁿ)) = #Fix(φ) · Tr(id | Γ(k̄, ℤ/ℓⁿ))`. -/
@[sga "4½ Rapport 3.2" "special case"]
theorem perfectDerivedTrace_selfMapCohomologyEndo_twistedGeometricFrobenius_eq_card_smul
    (ℓ n : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) (hn : 1 ≤ n)
    (hp₂ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} (ZMod (ℓ ^ n))
        (pullback.snd Y.hom (specAlgebraMap k kbar))
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ n))
            (Spec (.of kbar)).smallEtaleTopology)))))
    (hΓ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Q.obj (baseSectionsComplex (ZMod (ℓ ^ n))
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ n))
            (Spec (.of kbar)).smallEtaleTopology)).obj))) :
    perfectDerivedTrace (ZMod (ℓ ^ n)) ⟨_, hp₂⟩
        (DerivedCategory.Plus.ι.map (selfMapCohomologyEndo.{u, 0} (ZMod (ℓ ^ n))
          (pullback.snd Y.hom (specAlgebraMap k kbar))
          (twistedGeometricFrobenius Y σ kbar p q hcard)
          (twistedGeometricFrobenius_comp_toBase Y σ kbar p q hcard)
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ n))
              (Spec (.of kbar)).smallEtaleTopology)))) =
      Nat.card (fixedSections (pullback.snd Y.hom (specAlgebraMap k kbar))
        (twistedGeometricFrobenius Y σ kbar p q hcard)) •
          perfectDerivedTrace (ZMod (ℓ ^ n)) ⟨_, hΓ⟩ (𝟙 _) := by
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  have : SmoothOfRelativeDimension 1 (pullback.snd Y.hom (specAlgebraMap k kbar)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback Y.hom (specAlgebraMap k kbar)) inferInstance
  have halg := isAlgebraic_zmod_of_finite k kbar p
  have hℓ' : (ℓ : kbar) ≠ 0 := by
    rw [← map_natCast (algebraMap k kbar)]
    exact (map_ne_zero _).mpr hℓ
  have hq : 0 < q := Nat.pos_of_ne_zero (ne_zero_of_card_eq_pow hcard)
  have : Fact (1 < ℓ ^ n) :=
    ⟨Nat.one_lt_pow (by omega) (Fact.out : ℓ.Prime).one_lt⟩
  rw [perfectDerivedTrace_selfMapCohomologyEndo_eq_natCard_of_comp_eq_absoluteFrobeniusPow
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (twistedGeometricFrobenius Y σ kbar p q hcard)
      (twistedGeometricFrobenius_comp_toBase Y σ kbar p q hcard) p
      (isInCharacteristic_fieldBaseChange Y kbar p) q (twistedFrobeniusPsi Y σ kbar p q hcard)
      (twistedFrobeniusPsi_hom_comp Y σ kbar p q hcard)
      (comp_twistedFrobeniusPsi_hom Y σ kbar p q hcard) ℓ n halg hq hn hℓ' hp₂,
    perfectDerivedTrace_id_baseSectionsComplex_constant (ℓ ^ n)
      (by rw [Nat.cast_pow]; exact pow_ne_zero _ hℓ') hΓ,
    ← map_nsmul, nsmul_one]

end FiniteField

end Stacks.EtaleCohomology

end
