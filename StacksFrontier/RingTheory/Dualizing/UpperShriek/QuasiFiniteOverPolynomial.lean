module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.WeakRelativeNoetherNormalization
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeTorAmplitude
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeRestriction
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Homology.TorAmplitude.DerivedComparison
public import StacksFrontier.Homology.TorAmplitude.SingleOfCanonical
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.CompositionFiniteType
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FibreDimensionBoundUpper
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.PolynomialAlgebra
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingCohenMacaulay
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingTorAmplitude

/-!
# The relative dualizing complex of an algebra flat and quasi-finite over a polynomial algebra

Let `R` be a Noetherian ring and `A` a Noetherian `R`-algebra admitting a homomorphism
`θ : P = R[x_1, …, x_d] → A` over `R` that is flat and quasi-finite. Then the relative dualizing
complex `ω^•_{A/R}` has a single nonzero cohomology module, in degree `-d`, and that module is flat
over `R`. This is the affine core of the proof of [Stacks, Tag 0BV8]: `ω^•_{A/R} = ω^•_{A/P}[d]`
by the composition `R → P → A` ([Stacks, Tag 0BZT]) and `ω^•_{P/R} = P[d]`, while `ω^•_{A/P}` sits
in degree zero by the bounds of [Stacks, Tag 0E9Q], the fibres of `P → A` being finite.

## Main results

* `Dualizing.isZero_homology_upperShriekFunctor_unit_of_quasiFinite_mvPolynomial`: `H^i(ω^•_{A/R})`
  vanishes for `i ≠ -d`.
* `Dualizing.flat_homology_upperShriekFunctor_unit_of_quasiFinite_mvPolynomial`:
  `H^{-d}(ω^•_{A/R})` is flat over `R`.
* `StacksDraft.TorAmplitude.flat_homology_of_hasTorAmplitudeCanonical`: an object of `D(R)` of Tor
  amplitude in `[a, b]` with cohomology only in degree `a` has a flat cohomology module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace StacksDraft.TorAmplitude

/-- **A module of Tor amplitude in `[0, c]` is flat.** Read on a projective resolution `P` of `N`,
the cokernel of `P^{-1} → P^0` is flat by [Stacks, Tag 0653], and that cokernel is `N`. -/
theorem flat_of_hasTorAmplitudeCanonical_single {R : Type u} [CommRing R] (N : ModuleCat.{u} R)
    (c : ℤ)
    (h : HasTorAmplitudeCanonical R ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)
      0 c) :
    Module.Flat R N := by
  let P := FaithfullyFlat.projResComplex N
  have hPle : P.IsStrictlyLE 0 := by
    show CochainComplex.IsStrictlyLE
      ((CategoryTheory.ProjectiveResolution.of N).complex.extend
        ComplexShape.embeddingDownNat) 0
    infer_instance
  have hPbound : BoundedAbove P :=
    ⟨0, fun i hi => CochainComplex.isZero_of_isStrictlyLE P 0 i hi⟩
  let q : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N :=
    (CategoryTheory.ProjectiveResolution.of N).π'
  have hq : QuasiIso q := by
    dsimp [q]
    show QuasiIso
      (HomologicalComplex.extendMap (CategoryTheory.ProjectiveResolution.of N).π
        ComplexShape.embeddingDownNat ≫ _)
    have hπ' : QuasiIso (HomologicalComplex.extendMap
        (CategoryTheory.ProjectiveResolution.of N).π ComplexShape.embeddingDownNat) :=
      (HomologicalComplex.quasiIso_extendMap_iff _ _).2
        (CategoryTheory.ProjectiveResolution.quasiIso _)
    infer_instance
  let eQ : DerivedCategory.Q.obj P ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N :=
    asIso (DerivedCategory.Q.map q) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app N).symm
  have hP : HasTorAmplitude
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
      (canonicalTensorComparison R) (canonicalTensorIsLeftDerived R)
      (DerivedCategory.Q.obj P) 0 c :=
    (hasTorAmplitude_iff_hasFlatRepresentative (canonicalTensorComparison R)
      (canonicalTensorIsLeftDerived R) _ 0 c).2
      ((hasTorAmplitudeCanonical_iff_hasFlatRepresentative R _ 0 c).1
        (AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso eQ.symm 0 c h))
  have hcok := cokernel_flat_of_torAmplitude.{u, u} P 0 c hPbound
    (FaithfullyFlat.projResComplex_flat_X N) hP
  have : QuasiIsoAt q 0 := inferInstance
  let e : (cokernel (P.d (0 - 1) 0) : ModuleCat.{u} R) ≅ N :=
    (IsColimit.coconePointUniqueUpToIso (P.opcyclesIsCokernel (0 - 1) 0 (by simp))
        (colimit.isColimit _)).symm ≪≫
      (P.isoHomologyι 0 1 (by simp)
        ((CochainComplex.isZero_of_isStrictlyLE P 0 1 (by norm_num)).eq_of_tgt _ _)).symm ≪≫
      asIso (HomologicalComplex.homologyMap q 0) ≪≫
      HomologicalComplex.singleObjHomologySelfIso _ 0 N
  exact Module.Flat.of_linearEquiv e.symm.toLinearEquiv

/-- **A Tor amplitude bound on an object concentrated in its lowest degree makes its cohomology
flat.** If `K ∈ D(R)` has Tor amplitude in `[a, b]` and `H^i(K) = 0` for `i ≠ a`, then `H^a(K)` is
flat: `K⟦a⟧` is `H^a(K)` placed in degree zero, of Tor amplitude in `[0, b - a]`. -/
theorem flat_homology_of_hasTorAmplitudeCanonical {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) (hK : HasTorAmplitudeCanonical R K a b)
    (hz : ∀ i : ℤ, i ≠ a → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K)) :
    Module.Flat R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) a).obj K) := by
  let L := K⟦a⟧
  have hzL :
      ∀ i : ℤ, i ≠ 0 → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj L) :=
    fun i hi => (hz (i + a) (by omega)).of_iso (Dualizing.homologyShiftObjIso K i a)
  have : L.IsGE 0 := (DerivedCategory.isGE_iff L 0).2 fun i hi => hzL i (by omega)
  have : L.IsLE 0 := (DerivedCategory.isLE_iff L 0).2 fun i hi => hzL i (by omega)
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE L 0
  have hL : HasTorAmplitudeCanonical R L 0 (b - a) := by
    simpa using hasTorAmplitudeCanonical_shift K a b a hK
  have hM : HasTorAmplitudeCanonical R
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) 0 (b - a) :=
    AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e 0 (b - a) hL
  have hflat := flat_of_hasTorAmplitudeCanonical_single M (b - a) hM
  let eH : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) a).obj K ≅ M :=
    (eqToIso (congrArg (fun n => (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj K)
        (zero_add a))).symm ≪≫ (Dualizing.homologyShiftObjIso K 0 a).symm ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).app M
  exact Module.Flat.of_linearEquiv eH.toLinearEquiv

end StacksDraft.TorAmplitude

namespace Dualizing

variable {R A : Type u} [CommRing R] [IsNoetherianRing R] [CommRing A] [IsNoetherianRing A]

omit [IsNoetherianRing A] in
/-- The fibres of a quasi-finite homomorphism `P → A` have dimension zero at every prime. -/
private theorem relativeDimensionAt_le_zero_of_quasiFinite {P : Type u} [CommRing P]
    (θ : P →+* A) (hft : θ.FiniteType) (hqf : θ.QuasiFinite) (q : PrimeSpectrum A) :
    letI := θ.toAlgebra
    Algebra.relativeDimensionAt P q.asIdeal ≤ ((0 : ℕ) : WithBot ℕ∞) := by
  let := θ.toAlgebra
  have : Algebra.FiniteType P A := hft
  let e := MvPolynomial.isEmptyAlgEquiv P (Fin 0)
  let φ : MvPolynomial (Fin 0) P →ₐ[P] A := (Algebra.ofId P A).comp e.toAlgHom
  have hle : Algebra.relativeDimension P A ≤ ((0 : ℕ) : WithBot ℕ∞) :=
    (Algebra.relativeDimension_le_iff_exists_quasiFinite_mvPolynomial 0).2
      ⟨φ, hft.comp (RingHom.FiniteType.of_surjective _ e.surjective),
        hqf.comp (RingHom.QuasiFinite.of_finite (RingHom.Finite.of_surjective _ e.surjective))⟩
  exact (le_iSup (fun Q : PrimeSpectrum A => Algebra.relativeDimensionAt P Q.asIdeal) q).trans hle

/-- **The relative dualizing complex of an algebra flat and quasi-finite over a polynomial
algebra is concentrated in degree `-d`.** Let `a : R → A` be a homomorphism of Noetherian rings,
presented by `p`, which factors as `R → P = R[x_1, …, x_d] → A` through a flat quasi-finite
`θ : P → A`. Then `H^i(ω^•_{A/R}) = 0` for every `i ≠ -d`. -/
theorem isZero_homology_upperShriekFunctor_unit_of_quasiFinite_mvPolynomial {a : R →+* A}
    (p : PolynomialPresentation a) (d : ℕ) (θ : MvPolynomial (Fin d) R →+* A)
    (hθ : θ.comp MvPolynomial.C = a) (hqf : θ.QuasiFinite) (hfl : θ.Flat) (i : ℤ)
    (hi : i ≠ -(d : ℤ)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (p.upperShriekFunctor.{u, 0}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) := by
  subst hθ
  let P := MvPolynomial (Fin d) R
  have hft : θ.FiniteType := RingHom.FiniteType.of_comp_finiteType p.finiteType
  obtain ⟨q⟩ := nonempty_polynomialPresentation θ hft
  obtain ⟨τ, hτ⟩ := PolynomialPresentation.exists_upperShriekComp_of_finiteType.{u, 0}
    (PolynomialPresentation.mvPolynomial R d) q p
  let K := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)
  have hK : DerivedCategoryB.IsBoundedBelow K :=
    ⟨0, fun n hn => DerivedCategory.isZero_of_isGE (C := ModuleCat.{u} R) K 0 n hn⟩
  have := hτ K hK
  let L := (DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj (ModuleCat.of P P)
  -- `q^!` commutes with the shift
  let : (derivedHom.{u, 0, u} q.toRingHom).CommShift ℤ :=
    (nonempty_commShift_derivedHom.{u, 0} q.toRingHom).some
  have : q.derivedExtension.{u, 0}.CommShift ℤ := by
    unfold PolynomialPresentation.derivedExtension
    infer_instance
  let eShift : q.upperShriekFunctor.{u, 0}.obj (L⟦(d : ℤ)⟧) ≅
      (q.upperShriekFunctor.{u, 0}.obj L)⟦(d : ℤ)⟧ :=
    (shiftFunctor _ (q.variableCount : ℤ)).mapIso
        ((derivedHom.{u, 0, u} q.toRingHom).mapIso
            ((q.derivedExtension.{u, 0}.commShiftIso (d : ℤ)).app L) ≪≫
          ((derivedHom.{u, 0, u} q.toRingHom).commShiftIso (d : ℤ)).app _) ≪≫
      (shiftFunctorComm _ (d : ℤ) (q.variableCount : ℤ)).app _
  let e : p.upperShriekFunctor.{u, 0}.obj K ≅ (q.upperShriekFunctor.{u, 0}.obj L)⟦(d : ℤ)⟧ :=
    (asIso (τ.app K)).symm ≪≫
      q.upperShriekFunctor.{u, 0}.mapIso
        (PolynomialPresentation.mvPolynomialUpperShriekUnitIso R d) ≪≫ eShift
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso e ≪≫
    homologyShiftObjIso _ i (d : ℤ))
  let := θ.toAlgebra
  have : Module.Flat P A := hfl
  exact isZero_homology_upperShriekFunctor_unit_of_notMem_Icc (R := P) q 0
    (relativeDimensionAt_le_zero_of_quasiFinite θ hft hqf) (i + d)
    (fun h => hi (by simp only [Set.mem_Icc, CharP.cast_eq_zero, neg_zero] at h; omega))

/-- **The surviving cohomology module is flat over the base.** In the situation of
`Dualizing.isZero_homology_upperShriekFunctor_unit_of_quasiFinite_mvPolynomial`,
`H^{-d}(ω^•_{A/R})` is a flat `R`-module: `ω^•_{A/R}` has Tor amplitude in `[-d, 0]` over `R` by
[Stacks, Tag 0E9Q], the fibres of `R → A` having dimension at most `d`, and its cohomology is
concentrated in the lowest degree of that interval. -/
theorem flat_homology_upperShriekFunctor_unit_of_quasiFinite_mvPolynomial {a : R →+* A}
    (p : PolynomialPresentation a) (d : ℕ) (θ : MvPolynomial (Fin d) R →+* A)
    (hθ : θ.comp MvPolynomial.C = a) (hqf : θ.QuasiFinite) (hfl : θ.Flat) :
    Module.Flat R ((ModuleCat.restrictScalars a).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))))) := by
  have hz := isZero_homology_upperShriekFunctor_unit_of_quasiFinite_mvPolynomial p d θ hθ hqf hfl
  subst hθ
  let := (θ.comp MvPolynomial.C).toAlgebra
  have : Module.Flat R A :=
    RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr inferInstance) hfl
  let φ : MvPolynomial (Fin d) R →ₐ[R] A := { θ with commutes' := fun _ => rfl }
  have hamp := upperShriekFunctor_hasTorAmplitude_of_fiber_dimension_le p d
    (AlgebraicGeometry.forall_topologicalKrullDim_fiber_le_of_quasiFinite_mvPolynomial d φ hqf)
  let F := ModuleCat.restrictScalars.{u} (θ.comp MvPolynomial.C)
  let ω := p.upperShriekFunctor.{u, 0}.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))
  let eH := fun i : ℤ =>
    (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso F i).app ω
  have hflat := StacksDraft.TorAmplitude.flat_homology_of_hasTorAmplitudeCanonical
    (F.mapDerivedCategory.obj ω) (-(d : ℤ)) 0
    ((StacksDraft.TorAmplitude.hasTorAmplitudeIn_canonicalCertified_iff R _ _ _).1 hamp)
    (fun i hi => (F.map_isZero (hz i hi)).of_iso (eH i))
  exact @Module.Flat.of_linearEquiv R _ _ _ _ _ _ _ hflat (eH (-(d : ℤ))).symm.toLinearEquiv

end Dualizing
