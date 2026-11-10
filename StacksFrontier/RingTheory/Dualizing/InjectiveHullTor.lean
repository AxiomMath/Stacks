module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Algebra.Homology.SpectralSequence.Tor
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.Homology.KFlat.ProjectiveResolution
public import StacksFrontier.Homology.TensorComplex.SingleTensor
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Homology.Tor.DerivedTensorTor
public import StacksFrontier.RingTheory.Dualizing.CohenMacaulayConcentration
public import StacksFrontier.RingTheory.Dualizing.GorensteinCohenMacaulay
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.NormalizedDualizingComplex
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.RightAdjoint
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift
public import StacksFrontier.RingTheory.Dualizing.PowerTorsionComparison
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Normalized
public import StacksFrontier.RingTheory.LocalCohomology.CechFormula.TensorCompatibility
public import StacksFrontier.Homology.Tor.DerivedTensorTor

/-!
# Tor of an injective hull of the residue field over a Gorenstein local ring

Let `(A, 𝔪, κ)` be a Noetherian local Gorenstein ring of dimension `d` and let `E` be an
injective hull of `κ`. Then `Tor_i^A(E, κ)` vanishes for `i ≠ d`, and `Tor_d^A(E, κ) ≅ κ`.

The argument is the source's. Because `A` is Gorenstein, `A[0]` is a dualizing complex, and the
shift that normalizes it is `A[d] = A[0]⟦d⟧`: a shift of `A[0]` has its cohomology in a single
degree, and [stacks 0DW8] together with [stacks 0AWS] force that degree to be `-d`. By
[stacks 0A82] the local cohomology `RΓ_𝔪(A[d])` is `E[0]`, so by [stacks 0ALY], which moves local
cohomology across a derived tensor product,
`E[0] ⊗^L_A κ[0] = RΓ_𝔪(A[d]) ⊗^L_A κ[0] = RΓ_𝔪(A[d] ⊗^L_A κ[0]) = RΓ_𝔪(κ[d]) = κ[d]`,
the last step because `κ` is `𝔪`-power torsion. Reading cohomology in degree `-i` and comparing
the canonical derived tensor product with a projective resolution of `E` turns the left-hand side
into `Tor_i^A(E, κ)` and the right-hand side into `κ` for `i = d` and `0` otherwise.

## Main results

* `Dualizing.LocalDuality.isZero_tor_injectiveHull_residueField_of_ne_dimension` — the vanishing
  for `i ≠ d`.
* `Dualizing.LocalDuality.tor_injectiveHull_residueField_iso_of_eq_dimension` — the
  identification of `Tor_d^A(E, κ)` with `κ`.

## Implementation notes

`Tor` is Mathlib's monoidal `CategoryTheory.Tor` on `ModuleCat A`, derived in the second
variable, so `Tor_i^A(E, κ)` is `((Tor (ModuleCat A) i).obj E).obj κ`. An injective hull of `κ`
is an arbitrary essential monomorphism `j : κ ⟶ E` with `E` injective, that is
`Module.IsInjectiveHull j` ([stacks 08Y2]); all hulls are isomorphic, so the conclusion does not
depend on the choice.
The dimension enters as a natural number `d` with `ringKrullDim A = d`, as in
[stacks 0AWS].

## References

* [Stacks Project, Tag 0EBT](https://stacks.math.columbia.edu/tag/0EBT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing.LocalDuality

open Stacks.DerivedTensor (tensorResolutionHomologyIso torIsoOfKFlatResolution)

/-! ### The normalizing shift of a Gorenstein local ring -/

/-- For a Noetherian local Gorenstein ring `A` of dimension `d`, the complex `A[d] = A[0]⟦d⟧` is
a normalized dualizing complex. -/
theorem isNormalizedDualizingComplex_single_shift_of_isGorensteinLocalRing
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : IsGorensteinLocalRing A) (d : ℕ) (hdim : ringKrullDim A = (d : WithBot ℕ∞)) :
    IsNormalizedDualizingComplex.{u, 0}
      (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))⟦(d : ℤ)⟧) := by
  set U : DerivedCategory (ModuleCat.{u} A) :=
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) with hU
  obtain ⟨m, hm⟩ := exists_isNormalizedDualizingComplex_shift.{u, 0} U hA
  have hmd : m = -(d : ℤ) := by
    by_contra hne
    have h13 : IsCohenMacaulayLocalRing A ↔
        Nonempty ((U⟦-m⟧) ≅
          (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj (U⟦-m⟧))) := by
      have hheight : (IsLocalRing.maximalIdeal A : Ideal A).height = (d : ℕ∞) := by
        have hcast : ((IsLocalRing.maximalIdeal A : Ideal A).height : WithBot ℕ∞) =
            (d : WithBot ℕ∞) := by
          rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hdim]
        exact_mod_cast hcast
      have hld : localRingDimension A = d := by
        change (IsLocalRing.maximalIdeal A : Ideal A).height.toNat = d
        rw [hheight]
        simp
      have h' : IsCohenMacaulayLocalRing A ↔
          Nonempty ((U⟦-m⟧) ≅
            (DerivedCategory.singleFunctor (ModuleCat.{u} A)
                (-(localRingDimension A : ℤ))).obj
              ((DerivedCategory.homologyFunctor (ModuleCat.{u} A)
                (-(localRingDimension A : ℤ))).obj (U⟦-m⟧))) :=
        (isCohenMacaulay_tfae_dualizingComplex (U⟦-m⟧) hm).out 1 3
      rw [hld] at h'
      exact h'
    have hzero := isZero_homology_of_iso_single.{u, 0} (U⟦-m⟧) (-(d : ℤ)) _
      (h13.mp (IsGorensteinLocalRing.isCohenMacaulayLocalRing A hA)) m hne
    have hnt : Nontrivial ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) m).obj (U⟦-m⟧)) := by
      have eU : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj U ≅
          ModuleCat.of A A := by
        rw [hU]
        exact (DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat.{u} A) 0).app (ModuleCat.of A A)
      have eU' : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-m + m)).obj U ≅
          ModuleCat.of A A := by
        rw [show -m + m = (0 : ℤ) from by omega]
        exact eU
      refine ((homologyShiftIso.{u} U (-m) m).trans
        eU').toLinearEquiv.toEquiv.nontrivial_congr.mpr ?_
      exact inferInstanceAs (Nontrivial A)
    exact (not_nontrivial_iff_subsingleton.mpr
      (ModuleCat.isZero_iff_subsingleton.mp hzero)) hnt
  have hneg : -m = (d : ℤ) := by omega
  rw [hneg] at hm
  exact hm

/-! ### The injective hull as the local cohomology of `A[d]` -/

/-- Precomposing an injective hull with an isomorphism is again an injective hull. -/
private theorem isInjectiveHull_precompIso
    {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    {M M' I : 𝒜} (e : M' ≅ M) (i : M ⟶ I) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    Module.IsInjectiveHull (e.hom ≫ i) := by
  let : Mono (e.hom ≫ i) := inferInstance
  refine ⟨hi.1, ?_⟩
  intro X hX
  have hsub : Subobject.mk (e.hom ≫ i) = Subobject.mk i :=
    Subobject.mk_eq_mk_of_comm _ _ e (by simp)
  rw [hsub]
  exact hi.2 X hX

/-- For a Noetherian local Gorenstein ring `A` of dimension `d` and `E` any injective hull of the
residue field, the local cohomology `RΓ_𝔪(A[d])` is isomorphic to `E[0]`. -/
theorem nonempty_localCohomology_iso_single_injectiveHull
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : IsGorensteinLocalRing A) (d : ℕ) (hdim : ringKrullDim A = (d : WithBot ℕ∞))
    (E : ModuleCat.{u} A)
    (j : ModuleCat.of A (IsLocalRing.ResidueField A) ⟶ E) [Mono j]
    (hj : Module.IsInjectiveHull j) :
    Nonempty ((derivedPowerTorsionProperty A (IsLocalRing.maximalIdeal A)
          (IsNoetherian.noetherian (IsLocalRing.maximalIdeal A))).ι.obj
        ((localCohomologyFunctor A (IsLocalRing.maximalIdeal A)
          (IsNoetherian.noetherian (IsLocalRing.maximalIdeal A))).obj
          (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A A))⟦(d : ℤ)⟧)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj E) := by
  have hK := isNormalizedDualizingComplex_single_shift_of_isGorensteinLocalRing A hA d hdim
  let eM : (ModuleCat.uliftFunctor.{0} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ≅
      ModuleCat.of A (IsLocalRing.ResidueField A) :=
    (ULift.moduleEquiv : ULift.{0} (IsLocalRing.ResidueField A) ≃ₗ[A]
      IsLocalRing.ResidueField A).toModuleIso
  obtain ⟨i, hi, hHull⟩ :=
    exists_isInjectiveHull_homology_zero_localCohomology A _ hK
  let : Mono i := hi
  obtain ⟨e⟩ := Module.exists_iso_of_isInjectiveHull i (eM.hom ≫ j) hHull
    (isInjectiveHull_precompIso eM j hj)
  obtain ⟨eL⟩ := nonempty_localCohomology_iso_single_homology_zero.{u, 0} A _ hK
  exact ⟨eL ≪≫ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso e⟩

/-! ### Moving local cohomology across the derived tensor product -/

/-- If local cohomology acts as the identity on `L`, then it may be moved from the second to
the first factor of a derived tensor product with `L`. -/
private def localCohomology_tensor_iso_of_iso
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (K L : DerivedCategory (ModuleCat.{u} A))
    (eL : (Stacks.LocalCohomology.CechFormula.localCohomologyEndofunctor A I hI).obj L ≅ L) :
    (Stacks.LocalCohomology.CechFormula.derivedTensorProductBifunctor A).obj
        ((Stacks.LocalCohomology.CechFormula.localCohomologyEndofunctor A I hI).obj K, L) ≅
      (Stacks.LocalCohomology.CechFormula.derivedTensorProductBifunctor A).obj (K, L) := by
  let T := Stacks.LocalCohomology.CechFormula.derivedTensorProductBifunctor A
  exact ((Stacks.LocalCohomology.CechFormula.localCohomology_derivedTensorProduct_left
    A I hI).app (K, L)).symm ≪≫ T.mapIso (Iso.prod (Iso.refl K) eL)

/-! ### A projective-resolution model for `Tor` in the derived category -/

/-- **The derived tensor product computes `Tor`.** The degree `-i` cohomology of
`E[0] ⊗^L_A κ[0]` is `Tor_i^A(E, κ)`. -/
private def torDerivedTensorHomologyIso
    (A : Type u) [CommRing A] (E κ : ModuleCat.{u} A) (i : ℕ) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(i : ℤ))).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor A).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj E)).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj κ))) ≅
      (((Tor (ModuleCat.{u} A) i).obj E).obj κ) := by
  let Q := ProjectiveResolution.of E
  let P := Q.cochainComplex
  let E₀ := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj E
  let κ₀ := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj κ
  let : QuasiIso Q.π' := inferInstance
  let : P.IsStrictlyLE 0 := inferInstance
  have hP : P.KFlat := _root_.CochainComplex.KFlat.kFlat_projectiveResolution Q
  have hbounded : ∃ n : ℤ, ∀ j : ℤ, n < j → IsZero (P.X j) :=
    ⟨0, fun j hj => CochainComplex.isZero_of_isStrictlyLE P 0 j hj⟩
  have hflat : ∀ j : ℤ, Module.Flat A (P.X j) := by
    intro j
    have : Module.Projective A (P.X j) := ModuleCat.projective_of_module_projective _
    infer_instance
  let eP : DerivedCategory.Q.obj P ≅ E₀ := asIso (DerivedCategory.Q.map Q.π')
  let B := Stacks.LocalCohomology.CechFormula.derivedTensorProductBifunctor A
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(i : ℤ))
  let eComparison := StacksDraft.TorAmplitude.certifiedTensorHomologyIsoOfFlat
    (StacksDraft.TorAmplitude.canonicalTensorComparison A)
    (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived A)
    P hbounded hflat κ (-(i : ℤ))
  let eFlip := (NatIso.mapHomologicalComplex
    (BraidedCategory.tensorLeftIsoTensorRight κ) (ComplexShape.up ℤ)).app P
  let eTor := Stacks.DerivedTensor.torIsoOfKFlatResolution Q.π' hP κ (i : ℤ)
  have eTor' :
      (((tensorLeft κ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homology (-(i : ℤ)) ≅
        (((Tor (ModuleCat.{u} A) i).obj E).obj κ) := by
    change (((tensorLeft κ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homology
        (-(i : ℤ)) ≅
      ((((CochainComplex.Tor.moduleTensorBifunctor A).obj E).leftDerived i).obj κ)
    simpa only [P, CochainComplex.Tor.TorInDegree,
      dite_eq_left (show 0 ≤ (i : ℤ) by omega),
      Int.toNat_natCast] using eTor
  exact (H.mapIso (B.mapIso (Iso.prod eP (Iso.refl κ₀)))).symm ≪≫ eComparison ≪≫
    HomologicalComplex.homologyMapIso eFlip.symm (-(i : ℤ)) ≪≫ eTor'

/-! ### The residue field is power torsion -/

private theorem residueField_isIPowerTorsion (A : Type u) [CommRing A] [IsLocalRing A] :
    IsIPowerTorsion A (IsLocalRing.ResidueField A) (IsLocalRing.maximalIdeal A) := by
  intro x
  refine ⟨1, Nat.zero_lt_one, ?_⟩
  intro a ha
  have ham : a ∈ IsLocalRing.maximalIdeal A := by simpa using ha
  have hres : IsLocalRing.residue A a = 0 :=
    IsLocalRing.residue_eq_zero_iff a |>.2 ham
  change IsLocalRing.residue A a * x = 0
  simp [hres]

/-- A shifted single complex has zero cohomology away from the shift degree. -/
private theorem isZero_homology_single_of_ne
    (A : Type u) [CommRing A] (M : ModuleCat.{u} A) (n i : ℤ) (hi : i ≠ n) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj M)) := by
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · exact DerivedCategory.isZero_of_isGE _ n i hlt
  · exact DerivedCategory.isZero_of_isLE _ n i hgt

private theorem residueField_derivedPowerTorsion
    (A : Type u) [CommRing A] [IsLocalRing A] (hm : (IsLocalRing.maximalIdeal A).FG) :
    derivedPowerTorsionProperty A (IsLocalRing.maximalIdeal A) hm
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (IsLocalRing.ResidueField A))) := by
  intro i
  by_cases hi : i = 0
  · subst i
    let e := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 0).app
      (ModuleCat.of A (IsLocalRing.ResidueField A))
    change IsIPowerTorsion A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (IsLocalRing.ResidueField A))))
      (IsLocalRing.maximalIdeal A)
    exact (powerTorsionModuleProperty A (IsLocalRing.maximalIdeal A) hm).prop_of_iso e.symm
      (residueField_isIPowerTorsion A)
  · let K := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A))
    change IsIPowerTorsion A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)
      (IsLocalRing.maximalIdeal A)
    have hsub : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) :=
      ModuleCat.isZero_iff_subsingleton.mp
        (isZero_homology_single_of_ne A (ModuleCat.of A (IsLocalRing.ResidueField A)) 0 i hi)
    intro x
    refine ⟨1, Nat.zero_lt_one, fun a _ => ?_⟩
    simp [hsub.elim x 0]

/-- Local cohomology is the identity on a complex with power-torsion cohomology: the counit of
the coreflection is invertible there. -/
private def localCohomology_iso_of_powerTorsion
    (A : Type u) [CommRing A] (m : Ideal A) (hm : m.FG)
    (L : DerivedCategory (ModuleCat.{u} A))
    (hL : derivedPowerTorsionProperty A m hm L) :
    (Stacks.LocalCohomology.CechFormula.localCohomologyEndofunctor A m hm).obj L ≅ L := by
  let P := derivedPowerTorsionProperty A m hm
  let adj := localCohomologyAdjunction A m hm
  have hiso : IsIso (adj.counit.app L) :=
    isIso_localCohomologyAdjunction_counit A m hm ⟨L, hL⟩
  change (P.ι.obj ((localCohomologyFunctor A m hm).obj L)) ≅ L
  exact @asIso _ _ _ _ (adj.counit.app L) hiso

/-- `A[d] ⊗^L_A κ[0] ≅ κ[d]`: the dualizing complex of a Gorenstein ring is a shift of the
tensor unit, and tensoring with the unit is the identity. -/
private def dualizingTensorResidueFieldIso
    (A : Type u) [CommRing A] [IsLocalRing A] (d : ℕ) :
    (Stacks.LocalCohomology.CechFormula.derivedTensorProductBifunctor A).obj
        ((((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A A))⟦(d : ℤ)⟧),
         (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (IsLocalRing.ResidueField A))) ≅
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (IsLocalRing.ResidueField A)))⟦(d : ℤ)⟧ := by
  let S := CochainComplex.DerivedTensor.canonicalSymmetricDerivedTensorProduct A
  let T := S.tensorProduct
  let K := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  let κ := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
    (ModuleCat.of A (IsLocalRing.ResidueField A))
  let : (T.tensor.flip.obj κ).CommShift ℤ := T.commShift_left κ
  let eShift := ((T.tensor.flip.obj κ).commShiftIso (d : ℤ)).app K
  let eUnit := ((S.braiding.iso.app K).app κ) ≪≫ T.rightUnitor.app κ
  change ((T.tensor.flip.obj κ).obj (K⟦(d : ℤ)⟧)) ≅ κ⟦(d : ℤ)⟧
  exact eShift ≪≫ (shiftFunctor _ (d : ℤ)).mapIso eUnit

/-- For a Noetherian local Gorenstein ring `A` of dimension `d` with residue field `κ` and `E` an
injective hull of `κ`, there is an isomorphism `E[0] ⊗^L_A κ[0] ≅ κ[d]`. -/
theorem nonempty_injectiveHull_derivedTensor_residueField_iso
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : IsGorensteinLocalRing A) (d : ℕ) (hdim : ringKrullDim A = (d : WithBot ℕ∞))
    (E : ModuleCat.{u} A)
    (j : ModuleCat.of A (IsLocalRing.ResidueField A) ⟶ E) [Mono j]
    (hj : Module.IsInjectiveHull j) :
    Nonempty ((Stacks.LocalCohomology.CechFormula.derivedTensorProductBifunctor A).obj
        (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj E),
         ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
           (ModuleCat.of A (IsLocalRing.ResidueField A)))) ≅
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (IsLocalRing.ResidueField A)))⟦(d : ℤ)⟧) := by
  let K := ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
    (ModuleCat.of A A))⟦(d : ℤ)⟧
  let κ := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
    (ModuleCat.of A (IsLocalRing.ResidueField A))
  let E₀ := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj E
  let m := IsLocalRing.maximalIdeal A
  have hm : m.FG := IsNoetherian.noetherian m
  obtain ⟨eHull⟩ := nonempty_localCohomology_iso_single_injectiveHull A hA d hdim E j hj
  have eκ : (Stacks.LocalCohomology.CechFormula.localCohomologyEndofunctor A m hm).obj κ ≅ κ :=
    localCohomology_iso_of_powerTorsion A m hm κ (residueField_derivedPowerTorsion A hm)
  exact ⟨(Stacks.LocalCohomology.CechFormula.derivedTensorProductBifunctor A).mapIso
      (Iso.prod eHull (Iso.refl κ)).symm ≪≫
    localCohomology_tensor_iso_of_iso A m hm K κ eκ ≪≫ dualizingTensorResidueFieldIso A d⟩

/-! ### Tor of the injective hull with the residue field -/

/-- Given `E[0] ⊗^L_A κ[0] ≅ κ[d]`, the group `Tor_i^A(E, κ)` is the degree `-i` cohomology of
`κ[-d]`. -/
private def torIsoHomologySingle
    (A : Type u) [CommRing A] [IsLocalRing A] (d : ℕ) (E : ModuleCat.{u} A)
    (eTensor : (Stacks.LocalCohomology.CechFormula.derivedTensorProductBifunctor A).obj
        (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj E),
         ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
           (ModuleCat.of A (IsLocalRing.ResidueField A)))) ≅
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (IsLocalRing.ResidueField A)))⟦(d : ℤ)⟧) (i : ℕ) :
    (((Tor (ModuleCat.{u} A) i).obj E).obj (ModuleCat.of A (IsLocalRing.ResidueField A))) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(i : ℤ))).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj
          (ModuleCat.of A (IsLocalRing.ResidueField A))) :=
  (torDerivedTensorHomologyIso A E _ i).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(i : ℤ))).mapIso eTensor ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(i : ℤ))).mapIso
      (((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso
        (d : ℤ) (-(d : ℤ)) 0 (by omega)).app _)

/-- For `(A, 𝔪, κ)` a Noetherian local Gorenstein ring of dimension `d` and `E` an injective hull
of `κ`, the group `Tor_i^A(E, κ)` vanishes for every `i ≠ d`. -/
@[stacks 0EBT "vanishing away from the dimension"]
theorem isZero_tor_injectiveHull_residueField_of_ne_dimension
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : IsGorensteinLocalRing A) (d : ℕ) (hdim : ringKrullDim A = (d : WithBot ℕ∞))
    (E : ModuleCat.{u} A)
    (j : ModuleCat.of A (IsLocalRing.ResidueField A) ⟶ E) [Mono j]
    (hj : Module.IsInjectiveHull j) (i : ℕ) (hi : i ≠ d) :
    IsZero (((Tor (ModuleCat.{u} A) i).obj E).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A))) := by
  obtain ⟨eTensor⟩ := nonempty_injectiveHull_derivedTensor_residueField_iso A hA d hdim E j hj
  exact IsZero.of_iso
    (isZero_homology_single_of_ne A _ (-(d : ℤ)) (-(i : ℤ)) (by omega))
    (torIsoHomologySingle A d E eTensor i)

/-- For `(A, 𝔪, κ)` a Noetherian local Gorenstein ring of dimension `d` and `E` an injective hull
of `κ`, the group `Tor_d^A(E, κ)` is isomorphic to `κ`. -/
@[stacks 0EBT "the Tor group in the dimension"]
theorem tor_injectiveHull_residueField_iso_of_eq_dimension
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : IsGorensteinLocalRing A) (d : ℕ) (hdim : ringKrullDim A = (d : WithBot ℕ∞))
    (E : ModuleCat.{u} A)
    (j : ModuleCat.of A (IsLocalRing.ResidueField A) ⟶ E) [Mono j]
    (hj : Module.IsInjectiveHull j) :
    Nonempty ((((Tor (ModuleCat.{u} A) d).obj E).obj
        (ModuleCat.of A (IsLocalRing.ResidueField A))) ≅
      ModuleCat.of A (IsLocalRing.ResidueField A)) := by
  obtain ⟨eTensor⟩ := nonempty_injectiveHull_derivedTensor_residueField_iso A hA d hdim E j hj
  exact ⟨torIsoHomologySingle A d E eTensor d ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) (-(d : ℤ))).app _⟩

end Dualizing.LocalDuality

end
