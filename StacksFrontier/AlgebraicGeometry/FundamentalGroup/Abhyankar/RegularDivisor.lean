module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.RegularComplementFacts
public import StacksFrontier.AlgebraicGeometry.CartierAffineLocalConverse.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.AffineChart
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.EtaleLocalDecomposition
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.RegularDivisorExtension
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.CodimensionOneIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Abhyankar's lemma for a regular divisor

Let `X` be a locally Noetherian scheme, `D ⊆ X` an effective Cartier divisor which is a regular
scheme, and `Y ⟶ X ∖ D` a finite étale cover which is tamely ramified over `X` in codimension one.
Then, étale locally on `X`, `Y ⟶ X` is a finite disjoint union of standard tamely ramified
covers `Spec (A[x]/(x^e - φ))_φ ⟶ Spec A_φ` ([Stacks, Tag 0EYF]) with `e` invertible in `A`
([Stacks, Tag 0EYG]).

## Main results

* `AlgebraicGeometry.exists_etale_standardTamelyRamified_of_isTamelyRamifiedInCodimensionOne`:
  Abhyankar's lemma for a regular divisor, granted purity for regular local rings and
  [Stacks, Tag 0EYD].
* `AlgebraicGeometry.Abhyankar.isTamelyRamifiedInCodimensionOne_chart`: the cover stays tamely
  ramified in codimension one after base change to a flat regular local `Γ(X, V)`-algebra.
* `AlgebraicGeometry.Abhyankar.isRegularLocalRing_localization_fromSpec`: the local rings
  `Γ(X, V)_y` and `Γ(X, V)_y/φ` at points of `D` are regular.
* `AlgebraicGeometry.Abhyankar.exists_iso_sigma_standardTamelyRamifiedCover`: a ring
  decomposition of a base change of the cover gives the disjoint union of standard covers.

## References

* [Stacks Project, Tag 0EYG](https://stacks.math.columbia.edu/tag/0EYG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Abhyankar

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-- The complement of `D` meets an affine open `V` with `D(V) = (φ)` in `D(φ)`. -/
lemma fromSpec_preimage_compl_support (V : X.affineOpens) (φ : Γ(X, V.1))
    (hφ : D.ideal V = Ideal.span {φ}) :
    V.2.fromSpec ⁻¹ᵁ (D.support.compl : X.Opens) = PrimeSpectrum.basicOpen φ := by
  ext y
  have hyV : V.2.fromSpec y ∈ V.1 := V.2.range_fromSpec.subset ⟨y, rfl⟩
  show V.2.fromSpec y ∉ D.support ↔ y ∈ PrimeSpectrum.basicOpen φ
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hyV, hφ, Scheme.zeroLocus_span,
    Scheme.zeroLocus_singleton]
  show ¬ V.2.fromSpec y ∉ X.basicOpen φ ↔ _
  rw [not_not, ← SetLike.mem_coe, ← Set.mem_preimage, ← TopologicalSpace.Opens.map_coe]
  exact congrArg (fun W : (Spec Γ(X, V.1)).Opens ↦ y ∈ W) (V.2.fromSpec_preimage_basicOpen φ)
    |>.to_iff

/-- If the closed subscheme `D` is regular, then `Γ(X, V)/D(V)` is a regular ring for every affine
open `V` of the locally Noetherian scheme `X`. -/
lemma isRegularRing_quotient_ideal [IsLocallyNoetherian X]
    (hDreg : ∀ z : D.subscheme, IsRegularLocalRing (D.subscheme.presheaf.stalk z))
    (V : X.affineOpens) : IsRegularRing (Γ(X, V.1) ⧸ D.ideal V) := by
  have : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
  let j := D.subschemeCover.f V
  have : IsOpenImmersion j := D.subschemeCover.map_prop V
  have hreg : IsRegular (Spec (.of (Γ(X, V.1) ⧸ D.ideal V))) := by
    rw [isRegular_iff_regular_stalks]
    exact ⟨inferInstance, fun z ↦ (isRegularLocalRing_stalk_iff_of_isOpenImmersion j z).mpr
      (hDreg (j z))⟩
  have h := (isRegular_iff_isRegularRing_appTop _).mp hreg
  exact IsRegularRing.of_ringEquiv
    (Scheme.ΓSpecIso (.of (Γ(X, V.1) ⧸ D.ideal V))).commRingCatIsoToRingEquiv

/-- The local ring of a prime divisor at its generic point has dimension one. -/
private lemma ringKrullDim_stalk_genericPoint_eq_one {X : Scheme.{u}}
    (Z : StacksDraft.AlgebraicGeometry.Divisors.PrimeDivisorWeilGroup.PrimeDivisor X) :
    ringKrullDim (X.presheaf.stalk Z.genericPoint) = 1 := by
  have hco : Order.coheight Z.genericPoint = 1 :=
    AlgebraicGeometry.PrimeDivisor.coheight_genericPoint
      (⟨Z.idealSheaf, Z.integral, Z.codimension_one⟩ : AlgebraicGeometry.PrimeDivisor X)
  rw [ringKrullDim_stalk_eq_coheight, hco]
  rfl

/-- A regular local ring of a prime divisor at its generic point is a discrete valuation ring. -/
@[ega "IV 21.9.8" "special case"]
lemma exists_isDiscreteValuationRing_stalk_genericPoint {X : Scheme.{u}}
    (Z : StacksDraft.AlgebraicGeometry.Divisors.PrimeDivisorWeilGroup.PrimeDivisor X)
    (h : IsRegularLocalRing (X.presheaf.stalk Z.genericPoint)) :
    ∃ _ : IsDomain (X.presheaf.stalk Z.genericPoint),
      IsDiscreteValuationRing (X.presheaf.stalk Z.genericPoint) := by
  have hT := (Stacks.DiscreteValuationRing.Criteria.solution
    (X.presheaf.stalk Z.genericPoint)).out 3 1
  exact hT.mp ⟨h, ringKrullDim_stalk_genericPoint_eq_one Z⟩

/-- Along a flat map `R → T`, a height one prime of `T` containing the image of a nonzerodivisor
of `R` lies over a height one prime. -/
lemma height_comap_eq_one_of_flat {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [IsNoetherianRing R] [IsNoetherianRing T] [Module.Flat R T] (P : Ideal T) [P.IsPrime]
    (hP : P.height = 1) {a : R} (ha : a ∈ nonZeroDivisors R) (haP : algebraMap R T a ∈ P) :
    (P.comap (algebraMap R T)).height = 1 := by
  let p := P.comap (algebraMap R T)
  have : P.LiesOver p := ⟨rfl⟩
  have hsum := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P
  have hle : p.height ≤ 1 := by
    rw [← hP, hsum]
    exact le_self_add
  have hge : 1 ≤ p.height :=
    (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors ha).trans
      (Ideal.height_mono ((Ideal.span_singleton_le_iff_mem _).mpr haP))
  exact le_antisymm hle hge

/-- The dimension of the local ring of `X` at the image of a point `y` of an affine open `V` is the
height of `y`. -/
lemma ringKrullDim_stalk_fromSpec {X : Scheme.{u}} (V : X.affineOpens)
    (y : Spec Γ(X, V.1)) : ringKrullDim (X.presheaf.stalk (V.2.fromSpec y)) = y.asIdeal.height := by
  exact @IsLocalization.AtPrime.ringKrullDim_eq_height _ _ y.asIdeal _ _ _
    (TopCat.Presheaf.algebra_section_stalk X.presheaf _)
    (V.2.isLocalization_stalk' y (V.2.range_fromSpec.subset ⟨y, rfl⟩))

/-- A point of `Spec T` maps into `X ∖ D` along `Spec T ⟶ V ⊆ X` exactly when it lies in the
basic open of the equation of `D` on `V`. -/
lemma SpecMap_comp_fromSpec_mem_compl_iff (V : X.affineOpens) (φ : Γ(X, V.1))
    (hφ : D.ideal V = Ideal.span {φ}) (T : Type u) [CommRing T] [Algebra Γ(X, V.1) T]
    (y : Spec (.of T)) :
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) T)) ≫ V.2.fromSpec) y ∈
      (D.support.compl : X.Opens) ↔ algebraMap Γ(X, V.1) T φ ∉ y.asIdeal := by
  show Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) T)) y ∈
    V.2.fromSpec ⁻¹ᵁ (D.support.compl : X.Opens) ↔ _
  rw [fromSpec_preimage_compl_support D V φ hφ]
  exact Iff.rfl

open Stacks.FundamentalGroup in
/-- **Tameness of the cover after base change to a regular local ring.** Let `D ⊆ X` be a regular
effective Cartier divisor of a locally Noetherian scheme, cut out by a nonzerodivisor `φ` on an
affine open `V`, and let `f : Y ⟶ X ∖ D` be finite étale and tamely ramified over `X` in
codimension one. For a flat `Γ(X, V)`-algebra `T` which is a regular local ring with `φ ≠ 0` in
`T`, the base change of `f` to `D(φ) ⊆ Spec T` is tamely ramified over `Spec T` in codimension
one. The argument `h0EYD` is [Stacks, Tag 0EYD]. -/
theorem isTamelyRamifiedInCodimensionOne_chart [IsLocallyNoetherian X]
    (h0EYD : ∀ S : CodimensionOnePullbackSetup.{u}, IsTamelyRamifiedInCodimensionOne S.U.ι S.f →
      IsTamelyRamifiedInCodimensionOne (pullback.fst S.g S.U.ι) S.pulledBackCover)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hDreg : ∀ z : D.subscheme, IsRegularLocalRing (D.subscheme.presheaf.stalk z))
    {Y : Scheme.{u}} (f : Y ⟶ (D.support.compl : X.Opens)) [IsFinite f] [Etale f]
    (htame : IsTamelyRamifiedInCodimensionOne (Scheme.Opens.ι (D.support.compl : X.Opens)) f)
    (V : X.affineOpens) (φ : Γ(X, V.1)) (hφ : φ ∈ nonZeroDivisors Γ(X, V.1))
    (hVφ : D.ideal V = Ideal.span {φ})
    (T : Type u) [CommRing T] [Algebra Γ(X, V.1) T] [Module.Flat Γ(X, V.1) T]
    [IsRegularLocalRing T] (hφT : algebraMap Γ(X, V.1) T φ ≠ 0) :
    letI := (Localization.awayMap (algebraMap Γ(X, V.1) T) φ).toAlgebra
    IsTamelyRamifiedInCodimensionOne
      (Scheme.Opens.ι (X := Spec (.of T)) (PrimeSpectrum.basicOpen (algebraMap Γ(X, V.1) T φ)))
      (AffineFieldFactors.coverMap (R := .of T) (algebraMap Γ(X, V.1) T φ)
        (Localization.Away (algebraMap Γ(X, V.1) T φ) ⊗[Localization.Away φ]
          @chartRing _ (D.support.compl : X.Opens) _ V.2.fromSpec V.2.isOpenImmersion_fromSpec φ
            (fromSpec_preimage_compl_support D V φ hVφ) _ f)) := by
  have := V.2.isOpenImmersion_fromSpec
  let := (Localization.awayMap (algebraMap Γ(X, V.1) T) φ).toAlgebra
  have : IsDomain T := IsRegularLocalRing.isDomain T
  have : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
  have hTreg := (IsLocalRing.isRegularRing_tfae (R := T)).out 1 3
  have : IsRegularRing T := hTreg.mp inferInstance
  have hψU := fromSpec_preimage_compl_support D V φ hVφ
  let U : X.Opens := D.support.compl
  let g : Spec (.of T) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) T)) ≫ V.2.fromSpec
  have hrange : Set.range (pullback.fst g U.ι) = {y | algebraMap _ T φ ∉ y.asIdeal} := by
    rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
    ext y
    exact SpecMap_comp_fromSpec_mem_compl_iff D V φ hVφ T y
  have _ : ∀ z : Spec (.of T), z.asIdeal.IsPrime := fun z ↦ z.isPrime
  let _ : ∀ z : Spec (.of T), Algebra T ((Spec (.of T)).presheaf.stalk z) :=
    fun z ↦ StructureSheaf.stalkAlgebra (CommRingCat.of T) z
  have _ : ∀ z : Spec (.of T), IsLocalization.AtPrime ((Spec (.of T)).presheaf.stalk z) z.asIdeal :=
    fun z ↦ StructureSheaf.IsLocalization.to_stalk (CommRingCat.of T) z
  let S : CodimensionOnePullbackSetup.{u} :=
    { X := X
      X' := Spec (.of T)
      locallyNoetherian_X := inferInstance
      locallyNoetherian_X' := inferInstance
      g := g
      U := U
      dense_U := by
        rw [DenseRange, Scheme.Opens.range_ι]
        exact dense_of_isSchemeTheoreticallyDense _
          (Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor D hD)
      Y := Y
      f := f
      finite_f := inferInstance
      etale_f := inferInstance
      dense_U' := by
        show Dense (Set.range (pullback.fst g U.ι))
        rw [hrange]
        refine IsOpen.dense (PrimeSpectrum.basicOpen (algebraMap _ T φ)).isOpen
          ⟨⟨⊥, Ideal.isPrime_bot⟩, fun h ↦ hφT ((Submodule.mem_bot T).mp h)⟩
      dvr_X := fun Z hZ ↦ by
        have hZD : Z.genericPoint ∈ D.support := by
          by_contra h
          exact hZ h
        exact exists_isDiscreteValuationRing_stalk_genericPoint Z
          (isRegularLocalRing_stalk_of_isEffectiveCartierDivisor_of_stalk D hD _ hZD (hDreg _))
      dvr_X' := fun Z _ ↦
        exists_isDiscreteValuationRing_stalk_genericPoint Z
          (IsRegularRing.isRegularLocalRing_of_isLocalization (R := T) Z.genericPoint.asIdeal _)
      maps_boundary := fun Z' hZ' ↦ by
        have hφP : algebraMap _ T φ ∈ Z'.genericPoint.asIdeal := by
          by_contra h
          exact hZ' (hrange ▸ h)
        have hP : Z'.genericPoint.asIdeal.height = 1 := by
          have h1 := IsLocalization.AtPrime.ringKrullDim_eq_height (R := T)
            Z'.genericPoint.asIdeal ((Spec (.of T)).presheaf.stalk Z'.genericPoint)
          rw [ringKrullDim_stalk_genericPoint_eq_one] at h1
          exact_mod_cast h1.symm
        have hp := height_comap_eq_one_of_flat Z'.genericPoint.asIdeal hP hφ hφP
        let y : Spec Γ(X, V.1) :=
          ⟨Z'.genericPoint.asIdeal.comap (algebraMap Γ(X, V.1) T), inferInstance⟩
        have hgy : g Z'.genericPoint = V.2.fromSpec y := rfl
        have h1 : ringKrullDim (X.presheaf.stalk (V.2.fromSpec y)) = 1 := by
          rw [ringKrullDim_stalk_fromSpec, hp]
          rfl
        obtain ⟨Z, hZ⟩ := exists_primeDivisor_genericPoint_eq _ h1
        refine ⟨Z, ?_, hgy.trans hZ.symm⟩
        rw [hZ, ← hgy]
        exact fun h ↦ (SpecMap_comp_fromSpec_mem_compl_iff D V φ hVφ T _).mp h hφP }
  have h1 := isTamelyRamifiedInCodimensionOne_of_isPullback h0EYD S htame _ _
    (isPullback_chartU_comp U V.2.fromSpec φ hψU T) _ _
    (isPullback_chartY_comp U V.2.fromSpec φ hψU T f)
  refine IsTamelyRamifiedInCodimensionOne.of_iso
    (basicOpenIsoSpecAway (R := .of T) (algebraMap Γ(X, V.1) T φ)).symm (Iso.refl _) ?_ ?_ h1
  · rw [Iso.symm_hom, Iso.inv_comp_eq]
    exact (basicOpenIsoSpecAway_hom_SpecMap (R := .of T) _).symm
  · rw [Iso.refl_hom, Category.id_comp]
    rfl

/-- **The local rings at a point of a regular divisor.** If `y ∈ Spec Γ(X, V)` contains the
equation `φ` of `D` on `V`, then `Γ(X, V)_y` and `Γ(X, V)_y/φ` are regular local rings. -/
lemma isRegularLocalRing_localization_fromSpec [IsLocallyNoetherian X]
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hDreg : ∀ z : D.subscheme, IsRegularLocalRing (D.subscheme.presheaf.stalk z))
    (V : X.affineOpens) (φ : Γ(X, V.1)) (hVφ : D.ideal V = Ideal.span {φ})
    (y : Spec Γ(X, V.1)) (hy : φ ∈ y.asIdeal) :
    IsRegularLocalRing (Localization.AtPrime y.asIdeal) ∧
      IsRegularLocalRing (Localization.AtPrime y.asIdeal ⧸
        Ideal.span {algebraMap Γ(X, V.1) (Localization.AtPrime y.asIdeal) φ}) := by
  let x := V.2.fromSpec y
  have hxV : x ∈ V.1 := V.2.range_fromSpec.subset ⟨y, rfl⟩
  have hxD : x ∈ D.support := by
    by_contra h
    have h' : y ∈ V.2.fromSpec ⁻¹ᵁ (D.support.compl : X.Opens) := h
    rw [fromSpec_preimage_compl_support D V φ hVφ] at h'
    exact h' hy
  let : Algebra Γ(X, V.1) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) y.asIdeal := V.2.isLocalization_stalk' y hxV
  let e : Localization.AtPrime y.asIdeal ≃ₐ[Γ(X, V.1)] X.presheaf.stalk x :=
    IsLocalization.algEquiv y.asIdeal.primeCompl _ _
  have hreg := isRegularLocalRing_stalk_of_isEffectiveCartierDivisor_of_stalk D hD x hxD (hDreg _)
  refine ⟨IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv, ?_⟩
  let germ := X.presheaf.germ V.1 x hxV
  have hstalk : IdealSheafData.stalk D x = Ideal.span {germ.hom φ} := by
    rw [IdealSheafData.stalk_eq_map_germ D x V hxV, hVφ, Ideal.map_span, Set.image_singleton]
  let z := IdealSheafData.subschemePoint D x hxD
  let σ : (X.presheaf.stalk x ⧸ Ideal.span {germ.hom φ}) ≃+* D.subscheme.presheaf.stalk z :=
    (Ideal.quotEquivOfEq hstalk.symm).trans (IdealSheafData.subschemeStalkQuotEquiv D z)
  have hmap : Ideal.span {germ.hom φ} =
      (Ideal.span
        {algebraMap Γ(X, V.1) (Localization.AtPrime y.asIdeal) φ}).map e.toRingEquiv := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    exact (e.commutes φ).symm
  have := hDreg z
  exact IsRegularLocalRing.of_ringEquiv ((Ideal.quotientEquiv _ _ e.toRingEquiv hmap).trans σ).symm

/-- `∐ᵢ Spec Kᵢ ⟶ Spec (∏ᵢ Kᵢ)` is an isomorphism for a family indexed by `Fin n`. -/
lemma isIso_sigmaDesc_SpecMap_evalRingHom {n : ℕ} (K : Fin n → CommRingCat.{u}) :
    IsIso (Sigma.desc fun i ↦ Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun i ↦ K i) i))) := by
  let ε : Fin n ≃ ULift.{u} (Fin n) := Equiv.ulift.symm
  let K' : ULift.{u} (Fin n) → CommRingCat.{u} := fun j ↦ K j.down
  let τ : (∀ i, K i) ≃+* (∀ j, K' j) :=
    { toFun := fun x j ↦ x j.down
      invFun := fun y i ↦ y ⟨i⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  have h : (Sigma.desc fun i ↦ Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun i ↦ K i) i))) =
      (Sigma.reindex ε (fun j ↦ Spec (K' j))).hom ≫ sigmaSpec K' ≫
        (Scheme.Spec.mapIso τ.toCommRingCatIso.op).hom := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_desc]
    have := Sigma.ι_reindex_hom_assoc ε (fun j ↦ Spec (K' j)) i
      (sigmaSpec K' ≫ (Scheme.Spec.mapIso τ.toCommRingCatIso.op).hom)
    refine Eq.trans ?_ this.symm
    rw [ι_sigmaSpec_assoc, Functor.mapIso_hom, Iso.op_hom, RingEquiv.toCommRingCatIso_hom]
    exact Spec.map_comp (CommRingCat.ofHom τ.toRingHom)
      (CommRingCat.ofHom (Pi.evalRingHom (fun j ↦ K' j) (ε i)))
  have : Finite (ULift.{u} (Fin n)) := Finite.of_equiv _ ε
  let E : (∐ fun i ↦ Spec (K i)) ≅ Spec (.of (∀ i, K i)) :=
    Sigma.reindex ε (fun j ↦ Spec (K' j)) ≪≫ asIso (sigmaSpec K') ≪≫
      Scheme.Spec.mapIso τ.toCommRingCatIso.op
  rw [show _ = E.hom from h]
  infer_instance

/-- **Assembling the decomposition.** If `Spec C ⟶ Spec A_φ` is a base change of `f` along
`gU` and `C ≅ ∏ᵢ A[x]/(x^{eᵢ} - φ)_φ` over `A_φ`, then `Y ×_U Spec A_φ` is the disjoint union of
the standard tamely ramified covers. -/
lemma exists_iso_sigma_standardTamelyRamifiedCover {A : CommRingCat.{u}} (φ : A) {n : ℕ}
    (e : Fin n → ℕ) {Y U : Scheme.{u}} (f : Y ⟶ U)
    (gU : Spec (.of (Localization.Away φ)) ⟶ U) (C : Type u) [CommRing C]
    [Algebra (Localization.Away φ) C] (top : Spec (.of C) ⟶ Y)
    (hY : IsPullback top (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away φ) C))) f gU)
    (σ : (∀ i, Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A φ (e i)) φ)) ≃+* C)
    (hσ : ∀ r, σ (fun i ↦ Localization.awayMap
      (algebraMap A (standardTamelyRamifiedAlgebra A φ (e i))) φ r) = algebraMap _ C r) :
    ∃ ι : pullback f gU ≅ ∐ fun i ↦ Spec (.of (Localization.Away
        (algebraMap A (standardTamelyRamifiedAlgebra A φ (e i)) φ))),
      ι.hom ≫ Sigma.desc (fun i ↦ standardTamelyRamifiedCover A φ (e i)) = pullback.snd f gU := by
  have := isIso_sigmaDesc_SpecMap_evalRingHom (fun i ↦ CommRingCat.of (Localization.Away
    (algebraMap A (standardTamelyRamifiedAlgebra A φ (e i)) φ)))
  have hdesc : Sigma.desc (fun i ↦ standardTamelyRamifiedCover A φ (e i)) =
      Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun i ↦
        Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A φ (e i)) φ)) i))) ≫
        Spec.map (CommRingCat.ofHom (Pi.ringHom fun i ↦ Localization.awayMap
          (algebraMap A (standardTamelyRamifiedAlgebra A φ (e i))) φ)) := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_desc, Sigma.ι_desc_assoc, ← Spec.map_comp]
    rfl
  refine ⟨hY.isoPullback.symm ≪≫ Scheme.Spec.mapIso σ.toCommRingCatIso.op ≪≫
    (asIso (Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun i ↦
        Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A φ (e i)) φ)) i))))).symm,
    ?_⟩
  refine (congrArg (CategoryStruct.comp _) hdesc).trans ?_
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id_assoc]
  rw [← hY.isoPullback_inv_snd]
  congr 1
  rw [Functor.mapIso_hom, Iso.op_hom, RingEquiv.toCommRingCatIso_hom]
  show Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  ext1
  ext r
  exact hσ r

end AlgebraicGeometry.Abhyankar

namespace AlgebraicGeometry

open Abhyankar Stacks.FundamentalGroup

/-- **Abhyankar's lemma for a regular divisor**, granted purity for regular local rings and
[Stacks, Tag 0EYD]. Let `X` be a locally Noetherian scheme, `D ⊆ X` an effective Cartier divisor
which is a regular scheme, and `f : Y ⟶ X ∖ D` finite étale and tamely ramified over `X` in
codimension one. Then every `x ∈ X` has an étale neighbourhood `Spec A ⟶ X` on which `D` is cut
out by a nonzerodivisor `φ` with `A/φ` regular, such that the base change of `f` to
`Spec A_φ = Spec A ×_X (X ∖ D)` is a finite disjoint union of standard tamely ramified covers
`Spec (A[x]/(x^{eᵢ} - φ))_φ ⟶ Spec A_φ` with `eᵢ ≥ 1` invertible in `A`. The arguments are
`h0BMA`, purity for regular local rings ([Stacks, Tag 0BMA] (1)), and `h0EYD`, the tame half of
[Stacks, Tag 0EYD]. -/
theorem exists_etale_standardTamelyRamified_of_isTamelyRamifiedInCodimensionOne
    (h0BMA : PurityAtRegularLocalRings.{u})
    (h0EYD : ∀ S : CodimensionOnePullbackSetup.{u}, IsTamelyRamifiedInCodimensionOne S.U.ι S.f →
      IsTamelyRamifiedInCodimensionOne (pullback.fst S.g S.U.ι) S.pulledBackCover)
    {X : Scheme.{u}} [IsLocallyNoetherian X] (D : X.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hDreg : ∀ z : D.subscheme, IsRegularLocalRing (D.subscheme.presheaf.stalk z))
    {Y : Scheme.{u}} (f : Y ⟶ (D.support.compl : X.Opens)) [IsFinite f] [Etale f]
    (htame : Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne
      (Scheme.Opens.ι (D.support.compl : X.Opens)) f)
    (x : X) :
    ∃ (A : CommRingCat.{u}) (g : Spec A ⟶ X) (_ : Etale g) (a : Spec A) (_ : g a = x)
      (φ : A) (_ : IsNoetherianRing A) (_ : φ ∈ nonZeroDivisors A)
      (_ : IsRegularRing (A ⧸ Ideal.span {φ}))
      (gU : Spec (.of (Localization.Away φ)) ⟶ (D.support.compl : X.Opens))
      (_ : gU ≫ Scheme.Opens.ι (D.support.compl : X.Opens) =
        Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away φ))) ≫ g)
      (_ : IsPullback gU (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away φ))))
        (Scheme.Opens.ι (D.support.compl : X.Opens)) g)
      (n : ℕ) (e : Fin n → ℕ) (_ : ∀ i, 0 < e i ∧ IsUnit (e i : A)),
      ∃ ι : pullback f gU ≅ ∐ fun i ↦ Spec (.of (Localization.Away
          (algebraMap A (standardTamelyRamifiedAlgebra A φ (e i)) φ))),
        ι.hom ≫ Sigma.desc (fun i ↦ standardTamelyRamifiedCover A φ (e i)) =
          pullback.snd f gU := by
  classical
  obtain ⟨V, hxV, φ, hφ, hVφ⟩ :=
    (Stacks.CartierAffineLocalConverse.isEffectiveCartierDivisor_iff_nonZeroDivisor D).mp hD x
  have := V.2.isOpenImmersion_fromSpec
  have : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
  have hψU := fromSpec_preimage_compl_support D V φ hVφ
  let U : X.Opens := D.support.compl
  let p : Spec Γ(X, V.1) := V.2.primeIdealOf ⟨x, hxV⟩
  have hpx : V.2.fromSpec p = x := V.2.fromSpec_primeIdealOf ⟨x, hxV⟩
  obtain ⟨D', _, _, hD'et, q, hq, hqp, n, e, he, ⟨σ⟩⟩ :=
    exists_etale_kummerAway_algEquiv h0BMA φ hφ p.asIdeal
      (fun h ↦ isRegularLocalRing_localization_fromSpec D hD hDreg V φ hVφ p h)
      (chartRing U V.2.fromSpec φ hψU f)
      (fun _ _ hφ0 ↦ isTamelyRamifiedInCodimensionOne_chart D h0EYD hD hDreg f htame V φ hφ hVφ
        _ hφ0)
  let := (Localization.awayMap (algebraMap Γ(X, V.1) D') φ).toAlgebra
  have : Algebra.FiniteType Γ(X, V.1) D' := inferInstance
  have : IsNoetherianRing D' := Algebra.FiniteType.isNoetherianRing Γ(X, V.1) D'
  have hgEt : Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) D'))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr hD'et)
  have hU := isPullback_chartU_comp U V.2.fromSpec φ hψU D'
  have hY := isPullback_chartY_comp U V.2.fromSpec φ hψU D' f
  let φ' : D' := algebraMap Γ(X, V.1) D' φ
  have hσ : ∀ r, σ (fun i ↦ Localization.awayMap
      (algebraMap D' (standardTamelyRamifiedAlgebra D' φ' (e i))) φ' r) =
      algebraMap (Localization.Away φ') _ r := by
    have h : σ.toRingHom.comp (Pi.ringHom fun i ↦ Localization.awayMap
        (algebraMap D' (standardTamelyRamifiedAlgebra D' φ' (e i))) φ') =
        Algebra.TensorProduct.includeLeftRingHom := by
      apply IsLocalization.ringHom_ext (Submonoid.powers φ')
      ext d
      have hρ : (fun i ↦ Localization.awayMap
          (algebraMap D' (standardTamelyRamifiedAlgebra D' φ' (e i))) φ'
            (algebraMap D' (Localization.Away φ') d)) =
          algebraMap D' (∀ i, Localization.Away
            (algebraMap D' (standardTamelyRamifiedAlgebra D' φ' (e i)) φ')) d := by
        funext i
        exact (IsLocalization.map_eq _ _).trans (IsScalarTower.algebraMap_apply D' _ _ d).symm
      refine (congrArg σ hρ).trans ?_
      rw [σ.commutes]
      rfl
    exact fun r ↦ RingHom.congr_fun h r
  refine ⟨.of D', Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) D')) ≫ V.2.fromSpec,
    inferInstance, ⟨q, hq⟩, ?_, φ', inferInstance, ?_, ?_,
    Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap Γ(X, V.1) D') φ)) ≫
      chartU U V.2.fromSpec φ hψU, hU.w, hU, n, e, he, ?_⟩
  · rw [← hpx]
    show V.2.fromSpec _ = V.2.fromSpec p
    congr 1
    exact PrimeSpectrum.ext hqp
  · have hreg : IsSMulRegular D' φ := Module.Flat.isSMulRegular_of_nonZeroDivisors hφ
    rw [mem_nonZeroDivisors_iff_right]
    intro a ha
    apply hreg
    show φ • a = φ • (0 : D')
    rwa [smul_zero, Algebra.smul_def, mul_comm]
  · have hRq : IsRegularRing (Γ(X, V.1) ⧸ Ideal.span {φ}) := by
      rw [← hVφ]
      exact isRegularRing_quotient_ideal D hDreg V
    have hmap : (Ideal.span {φ}).map (algebraMap Γ(X, V.1) D') = Ideal.span {φ'} := by
      rw [Ideal.map_span, Set.image_singleton]
    let I : Ideal Γ(X, V.1) := Ideal.span {φ}
    have : IsRegularRing ((Γ(X, V.1) ⧸ I) ⊗[Γ(X, V.1)] D') :=
      Algebra.isRegularRing_of_smooth (Γ(X, V.1) ⧸ I) ((Γ(X, V.1) ⧸ I) ⊗[Γ(X, V.1)] D')
    let e2 : D' ⊗[Γ(X, V.1)] (Γ(X, V.1) ⧸ I) ≃ₐ[Γ(X, V.1)] (Γ(X, V.1) ⧸ I) ⊗[Γ(X, V.1)] D' :=
      Algebra.TensorProduct.comm Γ(X, V.1) D' (Γ(X, V.1) ⧸ I)
    have : IsRegularRing (D' ⊗[Γ(X, V.1)] (Γ(X, V.1) ⧸ I)) :=
      IsRegularRing.of_ringEquiv e2.symm.toRingEquiv
    let e1 : (D' ⧸ I.map (algebraMap Γ(X, V.1) D')) ≃ₐ[D'] D' ⊗[Γ(X, V.1)] (Γ(X, V.1) ⧸ I) :=
      Algebra.TensorProduct.quotIdealMapEquivTensorQuot D' I
    have : IsRegularRing (D' ⧸ I.map (algebraMap Γ(X, V.1) D')) :=
      IsRegularRing.of_ringEquiv e1.symm.toRingEquiv
    exact IsRegularRing.of_ringEquiv (Ideal.quotEquivOfEq hmap)
  · exact exists_iso_sigma_standardTamelyRamifiedCover (A := .of D') φ' e f _ _ _ hY
      σ.toRingEquiv hσ

end AlgebraicGeometry
