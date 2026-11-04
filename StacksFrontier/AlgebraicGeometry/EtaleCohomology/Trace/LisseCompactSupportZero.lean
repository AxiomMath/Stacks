module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportZeroCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicUpperVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.GaloisTrivializationInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SmallEtaleSitePresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.Unibranch
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.AffineOfNoProperComponent
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `H⁰_c` of a lisse sheaf on an affine curve vanishes

Let `U` be a smooth affine curve over a finite field `k`, with a compactification `j : U ⟶ Ū`,
and let `k̄` be an algebraically closed extension of `k`. Then `H⁰_c(U_k̄, G) = 0` for every
finite type locally constant sheaf `G` of `Λ`-modules on `U_étale`, and hence
`H⁰_c(U_k̄, F ⊗ Q_ℓ) = 0` for every lisse ℓ-adic sheaf `F` whose levels are finite type locally
constant, in particular for `F = ℱ_ρ` attached to a continuous `ρ : π₁(U, x̄) → GL_r(Q_ℓ)`.

This is the last assertion of [Stacks, Tag 03VL]: if `X` is not projective, then
`H⁰_c(X_k̄, ℱ_ρ) = 0`; a smooth curve which is affine is the case of the trace formula
(the non-projective curves of Step 3 of the proof of Tag 03UG are affine).

## Main results

All names are in the namespace `Stacks.EtaleCohomology`.

* `isZero_compactSupportFrobeniusCohomologyGroup_zero_of_isFiniteTypeLocallyConstant`:
  `H⁰_c(U_k̄, G) = 0` at a finite level.
* `LAdicSheaf.subsingleton_rationalGeometricCompactlySupportedCohomology_zero_of_isAffine`:
  `H⁰_c(U_k̄, F ⊗ Q_ℓ) = 0` for an ℓ-adic sheaf with finite type locally constant levels.
* `LAdicSheaf.subsingleton_rationalGeometricCompactlySupportedCohomology_zero_representationSheaf`:
  `H⁰_c(U_k̄, ℱ_τ) = 0` for a smooth affine curve and a continuous `τ`.
* `LAdicSheaf.subsingleton_rationalGeometricCompactlySupportedCohomology_zero_of_not_isProper`:
  `H⁰_c(X_k̄, ℱ_τ) = 0` for a smooth connected curve which is not proper over `k`.
* `isAffine_of_not_isProper_of_irreducibleSpace`: an irreducible separated scheme of finite type
  and dimension at most one over a field which is not proper is affine.

## References

* [Stacks Project, Tag 03VL](https://stacks.math.columbia.edu/tag/03VL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

section Level

variable {k : Type u} [Field k] [Finite k] {U : Scheme.{u}} (fU : U ⟶ Spec (.of k))
  [IsCurve k fU] [Smooth fU] [IsAffine U] (j : CompactificationOf (Over.mk fU)) (kbar : Type u)
  [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (Λ : Type) [CommRing Λ]

omit [IsAlgClosed kbar] in
/-- **`H⁰_c(U_k̄, G) = 0`** for a finite type locally constant sheaf `G` of `Λ`-modules on a
smooth affine curve `U` over a finite field. -/
@[sga "4½ Sommes_trig 1.18" "Clause b), special case"]
theorem isZero_compactSupportFrobeniusCohomologyGroup_zero_of_isFiniteTypeLocallyConstant
    (G : EtaleModules.{u, 0} Λ U)
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ U.smallEtaleTopology G) :
    IsZero (compactSupportFrobeniusCohomologyGroup.{u, 0} Λ fU j kbar
      ⟨(CochainComplex.singleFunctor _ 0).obj G, CochainComplex.plus_singleFunctor_obj G⟩ 0) := by
  have := Fintype.ofFinite k
  have hjU : j.immersion ≫ j.toBase = fU := Over.w j.obj.hom
  have : IsIntegral U := IsCurve.toIsVariety.toIsIntegral (k := k) (f := fU)
  have : IsNormal (Spec (CommRingCat.of k)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed k)
  have : IsNormal U := isNormal_of_smooth fU
  have hX : IsGeometricallyUnibranch U := isGeometricallyUnibranch_of_isNormal
  let x : GeometricPoint U := GeometricPoint.ofPoint U (Classical.arbitrary U)
  obtain ⟨A, M, -, ⟨e⟩⟩ := trivializedByPointedGaloisCovers hX x Λ G hG
  let W : U.Etale := (PointedGaloisCover.toEtale x).obj A
  let V : Scheme.{u} := A.obj.left
  let f : V ⟶ U := A.obj.hom
  have : IsFinite f := A.obj.prop.1
  have : Etale f := A.obj.prop.2
  have : ConnectedSpace V := inferInstanceAs (ConnectedSpace A.obj.left)
  have : IsAffine V := isAffine_of_isAffineHom f
  have : LocallyOfFiniteType (f ≫ fU) := inferInstance
  have : QuasiCompact (f ≫ fU) := inferInstance
  have : IsSeparated (f ≫ fU) := inferInstance
  obtain ⟨C⟩ := nonempty_coverCompactification k fU j.toBase j.immersion hjU f
  exact isZero_compactSupportFrobeniusCohomologyGroup_zero_of_cover fU j f kbar Λ C G M
    (etaleModuleInverseImageIsoConstantOfOverPullback W Λ G M e)

end Level

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
  ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]

omit [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **`H⁰_c(U_k̄, F ⊗ Q_ℓ) = 0`** for an ℓ-adic sheaf `F` with finite type locally constant
levels on a smooth affine curve over a finite field. -/
theorem LAdicSheaf.subsingleton_rationalGeometricCompactlySupportedCohomology_zero_of_isAffine
    [Finite k] [IsCurve k f] [Smooth f] [IsAffine X.1] [IsAlgClosed kbar] (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1)))
      (SmallEtale.topology B X.1 X.property) (F.level n)) :
    Subsingleton (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F 0) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hlevel (n : ℕ) : IsZero
      ((LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F 0).obj (op n)) := by
    have hG := (isFiniteTypeLocallyConstant_sheafEquiv_functor_iff B X (ZMod (ℓ ^ (n + 1)))
      (F.level n)).2 (hF n)
    have h := isZero_compactSupportFrobeniusCohomologyGroup_zero_of_isFiniteTypeLocallyConstant
      f j kbar (ZMod (ℓ ^ (n + 1))) (LAdicSheaf.etaleLevel B X ℓ F n) hG
    exact ((ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (n + 1))).map_isZero h).of_iso
      ((compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) 0).mapIso
        (LAdicSheaf.padicCoefficientComplexLevelIso B X ℓ F n) ≪≫
      (compactSupportFrobeniusCohomologyGroupRestrictScalarsIso (PadicInt.toZModPow (n + 1)) f j
        kbar (LAdicSheaf.levelComplex B X ℓ F n) 0).symm)
  have hlim : IsZero (LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F 0) :=
    (IsZero.iff_id_eq_zero _).2 (limit.hom_ext fun n => (hlevel n.unop).eq_of_tgt _ _)
  exact ModuleCat.subsingleton_of_isZero (Functor.map_isZero _ hlim)

omit [Fintype k] in
/-- An irreducible separated scheme of finite type and dimension at most one over a field which is
not proper is affine (the irreducible case of [Stacks, Tag 0A28]). -/
theorem isAffine_of_not_isProper_of_irreducibleSpace {X : Scheme.{u}} [IrreducibleSpace X]
    (f : X ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim X ≤ 1) (hf : ¬ IsProper f) : IsAffine X := by
  refine
    Stacks.AffineNoProperComponent.isAffine_of_topologicalKrullDim_le_one_of_forall_not_isProper
      k f hdim fun Z _ hP ↦ hf ?_
  have hZ : Z.1 = Set.univ :=
    Set.eq_univ_of_univ_subset (Z.2.2 (IrreducibleSpace.isIrreducible_univ X) (Set.subset_univ _))
  have : Surjective (Stacks.AffineNoProperComponent.componentIdealSheafData Z).subschemeι := by
    rw [surjective_iff, ← Set.range_eq_univ,
      Stacks.AffineNoProperComponent.range_subschemeι_componentIdealSheafData, hZ]
  have : UniversallyClosed f := UniversallyClosed.of_comp_surjective
    (Stacks.AffineNoProperComponent.componentIdealSheafData Z).subschemeι f
  exact ⟨⟩

/-- A connected scheme which is smooth of relative dimension one over a field is integral. -/
private theorem isIntegral_of_smoothOfRelativeDimension_one {K : Type u} [Field K]
    {X : Scheme.{u}} [ConnectedSpace X] (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] :
    IsIntegral X := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  exact Stacks.Chow.isIntegral_of_connectedSpace_of_smooth f

omit [Fintype k] in
/-- **`H⁰_c(U_k̄, ℱ_τ) = 0` on a smooth affine curve** `U` over a finite field `k`, for the lisse
ℓ-adic sheaf `ℱ_τ` of a continuous `τ : π₁(U, x̄) → GL_r(Q_ℓ)`, an algebraic closure `k̄` of `k`
and any compactification of `U`. -/
theorem
    LAdicSheaf.subsingleton_rationalGeometricCompactlySupportedCohomology_zero_representationSheaf
    [Finite k] [ConnectedSpace X.1] [SmoothOfRelativeDimension 1 f] [IsAffine X.1]
    [IsAlgClosure k kbar]
    (x : GeometricPoint X.1) {r : ℕ} (τ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ])
    (hτ : Continuous τ) :
    Subsingleton (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
      (LAdicSheaf.representationSheaf B X x τ hτ) 0) := by
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsIntegral X.1 := isIntegral_of_smoothOfRelativeDimension_one f
  have : IsCurve k f :=
    { topologicalKrullDim_eq_one :=
        topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 f }
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have := compactSpace_etaleFundamentalGroup X.1 x
  exact LAdicSheaf.subsingleton_rationalGeometricCompactlySupportedCohomology_zero_of_isAffine
    B X ℓ f j kbar _ fun n ↦
      isFiniteTypeLocallyConstant_representationLevelSheaf B X x _ _ _ (n + 1)

/-- **Stacks Project, Tag 03VL, last assertion: if `X` is not projective, then
`H⁰_c(X_k̄, ℱ_ρ) = 0`.** Here `X` is a smooth geometrically connected curve over the finite field
`k`, `ρ = τ : π₁(X, x̄) → GL_r(Q_ℓ)` is continuous, `H⁰_c(X_k̄, ℱ_ρ)` is the compactly supported
cohomology of `ℱ_τ ⊗ Q_ℓ` on `X_k̄` for an algebraic closure `k̄` (for any compactification), and
"not projective" is `¬ IsProper f` (a projective curve is proper over `k`, so this is the weaker
hypothesis). A connected smooth curve which is not proper is affine (Tag 0A28). -/
@[stacks 03VL "last assertion: H^0_c(X_kbar, F_rho) = 0 when X is not projective (here: not \
proper over k)"]
theorem LAdicSheaf.subsingleton_rationalGeometricCompactlySupportedCohomology_zero_of_not_isProper
    [ConnectedSpace X.1] [SmoothOfRelativeDimension 1 f] [IsAlgClosure k kbar]
    (hf : ¬ IsProper f) (x : GeometricPoint X.1) {r : ℕ}
    (τ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ]) (hτ : Continuous τ) :
    Subsingleton (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
      (LAdicSheaf.representationSheaf B X x τ hτ) 0) := by
  have : IsIntegral X.1 := isIntegral_of_smoothOfRelativeDimension_one f
  have : IsAffine X.1 := isAffine_of_not_isProper_of_irreducibleSpace f
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 f).le hf
  exact
    LAdicSheaf.subsingleton_rationalGeometricCompactlySupportedCohomology_zero_representationSheaf
      B X ℓ f j kbar x τ hτ

end Stacks.EtaleCohomology

end
