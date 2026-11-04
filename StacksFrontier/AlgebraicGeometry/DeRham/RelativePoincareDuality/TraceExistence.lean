module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.FormsWedgeTranspose
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.PairingDegenerateDegrees
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.SmoothOfRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingCupProduct
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothFormsDirectImage
public import StacksFrontier.Topology.Sheaves.Cohomology.MappingConeApproximation.ShiftLemmas
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothSpectralSequenceVanishing
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.RelativeEmbeddingDimensionForms

/-!
# Existence of the trace of relative Poincaré duality, from `Ω^n[n] ≅ ω^•_{X/S}`

In the situation of relative Poincaré duality ([Stacks, Tag 0G8G]) let `ω^•_{X/S} = a(𝒪_S)` be
the relative dualizing complex and `Tr : Rf_*ω^•_{X/S} ⟶ 𝒪_S` its trace ([Stacks, Tag 0B6S]).
Given an isomorphism `ψ : Ω^n_{X/S}[n] ≅ ω^•_{X/S}`, the map `t = Tr ∘ Rf_*ψ` has the property of
[Stacks, Tag 0G8I]: every pairing `Rf_*Ω^p ⊗^L Rf_*Ω^{n-p}[n] ⟶ 𝒪_S` is a perfect pairing of
perfect complexes. This is the source's argument: the complexes are perfect by
[Stacks, Tag 0FM0], and since `Ω^p ≅ SheafHom(Ω^{n-p}, Ω^n)` the derived wedge product is a perfect
pairing, so [Stacks, Tag 0G81] applies; in the degrees `p < 0` and `p > n` both sheaves of forms
vanish.

## Main results

* `AlgebraicGeometry.RelativeDualitySituation.isRelativePoincareTrace_of_iso`

## Implementation notes

[Stacks, Tag 0G81] is stated with the sheafification instances
`Stacks.AssociatedSheaf.hasModuleSheafify` and
`Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective` seated, and its hypothesis is an
application of the concrete adjunction
`Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.derivedTensorHomAdjunction`.
Comparing two elaborations of that adjunction with different instance proofs makes the
elaborator unfold it, so the hypothesis is discharged inside its own elaboration, with the
adjunction generalized to a variable before the facts proved about it are applied.

## References

* [Stacks Project, Tag 0G8I](https://stacks.math.columbia.edu/tag/0G8I)
* [Stacks Project, Tag 0G81](https://stacks.math.columbia.edu/tag/0G81)
* [Stacks Project, Tag 0B6S](https://stacks.math.columbia.edu/tag/0B6S)
* [Stacks Project, Tag 0FM0](https://stacks.math.columbia.edu/tag/0FM0)
-/

@[expose] public noncomputable section

open scoped Stacks.StandardDerivedModel Stacks.Topology.SheafTensorAdditiveOnOpens
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.RingedSite
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi (TensorHomAdjunction
  derivedTensorHomAdjunction)
open Stacks.DerivedTensor.RingedSite (canonicalDerivedTensorProduct)

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- `isIso_homEquiv_symm_formsDerivedWedge` with the target written `Ω^{a+b}` for `a + b : ℕ`. -/
theorem isIso_homEquiv_symm_formsDerivedWedge_natCast (a b : ℕ)
    [SmoothOfRelativeDimension (a + b) f] :
    IsIso (((derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite X.sheaf)).homEquiv
      (f.formsInDegreeZero a) (f.formsInDegreeZero b) (f.formsInDegreeZero ((a + b : ℕ) : ℤ))).symm
        (f.formsDerivedWedge a b)) := by
  have e : (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite X.sheaf)).homEquiv
      (f.formsInDegreeZero a) (f.formsInDegreeZero b) (f.formsInDegreeZero ((a + b : ℕ) : ℤ)) =
      (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite X.sheaf)).homEquiv
      (f.formsInDegreeZero a) (f.formsInDegreeZero b) (f.formsInDegreeZero ((a : ℤ) + (b : ℤ))) :=
    rfl
  rw [e]
  exact isIso_homEquiv_symm_formsDerivedWedge f a b

/-- For `n = a + b` the shifted wedge product is the commutation of `⊗^L` with the shift followed
by the shift of the wedge product. -/
theorem formsDerivedWedgeShift_natCast_eq (a b : ℕ) (h : (a : ℤ) + b = ((a + b : ℕ) : ℤ)) :
    letI := (canonicalDerivedTensorProduct (Stacks.SheafOfModules.ringedSite
        X.sheaf).O).commShift_right (f.formsInDegreeZero a)
    f.formsDerivedWedgeShift ((a + b : ℕ) : ℤ) a b ((a + b : ℕ) : ℤ) h =
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
          (Stacks.SheafOfModules.ringedSite X.sheaf).O).obj
        (f.formsInDegreeZero a)).commShiftIso ((a + b : ℕ) : ℤ)).hom.app (f.formsInDegreeZero b) ≫
        (f.formsDerivedWedge a b)⟦((a + b : ℕ) : ℤ)⟧' :=
  congrArg (_ ≫ ·) (congrArg (shiftFunctor _ ((a + b : ℕ) : ℤ)).map (Category.comp_id _))

/-- For any tensor–internal-Hom adjunction `DX` on `D(𝒪_X)` for which the wedge product
`Ω^a ⊗^L Ω^b ⟶ Ω^{a+b}` is a perfect pairing, so is its shift by `a + b`. -/
theorem isIso_homEquiv_symm_formsDerivedWedgeShift_of_isIso (DX : TensorHomAdjunction
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
          (Stacks.SheafOfModules.ringedSite X.sheaf).O)
      (Stacks.SheafOfModules.ringedSite X.sheaf).derivedSheafHomBifunctor) (a b : ℕ)
    (h : (a : ℤ) + b = ((a + b : ℕ) : ℤ))
    (hw : IsIso ((DX.homEquiv (f.formsInDegreeZero a) (f.formsInDegreeZero b)
      (f.formsInDegreeZero ((a + b : ℕ) : ℤ))).symm (f.formsDerivedWedge a b))) :
    IsIso ((DX.homEquiv (f.formsInDegreeZero a)
      ((f.formsInDegreeZero b)⟦((a + b : ℕ) : ℤ)⟧) ((f.formsInDegreeZero ((a + b : ℕ) : ℤ))⟦((a +
          b : ℕ) : ℤ)⟧)).symm
        (f.formsDerivedWedgeShift ((a + b : ℕ) : ℤ) a b ((a + b : ℕ) : ℤ) h)) := by
  rw [formsDerivedWedgeShift_natCast_eq f a b h]
  exact isIso_homEquiv_symm_commShiftIso_comp_shift DX ((a + b : ℕ) : ℤ)
    (f.formsInDegreeZero a) (f.formsInDegreeZero b) (f.formsInDegreeZero ((a + b : ℕ) : ℤ))
    (f.formsDerivedWedge a b) hw

/-- The shifted wedge product followed by an isomorphism `ψ : Ω^{a+b}[a+b] ≅ M` is a perfect
pairing `Ω^a ⊗^L Ω^b[a+b] ⟶ M` when the wedge product is. -/
theorem isIso_homEquiv_symm_formsDerivedWedgeShift_comp_of_isIso (DX : TensorHomAdjunction
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
          (Stacks.SheafOfModules.ringedSite X.sheaf).O)
      (Stacks.SheafOfModules.ringedSite X.sheaf).derivedSheafHomBifunctor) (a b : ℕ)
    (h : (a : ℤ) + b = ((a + b : ℕ) : ℤ))
    (hw : IsIso ((DX.homEquiv (f.formsInDegreeZero a) (f.formsInDegreeZero b)
      (f.formsInDegreeZero ((a + b : ℕ) : ℤ))).symm (f.formsDerivedWedge a b)))
    {M : DerivedCategory X.Modules} (ψ : (f.formsInDegreeZero ((a + b : ℕ) : ℤ))⟦((a + b : ℕ) :
        ℤ)⟧ ≅ M) :
    IsIso ((DX.homEquiv (f.formsInDegreeZero a)
      ((f.formsInDegreeZero b)⟦((a + b : ℕ) : ℤ)⟧) M).symm (f.formsDerivedWedgeShift ((a + b : ℕ)
          : ℤ) a b ((a + b : ℕ) : ℤ) h ≫ ψ.hom)) :=
  TensorHomAdjunction.isIso_homEquiv_symm_comp_of_isIso _ _ ψ.hom
    (isIso_homEquiv_symm_formsDerivedWedgeShift_of_isIso f DX a b h hw) ψ.isIso_hom

/-- For `f` smooth, `Ω^b_{X/S}[n]` has quasi-coherent cohomology. -/
theorem formsInDegreeZero_shift_mem [Smooth f] (b : ℕ) (n : ℤ) :
    DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) ((f.formsInDegreeZero b)⟦n⟧) := by
  have := AlgebraicGeometry.ProperSmoothDeRham.isFiniteLocallyFree_relativeDifferentialForms f b
  have := DerivedCategoryB.derivedCategoryB_isTriangulated (A := X.Modules) _
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X)
  have := DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms (A := X.Modules) _
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X)
  have h0 := Stacks.Duality.derivedCategoryB_singleFunctor_obj_inDegree
    (relativeDifferentialForms f b)
    (Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree _) 0
  have h1 := (DerivedCategoryB.derivedCategoryB (A := X.Modules)
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)).prop_of_iso
      ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app (relativeDifferentialForms f b)) h0
  exact (DerivedCategoryB.derivedCategoryB (A := X.Modules)
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)).le_shift n _ h1

/-- For `f` smooth, `Ω^b_{X/S}` in degree zero is a perfect complex: it is finite locally free. -/
private theorem isPerfectComplex_single_relativeDifferentialForms [Smooth f] (b : ℕ) :
    RingedSpace.IsPerfectComplex (X := X.toRingedSpace)
      ((CochainComplex.singleFunctor X.Modules 0).obj (relativeDifferentialForms f b)) := by
  have := AlgebraicGeometry.ProperSmoothDeRham.isFiniteLocallyFree_relativeDifferentialForms f b
  exact isPerfectComplex_single_of_isFiniteLocallyFree X _
    (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree _)

/-- For `f` smooth, `Ω^b_{X/S}` placed in degree zero is perfect: it is finite locally free. -/
theorem isPerfect_formsInDegreeZero [Smooth f] (b : ℕ) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) (f.formsInDegreeZero b) :=
  ⟨_, isPerfectComplex_single_relativeDifferentialForms f b,
    ⟨DerivedCategory.Q.mapIso (Iso.refl _)⟩⟩

/-- For `f` smooth, `Ω^b_{X/S}[n]` is pseudo-coherent. -/
theorem isPseudoCoherent_formsInDegreeZero_shift [Smooth f] (b : ℕ) (n : ℤ) :
    RingedSpace.IsPseudoCoherent (X := X.toRingedSpace)
      ((f.formsInDegreeZero b)⟦n⟧ : DerivedCategory X.Modules) := by
  have hE := AlgebraicGeometry.RingedSpace.IsPerfectComplex.isPseudoCoherentComplex
    (isPerfectComplex_single_relativeDifferentialForms f b)
  refine ⟨_, fun m => ?_, ⟨(DerivedCategory.Q.commShiftIso n).app _⟩⟩
  have h := AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_shift (hE (m + n)) n
  rwa [add_sub_cancel_right] at h


end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

section ProperFlat

attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

/-- **The pairing of a trace coming from an isomorphism `Ω^n[n] ≅ ω^•_{X/S}` is perfect**, in
degrees `a + b = n` with `a, b ≥ 0`: [Stacks, Tag 0G81] applies to
`K = Ω^a`, `M = Ω^b[n]` and the shifted wedge product followed by `ψ`, which is a perfect
pairing `Ω^a ⊗^L Ω^b[n] ⟶ ω^•_{X/S}` as `Ω^a ≅ SheafHom(Ω^b, Ω^n)`. -/
theorem isIso_homEquiv_symm_relativeHodgePairing_of_iso [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace X] [QuasiSeparatedSpace X] [IsProper f] (a b : ℕ) (h : (a : ℤ) + b = ((a + b :
        ℕ) : ℤ)) [SmoothOfRelativeDimension (a + b) f]
    (ψ : (f.formsInDegreeZero ((a + b : ℕ) : ℤ))⟦((a + b : ℕ) : ℤ)⟧ ≅
        (Stacks.Duality.relativeDualizingComplex f
      (Stacks.Duality.StandardModel.isQuasicoherent_homology_derivedPushforward f)
      (Stacks.Duality.derivedStructureSheafInDegree S 0)).obj) :
    IsIso (((derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite S.sheaf)).homEquiv
      ((Stacks.Duality.derivedPushforward f).obj (f.formsInDegreeZero a))
      ((Stacks.Duality.derivedPushforward f).obj ((f.formsInDegreeZero b)⟦((a + b : ℕ) : ℤ)⟧))
      (Stacks.Duality.derivedStructureSheafInDegree S 0).obj).symm
        (f.relativeHodgePairing ((a + b : ℕ) : ℤ) a b h ((Stacks.Duality.derivedPushforward f).map
            ψ.hom ≫
          (ObjectProperty.ι _).map (Stacks.Duality.relativeDualizingComplexTrace f
            (Stacks.Duality.StandardModel.isQuasicoherent_homology_derivedPushforward f)
            (Stacks.Duality.derivedStructureSheafInDegree S 0))))) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth (a + b) f
  refine (fun h81 => ?_) (Stacks.Duality.isIso_homEquiv_symm_relativeCupProduct_comp_trace f
    (f.formsInDegreeZero a) ⟨(f.formsInDegreeZero b)⟦((a + b : ℕ) : ℤ)⟧,
        formsInDegreeZero_shift_mem f b ((a + b : ℕ) : ℤ)⟩
    (isPseudoCoherent_formsInDegreeZero_shift f b ((a + b : ℕ) : ℤ)) (f.formsDerivedWedgeShift _ a
        b _ h ≫ ψ.hom) ?hphi)
  case hphi =>
    have hw := isIso_homEquiv_symm_formsDerivedWedge_natCast f a b
    generalize derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite X.sheaf) = DX at hw ⊢
    exact isIso_homEquiv_symm_formsDerivedWedgeShift_comp_of_isIso f DX a b h hw ψ
  generalize derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite S.sheaf) = DY at h81 ⊢
  have hm : Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct f.toLRSHom.toShHom
      (f.formsInDegreeZero a) ((f.formsInDegreeZero b)⟦((a + b : ℕ) : ℤ)⟧) ≫
      (Stacks.Duality.derivedPushforward f).map (f.formsDerivedWedgeShift _ a b _ h ≫ ψ.hom) ≫
        (ObjectProperty.ι _).map (Stacks.Duality.relativeDualizingComplexTrace f
          (Stacks.Duality.StandardModel.isQuasicoherent_homology_derivedPushforward f)
          (Stacks.Duality.derivedStructureSheafInDegree S 0)) =
      f.relativeHodgePairing ((a + b : ℕ) : ℤ) a b h ((Stacks.Duality.derivedPushforward f).map
          ψ.hom ≫
          (ObjectProperty.ι _).map (Stacks.Duality.relativeDualizingComplexTrace f
            (Stacks.Duality.StandardModel.isQuasicoherent_homology_derivedPushforward f)
            (Stacks.Duality.derivedStructureSheafInDegree S 0))) :=
    congrArg (_ ≫ ·) ((congrArg (· ≫ _) (Functor.map_comp _ _ _)).trans (Category.assoc _ _ _))
  rw [← hm]
  exact h81

end ProperFlat

/-- `Rf_*Ω^a_{X/S}` is perfect for `f` proper and smooth ([Stacks, Tag 0FM0]). -/
theorem isPerfect_derivedPushforward_formsInDegreeZero [IsProper f] [Smooth f] (a : ℕ) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.toRingedSpace)
      ((Stacks.Duality.derivedPushforward f).obj (f.formsInDegreeZero a)) :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso (X := S.toRingedSpace)
    ((Stacks.Duality.derivedPushforward f).mapIso ((DerivedCategory.quotientCompQhIso X.Modules).app
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj
        (relativeDifferentialForms f a))))
    (AlgebraicGeometry.ProperSmoothDeRham.isPerfect_derivedPushforward_forms f a)

/-- `Rf_*Ω^b_{X/S}[n]` is perfect for `f` proper and smooth. -/
theorem isPerfect_derivedPushforward_formsInDegreeZero_shift [IsProper f] [Smooth f] (b : ℕ)
    (n : ℤ) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.toRingedSpace)
      ((Stacks.Duality.derivedPushforward f).obj ((f.formsInDegreeZero b)⟦n⟧)) := by
  let := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift
    f.toLRSHom.toShHom
  exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso (X := S.toRingedSpace)
    (((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
      f.toLRSHom.toShHom).commShiftIso n).app (f.formsInDegreeZero b)).symm
    (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift (X := S.toRingedSpace)
      (isPerfect_derivedPushforward_formsInDegreeZero f b) n)

section ProperFlat'

attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

/-- **All pairings of the trace `Rf_*ψ ≫ Tr` are perfect pairings of perfect complexes**, for
`f` proper and smooth of relative dimension `n` and `ψ : Ω^n[n] ≅ ω^•_{X/S}`. -/
theorem isPerfectDerivedPairing_relativeHodgePairing_of_iso [CompactSpace S]
    [QuasiSeparatedSpace S] [CompactSpace X] [QuasiSeparatedSpace X] [IsProper f] (n : ℕ)
    [SmoothOfRelativeDimension n f]
    (ψ : (f.formsInDegreeZero n)⟦(n : ℤ)⟧ ≅ (Stacks.Duality.relativeDualizingComplex f
      (Stacks.Duality.StandardModel.isQuasicoherent_homology_derivedPushforward f)
      (Stacks.Duality.derivedStructureSheafInDegree S 0)).obj) (p q : ℤ) (h : p + q = n) :
    IsPerfectDerivedPairing (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite S.sheaf))
      (f.relativeHodgePairing n p q h ((Stacks.Duality.derivedPushforward f).map ψ.hom ≫
          (ObjectProperty.ι _).map (Stacks.Duality.relativeDualizingComplexTrace f
            (Stacks.Duality.StandardModel.isQuasicoherent_homology_derivedPushforward f)
            (Stacks.Duality.derivedStructureSheafInDegree S 0)))) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  by_cases hpq : 0 ≤ p ∧ 0 ≤ q
  · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hpq.1
    obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hpq.2
    obtain rfl : a + b = n := by omega
    refine ⟨isPerfect_derivedPushforward_formsInDegreeZero f a,
      isPerfect_derivedPushforward_formsInDegreeZero_shift f b _, ?_⟩
    have hc := isIso_homEquiv_symm_relativeHodgePairing_of_iso f a b h ψ
    generalize derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite S.sheaf) = DY at hc ⊢
    exact hc
  · have hz (r : ℤ) (hr : r < 0 ∨ (n : ℤ) < r) : IsZero (relativeDifferentialForms f r) := by
      rcases lt_or_ge r 0 with hr' | hr'
      · exact Stacks.DeRhamSmooth.isZero_relativeDifferentialForms_of_neg f r hr'
      · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hr'
        exact Scheme.Hom.isZero_relativeDifferentialForms_of_smoothOfRelativeDimension f n a
          (by omega)
    refine isPerfectDerivedPairing_relativeHodgePairing_of_isZero f _ n p q h _ ?_ ?_
    · exact hz p (by omega)
    · exact hz q (by omega)

end ProperFlat'

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.RelativeDualitySituation

variable (D : RelativeDualitySituation.{u})

/-- The source of the relative duality situation is quasi-compact. -/
instance compactSpace_X : CompactSpace D.X := QuasiCompact.compactSpace_of_compactSpace D.f
/-- The source of the relative duality situation is quasi-separated. -/
instance quasiSeparatedSpace_X : QuasiSeparatedSpace D.X := quasiSeparatedSpace_of_quasiSeparated
    D.f

section ProperFlat

attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

/-- **Existence in [Stacks, Tag 0G8I], given `Ω^n_{X/S}[n] ≅ ω^•_{X/S}`**: for an isomorphism
`ψ` from `Ω^n_{X/S}[n]` to the relative dualizing complex `a(𝒪_S)`, the composite
`Rf_*Ω^n[n] ≅ Rf_*a(𝒪_S) ⟶ 𝒪_S` of `Rf_*ψ` and the trace of [Stacks, Tag 0B6S] has the property
of [Stacks, Tag 0G8I]. -/
theorem isRelativePoincareTrace_of_iso
    (ψ : (D.f.formsInDegreeZero D.n)⟦(D.n : ℤ)⟧ ≅ (Stacks.Duality.relativeDualizingComplex D.f
      (Stacks.Duality.StandardModel.isQuasicoherent_homology_derivedPushforward D.f)
      (Stacks.Duality.derivedStructureSheafInDegree D.S 0)).obj) :
    D.IsRelativePoincareTrace ((Stacks.Duality.derivedPushforward D.f).map ψ.hom ≫
      (ObjectProperty.ι _).map (Stacks.Duality.relativeDualizingComplexTrace D.f
        (Stacks.Duality.StandardModel.isQuasicoherent_homology_derivedPushforward D.f)
        (Stacks.Duality.derivedStructureSheafInDegree D.S 0))) := fun p => by
  have h := Scheme.Hom.isPerfectDerivedPairing_relativeHodgePairing_of_iso D.f D.n ψ p (D.n - p)
    (by ring)
  generalize derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite D.S.sheaf) = DY at h ⊢
  exact h

end ProperFlat

end AlgebraicGeometry.RelativeDualitySituation

end
