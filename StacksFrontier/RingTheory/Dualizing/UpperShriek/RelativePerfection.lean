module

public import StacksFrontier.Homology.KFlat.BaseChange
public import StacksFrontier.Homology.RelativelyPerfect.Criterion
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
public import StacksFrontier.RingTheory.Dualizing.Relative
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizing
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingBaseChange

/-!
# The relative dualizing complex is perfect relative to the base

Let `φ : R → A` be a flat homomorphism of finite type of Noetherian rings and let
`ω_{A/R} = φ^!(R)` be its relative dualizing complex, the value of algebraic upper shriek at the
base ring placed in cohomological degree zero. Given the projection-formula compatibility
`Dualizing.PolynomialPresentation.ProjectionCompatibility` at every residue field of `R`, this file
proves that `ω_{A/R}` is perfect relative to `R`, and that together with the diagonal condition it
is a relative dualizing complex.

## Main results

* `Dualizing.isZero_homology_extendScalars_of_isZero_homology_baseChangeAlgebra`: for a complex `P`
  of `A`-modules, if a cohomology module of `(R' ⊗_R A) ⊗_A P` vanishes, then so does the
  cohomology module in the same degree of `R' ⊗_R P`, for `P` regarded as a complex of
  `R`-modules.
* `Dualizing.PolynomialPresentation.relativeDualizingComplex_fibre_isGE_of_flat`: the derived
  fibre `ω_{A/R} ⊗_R^L κ(p)` is bounded below, given the projection-formula compatibility at
  `κ(p)`.
* `Dualizing.PolynomialPresentation.relativeDualizingComplex_isRelativelyPerfect_of_flat`:
  `ω_{A/R}` is perfect relative to `R`.
* `Dualizing.PolynomialPresentation.relativeDualizingComplex_isRelativeDualizing_of_flat`:
  `ω_{A/R}` is a relative dualizing complex, given the diagonal condition
  `RHom_{A ⊗_R A}(A, ω_{A/R} ⊗_A^L (A ⊗_R A)) ≅ A[0]`.

## References

* [Stacks Project, Tag 0E2E](https://stacks.math.columbia.edu/tag/0E2E)
* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0GHJ](https://stacks.math.columbia.edu/tag/0GHJ)
* [Stacks Project, Tag 0BZV](https://stacks.math.columbia.edu/tag/0BZV)
* [Stacks Project, Tag 0BZW](https://stacks.math.columbia.edu/tag/0BZW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

open scoped TensorProduct

open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] extensionOfScalarsComplexGeneral

universe u

namespace Dualizing

/-! ### Change of rings on complexes -/

section ChangeOfRings

variable {S T : Type u} [CommRing S] [CommRing T]

/-- Restriction of scalars along `f` neither creates nor destroys the vanishing of a cohomology
module of a complex. -/
theorem isZero_homology_restrictScalars_iff (f : S →+* T)
    (K : CochainComplex (ModuleCat.{u} T) ℤ) (i : ℤ) :
    IsZero ((((ModuleCat.restrictScalars f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).homology i) ↔ IsZero (K.homology i) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff, HomologicalComplex.exactAt_iff,
    ShortComplex.moduleCat_exact_iff, ShortComplex.moduleCat_exact_iff]
  rfl

/-- Restricting the base change `T ⊗_S -` back to `S` is tensoring on the left with `T` viewed as
an `S`-module. -/
def extendRestrictTensorLeftIso (f : S →+* T) :
    ModuleCat.extendScalars.{u, u, u} f ⋙ ModuleCat.restrictScalars f ≅
      tensorLeft ((ModuleCat.restrictScalars f).obj (ModuleCat.of T T)) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- Restricting the base change `T ⊗_S -` back to `S` is tensoring on the right with `T` viewed
as an `S`-module. -/
def extendRestrictTensorRightIso (f : S →+* T) :
    ModuleCat.extendScalars.{u, u, u} f ⋙ ModuleCat.restrictScalars f ≅
      tensorRight ((ModuleCat.restrictScalars f).obj (ModuleCat.of T T)) :=
  extendRestrictTensorLeftIso f ≪≫ BraidedCategory.tensorLeftIsoTensorRight _

end ChangeOfRings

/-! ### The projection formula at a base-changed algebra -/

section Projection

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- **The projection formula at an algebra which is a base change.** Let `C` be an `A`-algebra
whose underlying `A`-module is identified by `eC` with the base change `A ⊗_R N` of an `R`-module
`N`. Restricted to `R`, the base change `C ⊗_A -` of an `A`-module is the tensor product over `R`
of its underlying `R`-module with `N`. -/
def restrictExtendTensorRightIso (C : Type u) [CommRing C] [Algebra A C] (N : ModuleCat.{u} R)
    (eC : (ModuleCat.restrictScalars (algebraMap A C)).obj (ModuleCat.of C C) ≅
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R A)).obj N) :
    ModuleCat.extendScalars.{u, u, u} (algebraMap A C) ⋙
        ModuleCat.restrictScalars (algebraMap A C) ⋙
        ModuleCat.restrictScalars (algebraMap R A) ≅
      ModuleCat.restrictScalars (algebraMap R A) ⋙ tensorRight N := by
  have hproj : tensorRight ((ModuleCat.extendScalars.{u, u, u} (algebraMap R A)).obj N) ⋙
        ModuleCat.restrictScalars (algebraMap R A) ≅
      ModuleCat.restrictScalars (algebraMap R A) ⋙ tensorRight N :=
    NatIso.ofComponents (fun M => projectionFormulaIso (algebraMap R A) M N)
      (fun f => projectionFormulaIso_natural_left (algebraMap R A) N f)
  exact Functor.isoWhiskerRight (extendRestrictTensorLeftIso (algebraMap A C) ≪≫
      BraidedCategory.tensorLeftIsoTensorRight _ ≪≫
      (tensoringRight (ModuleCat.{u} A)).mapIso eC)
      (ModuleCat.restrictScalars (algebraMap R A)) ≪≫ hproj

end Projection

/-! ### The two derived fibres agree -/

section Fibre

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']

/-- The base-changed algebra `R' ⊗_R A`, viewed as an `A`-module through the coprojection
`includeRight : A → R' ⊗_R A`, is the base change `A ⊗_R R'` of `R'`. -/
def baseChangeAlgebraIso :
    (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight : A →ₐ[R] TensorProduct R R' A).toRingHom).obj
        (ModuleCat.of (TensorProduct R R' A) (TensorProduct R R' A)) ≅
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R A)).obj
        ((ModuleCat.restrictScalars (algebraMap R R')).obj (ModuleCat.of R' R')) := by
  letI : Algebra A (TensorProduct R R' A) :=
    (Algebra.TensorProduct.includeRight : A →ₐ[R] TensorProduct R R' A).toRingHom.toAlgebra
  set N : ModuleCat.{u} R :=
    (ModuleCat.restrictScalars (algebraMap R R')).obj (ModuleCat.of R' R')
  have hsmul (a : A) (z : TensorProduct R R' A) :
      a • z = ((1 : R') ⊗ₜ[R] a) * z := Algebra.smul_def a z
  let m0 : TensorProduct R R' A ≃ₗ[R] TensorProduct R A (N : Type u) :=
    (TensorProduct.comm R R' A).trans
      (TensorProduct.congr (LinearEquiv.refl R A)
        (StacksDraft.TorAmplitude.FaithfullyFlat.restrictScalarsSelfEquiv R R').symm)
  have hm : ∀ (a : A) (z : TensorProduct R R' A), m0 (a • z) = a • m0 z := by
    intro a z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r b =>
        rw [hsmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        change m0 (r ⊗ₜ[R] (a * b)) = a • m0 (r ⊗ₜ[R] b)
        simp only [m0, LinearEquiv.trans_apply, TensorProduct.comm_tmul,
          TensorProduct.congr_tmul, LinearEquiv.refl_apply]
        rfl
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  let m : TensorProduct R R' A ≃ₗ[A] TensorProduct R A (N : Type u) :=
    { __ := m0.toAddEquiv, map_smul' := hm }
  exact LinearEquiv.toModuleIso
    ((StacksDraft.TorAmplitude.FaithfullyFlat.restrictScalarsSelfEquiv A
      (TensorProduct R R' A)).trans
      (m.trans
        (StacksDraft.TorAmplitude.FaithfullyFlat.extendScalarsCarrierEquiv R A N).symm))

/-- Let `P` be a complex of `A`-modules. If the cohomology in degree `i` of the termwise base
change of `P` along the coprojection `A → R' ⊗_R A` vanishes, then so does the cohomology in degree
`i` of the termwise base change along `R → R'` of the complex of `R`-modules underlying `P`. -/
theorem isZero_homology_extendScalars_of_isZero_homology_baseChangeAlgebra
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ)
    (hz : IsZero ((((ModuleCat.extendScalars.{u, u, u}
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R R' A).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P).homology i)) :
    IsZero ((((ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)).homology i) := by
  let _ : Algebra A (TensorProduct R R' A) :=
    (Algebra.TensorProduct.includeRight : A →ₐ[R] TensorProduct R R' A).toRingHom.toAlgebra
  have h1 := (isZero_homology_restrictScalars_iff (algebraMap R A) _ i).2
    ((isZero_homology_restrictScalars_iff (algebraMap A (TensorProduct R R' A)) _ i).2 hz)
  have h2 := h1.of_iso
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i).mapIso
      ((NatIso.mapHomologicalComplex
        (restrictExtendTensorRightIso (TensorProduct R R' A)
          ((ModuleCat.restrictScalars (algebraMap R R')).obj (ModuleCat.of R' R'))
          baseChangeAlgebraIso) (ComplexShape.up ℤ)).app P).symm)
  have h3 := h2.of_iso
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i).mapIso
      ((NatIso.mapHomologicalComplex (extendRestrictTensorRightIso (algebraMap R R'))
        (ComplexShape.up ℤ)).app
          (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)))
  exact (isZero_homology_restrictScalars_iff (algebraMap R R') _ i).1 h3

end Fibre

/-! ### Relative perfection of the relative dualizing complex -/

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

namespace PolynomialPresentation

/-- **The relative dualizing complex of a flat homomorphism of finite type is pseudo-coherent**:
for `φ : R → A` flat of finite type between Noetherian rings, `ω_{A/R} = φ^!(R)`, with the base
ring itself in degree zero, is pseudo-coherent. -/
theorem relativeDualizingComplex_isPseudoCoherent_of_flat
    [IsNoetherianRing R] [IsNoetherianRing A]
    (p : PolynomialPresentation (algebraMap R A)) (hflat : (algebraMap R A).Flat) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      (p.upperShriekFunctor.{u, 0}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) :=
  (upperShriekFunctor_unit_isPseudoCoherent_of_flat.{u, 0} p hflat).ofIso
    (p.upperShriekFunctor.{u, 0}.mapIso
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).mapIso
        (LinearEquiv.toModuleIso (ULift.moduleEquiv : ULift.{0} R ≃ₗ[R] R))))

/-- If the comparison map at a complex `P` is an isomorphism and `P` represents `X`, then the
cohomology of the derived base change of `X` vanishes iff that of the termwise base change of `P`
does. -/
private theorem isZero_homology_totalDerived_iff {S T : Type u} [CommRing S] [CommRing T]
    (f : S →+* T) (P : CochainComplex (ModuleCat.{u} S) ℤ) (hP : IsIso
      ((totalDerivedExtensionScalars.{u, u, u} f).comparison.app P))
    (X : DerivedCategory (ModuleCat.{u} S)) (e : DerivedCategory.Q.obj P ≅ X) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} T) i).obj
        ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj X)) ↔
      IsZero ((((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P).homology i) :=
  ((DerivedCategory.homologyFunctor (ModuleCat.{u} T) i).mapIso
    ((totalDerivedExtensionScalars.{u, u, u} f).functor.mapIso e.symm ≪≫
      @asIso _ _ _ _ _ hP) ≪≫ (DerivedCategory.homologyFunctorFactors _ i).app _).isZero_iff

/-- **The derived fibres of the relative dualizing complex are bounded below.** Let `φ : R → A` be
flat of finite type between Noetherian rings and let `q` be a prime of `R`. Given the
projection-formula compatibility `hProj` at the residue field `κ(q)`, the derived fibre
`ω_{A/R} ⊗_R^L κ(q)` is cohomologically bounded below. -/
theorem relativeDualizingComplex_fibre_isGE_of_flat
    [IsNoetherianRing R] [IsNoetherianRing A]
    (p : PolynomialPresentation (algebraMap R A)) (hflat : (algebraMap R A).Flat)
    (q : PrimeSpectrum R) (hProj : p.ProjectionCompatibility q.asIdeal.ResidueField) :
    ∃ a : ℤ,
      ((totalDerivedExtensionScalars.{u, u, u}
          (algebraMap R q.asIdeal.ResidueField)).functor.obj
        ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
          (p.upperShriekFunctor.{u, 0}.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
              (ModuleCat.of R R))))).IsGE a := by
  let R' := q.asIdeal.ResidueField
  let ω := p.upperShriekFunctor.{u, 0}.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))
  obtain ⟨P, hP, ⟨eP⟩⟩ := p.relativeDualizingComplex_isPseudoCoherent_of_flat hflat
  obtain ⟨c, hc⟩ := hP.upperBound
  have hfree (i : ℤ) : Module.Free A (P.X i) := (hP.finiteFree i).2
  let DT := totalDerivedExtensionScalars.{u, u, u}
    (Algebra.TensorProduct.includeRight : A →ₐ[R] TensorProduct R R' A).toRingHom
  obtain ⟨eBC⟩ := relativeDualizingComplexBaseChange_of_flatAlgebra p hflat
    DT.functor DT.comparison DT.isLeftDerived
  obtain ⟨a, ha⟩ := (p.baseChange (R' := R')).upperShriekFunctor_isBoundedBelow.{u, 0}
    ((derivedCategoryBBounded_singleFunctor_obj.{u, 0} (ModuleCat.of R' R') inferInstance).1.1)
  have hcmp : IsIso (DT.comparison.app P) := DT.comparison_isIso_of_projective P c
  have hzP (i : ℤ) (hi : i < a) :
      IsZero ((((ModuleCat.extendScalars.{u, u, u}
        (Algebra.TensorProduct.includeRight :
          A →ₐ[R] TensorProduct R R' A).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P).homology i) :=
    (isZero_homology_totalDerived_iff _ P hcmp ω eP i).1
      ((ha i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso eBC))
  let G := ModuleCat.restrictScalars (algebraMap R A)
  let E : CochainComplex (ModuleCat.{u} R) ℤ :=
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hEle : E.IsStrictlyLE c :=
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff P G c).2 hc
  let _ : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
  have hEflat (i : ℤ) : Module.Flat R (E.X i) := by
    let _ : Module R (P.X i) := Module.compHom (P.X i) (algebraMap R A)
    let _ : IsScalarTower R A (P.X i) := IsScalarTower.of_compHom R A (P.X i)
    exact Module.Flat.trans R A (P.X i)
  let eE : DerivedCategory.Q.obj E ≅ G.mapDerivedCategory.obj ω :=
    (G.mapDerivedCategoryFactors.app P).symm ≪≫ G.mapDerivedCategory.mapIso eP
  let D := totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')
  have hDcmp : IsIso (D.comparison.app E) :=
    D.comparison_isIso_of_kFlat E (CochainComplex.KFlat.kFlat_of_flat E c)
  exact ⟨a, (DerivedCategory.isGE_iff _ a).2 fun i hi =>
    (isZero_homology_totalDerived_iff _ E hDcmp _ eE i).2
      (isZero_homology_extendScalars_of_isZero_homology_baseChangeAlgebra P i (hzP i hi))⟩

/-- **The relative dualizing complex of a flat homomorphism of finite type of Noetherian rings is
perfect relative to the base.** For `φ : R → A` flat of finite type between Noetherian rings,
`ω_{A/R} = φ^!(R)` is perfect relative to `R` with respect to the canonical derived tensor
product, given the projection-formula compatibility `hProj` at the residue field of every prime of
`R`. -/
theorem relativeDualizingComplex_isRelativelyPerfect_of_flat
    [IsNoetherianRing R] [IsNoetherianRing A]
    (p : PolynomialPresentation (algebraMap R A)) (hflat : (algebraMap R A).Flat)
    (hProj : ∀ q : PrimeSpectrum R, p.ProjectionCompatibility q.asIdeal.ResidueField) :
    letI : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
    letI : Algebra.FinitePresentation R A :=
      Algebra.FinitePresentation.of_finiteType.mp (RingHom.finiteType_algebraMap.mp p.finiteType)
    PseudoCoherence.IsRelativelyPerfect.{u, u, u}
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison R)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R)
      (p.upperShriekFunctor.{u, 0}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) := by
  let : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
  let : Algebra.FinitePresentation R A :=
    Algebra.FinitePresentation.of_finiteType.mp (RingHom.finiteType_algebraMap.mp p.finiteType)
  have hPC := p.relativeDualizingComplex_isPseudoCoherent_of_flat hflat
  refine (PseudoCoherence.isRelativelyPerfect_iff_isBoundedBelow_and_fibres_isBoundedBelow.{u}
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
    (StacksDraft.TorAmplitude.canonicalTensorComparison R)
    (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R) _ hPC).2 ⟨?_, ?_⟩
  · obtain ⟨a, ha⟩ := p.upperShriekFunctor_isBoundedBelow.{u, 0}
      ((derivedCategoryBBounded_singleFunctor_obj.{u, 0} (ModuleCat.of R R) inferInstance).1.1)
    exact ⟨a, (DerivedCategory.isGE_iff _ a).2 ha⟩
  · exact fun q => p.relativeDualizingComplex_fibre_isGE_of_flat hflat q (hProj q)

/-- For `φ : R → A` flat of finite type between Noetherian rings, `ω_{A/R} = φ^!(R)` is a
relative dualizing complex, given the projection-formula compatibility `hProj` at the residue field
of every prime of `R` and the diagonal condition `hdiag`:
`RHom_{A ⊗_R A}(A, ω_{A/R} ⊗_A^L (A ⊗_R A)) ≅ A[0]`, which is the second condition of
`IsRelativeDualizingComplex`. -/
theorem relativeDualizingComplex_isRelativeDualizing_of_flat
    [IsNoetherianRing R] [IsNoetherianRing A]
    (p : PolynomialPresentation (algebraMap R A)) (hflat : (algebraMap R A).Flat)
    (hProj : ∀ q : PrimeSpectrum R, p.ProjectionCompatibility q.asIdeal.ResidueField)
    (hdiag :
      letI : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
      Nonempty
        ((derivedHom.{u, u}
          (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
            ((diagonalDerivedExtension R A).obj
              (p.upperShriekFunctor.{u, 0}.obj
                ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
                  (ModuleCat.of R R)))) ≅
          (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))) :
    letI : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
    letI : Algebra.FinitePresentation R A :=
      Algebra.FinitePresentation.of_finiteType.mp (RingHom.finiteType_algebraMap.mp p.finiteType)
    IsRelativeDualizingComplex R A
      (p.upperShriekFunctor.{u, 0}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) := by
  let : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
  let : Algebra.FinitePresentation R A :=
    Algebra.FinitePresentation.of_finiteType.mp (RingHom.finiteType_algebraMap.mp p.finiteType)
  exact ⟨p.relativeDualizingComplex_isRelativelyPerfect_of_flat hflat hProj, hdiag⟩

end PolynomialPresentation

end Dualizing

end
