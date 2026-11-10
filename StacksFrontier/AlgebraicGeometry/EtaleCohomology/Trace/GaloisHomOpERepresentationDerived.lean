module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpEDerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpDerivedGlobalSectionsCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisCompactSupportTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricDerivedGaloisInvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafHomOp

/-!
# `E = Γ^Gal(X̄, ℋom^•_ℤ(I, K))` computes `RΓ^Gal(X, ℋom_ℤ(ℱ_M, ℱ_μ))`

On a smooth geometrically connected curve `X` over `k` with compactification `j : X ⟶ X̄`, let
`M` be a finite `Λ`-module with a continuous action of `π₁(X, x)`, `I` an injective resolution of
`(j_! ℱ_M)[0]`, and `K` the complex of abelian sheaves underlying an injective resolution of
`j_! ℱ_μ`, `ℱ_μ` the sheaf of `n`-th roots of unity. Then the complex `E` of the evaluation
pairing of Tag 03VM represents `RΓ^Gal(X, ℋom_ℤ(ℱ_M, ℱ_μ))`.

## Main definitions

* `AlgebraicGeometry.galoisHomOpERepresentationDerivedIso`: the isomorphism
  `E ≅ RΓ^Gal(X, ℋom_ℤ(ℱ_M, ℱ_μ))` in the derived category of discrete Galois `Λᵐᵒᵖ`-modules.
* `AlgebraicGeometry.galoisHomOpECyclotomicDerivedIso`: the same, with target written through
  `AlgebraicGeometry.etaleHomOpRepresentationFunctor` at the point below `y`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry Stacks.GroupCohomology Stacks.Frobenius Stacks.EtaleCohomology
open Stacks.AbelianInternalHom Stacks.ConstantSheaf

universe w₁ w₂ w₃ w₄ u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar]
  [CompactSpace (kbar ≃ₐ[k] kbar)]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) (n : ℕ) [NeZero n]
  (j : CompactificationOf (Over.mk f))
  (K₀ : letI := connectedSpace_of_isCurve B X f
    CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor _ 0).obj
        ((etaleModuleExtensionByZero (ZMod n) j.immersion).obj
          ((representationSheaf B X _ (ZMod n)).obj (cyclotomicContinuousModule B X f kbar y n)))))
  (Λ : Type) [Ring Λ] [Finite Λ] [Algebra (ZMod n) Λ]
  [HasDerivedCategory.{w₁} (EtaleModules.{u, 0} Λᵐᵒᵖ (Over.mk f).left)]
  [HasDerivedCategory.{w₂} (GaloisModules Λᵐᵒᵖ k kbar)]
  [HasDerivedCategory.{w₃} (EtaleModules.{u, 0} Λᵐᵒᵖ (fieldBaseChange (Over.mk f) kbar))]
  [HasDerivedCategory.{w₄} (ModuleCat.{u + 1} Λᵐᵒᵖ)]

/-- `n = 0` in a `ℤ/n`-algebra. -/
lemma natCast_eq_zero_of_zmodAlgebra {n : ℕ} (Λ : Type) [Ring Λ] [Algebra (ZMod n) Λ] :
    ((n : ℕ) : Λ) = 0 := by
  rw [← map_natCast (algebraMap (ZMod n) Λ), ZMod.natCast_self, map_zero]

/-- **`E = Γ^Gal(X̄, ℋom^•_ℤ(I, K)) ≅ RΓ^Gal(X, ℋom_ℤ(ℱ_M, ℱ_μ))`**, for `I` an injective
resolution of `(j_! ℱ_M)[0]` and `K` the complex of abelian sheaves underlying an injective
resolution of `j_! ℱ_μ`, in the derived category of discrete Galois `Λᵐᵒᵖ`-modules. -/
def galoisHomOpERepresentationDerivedIso [ConnectedSpace X.1] (x : GeometricPoint X.1)
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (I : CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor (EtaleModules.{u, 0} Λ (Over.mk j.toBase).left) 0).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
          ((representationSheaf B X x Λ).obj M))))
    [K₀.cocomplex.IsStrictlyGE 0]
    (hG' : IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, 0, 0} X.1.smallEtaleTopology
      (ZMod n) ((etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) X.1).obj
        ((representationSheaf B X x Λ).obj M)))
    (hω : letI := connectedSpace_of_isCurve B X f
      Stacks.ModuleInternalHom.IsLocallyConstantInjective X.1.smallEtaleTopology (ZMod n)
        ((representationSheaf B X _ (ZMod n)).obj (cyclotomicContinuousModule B X f kbar y n))) :
    DerivedCategory.Q.obj (galoisHomOpE (Over.mk j.toBase) kbar I.cocomplex
        (cyclotomicIntResolution B X f kbar y n j K₀)) ≅
      (DerivedCategory.Plus.singleFunctor _ 0 ⋙ galoisDerivedGlobalSections Λᵐᵒᵖ (Over.mk f) kbar ⋙
        DerivedCategory.Plus.ι).obj
        (homOpSheaf X.1.smallEtaleTopology ((representationSheaf B X x Λ).obj M)
          (letI := connectedSpace_of_isCurve B X f; toAb _ ((representationSheaf B X _ (ZMod n)).obj
            (cyclotomicContinuousModule B X f kbar y n)))) :=
  galoisHomOpEDerivedGlobalSectionsOverIso Λ kbar (compactificationImmersionOverHom j)
    ((representationSheaf B X x Λ).obj M)
    ((etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) X.1).obj
      ((representationSheaf B X x Λ).obj M))
    (Iso.refl _) hG' _ hω K₀.cocomplex K₀.ι (hι₀ := K₀.quasiIso) (natCast_eq_zero_of_zmodAlgebra Λ)
    rfl I _ rfl

omit [Smooth f] [CompactSpace (kbar ≃ₐ[k] kbar)] [Algebra (ZMod n) Λ]
  [HasDerivedCategory.{w₁} (EtaleModules.{u, 0} Λᵐᵒᵖ (Over.mk f).left)]
  [HasDerivedCategory.{w₂} (GaloisModules Λᵐᵒᵖ k kbar)]
  [HasDerivedCategory.{w₃} (EtaleModules.{u, 0} Λᵐᵒᵖ (fieldBaseChange (Over.mk f) kbar))]
  [HasDerivedCategory.{w₄} (ModuleCat.{u + 1} Λᵐᵒᵖ)] in
/-- `ℋom_ℤ(ℱ_M, ℱ_μ)` is the value of `AlgebraicGeometry.etaleHomOpRepresentationFunctor` at `M`,
for `M` over the point `x_y` of `X` below `y`. -/
theorem homOpSheaf_cyclotomic_eq_etaleHomOpRepresentationFunctor_obj [ConnectedSpace X.1]
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    homOpSheaf X.1.smallEtaleTopology
        ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj M)
        (letI := connectedSpace_of_isCurve B X f; toAb _ ((representationSheaf B X _ (ZMod n)).obj
          (cyclotomicContinuousModule B X f kbar y n))) =
      (etaleHomOpRepresentationFunctor B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ n
          (cyclotomicContinuousModule B X f kbar y n)).obj (op M) :=
  rfl

/-- **`E ≅ RΓ^Gal(X, ℋom_ℤ(ℱ_M, ℱ_μ))`** with target written through
`AlgebraicGeometry.etaleHomOpRepresentationFunctor`, for `M` over the point `x_y` of `X` below `y`
(`AlgebraicGeometry.galoisHomOpERepresentationDerivedIso`). -/
def galoisHomOpECyclotomicDerivedIso [ConnectedSpace X.1]
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (I : CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor (EtaleModules.{u, 0} Λ (Over.mk j.toBase).left) 0).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
          ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
            (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj M))))
    [K₀.cocomplex.IsStrictlyGE 0]
    (hG' : IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, 0, 0} X.1.smallEtaleTopology
      (ZMod n) ((etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) X.1).obj
        ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj M)))
    (hω : letI := connectedSpace_of_isCurve B X f
      Stacks.ModuleInternalHom.IsLocallyConstantInjective X.1.smallEtaleTopology (ZMod n)
        ((representationSheaf B X _ (ZMod n)).obj (cyclotomicContinuousModule B X f kbar y n))) :
    DerivedCategory.Q.obj (galoisHomOpE (Over.mk j.toBase) kbar I.cocomplex
        (cyclotomicIntResolution B X f kbar y n j K₀)) ≅
      (DerivedCategory.Plus.singleFunctor _ 0 ⋙ galoisDerivedGlobalSections Λᵐᵒᵖ (Over.mk f) kbar ⋙
        DerivedCategory.Plus.ι).obj
        ((etaleHomOpRepresentationFunctor B X (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ n
            (cyclotomicContinuousModule B X f kbar y n)).obj (op M)) :=
  galoisHomOpERepresentationDerivedIso B X f kbar y n j K₀ Λ _ M I hG' hω ≪≫
    eqToIso (congrArg (fun A ↦ (DerivedCategory.Plus.singleFunctor _ 0 ⋙
      galoisDerivedGlobalSections Λᵐᵒᵖ (Over.mk f) kbar ⋙ DerivedCategory.Plus.ι).obj A)
      (homOpSheaf_cyclotomic_eq_etaleHomOpRepresentationFunctor_obj B X f kbar y n Λ M))

end AlgebraicGeometry

end
