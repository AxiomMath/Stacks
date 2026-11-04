module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpERepresentationDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafLocalValue
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.RestrictScalarsConstructible
public import StacksFrontier.Algebra.Module.Injective.ZModSelfInjective
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# `E ≅ RΓ^Gal(X, ℋom_ℤ(ℱ_M, ℱ_μ))` when `n` is invertible

The identification `AlgebraicGeometry.galoisHomOpECyclotomicDerivedIso` of the complex
`E = Γ^Gal(X̄, ℋom^•_ℤ(I, K))` of the evaluation pairing of Tag 03VM with
`RΓ^Gal(X, ℋom_ℤ(ℱ_M, ℱ_μ))` has two side conditions, both automatic when `n` is invertible in
`k̄`:

* `ℱ_M`, as a sheaf of `ℤ/n`-modules, is locally constant with finitely presented values: its
  local values are `M` (`AlgebraicGeometry.isLocallyConstantWith_representationSheaf`), a finite
  set, hence finitely presented over the noetherian ring `ℤ/n`;
* `ℱ_μ` is locally constant with injective values: its local values are `μ_n(k̄) ≅ ℤ/n`, and
  `ℤ/n` is self-injective (`ZMod.baer_self`).

## Main results

* `isFinitePresentationLocallyConstantModuleSheaf_restrictScalars_representationSheaf` (in
  `AlgebraicGeometry`).
* `AlgebraicGeometry.isLocallyConstantInjective_representationSheaf_cyclotomic`.
* `AlgebraicGeometry.galoisHomOpECyclotomicDerivedIsoOfIsUnit` — the identification without the
  side conditions.

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry Stacks.GroupCohomology Stacks.Frobenius Stacks.EtaleCohomology
open Stacks.AbelianInternalHom Stacks.ConstantSheaf

universe w w₁ w₂ w₃ w₄ u

namespace Stacks.EtaleCohomology

/-- **`μ_n(K)` satisfies Baer's criterion over `ℤ/n`** for a separably closed field `K` in
which `n` is invertible: it is cyclic of order `n`, so isomorphic to `ℤ/n`, which is
self-injective. -/
theorem baer_uliftRootsOfUnity (K : Type*) [Field K] [IsSepClosed K] (n : ℕ) [NeZero n]
    (hn : IsUnit ((n : ℕ) : K)) :
    Module.Baer (ZMod n) (ULift.{w} (Additive (rootsOfUnity n K))) := by
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  have hc : IsAddCyclic (Additive (rootsOfUnity n K)) := isAddCyclic_additive_iff.2 inferInstance
  have hcard : Nat.card (Additive (rootsOfUnity n K)) = n :=
    HasEnoughRootsOfUnity.natCard_rootsOfUnity K n
  let e : ZMod n ≃+ ULift.{w} (Additive (rootsOfUnity n K)) :=
    ((ZMod.ringEquivCongr hcard.symm).toAddEquiv.trans (zmodAddCyclicAddEquiv hc)).trans
      AddEquiv.ulift.symm
  exact Module.Baer.of_equiv
    (LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap n) e.bijective)
    (ZMod.baer_self n)

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

section FinitePresentation

/-- Sheafification of presheaves of `Λ`-modules on a slice of Mathlib's small étale site, at the
module universe `u + 1`. -/
local instance (priority := 3000) etaleModules_over_hasSheafify_typeZero (Λ : Type) [Ring Λ]
    (Y : Scheme.{u}) (V : Y.Etale) :
    HasSheafify (Y.smallEtaleTopology.over V) (ModuleCat.{u + 1} Λ) :=
  Stacks.ModuleSheaf.hasSheafify_over_moduleCat.{u + 1, 0, u + 1, u} Λ Y.smallEtaleTopology V

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (n : ℕ) [NeZero n] (Λ : Type) [Ring Λ] [Finite Λ] [Algebra (ZMod n) Λ]

/-- **`ℱ_M` is a locally constant sheaf of finitely presented `ℤ/n`-modules**, for a finite
`ℤ/n`-algebra `Λ` and a finite `Λ`-module `M` with continuous `π₁(X, x)`-action: its local values
are `M` (`AlgebraicGeometry.isLocallyConstantWith_representationSheaf`), which is finite, hence
finitely presented over the noetherian ring `ℤ/n`. -/
theorem isFinitePresentationLocallyConstantModuleSheaf_restrictScalars_representationSheaf
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, 0, 0} X.1.smallEtaleTopology
      (ZMod n) ((etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) X.1).obj
        ((representationSheaf B X x Λ).obj M)) := by
  have h := isLocallyConstantWith_restrictScalars.{u + 1} X.1.smallEtaleTopology
    (algebraMap (ZMod n) Λ) _ _ (isLocallyConstantWith_representationSheaf B X x Λ M)
  intro U
  obtain ⟨I, V, f, hf, hV⟩ := h U
  refine ⟨I, V, f, hf, fun i ↦ ?_⟩
  obtain ⟨E', ⟨E, ⟨eE⟩, ⟨e'⟩⟩, he⟩ := hV i
  refine ⟨E', ?_, he⟩
  have : Module.Finite Λ M.obj.obj.obj.V := M.property
  have : Finite M.obj.obj.obj.V := Module.finite_of_finite Λ
  have : Finite ((ModuleCat.restrictScalars (algebraMap (ZMod n) Λ)).obj M.obj.obj.obj.V) :=
    inferInstanceAs (Finite M.obj.obj.obj.V)
  have : Finite E' := Finite.of_equiv _
    (e'.symm ≪≫
      (ModuleCat.restrictScalars (algebraMap (ZMod n) Λ)).mapIso eE).toLinearEquiv.toEquiv.symm
  have : Module.Finite (ZMod n) E' := Module.Finite.of_finite
  exact Module.finitePresentation_of_finite _ _

end FinitePresentation

section Cyclotomic

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) (n : ℕ) [NeZero n]

/-- **`ℱ_μ` is locally constant with injective values**, when `n` is invertible in `k̄`: its local
values are `μ_n(k̄) ≅ ℤ/n` (`AlgebraicGeometry.isLocallyConstantWith_representationSheaf`), and
`ℤ/n` is self-injective. -/
theorem isLocallyConstantInjective_representationSheaf_cyclotomic
    (hn : IsUnit ((n : ℕ) : kbar)) :
    letI := connectedSpace_of_isCurve B X f
    Stacks.ModuleInternalHom.IsLocallyConstantInjective X.1.smallEtaleTopology (ZMod n)
      ((representationSheaf B X _ (ZMod n)).obj (cyclotomicContinuousModule B X f kbar y n)) := by
  let := connectedSpace_of_isCurve B X f
  have h := isLocallyConstantWith_representationSheaf B X _ (ZMod n)
    (cyclotomicContinuousModule B X f kbar y n)
  have hV : Module.Baer (ZMod n)
      (cyclotomicContinuousModule B X f kbar y n).obj.obj.obj.V :=
    baer_uliftRootsOfUnity.{u + 1} kbar n hn
  intro U
  obtain ⟨I, V, g, hg, hU⟩ := h U
  refine ⟨I, V, g, hg, fun i ↦ ?_⟩
  obtain ⟨E, ⟨eE⟩, he⟩ := hU i
  exact ⟨E, (Module.Baer.of_equiv eE.symm.toLinearEquiv hV).injective, he⟩

end Cyclotomic

section DerivedIso

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

/-- **`E = Γ^Gal(X̄, ℋom^•_ℤ(I, K)) ≅ RΓ^Gal(X, ℋom_ℤ(ℱ_M, ℱ_μ))`** for `n` invertible in `k̄`:
`AlgebraicGeometry.galoisHomOpERepresentationDerivedIso` with its two side conditions
discharged. -/
def galoisHomOpERepresentationDerivedIsoOfIsUnit (hn : IsUnit ((n : ℕ) : kbar))
    [ConnectedSpace X.1] (x : GeometricPoint X.1)
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (I : CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor (EtaleModules.{u, 0} Λ (Over.mk j.toBase).left) 0).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
          ((representationSheaf B X x Λ).obj M))))
    [K₀.cocomplex.IsStrictlyGE 0] :
    DerivedCategory.Q.obj (galoisHomOpE (Over.mk j.toBase) kbar I.cocomplex
        (cyclotomicIntResolution B X f kbar y n j K₀)) ≅
      (DerivedCategory.Plus.singleFunctor _ 0 ⋙ galoisDerivedGlobalSections Λᵐᵒᵖ (Over.mk f) kbar ⋙
        DerivedCategory.Plus.ι).obj
        (homOpSheaf X.1.smallEtaleTopology ((representationSheaf B X x Λ).obj M)
          (letI := connectedSpace_of_isCurve B X f; toAb _ ((representationSheaf B X _ (ZMod n)).obj
            (cyclotomicContinuousModule B X f kbar y n)))) :=
  galoisHomOpERepresentationDerivedIso B X f kbar y n j K₀ Λ x M I
    (isFinitePresentationLocallyConstantModuleSheaf_restrictScalars_representationSheaf B X x n Λ M)
    (isLocallyConstantInjective_representationSheaf_cyclotomic B X f kbar y n hn)

/-- **`E ≅ RΓ^Gal(X, ℋom_ℤ(ℱ_M, ℱ_μ))`** for `n` invertible in `k̄`, with target written through
`AlgebraicGeometry.etaleHomOpRepresentationFunctor`, for `M` over the point `x_y` of `X` below
`y`: `AlgebraicGeometry.galoisHomOpECyclotomicDerivedIso` with its two side conditions
discharged. -/
def galoisHomOpECyclotomicDerivedIsoOfIsUnit (hn : IsUnit ((n : ℕ) : kbar)) [ConnectedSpace X.1]
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (I : CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor (EtaleModules.{u, 0} Λ (Over.mk j.toBase).left) 0).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
          ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
            (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj M))))
    [K₀.cocomplex.IsStrictlyGE 0] :
    DerivedCategory.Q.obj (galoisHomOpE (Over.mk j.toBase) kbar I.cocomplex
        (cyclotomicIntResolution B X f kbar y n j K₀)) ≅
      (DerivedCategory.Plus.singleFunctor _ 0 ⋙ galoisDerivedGlobalSections Λᵐᵒᵖ (Over.mk f) kbar ⋙
        DerivedCategory.Plus.ι).obj
        ((etaleHomOpRepresentationFunctor B X (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ n
            (cyclotomicContinuousModule B X f kbar y n)).obj (op M)) :=
  galoisHomOpECyclotomicDerivedIso B X f kbar y n j K₀ Λ M I
    (isFinitePresentationLocallyConstantModuleSheaf_restrictScalars_representationSheaf B X _ n Λ M)
    (isLocallyConstantInjective_representationSheaf_cyclotomic B X f kbar y n hn)

end DerivedIso

end AlgebraicGeometry

end
