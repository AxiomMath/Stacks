module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafCohomologyDelta
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSmoothModelNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveSecondCohomologyRightExact
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.TwoSubReindex

/-!
# `(M, ρ) ↦ H_c^{2-i}(X_k̄, ℱ_ρ)` as a homological δ-functor on representations

Let `X` be a smooth geometrically connected curve over a field `k`, `j` a compactification of `X`
over `k`, `k̄` an algebraically closed extension of `k`, `x` a geometric point of `X` and `Λ` a
finite ring. Compactly supported cohomology of `X_k̄` is computed on the smooth projective model
`C` of `X_k̄` (`Stacks.EtaleCohomology.galoisCompactSupportSmoothModelIso`):
`H^q_c(X_k̄, ℱ) ≅ H^q(C, j_{C!}(ℱ|_{X_k̄}))`, naturally in `ℱ`.

This file makes the right hand side, as a function of the representation, a δ-functor:

* `AlgebraicGeometry.compactSupportRepresentationSheaf`: the exact functor
  `ρ ↦ j_{C!}(ℱ_ρ|_{X_k̄})` from finite `Λ`-modules with continuous `π₁(X, x)`-action to sheaves of
  `Λ`-modules on `C`;
* `AlgebraicGeometry.compactSupportRepresentationCohomology`: the cohomological δ-functor
  `ρ ↦ H^q(C, j_{C!}(ℱ_ρ|_{X_k̄}))`, the right derived functors of global sections on `C`
  precomposed with that exact functor;
* `AlgebraicGeometry.isZero_compactSupportRepresentationCohomology_three`: its degree three part
  vanishes (Tag 03SC on the curve `C`);
* `AlgebraicGeometry.compactSupportRepresentationHomology`: the homological δ-functor
  `Tᵢ(ρ) = H^{2-i}(C, j_{C!}(ℱ_ρ|_{X_k̄}))`, `Tᵢ = 0` for `i > 2`. This is the family of functors
  `(M, ρ) ↦ H_c^{2-i}(X_k̄, ℱ_ρ)` of Stacks 03VM.
* `AlgebraicGeometry.compactSupportRepresentationHomologyIso`: `Tᵢ(ρ) ≅ H_c^{2-i}(X_k̄, ℱ_ρ)`,
  and its naturality in `ρ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1]
  (x : GeometricPoint X.1) (Λ : Type) [Ring Λ] [Finite Λ]
  {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
  [GeometricallyConnected f] (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar]

/-- **`ρ ↦ j_{C!}(ℱ_ρ|_{X_k̄})`**, the sheaf on the smooth projective model `C` of `X_k̄` whose
cohomology is the compactly supported cohomology of `ℱ_ρ` on `X_k̄`. -/
def compactSupportRepresentationSheaf :
    FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x) ⥤
      EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb :=
  geometricRepresentationSheaf B X x Λ f kbar ⋙
    etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j

/-- `ρ ↦ j_{C!}(ℱ_ρ|_{X_k̄})` preserves finite limits. -/
theorem preservesFiniteLimits_compactSupportRepresentationSheaf :
    PreservesFiniteLimits (compactSupportRepresentationSheaf B X x Λ f j kbar) :=
  have := preservesFiniteLimits_geometricRepresentationSheaf B X x Λ f kbar
  Limits.comp_preservesFiniteLimits _ _

/-- `ρ ↦ j_{C!}(ℱ_ρ|_{X_k̄})` preserves finite colimits. -/
theorem preservesFiniteColimits_compactSupportRepresentationSheaf :
    PreservesFiniteColimits (compactSupportRepresentationSheaf B X x Λ f j kbar) :=
  have := preservesFiniteColimits_geometricRepresentationSheaf B X x Λ f kbar
  Limits.comp_preservesFiniteColimits _ _

/-- `ρ ↦ j_{C!}(ℱ_ρ|_{X_k̄})` is additive, being exact. -/
instance additive_compactSupportRepresentationSheaf :
    (compactSupportRepresentationSheaf B X x Λ f j kbar).Additive :=
  have := preservesFiniteLimits_compactSupportRepresentationSheaf B X x Λ f j kbar
  Functor.additive_of_preserves_binary_products _

/-- **The cohomological δ-functor `ρ ↦ H^q(C, j_{C!}(ℱ_ρ|_{X_k̄}))`**: the right derived functors
of global sections on the smooth projective model `C` of `X_k̄`, precomposed with the exact functor
`ρ ↦ j_{C!}(ℱ_ρ|_{X_k̄})`. -/
def compactSupportRepresentationCohomology :
    DeltaFunctor (FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
      (ModuleCat.{u + 1} Λ) :=
  let := etaleModules_enoughInjectives.{u, 0} Λ (geometricSmoothModel f j kbar).Vb
  let := HasDerivedCategory.standard (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb)
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} Λ)
  have := preservesFiniteLimits_compactSupportRepresentationSheaf B X x Λ f j kbar
  have := preservesFiniteColimits_compactSupportRepresentationSheaf B X x Λ f j kbar
  (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb)).precomp
    (compactSupportRepresentationSheaf B X x Λ f j kbar)

/-- The degree-`n` component of `AlgebraicGeometry.compactSupportRepresentationCohomology` is
`ρ ↦ Rⁿ Γ(C, j_{C!}(ℱ_ρ|_{X_k̄}))`. -/
theorem compactSupportRepresentationCohomology_functor (n : ℕ) :
    (compactSupportRepresentationCohomology B X x Λ f j kbar).functor n =
      compactSupportRepresentationSheaf B X x Λ f j kbar ⋙
        letI := etaleModules_enoughInjectives.{u, 0} Λ (geometricSmoothModel f j kbar).Vb
        (etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerived n :=
  rfl

/-- **`H³(C, j_{C!}(ℱ_ρ|_{X_k̄})) = 0`** (Tag 03SC on the curve `C` over `k̄`). -/
theorem isZero_compactSupportRepresentationCohomology_three
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    IsZero (((compactSupportRepresentationCohomology B X x Λ f j kbar).functor 3).obj M) := by
  let := etaleModules_enoughInjectives.{u, 0} Λ (geometricSmoothModel f j kbar).Vb
  let := HasDerivedCategory.standard (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb)
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} Λ)
  have := (geometricSmoothModel f j kbar).isCurve
  exact (isZero_rightDerivedPlus_three_of_isCurve (geometricSmoothModel f j kbar).q Λ
    ((compactSupportRepresentationSheaf B X x Λ f j kbar).obj M)).of_iso
    ((Stacks.DerivedIndexing.rightDerivedIso _ 3).app _)

/-- **The homological δ-functor `Tᵢ(ρ) = H_c^{2-i}(X_k̄, ℱ_ρ)`** of Stacks 03VM, computed on the
smooth projective model `C` of `X_k̄`: `Tᵢ(ρ) = H^{2-i}(C, j_{C!}(ℱ_ρ|_{X_k̄}))` for `i ≤ 2` and
`Tᵢ = 0` for `i > 2`, with the connecting maps of cohomology on `C` read backwards. -/
def compactSupportRepresentationHomology :
    Stacks.CategoryHomology.HomologicalDeltaFunctor
      (FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
      (ModuleCat.{u + 1} Λ) :=
  Stacks.CategoryHomology.HomologicalDeltaFunctor.ofDeltaFunctorTwoSub
    (compactSupportRepresentationCohomology B X x Λ f j kbar)
    (isZero_compactSupportRepresentationCohomology_three B X x Λ f j kbar)

/-- **`Tᵢ(ρ) ≅ H_c^{2-i}(X_k̄, ℱ_ρ)`**: the `i`-th functor of
`AlgebraicGeometry.compactSupportRepresentationHomology` is compactly supported cohomology of
`ℱ_ρ` on `X_k̄` in degree `2 - i`, for `i ≤ 2`. -/
def compactSupportRepresentationHomologyIso (i : ℕ) (hi : i ≤ 2)
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    ((compactSupportRepresentationHomology B X x Λ f j kbar).functor i).obj M ≅
      galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X x Λ).obj M)) ((2 - i : ℕ) : ℤ) :=
  let := etaleModules_enoughInjectives.{u, 0} Λ (geometricSmoothModel f j kbar).Vb
  let := HasDerivedCategory.standard (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb)
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} Λ)
  have e : ((compactSupportRepresentationHomology B X x Λ f j kbar).functor i).obj M =
      ((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerived
        (2 - i)).obj ((compactSupportRepresentationSheaf B X x Λ f j kbar).obj M) := by
    rcases i with _ | _ | _ | i
    · rfl
    · rfl
    · rfl
    · omega
  eqToIso e ≪≫ (Stacks.DerivedIndexing.rightDerivedIso _ (2 - i)).app _ ≪≫
    (galoisCompactSupportSmoothModelIso f j kbar Λ ((representationSheaf B X x Λ).obj M)
      ((2 - i : ℕ) : ℤ)).symm

end AlgebraicGeometry

end
