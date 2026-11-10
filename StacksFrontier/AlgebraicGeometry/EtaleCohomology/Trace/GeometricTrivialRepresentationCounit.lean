module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportGeometricCoinvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantSheafCounitTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafTrivialization

/-!
# `ℱ_ρ|_{X_k̄}` is the constant sheaf on its global sections when `π₁(X_k̄)` acts trivially

Let `X` be a geometrically connected smooth curve over `k` and `ρ` a finite `Λ`-module with a
continuous action of `π₁(X, η̄)` on which the image of `π₁(X_k̄, η̄)` acts trivially. Then
`G = ℱ_ρ|_{X_k̄}` is constant, and the counit `Γ(X_k̄, G)_{X_k̄} ⟶ G` of the constant sheaf
adjunction is an isomorphism. It is the canonical identification of `G` with a constant sheaf:
the proof that it is an isomorphism compares `G` with `M_{X_k̄}` through Tag 0DV6
(`AlgebraicGeometry.representationSheafFieldBaseChangeIso`), but the counit itself involves no
choice.

## Main results

* `Stacks.EtaleCohomology.isIso_constantSheafΓAdj_unit_app_of_finite` — on a nonempty scheme,
  the unit `M ⟶ Γ(X, M_X)` is an isomorphism when `M` is finite and `Γ(X, M_X)` has at most as
  many elements.
* `AlgebraicGeometry.isIso_constantSheafΓAdj_counit_geometricRepresentationSheaf` — the counit is
  an isomorphism for `ℱ_ρ|_{X_k̄}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Stacks.GroupCohomology Stacks.Frobenius Stacks.EtaleCohomology

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCatHasColimitsOfSizeSmallEtale
  hasGlobalSectionsFunctorSmallEtaleModuleCat

/-- **The unit `M ⟶ Γ(X, M_X)` is an isomorphism** on a nonempty scheme, for a finite `M` such
that `Γ(X, M_X)` is in bijection with `M`. -/
theorem isIso_constantSheafΓAdj_unit_app_of_equiv (Λ : Type) [Ring Λ] {X : Scheme.{u}}
    [Nonempty X] (M : ModuleCat.{u + 1} Λ) [Finite M]
    (e : ((etaleModuleGlobalSections.{u, 0} Λ X).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) ≃ M) :
    IsIso ((constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).unit.app M) := by
  have hinj := injective_constantSheafΓAdj_unit_app Λ M (X := X)
  have : Finite ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
      Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
    Finite.of_equiv _ e.symm
  have hbij := hinj.bijective_of_nat_card_le (Nat.card_congr e).le
  exact (ConcreteCategory.isIso_iff_bijective _).2 hbij

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

attribute [local instance] Stacks.EtaleCohomology.moduleCatHasColimitsOfSizeSmallEtale
  Stacks.EtaleCohomology.hasGlobalSectionsFunctorSmallEtaleModuleCat

section Counit

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar]
  (Λ : Type) [Ring Λ] [Fintype Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar))

omit [Smooth f] [IsAlgClosed kbar] [Fintype Λ] in
/-- **The counit `Γ(X_k̄, G)_{X_k̄} ⟶ G` is an isomorphism for `G = ℱ_ρ|_{X_k̄}`** when the image
of `π₁(X_k̄, η̄)` acts trivially on `ρ`. -/
theorem isIso_constantSheafΓAdj_counit_geometricRepresentationSheaf [Finite Λ]
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (hρ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, ρ.obj.obj.obj.ρ (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1) :
    letI := connectedSpace_of_isCurve B X f
    IsIso ((constantSheafΓAdj (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).counit.app
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk f) kbar)).obj
        ((representationSheaf B X _ Λ).obj ρ))) := by
  have := Fintype.ofFinite Λ
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have : Nonempty (fieldBaseChange (Over.mk f) kbar) :=
    (inferInstance : ConnectedSpace (fieldBaseChange (Over.mk f) kbar)).toNonempty
  let U := fieldBaseChangeObj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)
  let φ := etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
    (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y
  let M : ObjectProperty.FullSubcategory (ModuleCat.isFG.{u + 1} Λ) :=
    ⟨ρ.obj.obj.obj.V, ρ.property⟩
  have : Module.Finite Λ M.obj := M.property
  have : Finite M.obj := Module.finite_of_finite Λ
  -- `G ≅ ℱ_{triv M} ≅ (M lifted)_{X_k̄}`
  let e₁ := (representationSheafFieldBaseChangeIso B X f kbar Λ y).app ρ
  let e₂ := (representationSheaf B U y Λ).mapIso
    (finiteTypeContinuousModuleTrivialIsoRes Λ φ ρ hρ).symm
  let e₃ := (representationSheafTrivialIsoConstant B U y Λ).app M
  let M₀ := (ModuleCat.uliftFunctor.{0, u + 1} Λ).obj M.obj
  have : Finite M₀ := Finite.of_equiv _ Equiv.ulift.symm
  -- `Γ(X_k̄, (M₀)_{X_k̄}) ≅ M₀`
  let g : (etaleModuleGlobalSections.{u, 0} Λ U.1).obj
      ((constantSheaf U.1.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M₀) ≅ M₀ :=
    (etaleModuleGlobalSections.{u, 0} Λ U.1).mapIso e₃.symm ≪≫
      (representationSheafGlobalSectionsIso B U y Λ).app
        ((finiteTypeContinuousModuleTrivial Λ _).obj M) ≪≫
      (ModuleCat.uliftFunctor.{0, u + 1} Λ).mapIso
        ((finiteTypeContinuousModuleTrivialInvariantsIso Λ _).app M)
  exact isIso_constantSheafΓAdj_counit_app_of_iso Λ (e₃.symm ≪≫ e₂.symm ≪≫ e₁.symm)
    (isIso_constantSheafΓAdj_unit_app_of_equiv Λ M₀ g.toLinearEquiv.toEquiv)

end Counit

end AlgebraicGeometry

end
