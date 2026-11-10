module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportGeometricCoinvariantsEquiv
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportTateTwistCoinvariants
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GeometricQuotientGaloisEquiv

/-!
# The Galois action on the geometric coinvariants `M_{π₁(X_k̄)}`

For a representation `ρ` of `π₁(X, η̄)`, the coinvariants of its restriction along
`π₁(X_k̄, η̄) ⟶ π₁(X, η̄)` are the coinvariants of the image `N`, a normal subgroup, so they carry
the residual action of `π₁(X, η̄) ⧸ N ≃ Aut(k̄/k)`
(`AlgebraicGeometry.geometricQuotientGaloisEquiv`, Tags 0BTX and 0BNE): the `Gal(k^{sep}/k)`-module
`M_{π₁(X_k̄, η̄)}` of Tag 03VK, as `Stacks.EtaleCohomology.galoisCoinvariantsRepresentation`.

## Main definitions

* `AlgebraicGeometry.geometricCoinvariantsRangeEquiv` — the coinvariants of the restriction are
  the coinvariants of the image `N`.
* `AlgebraicGeometry.compactSupportGaloisTwistEquiv` — `H²_c(X_k̄, ℱ_ρ) ≃ Hom(μ_n(k̄), M_N)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Stacks.GroupCohomology Stacks.Frobenius Stacks.EtaleCohomology

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

section Galois

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar]
  (Λ : Type) [Ring Λ] [Fintype Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar))

omit [Smooth f] [IsAlgClosed kbar] [Fintype Λ] in
/-- **The coinvariants of the restriction to `π₁(X_k̄)` are the coinvariants of its image.** -/
theorem coinvariantsKer_geometricRepresentation_eq [Finite Λ]
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    Stacks.Trace.coinvariantsKer (geometricRepresentation B X f kbar Λ y ρ) =
      Stacks.Trace.coinvariantsKer ((finiteTypeContinuousModuleRepresentation Λ _ ρ).comp
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom.range.subtype) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  refine congrArg (Submodule.span Λ) (Set.ext fun v => ⟨?_, ?_⟩)
  · rintro ⟨⟨g, m⟩, rfl⟩
    exact ⟨(⟨_, g, rfl⟩, m), rfl⟩
  · rintro ⟨⟨⟨_, g, rfl⟩, m⟩, rfl⟩
    exact ⟨(g, m), rfl⟩

/-- **`M_{π₁(X_k̄)}` as the coinvariants of the image `N` of `π₁(X_k̄, η̄)` in `π₁(X, η̄)`.** -/
def geometricCoinvariantsRangeEquiv
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    Stacks.Trace.coinvariants (geometricRepresentation B X f kbar Λ y ρ) ≃ₗ[Λ]
      Stacks.Trace.coinvariants ((finiteTypeContinuousModuleRepresentation Λ _ ρ).comp
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom.range.subtype) :=
  Submodule.quotEquivOfEq _ _ (coinvariantsKer_geometricRepresentation_eq B X f kbar Λ y ρ)

/-- **The `Gal(k^{sep}/k) = Aut(k̄/k)`-module `M_{π₁(X_k̄, η̄)}` of Tag 03VK**: the residual action
of `π₁(X, η̄) ⧸ N ≃ Aut(k̄/k)` on the coinvariants of `N`. -/
abbrev geometricCoinvariantsGaloisRepresentation
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    Representation Λ (kbar ≃ₐ[k] kbar)
      (Stacks.Trace.coinvariants ((finiteTypeContinuousModuleRepresentation Λ _ ρ).comp
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom.range.subtype)) :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  galoisCoinvariantsRepresentation (finiteTypeContinuousModuleRepresentation Λ _ ρ) _
    (geometricQuotientGaloisEquiv B X f kbar y)

end Galois

section Congr

variable {R : Type*} [Ring R] {A M M' : Type*} [AddCommGroup A] [AddCommGroup M]
  [AddCommGroup M'] [Module R M] [Module R M']

/-- Postcomposition with a linear isomorphism, on additive maps out of `A`. -/
def addMonoidHomCongrRightLinearEquiv (e : M ≃ₗ[R] M') : (A →+ M) ≃ₗ[R] (A →+ M') where
  toFun g := e.toAddMonoidHom.comp g
  invFun g := e.symm.toAddMonoidHom.comp g
  left_inv g := AddMonoidHom.ext fun a => e.symm_apply_apply (g a)
  right_inv g := AddMonoidHom.ext fun a => e.apply_symm_apply (g a)
  map_add' g g' := AddMonoidHom.ext fun a => map_add e (g a) (g' a)
  map_smul' c g := AddMonoidHom.ext fun a => map_smul e c (g a)

end Congr

section Twist

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar]
  (Λ : Type) [Ring Λ] [Fintype Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar))
  (j : CompactificationOf (Over.mk f)) (hn : IsUnit ((Fintype.card Λ : ℕ) : kbar))

/-- **`H²_c(X_k̄, ℱ_ρ) ≃ Hom(μ_n(k̄), M_{π₁(X_k̄, η̄)}) = M_{π₁(X_k̄, η̄)}(-1)`**, with the
coinvariants taken over the image of `π₁(X_k̄, η̄)` in `π₁(X, η̄)`, which carries the Galois action
`AlgebraicGeometry.geometricCoinvariantsGaloisRepresentation`. No root of unity is chosen in its
values (`AlgebraicGeometry.compactSupportGeometricTwistEquiv_apply_ofMul`). -/
def compactSupportGaloisTwistEquiv
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X _ Λ).obj ρ)) ((2 : ℕ) : ℤ) ≃ₗ[Λ]
      (Additive (_root_.rootsOfUnity (Fintype.card Λ) kbar) →+
        Stacks.Trace.coinvariants ((finiteTypeContinuousModuleRepresentation Λ _ ρ).comp
          (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
            (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom.range.subtype)) :=
  (compactSupportGeometricTwistEquiv B X f kbar Λ y j hn ρ).trans
    (addMonoidHomCongrRightLinearEquiv (geometricCoinvariantsRangeEquiv B X f kbar Λ y ρ))

end Twist

end AlgebraicGeometry

end
