module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportGroupHomologyNotProjectiveLine
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RootsOfUnityHomTwist
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.DerivedLowerShriekFibreHomology

/-!
# The twisted homology `H_i(π₁(X_k̄), M)(-1)`

The Tate twist `N(-1)` of a `Λ`-module `N` killed by `n = #Λ` is, with no choice of root of
unity, `Hom(μ_n(k̄), N)` (`Stacks.EtaleCohomology.rootsOfUnityHomEvalEquiv`). Postcomposing the
universal homology `H_i(π₁(X_k̄), -)` with the exact functor `N ↦ Hom(μ_n(k̄), N)` gives the
universal homological δ-functor `M ↦ H_i(π₁(X_k̄), M)(-1)` of Tag 03VM. Any isomorphism in
degree zero `H²_c(X_k̄, ℱ_ρ) ≅ (M_{π₁(X_k̄)})(-1)` (Tag 03VK) extends uniquely to an isomorphism of
δ-functors `H_c^{2-i}(X_k̄, ℱ_ρ) ≅ H_i(π₁(X_k̄), M)(-1)`, and an endomorphism of both δ-functors
commuting with it in degree zero (for instance the action of `Gal(k̄/k)`) commutes with it in every
degree.

## Main definitions

* `Stacks.EtaleCohomology.rootsOfUnityHomFunctor` — `N ↦ Hom(μ_n, N)`.
* `AlgebraicGeometry.geometricGroupHomologyTwist` — `M ↦ H_i(π₁(X_k̄), M)(-1)`.
* `AlgebraicGeometry.compactSupportGroupHomologyTwistIsoOfZero`.

## Main results

* `AlgebraicGeometry.isUniversal_geometricGroupHomologyTwist`.
* `Stacks.CategoryHomology.HomologicalDeltaFunctor.comm_of_comm_app_zero` — equivariance in every
  degree from equivariance in degree zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.EtaleCohomology
  Stacks.Frobenius

universe u

namespace Stacks.CategoryHomology.HomologicalDeltaFunctor

variable {A : Type*} [Category A] [Abelian A] {B : Type*} [Category B] [Abelian B]

/-- **Equivariance in every degree from equivariance in degree zero.** Endomorphisms `σ` of `T` and
`τ` of a universal `H` commuting with `α : T ⟶ H` in degree zero commute with it in every
degree. -/
theorem comm_of_comm_app_zero {T H : HomologicalDeltaFunctor A B} [H.IsUniversal] (α : T ⟶ H)
    (σ : T ⟶ T) (τ : H ⟶ H) (h : σ.app 0 ≫ α.app 0 = α.app 0 ≫ τ.app 0) :
    σ ≫ α = α ≫ τ :=
  IsUniversal.hom_ext_zero (by rw [comp_app, comp_app, h])

end Stacks.CategoryHomology.HomologicalDeltaFunctor

namespace Stacks.EtaleCohomology

/-- **`N ↦ Hom(μ_n(K), N)`**, the Tate twist `(-1)` on `Λ`-modules killed by `n`. -/
def rootsOfUnityHomFunctor (Λ : Type) [Ring Λ] (K : Type u) [Field K] (n : ℕ) :
    ModuleCat.{u + 1} Λ ⥤ ModuleCat.{u + 1} Λ where
  obj N := ModuleCat.of Λ (Additive (_root_.rootsOfUnity n K) →+ N)
  map g := ModuleCat.ofHom
    { toFun := fun φ ↦ g.hom.toAddMonoidHom.comp φ
      map_add' := fun φ ψ ↦ AddMonoidHom.ext fun x ↦ g.hom.map_add (φ x) (ψ x)
      map_smul' := fun r φ ↦ AddMonoidHom.ext fun x ↦ g.hom.map_smul r (φ x) }
  map_id _ := rfl
  map_comp _ _ := rfl

variable (Λ : Type) [Ring Λ] (K : Type u) [Field K] (n : ℕ)
  [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) [Fintype Λ] (hn : Fintype.card Λ = n)

include hn in
/-- A module over a finite ring of order `n` is killed by `n`. -/
lemma nsmul_eq_zero_of_card_eq (N : ModuleCat.{u + 1} Λ) (m : N) : n • m = 0 := by
  subst hn
  exact card_nsmul_eq_zero_of_module Λ m

include hζ hn in
/-- **`Hom(μ_n, -) ≅ 𝟭`** on `Λ`-modules, by evaluation at the primitive root `ζ`. -/
def rootsOfUnityHomFunctorIsoId : rootsOfUnityHomFunctor Λ K n ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun N ↦ ((rootsOfUnityHomEvalEquiv hζ Λ (nsmul_eq_zero_of_card_eq Λ n hn N)).toModuleIso :
      (rootsOfUnityHomFunctor Λ K n).obj N ≅ N))
    (fun _ ↦ rfl)

include hζ hn in
/-- `N ↦ Hom(μ_n(K), N)` preserves finite limits when `K` has a primitive `n`-th root of unity. -/
lemma preservesFiniteLimits_rootsOfUnityHomFunctor :
    PreservesFiniteLimits (rootsOfUnityHomFunctor Λ K n) :=
  preservesFiniteLimits_of_natIso (rootsOfUnityHomFunctorIsoId Λ K n hζ hn).symm

include hζ hn in
/-- `N ↦ Hom(μ_n(K), N)` preserves finite colimits when `K` has a primitive `n`-th root of
unity. -/
lemma preservesFiniteColimits_rootsOfUnityHomFunctor :
    PreservesFiniteColimits (rootsOfUnityHomFunctor Λ K n) :=
  preservesFiniteColimits_of_natIso (rootsOfUnityHomFunctorIsoId Λ K n hζ hn).symm

omit [NeZero n] [Fintype Λ] in
/-- `N ↦ Hom(μ_n(K), N)` is an additive functor. -/
instance : (rootsOfUnityHomFunctor Λ K n).Additive where
  map_add := by
    intros
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro φ; apply AddMonoidHom.ext; intro x
    rfl

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

attribute [local instance] compactSpace_etaleFundamentalGroup

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [IsAlgClosure k kbar]
  (Λ : Type) [Ring Λ] [Fintype Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) (j : CompactificationOf (Over.mk f))
  [CompactSpace X.1] [QuasiSeparatedSpace X.1] (hn : IsUnit ((Fintype.card Λ : ℕ) : kbar))

include hn in
/-- **The twisted homology `M ↦ H_i(π₁(X_k̄, η̄), M)(-1)`**, `(-1) = Hom(μ_{#Λ}(k̄), -)`. -/
def geometricGroupHomologyTwist :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    Stacks.CategoryHomology.HomologicalDeltaFunctor
      (FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
      (ModuleCat.{u + 1} Λ) :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  haveI := preservesFiniteLimits_rootsOfUnityHomFunctor Λ kbar (Fintype.card Λ)
    (exists_isPrimitiveRoot_of_isUnit hn).choose_spec rfl
  haveI := preservesFiniteColimits_rootsOfUnityHomFunctor Λ kbar (Fintype.card Λ)
    (exists_isPrimitiveRoot_of_isUnit hn).choose_spec rfl
  (geometricGroupHomology B X f kbar Λ y).postcomp
    (rootsOfUnityHomFunctor Λ kbar (Fintype.card Λ))

omit [Smooth f] [IsAlgClosure k kbar] [CompactSpace X.1] [QuasiSeparatedSpace X.1] in
/-- In degree `i`, the twisted homology is `H_i(π₁(X_k̄, η̄), -)` followed by
`Hom(μ_{#Λ}(k̄), -)`. -/
lemma geometricGroupHomologyTwist_functor (i : ℕ) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    (geometricGroupHomologyTwist B X f kbar Λ y hn).functor i =
      (geometricGroupHomology B X f kbar Λ y).functor i ⋙
        rootsOfUnityHomFunctor Λ kbar (Fintype.card Λ) :=
  rfl

variable (hcomp : letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    IsIso (geometricComparison B X Λ f kbar (contains_fieldBaseChange_of_isCurve B X f kbar) y))
  (hcompOp : letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    IsIso (geometricComparison B X Λᵐᵒᵖ f kbar (contains_fieldBaseChange_of_isCurve B X f kbar) y))

include hn hcompOp j in
/-- **`M ↦ H_i(π₁(X_k̄), M)(-1)` is a universal homological δ-functor.** -/
theorem isUniversal_geometricGroupHomologyTwist :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    (geometricGroupHomologyTwist B X f kbar Λ y hn).IsUniversal := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  have := preservesFiniteLimits_rootsOfUnityHomFunctor Λ kbar (Fintype.card Λ)
    (exists_isPrimitiveRoot_of_isUnit hn).choose_spec rfl
  have := preservesFiniteColimits_rootsOfUnityHomFunctor Λ kbar (Fintype.card Λ)
    (exists_isPrimitiveRoot_of_isUnit hn).choose_spec rfl
  have := coeffaceable_geometricGroupHomology B X f kbar Λ y j hn hcompOp
  have : (geometricGroupHomologyTwist B X f kbar Λ y hn).Coeffaceable :=
    Stacks.CategoryHomology.HomologicalDeltaFunctor.Coeffaceable.postcomp
      (rootsOfUnityHomFunctor Λ kbar (Fintype.card Λ)) (geometricGroupHomology B X f kbar Λ y)
  exact Stacks.CategoryHomology.HomologicalDeltaFunctor.isUniversal_of_coeffaceable _

include hn hcomp hcompOp j in
/-- **`H_c^{2-i}(X_k̄, ℱ_ρ) ≅ H_i(π₁(X_k̄, η̄), M)(-1)`** as homological δ-functors, extending any
degree-zero isomorphism `H²_c(X_k̄, ℱ_ρ) ≅ (M_{π₁(X_k̄)})(-1)` (Tag 03VK). -/
def compactSupportGroupHomologyTwistIsoOfZero {ζ : kbar} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ))
    (e₀ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      (compactSupportRepresentationHomology B X
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)
        Λ f j kbar).functor 0 ≅ (geometricGroupHomologyTwist B X f kbar Λ y hn).functor 0) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    compactSupportRepresentationHomology B X
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)
        Λ f j kbar ≅ geometricGroupHomologyTwist B X f kbar Λ y hn :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  haveI := isUniversal_compactSupportRepresentationHomology B X f kbar Λ y j hn hζ hcomp hcompOp
  haveI := isUniversal_geometricGroupHomologyTwist B X f kbar Λ y j hn hcompOp
  Stacks.CategoryHomology.HomologicalDeltaFunctor.IsUniversal.isoOfIso e₀

end AlgebraicGeometry

end
