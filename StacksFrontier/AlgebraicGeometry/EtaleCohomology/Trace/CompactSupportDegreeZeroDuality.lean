module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportCanonicalTwistNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafCompactSupportCoinvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CyclotomicRepresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.GlobalSections
public import StacksFrontier.Algebra.Module.CharacterModule.MulOpposite
public import StacksFrontier.Algebra.Module.CharacterModule.CyclicHomPairing

/-!
# Degree-zero duality: `H²_c(X_k̄, ℱ_ρ) = Hom_{π₁(X_k̄)}(M, μ_n)^∨`

Let `X` be a geometrically connected smooth curve over a field `k`, `k̄` an algebraic closure of
`k` separable over `k`, `η̄` a geometric point of `X_k̄`, `Λ` a finite ring with `n = #Λ`
invertible, and `ℱ_ρ` the sheaf attached to a finite `Λ`-module `M` with a continuous action `ρ`
of `π₁(X, η̄)`. Let `N` be the image of `π₁(X_k̄, η̄)`. This file proves the degree-zero case of
the Poincaré duality of [Stacks, Tag 03VM]:

`H²_c(X_k̄, ℱ_ρ) ≅ Hom_ℤ(Hom_N(M, μ_n(k̄)), ℚ/ℤ)`,

as `Λ`-modules and naturally in `ρ`. The class `α` goes to `b ↦ tr(b_* α)`, where
`Ψ : H²_c(X_k̄, ℱ_ρ) ≅ Hom(μ_n, M_N)` is the choice-free isomorphism of Tag 03VK
(`AlgebraicGeometry.compactSupportCanonicalTwistEquiv`). The map `b_*` is composition with the map
`b̄ : M_N → μ_n` induced by `b`, and `tr : Hom(μ_n, μ_n) = ℤ/n ⊂ ℚ/ℤ` involves no choice of a
root of unity. Here `Hom_N(M, μ_n)` is the `N`-invariants of the dual
`Hom(M, μ_n) = M^∨(1)` of `AlgebraicGeometry.cyclotomicDual`, a `Λᵐᵒᵖ`-module, and its character
module is a `Λ`-module (`CharacterModule.MulOppositeAction`).

The proof composes three bijections: `Ψ`; the composition pairing
`Hom(A, P) ≅ Hom(P, A)^∨` for `A` cyclic of order `n` and `nP = 0`
(`Stacks.CharacterModule.cyclicTwistPairing`); and `Hom_N(M, μ_n) ≅ Hom(M_N, μ_n)`, since `N` acts
trivially on `μ_n` (`AlgebraicGeometry.geometricCyclotomicDualInvariantsLift`).

## Main definitions

* `Stacks.CharacterModule.cyclicTwistPairing` — `Hom(A, P) → Hom(P, A)^∨`, `φ ↦ (ψ ↦ (ψ ∘ φ)/n)`.
* `AlgebraicGeometry.geometricCyclotomicDualInvariants` — `ρ ↦ Hom_N(M, μ_n)`, contravariant.
* `AlgebraicGeometry.compactSupportDegreeZeroPairing` — `α ↦ (b ↦ tr(b_* α))`.
* `AlgebraicGeometry.compactSupportDegreeZeroDualityIso` — `T₀ ≅ Hom_N(-, μ_n)^∨`, natural in `ρ`,
  for the homological δ-functor `T` of `AlgebraicGeometry.compactSupportRepresentationHomology`.

## Main results

* `Stacks.CharacterModule.cyclicTwistPairing_bijective`.
* `AlgebraicGeometry.compactSupportDegreeZeroPairing_apply` — the formula.
* `AlgebraicGeometry.bijective_compactSupportDegreeZeroPairing` — degree-zero duality.
* `AlgebraicGeometry.compactSupportDegreeZeroPairing_naturality` — naturality in `ρ`, from the
  naturality of `Ψ` (`AlgebraicGeometry.compactSupportCanonicalTwistEquiv_naturality`).

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Stacks.GroupCohomology Stacks.Frobenius Stacks.EtaleCohomology
open scoped CharacterModule.MulOppositeAction Stacks.ContinuousCohomology.InternalHomAction

universe u

namespace Stacks.CharacterModule

section TwistPairing

variable {A : Type*} [AddCommGroup A] {P : Type*} [AddCommGroup P] {n : ℕ} [NeZero n]
  [IsAddCyclic A] (hA : Nat.card A = n)

/-- **The pairing `Hom(A, P) → Hom(P, A)^∨`**, `φ ↦ (ψ ↦ (ψ ∘ φ)/n)`: the composition pairing of
`Stacks.CharacterModule.cyclicHomPairing` read from the other side. -/
def cyclicTwistPairing : (A →+ P) →+ CharacterModule (P →+ A) where
  toFun φ := (zmodToRatCircle n).comp ((cyclicEndScalarHom hA).comp (AddMonoidHom.compHom.flip φ))
  map_zero' := AddMonoidHom.ext fun ψ ↦ by
    change zmodToRatCircle n (cyclicEndScalarHom hA (ψ.comp 0)) = 0
    rw [AddMonoidHom.comp_zero, map_zero, map_zero]
  map_add' φ φ' := AddMonoidHom.ext fun ψ ↦ by
    change zmodToRatCircle n (cyclicEndScalarHom hA (ψ.comp (φ + φ'))) =
      zmodToRatCircle n (cyclicEndScalarHom hA (ψ.comp φ)) +
        zmodToRatCircle n (cyclicEndScalarHom hA (ψ.comp φ'))
    rw [AddMonoidHom.comp_add, map_add, map_add]

/-- `cyclicTwistPairing hA φ` sends `ψ` to the class of the scalar `ψ ∘ φ` in `ℚ/ℤ`. -/
theorem cyclicTwistPairing_apply (φ : A →+ P) (ψ : P →+ A) :
    (cyclicTwistPairing hA φ : (P →+ A) →+ AddCircle (1 : ℚ)) ψ =
      zmodToRatCircle n (cyclicEndScalar hA (ψ.comp φ)) :=
  rfl

variable (hP : ∀ p : P, n • p = 0)

include hP in
/-- **`Hom(A, P) ≅ Hom(P, A)^∨`** for `A` cyclic of order `n` and `P` finite killed by `n`. -/
theorem cyclicTwistPairing_bijective [Finite P] :
    Function.Bijective (cyclicTwistPairing hA (P := P)) := by
  have : Finite A := Nat.finite_of_card_ne_zero (hA ▸ NeZero.ne n)
  have : Finite (A →+ P) := Finite.of_injective _ DFunLike.coe_injective
  have : Finite (P →+ A) := Finite.of_injective _ DFunLike.coe_injective
  have hb := cyclicHomPairing_bijective hA hP
  have hinj : Function.Injective (cyclicTwistPairing hA (P := P)) := by
    rw [injective_iff_map_eq_zero]
    intro φ hφ
    refine CharacterModule.eq_zero_of_character_apply fun c ↦ ?_
    obtain ⟨ψ, rfl⟩ := hb.2 c
    exact DFunLike.congr_fun hφ ψ
  refine hinj.bijective_of_nat_card_le (le_of_eq ?_)
  rw [CharacterModule.natCard_eq, Nat.card_congr (Equiv.ofBijective _ hb),
    CharacterModule.natCard_eq]

section Linear

variable (R : Type*) [Ring R] [Module R P]

/-- **`Hom(A, P) → Hom(P, A)^∨` is `R`-linear** for an `R`-module `P`: `R` acts on `Hom(A, P)`
through `P`, on `Hom(P, A)` from the right through `P`, and on the character module through
that right action (`CharacterModule.MulOppositeAction`). -/
def cyclicTwistPairingLinear : (A →+ P) →ₗ[R] CharacterModule (P →+ A) where
  toFun := cyclicTwistPairing hA
  map_add' := map_add _
  map_smul' _ _ := rfl

/-- The underlying map of `cyclicTwistPairingLinear` is `cyclicTwistPairing`. -/
theorem cyclicTwistPairingLinear_apply (φ : A →+ P) :
    cyclicTwistPairingLinear hA R φ = cyclicTwistPairing hA φ :=
  rfl

end Linear

end TwistPairing

end Stacks.CharacterModule

namespace Stacks.Trace

variable {Λ : Type*} [Ring Λ] {G : Type*} [Group G] {P : Type*} [AddCommGroup P] [Module Λ P]
  {A : Type*} [AddCommGroup A]

/-- An additive map invariant under `σ` kills the differences `σ g p - p`. -/
theorem coinvariantsKer_le_ker (σ : Representation Λ G P) (b : P →+ A)
    (hb : ∀ g p, b (σ g p) = b p) : (coinvariantsKer σ).toAddSubgroup ≤ b.ker := by
  intro x hx
  have key : ∀ x ∈ coinvariantsKer σ, ∀ a : Λ, b (a • x) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨⟨g, p⟩, rfl⟩ := h
      intro a
      rw [smul_sub, ← map_smul, map_sub, hb, sub_self]
    | zero => exact fun a ↦ by rw [smul_zero, map_zero]
    | add x y _ _ hx hy => exact fun a ↦ by rw [smul_add, map_add, hx, hy, add_zero]
    | smul c x _ hx => exact fun a ↦ by simpa only [smul_smul] using hx _
  simpa using key x hx 1

/-- **An additive map invariant under `σ` factors through the coinvariants.** -/
def coinvariantsAddLift (σ : Representation Λ G P) (b : P →+ A) (hb : ∀ g p, b (σ g p) = b p) :
    coinvariants σ →+ A :=
  QuotientAddGroup.lift (coinvariantsKer σ).toAddSubgroup b (coinvariantsKer_le_ker σ b hb)

/-- `coinvariantsAddLift σ b hb` sends the class of `p` to `b p`. -/
theorem coinvariantsAddLift_mk (σ : Representation Λ G P) (b : P →+ A)
    (hb : ∀ g p, b (σ g p) = b p) (p : P) :
    coinvariantsAddLift σ b hb (coinvariantsMk σ p) = b p :=
  rfl

/-- The coinvariants map is surjective. -/
theorem coinvariantsMk_surjective (σ : Representation Λ G P) :
    Function.Surjective (coinvariantsMk σ) :=
  Submodule.mkQ_surjective _

/-- Additive maps out of the coinvariants agree if they agree on classes. -/
private theorem coinvariants_addMonoidHom_ext {σ : Representation Λ G P} {f g : coinvariants σ →+ A}
    (h : ∀ p, f (coinvariantsMk σ p) = g (coinvariantsMk σ p)) : f = g :=
  AddMonoidHom.ext fun z ↦ by
    obtain ⟨p, rfl⟩ := coinvariantsMk_surjective σ z
    exact h p

end Stacks.Trace

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.EtaleCohomology.etaleModulesEnoughInjectivesZeroTraceTwist
  Stacks.EtaleCohomology.moduleCatHasColimitsOfSizeSmallEtale
  Stacks.EtaleCohomology.hasGlobalSectionsFunctorSmallEtaleModuleCat

namespace AlgebraicGeometry

section Duality

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar]
  (Λ : Type) [Ring Λ] [Fintype Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar))

/-- **`ρ ↦ Hom_N(M, μ_n(k̄))`**, `n = #Λ`: the invariants under `π₁(X_k̄, η̄)` of the dual
`Hom(M, μ_n) = M^∨(1)` (`AlgebraicGeometry.cyclotomicDual`), a contravariant functor to
`Λᵐᵒᵖ`-modules. Since the image `N` of `π₁(X_k̄, η̄)` acts trivially on `μ_n`, these are the
`N`-equivariant additive maps `M → μ_n`. This is the shape of `H⁰(X_k̄, ℱ_{Hom(M, μ_n)})` under
`AlgebraicGeometry.geometricGlobalSectionsInvariantsEquiv`. -/
def geometricCyclotomicDualInvariants :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    (FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))ᵒᵖ ⥤ ModuleCat.{u + 1} Λᵐᵒᵖ :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  cyclotomicDual B X f kbar y (Fintype.card Λ) Λ ⋙
    finiteTypeContinuousModuleRes Λᵐᵒᵖ (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y) ⋙
    finiteTypeContinuousModuleInvariants Λᵐᵒᵖ
      (EtaleFundamentalGroup (fieldBaseChange (Over.mk f) kbar) y)

/-- The additive map `M → μ_n` underlying an element of `Hom_N(M, μ_n)`. -/
def geometricCyclotomicDualInvariantsToHom
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (b : (geometricCyclotomicDualInvariants B X f kbar Λ y).obj (Opposite.op ρ)) :
    ρ.obj.obj.obj.V →+ ULift.{u + 1} (Additive (_root_.rootsOfUnity (Fintype.card Λ) kbar)) :=
  b.1

omit [Smooth f] in
/-- An element of `Hom_N(M, μ_n)` is invariant under the image of `π₁(X_k̄)`. -/
theorem geometricCyclotomicDualInvariantsToHom_apply_eq
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (b : (geometricCyclotomicDualInvariants B X f kbar Λ y).obj (Opposite.op ρ))
    (g : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom.range)
    (m : ρ.obj.obj.obj.V) :
    letI := connectedSpace_of_isCurve B X f
    geometricCyclotomicDualInvariantsToHom B X f kbar Λ y ρ b
        ((finiteTypeContinuousModuleRepresentation Λ _ ρ) g.1 m) =
      geometricCyclotomicDualInvariantsToHom B X f kbar Λ y ρ b m := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  obtain ⟨γ, h, rfl⟩ := g
  have hb := congrArg (fun φ : ρ.obj.obj.obj.V →+
      ULift.{u + 1} (Additive (_root_.rootsOfUnity (Fintype.card Λ) kbar)) ↦ φ m) (b.2 h⁻¹)
  have htriv := cyclotomicContinuousModule_ρ_eq_one_of_mem_range B X f kbar y (Fintype.card Λ)
    ((etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y) h⁻¹) ⟨h⁻¹, rfl⟩
  change ((cyclotomicContinuousModule B X f kbar y (Fintype.card Λ)).obj.obj.obj.ρ
      ((etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y) h⁻¹)).asHom.hom
      (geometricCyclotomicDualInvariantsToHom B X f kbar Λ y ρ b
        ((ρ.obj.obj.obj.ρ (((etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y) h⁻¹)⁻¹)).asHom.hom m)) =
    geometricCyclotomicDualInvariantsToHom B X f kbar Λ y ρ b m at hb
  rwa [htriv, map_inv (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
    (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y) h, inv_inv] at hb

/-- **`b ↦ b̄`, `Hom_N(M, μ_n) → Hom(M_N, μ_n)`**: an `N`-equivariant map to `μ_n`, on which `N`
acts trivially, factors through the coinvariants `M_N` (the module of `ρ_N`,
`AlgebraicGeometry.geometricNormalCoinvariants`). It is `Λᵐᵒᵖ`-linear for the actions through `M`
and `M_N`. -/
def geometricCyclotomicDualInvariantsLift
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    (geometricCyclotomicDualInvariants B X f kbar Λ y).obj (Opposite.op ρ) →ₗ[Λᵐᵒᵖ]
      ((geometricNormalCoinvariants B X f kbar Λ y ρ).obj.obj.obj.V →+
        Additive (_root_.rootsOfUnity (Fintype.card Λ) kbar)) where
  toFun b :=
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    Stacks.Trace.coinvariantsAddLift _
      ((AddEquiv.ulift : ULift.{u + 1} (Additive (_root_.rootsOfUnity (Fintype.card Λ) kbar)) ≃+
          Additive (_root_.rootsOfUnity (Fintype.card Λ) kbar)).toAddMonoidHom.comp
        (geometricCyclotomicDualInvariantsToHom B X f kbar Λ y ρ b))
      fun g m ↦ congrArg ULift.down
        (geometricCyclotomicDualInvariantsToHom_apply_eq B X f kbar Λ y ρ b g m)
  map_add' b b' := by
    let := connectedSpace_of_isCurve B X f
    let := connectedSpace_fieldBaseChange f kbar
    refine AddMonoidHom.ext fun z ↦ ?_
    obtain ⟨m, rfl⟩ := Stacks.Trace.coinvariantsMk_surjective _ z
    rfl
  map_smul' r b := by
    let := connectedSpace_of_isCurve B X f
    let := connectedSpace_fieldBaseChange f kbar
    refine AddMonoidHom.ext fun z ↦ ?_
    obtain ⟨m, rfl⟩ := Stacks.Trace.coinvariantsMk_surjective _ z
    rfl

omit [Smooth f] in
/-- The map `M_N → μ_n` induced by `b` sends the class of `m` to `b m`. -/
theorem geometricCyclotomicDualInvariantsLift_mk
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (b : (geometricCyclotomicDualInvariants B X f kbar Λ y).obj (Opposite.op ρ))
    (m : ρ.obj.obj.obj.V) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    geometricCyclotomicDualInvariantsLift B X f kbar Λ y ρ b
        (Stacks.Trace.coinvariantsMk _ m) =
      (geometricCyclotomicDualInvariantsToHom B X f kbar Λ y ρ b m).down :=
  rfl

omit [Smooth f] in
/-- `b ↦ b̄` is injective: the coinvariants map is surjective. -/
theorem injective_geometricCyclotomicDualInvariantsLift
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    Function.Injective (geometricCyclotomicDualInvariantsLift B X f kbar Λ y ρ) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  intro b b' h
  apply Subtype.ext
  have e : geometricCyclotomicDualInvariantsToHom B X f kbar Λ y ρ b =
      geometricCyclotomicDualInvariantsToHom B X f kbar Λ y ρ b' :=
    AddMonoidHom.ext fun m ↦ ULift.ext (DFunLike.congr_fun h (Stacks.Trace.coinvariantsMk _ m))
  exact e

omit [Smooth f] in
/-- `b ↦ b̄` is surjective: `m ↦ c(m̄)` is `N`-equivariant for every `c : M_N → μ_n`, since `N`
acts trivially on `μ_n`. -/
theorem surjective_geometricCyclotomicDualInvariantsLift
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    Function.Surjective (geometricCyclotomicDualInvariantsLift B X f kbar Λ y ρ) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  intro c
  let φ : ρ.obj.obj.obj.V →+ ULift.{u + 1} (Additive (_root_.rootsOfUnity (Fintype.card Λ) kbar)) :=
    ((AddEquiv.ulift : ULift.{u + 1} (Additive (_root_.rootsOfUnity (Fintype.card Λ) kbar)) ≃+
        Additive (_root_.rootsOfUnity (Fintype.card Λ) kbar)).symm.toAddMonoidHom.comp c).comp
      (Stacks.Trace.coinvariantsMk ((finiteTypeContinuousModuleRepresentation Λ _ ρ).comp
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom
        y).toMonoidHom.range.subtype)).toAddMonoidHom
  refine ⟨⟨φ, fun g ↦ ?_⟩, ?_⟩
  · have htriv := cyclotomicContinuousModule_ρ_eq_one_of_mem_range B X f kbar y (Fintype.card Λ)
      ((etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y) g) ⟨g, rfl⟩
    refine AddMonoidHom.ext fun m ↦ ?_
    change ((cyclotomicContinuousModule B X f kbar y (Fintype.card Λ)).obj.obj.obj.ρ
        ((etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y) g)).asHom.hom (φ ((ρ.obj.obj.obj.ρ
        ((etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y) g)⁻¹).asHom.hom m)) = φ m
    rw [htriv]
    exact congrArg (fun z ↦ ULift.up (c z)) (Stacks.Trace.coinvariantsMk_group_action
      ((finiteTypeContinuousModuleRepresentation Λ _ ρ).comp
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom.range.subtype)
      ⟨((etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y) g)⁻¹, g⁻¹,
        map_inv (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y) g⟩ m)
  · exact Stacks.Trace.coinvariants_addMonoidHom_ext fun m ↦ rfl

omit [Smooth f] in
/-- `b ↦ b̄` is natural: `b̄' ∘ v_N` is the lift of `b' ∘ v`. -/
theorem geometricCyclotomicDualInvariantsLift_naturality
    {ρ ρ' : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))} (v : ρ ⟶ ρ')
    (b' : (geometricCyclotomicDualInvariants B X f kbar Λ y).obj (Opposite.op ρ')) :
    (geometricCyclotomicDualInvariantsLift B X f kbar Λ y ρ' b').comp
        (geometricNormalCoinvariantsMap B X f kbar Λ y v).hom.hom.hom.hom.hom.toAddMonoidHom =
      geometricCyclotomicDualInvariantsLift B X f kbar Λ y ρ
        (((geometricCyclotomicDualInvariants B X f kbar Λ y).map v.op).hom b') := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  exact Stacks.Trace.coinvariants_addMonoidHom_ext fun m ↦ rfl

variable (j : CompactificationOf (Over.mk f)) (hn : IsUnit ((Fintype.card Λ : ℕ) : kbar))

omit [Algebra.IsSeparable k kbar] in
include hn in
/-- `μ_n(k̄)` has `n = #Λ` elements. -/
theorem natCard_additive_rootsOfUnity_card :
    Nat.card (Additive (_root_.rootsOfUnity (Fintype.card Λ) kbar)) = Fintype.card Λ := by
  have : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  exact (exists_isPrimitiveRoot_of_isUnit hn).choose_spec.card_rootsOfUnity

/-- **The degree-zero pairing `α ↦ (b ↦ tr(b_* α))`**, from `T₀(ρ) = H²_c(X_k̄, ℱ_ρ)` to the
character module of `Hom_N(M, μ_n)`. For `b : M → μ_n` `N`-equivariant, `b_* α` is `b̄ ∘ Ψ(α)`,
where `Ψ(α) : μ_n → M_N` is Tag 03VK (`AlgebraicGeometry.compactSupportCanonicalTwistEquiv`) and
`b̄ : M_N → μ_n` is induced by `b`. Then `tr : Hom(μ_n, μ_n) = ℤ/n ⊂ ℚ/ℤ` is the scalar of the
endomorphism (`Stacks.CharacterModule.cyclicEndScalar`) divided by `n`. No root of unity is
chosen. The formula is `AlgebraicGeometry.compactSupportDegreeZeroPairing_apply`. -/
def compactSupportDegreeZeroPairing
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    ((compactSupportRepresentationHomology B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j kbar).functor 0).obj ρ →ₗ[Λ]
      CharacterModule ((geometricCyclotomicDualInvariants B X f kbar Λ y).obj (Opposite.op ρ)) :=
  letI := connectedSpace_of_isCurve B X f
  haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  (CharacterModule.dualOfMulOpposite (geometricCyclotomicDualInvariantsLift B X f kbar Λ y ρ)).comp
    ((Stacks.CharacterModule.cyclicTwistPairingLinear (natCard_additive_rootsOfUnity_card kbar Λ hn)
      Λ).comp ((compactSupportCanonicalTwistEquiv B X f kbar Λ y j hn ρ).toLinearMap.comp
        (compactSupportRepresentationHomologyZeroIso B X _ Λ f j kbar ρ).hom.hom))

/-- **The formula**: the pairing of `α` with `b` is `tr(b̄ ∘ Ψ(α))`. -/
theorem compactSupportDegreeZeroPairing_apply
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (α : letI := connectedSpace_of_isCurve B X f
      ((compactSupportRepresentationHomology B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j kbar).functor 0).obj ρ)
    (b : (geometricCyclotomicDualInvariants B X f kbar Λ y).obj (Opposite.op ρ)) :
    letI := connectedSpace_of_isCurve B X f
    haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
    compactSupportDegreeZeroPairing B X f kbar Λ y j hn ρ α b =
      Stacks.CharacterModule.zmodToRatCircle (Fintype.card Λ)
        (Stacks.CharacterModule.cyclicEndScalar (natCard_additive_rootsOfUnity_card kbar Λ hn)
          ((geometricCyclotomicDualInvariantsLift B X f kbar Λ y ρ b).comp
            (compactSupportCanonicalTwistEquiv B X f kbar Λ y j hn ρ
              ((compactSupportRepresentationHomologyZeroIso B X _ Λ f j kbar ρ).hom.hom α)))) :=
  rfl

/-- **Degree-zero duality**: `H²_c(X_k̄, ℱ_ρ) ≅ Hom_N(M, μ_n)^∨` through the pairing
`α ↦ (b ↦ tr(b_* α))`. -/
theorem bijective_compactSupportDegreeZeroPairing
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    Function.Bijective (compactSupportDegreeZeroPairing B X f kbar Λ y j hn ρ) := by
  let := connectedSpace_of_isCurve B X f
  have : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  have : Module.Finite Λ (geometricNormalCoinvariants B X f kbar Λ y ρ).obj.obj.obj.V :=
    (geometricNormalCoinvariants B X f kbar Λ y ρ).property
  have : Finite (geometricNormalCoinvariants B X f kbar Λ y ρ).obj.obj.obj.V :=
    Module.finite_of_finite Λ
  have hdual : Function.Bijective (CharacterModule.dualOfMulOpposite
      (geometricCyclotomicDualInvariantsLift B X f kbar Λ y ρ)) :=
    ⟨CharacterModule.comp_injective_of_surjective _
        (surjective_geometricCyclotomicDualInvariantsLift B X f kbar Λ y ρ),
      CharacterModule.comp_surjective_of_injective _
        (injective_geometricCyclotomicDualInvariantsLift B X f kbar Λ y ρ)⟩
  exact hdual.comp ((Stacks.CharacterModule.cyclicTwistPairing_bijective
    (natCard_additive_rootsOfUnity_card kbar Λ hn) (card_nsmul_eq_zero_of_module Λ)).comp
      ((compactSupportCanonicalTwistEquiv B X f kbar Λ y j hn ρ).bijective.comp
        (compactSupportRepresentationHomologyZeroIso B X _ Λ f j kbar ρ).toLinearEquiv.bijective))

/-- **The pairing is natural in `ρ`**: for `v : ρ ⟶ ρ'`, the pairing of `T₀(v) α` with `b'` is
the pairing of `α` with `b' ∘ v`. -/
theorem compactSupportDegreeZeroPairing_naturality {ρ ρ' : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))} (v : ρ ⟶ ρ')
    (α : letI := connectedSpace_of_isCurve B X f
      ((compactSupportRepresentationHomology B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j kbar).functor 0).obj ρ) :
    letI := connectedSpace_of_isCurve B X f
    compactSupportDegreeZeroPairing B X f kbar Λ y j hn ρ'
        ((((compactSupportRepresentationHomology B X (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j kbar).functor 0).map v).hom
            α) =
      CharacterModule.dualOfMulOpposite
        ((geometricCyclotomicDualInvariants B X f kbar Λ y).map v.op).hom
        (compactSupportDegreeZeroPairing B X f kbar Λ y j hn ρ α) := by
  let := connectedSpace_of_isCurve B X f
  have : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  refine CharacterModule.ext _ fun b' ↦ ?_
  have h1 := congrArg (fun φ ↦ ModuleCat.Hom.hom φ α)
    (compactSupportRepresentationHomologyZeroIso_hom_naturality B X _ Λ f j kbar v)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h1
  rw [CharacterModule.dualOfMulOpposite_apply, compactSupportDegreeZeroPairing_apply,
    compactSupportDegreeZeroPairing_apply, h1, compactSupportCanonicalTwistEquiv_naturality,
    ← AddMonoidHom.comp_assoc, geometricCyclotomicDualInvariantsLift_naturality]

/-- The component at `ρ` of degree-zero duality: the pairing, an isomorphism of `Λ`-modules. -/
def compactSupportDegreeZeroDualityIsoApp (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    ((compactSupportRepresentationHomology B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j kbar).functor 0).obj ρ ≅
      ((geometricCyclotomicDualInvariants B X f kbar Λ y).rightOp ⋙
        CharacterModule.moduleCatDualOfMulOppositeFunctor Λ).obj ρ :=
  (LinearEquiv.ofBijective (compactSupportDegreeZeroPairing B X f kbar Λ y j hn ρ)
    (bijective_compactSupportDegreeZeroPairing B X f kbar Λ y j hn ρ)).toModuleIso

/-- The forward map of `compactSupportDegreeZeroDualityIsoApp` is
`compactSupportDegreeZeroPairing`. -/
theorem compactSupportDegreeZeroDualityIsoApp_hom_apply (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (α : letI := connectedSpace_of_isCurve B X f
      ((compactSupportRepresentationHomology B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j kbar).functor 0).obj ρ) :
    (compactSupportDegreeZeroDualityIsoApp B X f kbar Λ y j hn ρ).hom.hom α =
      compactSupportDegreeZeroPairing B X f kbar Λ y j hn ρ α :=
  rfl

/-- **Degree-zero duality, naturally in `ρ`**: `T₀ = H²_c(X_k̄, ℱ_-) ≅ Hom_N(-, μ_n)^∨` as functors
to `Λ`-modules, through the pairing `α ↦ (b ↦ tr(b_* α))`
(`AlgebraicGeometry.compactSupportDegreeZeroPairing_apply`). -/
def compactSupportDegreeZeroDualityIso :
    letI := connectedSpace_of_isCurve B X f
    (compactSupportRepresentationHomology B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j kbar).functor 0 ≅
      (geometricCyclotomicDualInvariants B X f kbar Λ y).rightOp ⋙
        CharacterModule.moduleCatDualOfMulOppositeFunctor Λ :=
  letI := connectedSpace_of_isCurve B X f
  NatIso.ofComponents (compactSupportDegreeZeroDualityIsoApp B X f kbar Λ y j hn)
    (fun {ρ ρ'} v ↦ by
      refine ModuleCat.hom_ext (LinearMap.ext fun α ↦ ?_)
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
        compactSupportDegreeZeroDualityIsoApp_hom_apply,
        compactSupportDegreeZeroDualityIsoApp_hom_apply]
      exact compactSupportDegreeZeroPairing_naturality B X f kbar Λ y j hn v α)

/-- The component of `AlgebraicGeometry.compactSupportDegreeZeroDualityIso` at `ρ` is the
pairing `AlgebraicGeometry.compactSupportDegreeZeroPairing`. -/
theorem compactSupportDegreeZeroDualityIso_hom_app_apply
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (α : letI := connectedSpace_of_isCurve B X f
      ((compactSupportRepresentationHomology B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f j kbar).functor 0).obj ρ) :
    ((compactSupportDegreeZeroDualityIso B X f kbar Λ y j hn).hom.app ρ).hom α =
      compactSupportDegreeZeroPairing B X f kbar Λ y j hn ρ α :=
  rfl

end Duality

end AlgebraicGeometry

end
