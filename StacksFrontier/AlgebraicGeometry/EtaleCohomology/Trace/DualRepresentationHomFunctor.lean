module

public import StacksFrontier.Algebra.Module.GroupAlgebra.DualRepresentationHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.EtaleModuleHomExact
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.FunctorTrace
public import StacksFrontier.NumberTheory.Padics.ZModDualReflexive

/-!
# The functor `Hom_{A[H]}(N^∨, -)` of a representation

Let `A` be a commutative ring, `H` a finite group, `Λ` an `A`-algebra and `N` a `Λ`-module with an
action `ρ` of `H` by `Λ`-linear maps. The dual `N^∨ = Hom_A(N, A)` is an `(A[H], Λ)`-bimodule:
`A[H]` acts through the contragredient action and `Λ` on the right by `φ · λ = φ ∘ (λ •)`.
So `Hom_{A[H]}(N^∨, -)` is a functor from `A[H]`-modules to `Λ`-modules
(`Stacks.EtaleCohomology.homFunctor`), and it carries `A[H]` to `N`:
`y ↦ (φ ↦ ∑_g φ(g y) g)` is `Λ`-linear and bijective when `N` is reflexive over `A`
(`MonoidAlgebra.bijective_dualRepHom`). Consequently, for `N` finitely generated projective over
`Λ` and finite, it carries finitely generated projective `A[H]`-modules to finitely generated
projective `Λ`-modules. This is the functor `Φ'` of Step 7 of the proof of
[Stacks, Tag 03UG].

## Main definitions

* `MonoidAlgebra.restrictRep`, `MonoidAlgebra.dualRepModule`, `MonoidAlgebra.dualRepRightAction`.

## Main results

* `MonoidAlgebra.homFunctorRegularEquiv`: `Hom_{A[H]}(N^∨, A[H]) ≅ N` as `Λ`-modules.
-/

@[expose] public noncomputable section

open CategoryTheory Finset

universe w

namespace MonoidAlgebra

variable {A : Type} [CommRing A] {H : Type} [Group H] [Fintype H] {Λ : Type} [Ring Λ]
  [Algebra A Λ] {N : Type w} [AddCommGroup N] [Module Λ N] [Module A N] [IsScalarTower A Λ N]
  (ρ : H →* Module.End Λ N)

/-- The action `ρ`, by `A`-linear maps. -/
def restrictRep : H →* Module.End A N where
  toFun h := (ρ h).restrictScalars A
  map_one' := by
    ext y
    simp
  map_mul' g h := by
    ext y
    simp

/-- Multiplication by `λ ∈ Λ`, as an `A`-linear endomorphism of `N`. -/
def lsmulA (l : Λ) : N →ₗ[A] N where
  toFun y := l • y
  map_add' := smul_add l
  map_smul' a y := smul_comm l a y

/-- The right action `φ ↦ φ ∘ (λ •)` of `λ ∈ Λ` on `N^∨`, by `A[H]`-linear maps. -/
def dualRepRightMul (l : Λ) :
    DualRep (restrictRep (A := A) ρ) →ₗ[MonoidAlgebra A H] DualRep (restrictRep (A := A) ρ) where
  toFun φ := (DualRep.equiv _).symm ((DualRep.equiv _ φ).comp (lsmulA (A := A) (N := N) l))
  map_add' φ φ' := by
    apply (DualRep.equiv (restrictRep (A := A) ρ)).injective
    ext y
    simp
  map_smul' r φ := by
    induction r using MonoidAlgebra.induction_linear with
    | zero =>
      apply (DualRep.equiv (restrictRep (A := A) ρ)).injective
      ext y
      change DualRep.equiv _ ((0 : MonoidAlgebra A H) • φ) (l • y) =
        DualRep.equiv _ ((0 : MonoidAlgebra A H) • _) y
      simp
    | add s t hs ht =>
      simp only [RingHom.id_apply] at hs ht ⊢
      rw [add_smul, map_add, LinearMap.add_comp, map_add, hs, ht, add_smul]
    | single h a =>
      apply (DualRep.equiv (restrictRep (A := A) ρ)).injective
      ext y
      change DualRep.equiv _ (single h a • φ) (l • y) =
        DualRep.equiv _ (single h a •
          (DualRep.equiv _).symm ((DualRep.equiv _ φ).comp (lsmulA (A := A) (N := N) l))) y
      rw [single_smul_dualRep, single_smul_dualRep]
      change a * DualRep.equiv _ φ ((ρ h⁻¹) (l • y)) = a * DualRep.equiv _ φ (l • (ρ h⁻¹) y)
      rw [map_smul]

omit [Fintype H] in
/-- The right action of `l : Λ` on `N^∨` sends a functional `φ` to `y ↦ φ (l • y)`. -/
lemma dualRepRightMul_apply (l : Λ) (φ : DualRep (restrictRep (A := A) ρ)) (y : N) :
    DualRep.equiv _ (dualRepRightMul (A := A) ρ l φ) y = DualRep.equiv _ φ (l • y) :=
  rfl

/-- **The `(A[H], Λ)`-bimodule `N^∨`**, as an `A[H]`-module. -/
def dualRepModule : ModuleCat.{w} (MonoidAlgebra A H) :=
  ModuleCat.of _ (DualRep (restrictRep (A := A) ρ))

/-- The right action of `Λ` on `N^∨`, as a ring morphism `Λ →+* (End_{A[H]} N^∨)ᵐᵒᵖ`. -/
def dualRepRightAction : Λ →+* (End (dualRepModule (A := A) ρ))ᵐᵒᵖ where
  toFun l := MulOpposite.op (ModuleCat.ofHom (dualRepRightMul (A := A) ρ l))
  map_one' := by
    apply MulOpposite.unop_injective
    refine ModuleCat.hom_ext (LinearMap.ext fun φ => ?_)
    apply (DualRep.equiv (restrictRep (A := A) ρ)).injective
    ext y
    exact congrArg (DualRep.equiv _ φ) (one_smul Λ y)
  map_mul' l l' := by
    apply MulOpposite.unop_injective
    refine ModuleCat.hom_ext (LinearMap.ext fun φ => ?_)
    apply (DualRep.equiv (restrictRep (A := A) ρ)).injective
    ext y
    exact congrArg (DualRep.equiv _ φ) (mul_smul l l' y)
  map_zero' := by
    apply MulOpposite.unop_injective
    refine ModuleCat.hom_ext (LinearMap.ext fun φ => ?_)
    apply (DualRep.equiv (restrictRep (A := A) ρ)).injective
    ext y
    change DualRep.equiv _ φ ((0 : Λ) • y) = 0
    rw [zero_smul, map_zero]
  map_add' l l' := by
    apply MulOpposite.unop_injective
    refine ModuleCat.hom_ext (LinearMap.ext fun φ => ?_)
    apply (DualRep.equiv (restrictRep (A := A) ρ)).injective
    ext y
    change DualRep.equiv _ φ ((l + l') • y) = DualRep.equiv _ φ (l • y) + DualRep.equiv _ φ (l' • y)
    rw [add_smul, map_add]

/-- `ψ_y`, as an element of `Hom_{A[H]}(N^∨, A[H])`, with `A[H]` lifted to the universe of `N`. -/
def homFunctorRegularMap :
    N →ₗ[Λ] (Stacks.EtaleCohomology.homFunctor (dualRepModule (A := A) ρ)
      (dualRepRightAction (A := A) ρ)).obj
        (ModuleCat.of (MonoidAlgebra A H) (ULift.{w} (MonoidAlgebra A H))) where
  toFun y := ModuleCat.ofHom
    ((ULift.moduleEquiv (R := MonoidAlgebra A H)).symm.toLinearMap.comp
      (dualRepHom (restrictRep (A := A) ρ) y))
  map_add' y y' := by
    refine ModuleCat.hom_ext (LinearMap.ext fun φ => ULift.ext _ _ ?_)
    change ∑ g : H, single g (DualRep.equiv _ φ ((ρ g) (y + y'))) =
      ∑ g : H, single g (DualRep.equiv _ φ ((ρ g) y)) +
        ∑ g : H, single g (DualRep.equiv _ φ ((ρ g) y'))
    simp only [map_add, single_add, sum_add_distrib]
  map_smul' l y := by
    refine ModuleCat.hom_ext (LinearMap.ext fun φ => ULift.ext _ _ ?_)
    change ∑ g : H, single g (DualRep.equiv _ φ ((ρ g) (l • y))) =
      ∑ g : H, single g (DualRep.equiv _ (dualRepRightMul (A := A) ρ l φ) ((ρ g) y))
    simp only [dualRepRightMul_apply, map_smul]

/-- **`Hom_{A[H]}(N^∨, A[H]) ≅ N` as `Λ`-modules**, for `A = ℤ/n` and `N` finite. -/
theorem bijective_homFunctorRegularMap {n : ℕ} [NeZero n] {Λ : Type} [Ring Λ]
    [Algebra (ZMod n) Λ] [Module Λ N] [Module (ZMod n) N] [IsScalarTower (ZMod n) Λ N]
    [Finite N] (ρ : H →* Module.End Λ N) :
    Function.Bijective (homFunctorRegularMap (A := ZMod n) ρ) := by
  have hb := bijective_dualRepHom (restrictRep (A := ZMod n) ρ)
    (Stacks.LAdic.bijective_dual_eval_zmod N)
  refine ⟨fun y y' h => hb.1 (LinearMap.ext fun φ => ?_), fun f => ?_⟩
  · exact congrArg (fun F : dualRepModule (A := ZMod n) ρ ⟶
      ModuleCat.of (MonoidAlgebra (ZMod n) H) (ULift.{w} (MonoidAlgebra (ZMod n) H)) =>
        (ModuleCat.Hom.hom F φ).down) h
  · obtain ⟨y, hy⟩ := hb.2 ((ULift.moduleEquiv (R := MonoidAlgebra (ZMod n) H)).toLinearMap.comp
      f.hom)
    exact ⟨y, ModuleCat.hom_ext (LinearMap.ext fun φ => ULift.ext _ _ (congrArg (fun F => F φ) hy))⟩

/-- A finite projective module `P` is a retract of a finite free module: there are maps
`σ j : P ⟶ R` and `π j : R ⟶ P` with `∑ j, σ j ≫ π j = 𝟙 P`. -/
theorem exists_sum_comp_eq_id_of_projective {R : Type} [Ring R] (P : ModuleCat.{w} R)
    [Module.Finite R P] [Module.Projective R P] :
    ∃ (k : ℕ) (σ : Fin k → (P ⟶ ModuleCat.of R (ULift.{w} R)))
      (π : Fin k → (ModuleCat.of R (ULift.{w} R) ⟶ P)), ∑ j, σ j ≫ π j = 𝟙 P := by
  obtain ⟨k, π, hπ⟩ := Module.Finite.exists_fin' R P
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let up := (ULift.moduleEquiv (R := R) (M := R)).symm
  refine ⟨k, fun j => ModuleCat.ofHom (up.toLinearMap.comp ((LinearMap.proj j).comp σ)),
    fun j => ModuleCat.ofHom (π.comp ((LinearMap.single R (fun _ : Fin k => R) j).comp
      up.symm.toLinearMap)), ModuleCat.hom_ext (LinearMap.ext fun x => ?_)⟩
  have hx : ∑ j, LinearMap.single R (fun _ : Fin k => R) j (σ x j) = σ x := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have := congrArg π hx
  rw [map_sum] at this
  simp only [up, ModuleCat.hom_sum, ModuleCat.hom_comp, ModuleCat.hom_id,
    ModuleCat.hom_ofHom, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply]
  exact this.trans (LinearMap.congr_fun hσ x)

omit [Fintype H] in
open Stacks.EtaleCohomology in
/-- **`Hom_{A[H]}(N^∨, -)` carries finite projective modules to finite projective modules**, for
`A = ℤ/n` and `N` finite and finite projective over `Λ`: a finite projective `A[H]`-module `P` is
a retract of `A[H]^k`, so `Hom(N^∨, P)` is a retract of `Hom(N^∨, A[H])^k ≅ N^k`. -/
theorem preservesFiniteProjective_homFunctor {n : ℕ} [NeZero n] {Λ : Type} [Ring Λ] [Finite H]
    [Algebra (ZMod n) Λ] [Module Λ N] [Module (ZMod n) N] [IsScalarTower (ZMod n) Λ N]
    [Finite N] [Module.Finite Λ N] [Module.Projective Λ N] (ρ : H →* Module.End Λ N) :
    CategoryTheory.FilteredDerived.PreservesFiniteProjective.{0, w}
      (homFunctor (dualRepModule (A := ZMod n) ρ) (dualRepRightAction (A := ZMod n) ρ)) := by
  have := Fintype.ofFinite H
  intro P hPf hPp
  let R := MonoidAlgebra (ZMod n) H
  let X := dualRepModule (A := ZMod n) ρ
  let Φ := homFunctor X (dualRepRightAction (A := ZMod n) ρ)
  let Rw := ModuleCat.of R (ULift.{w} R)
  obtain ⟨k, σj, πj, hsum⟩ := exists_sum_comp_eq_id_of_projective P
  have sum_comp_comp {Y Z W : ModuleCat.{w} R} (f : X ⟶ Y) (a : Fin k → (Y ⟶ Z))
      (b : Fin k → (Z ⟶ W)) : ∑ j, (f ≫ a j) ≫ b j = f ≫ ∑ j, a j ≫ b j := by
    rw [Preadditive.comp_sum]
    exact Finset.sum_congr rfl fun j _ => Category.assoc _ _ _
  let i : Φ.obj P →ₗ[Λ] (Fin k → Φ.obj Rw) :=
    { toFun := fun f j => (show X ⟶ P from f) ≫ σj j
      map_add' := fun f g => funext fun j => Preadditive.add_comp _ _ _ _ _ _
      map_smul' := fun l f => funext fun j => Category.assoc _ _ _ }
  let r : (Fin k → Φ.obj Rw) →ₗ[Λ] Φ.obj P :=
    { toFun := fun g => ∑ j, (show X ⟶ Rw from g j) ≫ πj j
      map_add' := fun g g' => by
        show ∑ j, ((g j : X ⟶ Rw) + g' j) ≫ πj j = ∑ j, _ + ∑ j, _
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => Preadditive.add_comp _ _ _ _ _ _
      map_smul' := fun l g => sum_comp_comp (dualRepRightAction (A := ZMod n) ρ l).unop _ _ }
  have hri : r.comp i = LinearMap.id := LinearMap.ext fun f => by
    show ∑ j, ((show X ⟶ P from f) ≫ σj j) ≫ πj j = f
    rw [sum_comp_comp, hsum, Category.comp_id]
  let e : (Fin k → Φ.obj Rw) ≃ₗ[Λ] (Fin k → N) := LinearEquiv.piCongrRight fun _ =>
    (LinearEquiv.ofBijective _ (bijective_homFunctorRegularMap (n := n) ρ)).symm
  have : Module.Projective Λ (Fin k → N) :=
    Module.Projective.of_equiv' (DirectSum.linearEquivFunOnFintype Λ (Fin k) (fun _ => N))
  have : Module.Projective Λ (Fin k → Φ.obj Rw) := Module.Projective.of_equiv e.symm
  have : Module.Finite Λ (Fin k → Φ.obj Rw) := Module.Finite.equiv e.symm
  exact ⟨Module.Finite.of_surjective r (fun f => ⟨i f, LinearMap.congr_fun hri f⟩),
    Module.Projective.of_split i r hri⟩

omit [Fintype H] in
/-- **`A` acts on `N^∨` through `Λ`**: the right action of `algebraMap A Λ a` is multiplication by
the central scalar `a`. -/
theorem dualRepRightAction_algebraMap (a : A) :
    dualRepRightAction (A := A) ρ (algebraMap A Λ a) =
      Stacks.EtaleCohomology.centralScalars (A := A) (dualRepModule (A := A) ρ) a := by
  apply MulOpposite.unop_injective
  refine ModuleCat.hom_ext (LinearMap.ext fun φ => ?_)
  apply (DualRep.equiv (restrictRep (A := A) ρ)).injective
  ext y
  show DualRep.equiv _ φ (algebraMap A Λ a • y) =
    DualRep.equiv (restrictRep (A := A) ρ)
      (single (1 : H) a • (φ : DualRep (restrictRep (A := A) ρ))) y
  refine Eq.trans ?_ (single_smul_dualRep (restrictRep (A := A) ρ) (1 : H) a
    (show DualRep (restrictRep (A := A) ρ) from φ) y).symm
  rw [inv_one, map_one, Module.End.one_apply, algebraMap_smul, map_smul, smul_eq_mul]

omit [Fintype H] in
/-- `N^∨` is finite when `N` is, for `A = ℤ/n`. -/
theorem finite_dualRepModule {n : ℕ} [NeZero n] {Λ : Type} [Ring Λ] [Algebra (ZMod n) Λ]
    [Module Λ N] [Module (ZMod n) N] [IsScalarTower (ZMod n) Λ N] [Finite N]
    (ρ : H →* Module.End Λ N) :
    Finite (dualRepModule (A := ZMod n) ρ) :=
  Finite.of_injective
    (fun φ : DualRep (restrictRep (A := ZMod n) ρ) =>
      ((DualRep.equiv _ φ : Module.Dual (ZMod n) N) : N → ZMod n))
    (fun _ _ h => (DualRep.equiv _).injective (DFunLike.coe_injective h))

omit [Fintype H] in
/-- **`N^∨` is a finite `A[H]`-module** (the hypothesis `hX` of Step 7), for `N` finite. -/
theorem moduleFinite_dualRepModule {n : ℕ} [NeZero n] {Λ : Type} [Ring Λ] [Algebra (ZMod n) Λ]
    [Module Λ N] [Module (ZMod n) N] [IsScalarTower (ZMod n) Λ N] [Finite N]
    (ρ : H →* Module.End Λ N) :
    Module.Finite (MonoidAlgebra (ZMod n) H) (dualRepModule (A := ZMod n) ρ) :=
  have := finite_dualRepModule (n := n) ρ
  Module.Finite.of_finite

end MonoidAlgebra

end
