module

public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer
public import Mathlib.CategoryTheory.Limits.Shapes.SplitEqualizer
public import StacksFrontier.AlgebraicGeometry.Descent.Module.DescentData
public import StacksCore.Tactic.StacksAttribute

/-!
# The split equalizer attached to a module descent datum

A descent datum on a module determines a canonical map from the module to one of its two
pullbacks. This map and the two further pullbacks form a split equalizer of `A`-modules.
Applying character duality to that diagram, which reverses every arrow, produces a split
coequalizer.

## Main definitions

* `ModuleCat.DescentData.descentComparisonHom` is the first arrow associated to a module
  descent datum.
* `ModuleCat.DescentData.transition12AfterUnitHom` and
  `ModuleCat.DescentData.rightUnitBaseChangeHom` are the parallel arrows.

## Main results

* `ModuleCat.DescentData.isSplitEqualizer_descentComparison` says that the resulting diagram
  is a split equalizer.
* `ModuleCat.DescentData.isSplitCoequalizer_characterModule_descentComparison` is the split
  coequalizer of character modules associated to a descent datum.

## Implementation notes

We use the standard identifications of the three modules in the source with `N`,
`A ⊗[R] N`, and `(A ⊗[R] A) ⊗[R] N`. Thus the first map sends `n` to the transition
applied to `n ⊗ 1`; the parallel arrows are the pullback of the transition in positions
`1, 2` after adjoining a unit, and the map `a ⊗ n ↦ (a ⊗ 1) ⊗ n`. Their displayed
formulas are initially `R`-linear and uniquely determine the displayed `A`-linear arrows.
The first formula is `ModuleCat.DescentData.descentComparisonLeft`.
The split equalizer is in `A`-modules. The first module is universe-lifted to accommodate
tensor products without restricting the universe of the descent datum. The action on
the second and third terms is through the first tensor factor; this is the action
transported by the displayed canonical identifications.
Indeed, the transition's linearity for the left copy of `A` gives
`θ((a • n) ⊗ 1) = a • θ(n ⊗ 1)` for precisely this action. The parallel arrows
preserve the same first tensor factor.

The three objects and arrows of the split coequalizer are the character duals of the
canonical descent equalizer, in reverse order. The universe lift in the final term is
the one used by that equalizer.

## References

* [Stacks Project, Tag 08WZ](https://stacks.math.columbia.edu/tag/08WZ)
* [Stacks Project, Tag 08X1](https://stacks.math.columbia.edu/tag/08X1)
-/

@[expose] public section

universe u v w

noncomputable section

namespace ModuleCat.DescentData

open CategoryTheory TensorProduct

section CharacterDuality

/-- Character duality fixes the identity map. -/
private theorem characterDual_id {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M]
    [Module R M] : CharacterModule.dual (LinearMap.id : M →ₗ[R] M) = LinearMap.id :=
  rfl

/-- Character duality carries a split equalizer to a split coequalizer: it reverses every
arrow, so the two retractions become the two sections. -/
private theorem characterDual_isSplitCoequalizer
    {R : Type u} [CommRing R] {X Y W : ModuleCat.{v} R}
    {f g : X ⟶ Y} {ι : W ⟶ X} (q : IsSplitEqualizer f g ι) :
    Nonempty (IsSplitCoequalizer
      (ModuleCat.ofHom (CharacterModule.dual f.hom))
      (ModuleCat.ofHom (CharacterModule.dual g.hom))
      (ModuleCat.ofHom (CharacterModule.dual ι.hom))) := by
  refine ⟨⟨ModuleCat.ofHom (CharacterModule.dual q.leftRetraction.hom),
    ModuleCat.ofHom (CharacterModule.dual q.rightRetraction.hom), ?_, ?_, ?_, ?_⟩⟩
  all_goals apply ModuleCat.hom_ext
  · simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, CharacterModule.dual_comp] using
      congrArg (fun h : W ⟶ Y => CharacterModule.dual h.hom) q.condition
  · simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_id,
      CharacterModule.dual_comp, characterDual_id] using
      congrArg (fun h : W ⟶ W => CharacterModule.dual h.hom) q.ι_leftRetraction
  · simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_id,
      CharacterModule.dual_comp, characterDual_id] using
      congrArg (fun h : X ⟶ X => CharacterModule.dual h.hom) q.bottom_rightRetraction
  · simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, CharacterModule.dual_comp] using
      congrArg (fun h : X ⟶ X => CharacterModule.dual h.hom) q.top_rightRetraction

end CharacterDuality

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]

/-- Apply the descent transition to `n ⊗ 1`. -/
def descentComparisonLeft (D : DescentData.{u, v, w} R A) (n : D.module) :
    A ⊗[R] restrictModule R A D.module :=
  D.transitionRestrictScalars R A (n ⊗ₜ[R] (1 : A))

/-- Pull back the transition in tensor positions `1, 2`, after adjoining a unit. -/
def transition12AfterUnit (D : DescentData.{u, v, w} R A) :
    (A ⊗[R] restrictModule R A D.module) →ₗ[R]
      ((A ⊗[R] A) ⊗[R] restrictModule R A D.module) :=
  (transition12 R A D.module D.transition).comp
    ((TensorProduct.mk R (A ⊗[R] restrictModule R A D.module) A).flip 1)

/-- The second parallel arrow, inserting `1` in the right tensor factor of `A ⊗[R] A`. -/
def rightUnitBaseChange (D : DescentData.{u, v, w} R A) :
    (A ⊗[R] restrictModule R A D.module) →ₗ[R]
      ((A ⊗[R] A) ⊗[R] restrictModule R A D.module) :=
  TensorProduct.map ((TensorProduct.mk R A A).flip 1) LinearMap.id

/-- On the target tensor product, acting by `a ⊗ 1` is acting by `a` through the first
tensor factor. -/
private theorem target_first_factor_smul (N : ModuleCat.{w} A) (a : A)
    (x : A ⊗[R] restrictModule R A N) :
    (a ⊗ₜ[R] (1 : A)) • x = a • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul b n =>
      rw [targetTensor_smul_tmul]
      simp [smul_tmul']

/-- An additive map out of a tensor product that commutes with the action of `a` on pure
tensors commutes with it everywhere. -/
private theorem map_smul_of_tmul {R A M N Y F : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] [AddCommMonoid Y] [DistribSMul A (M ⊗[R] N)]
    [DistribSMul A Y] [FunLike F (M ⊗[R] N) Y] [AddMonoidHomClass F (M ⊗[R] N) Y] (f : F)
    (a : A) (h : ∀ (m : M) (n : N), f (a • m ⊗ₜ[R] n) = a • f (m ⊗ₜ[R] n))
    (x : M ⊗[R] N) : f (a • x) = a • f x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul m n => exact h m n

/-- The first displayed formula is additive. -/
private theorem descentComparisonLeft_add (D : DescentData.{u, v, w} R A)
    (x y : D.module) :
    descentComparisonLeft R A D (x + y) =
      descentComparisonLeft R A D x + descentComparisonLeft R A D y := by
  show D.transition
      (((show restrictModule R A D.module from x) +
        (show restrictModule R A D.module from y)) ⊗ₜ[R] (1 : A)) =
    D.transition ((show restrictModule R A D.module from x) ⊗ₜ[R] (1 : A)) +
      D.transition ((show restrictModule R A D.module from y) ⊗ₜ[R] (1 : A))
  rw [add_tmul, map_add]

/-- The first displayed formula commutes with the action of `A`. -/
private theorem descentComparisonLeft_smul (D : DescentData.{u, v, w} R A) (a : A)
    (n : D.module) :
    descentComparisonLeft R A D (a • n) = a • descentComparisonLeft R A D n := by
  have h : D.transition ((a ⊗ₜ[R] (1 : A)) • ((show restrictModule R A D.module from n) ⊗ₜ[R]
      (1 : A))) = (a ⊗ₜ[R] (1 : A)) • D.transition (n ⊗ₜ[R] (1 : A)) :=
    D.transition.map_smul _ _
  have hn : restrictedScalarAction R A D.module a n = a • n :=
    restrictedScalarAction_apply R A D.module a n
  rwa [sourceTensor_smul_tmul, hn, one_mul, target_first_factor_smul] at h

/-- Regrouping a triple tensor product pulls a product in the first factor out as a scalar
on the first factor of the regrouped term. -/
private theorem assoc_symm_first_smul (N : ModuleCat.{w} A) (a b : A)
    (z : A ⊗[R] restrictModule R A N) :
    (TensorProduct.assoc R A A (restrictModule R A N)).symm
        ((a * b) ⊗ₜ[R] z) =
      a • (TensorProduct.assoc R A A (restrictModule R A N)).symm (b ⊗ₜ[R] z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simp only [tmul_add, map_add, hz, hz', smul_add]
  | tmul c n => simp [TensorProduct.assoc_symm_tmul, smul_tmul']

/-- The `R`-linear retraction `a ⊗ n ↦ a • n` of the first parallel arrow. -/
private def equalizerLeftRetractionR (D : DescentData.{u, v, w} R A) :
    (A ⊗[R] restrictModule R A D.module) →ₗ[R] restrictModule R A D.module :=
  TensorProduct.lift (restrictedScalarAction R A D.module).toLinearMap

/-- The `R`-linear multiplication map `a ⊗ b ↦ a * b` on `A ⊗[R] A`. -/
private def equalizerScalarProductR : A ⊗[R] A →ₗ[R] A :=
  TensorProduct.lift (LinearMap.mul R A)

/-- The retraction `a ⊗ n ↦ a • n`, promoted to an `A`-linear map. -/
private def equalizerLeftRetraction (D : DescentData.{u, v, w} R A) :
    (A ⊗[R] restrictModule R A D.module) →ₗ[A] D.module where
  toFun x := equalizerLeftRetractionR R A D x
  map_add' x y := (equalizerLeftRetractionR R A D).map_add x y
  map_smul' a x := map_smul_of_tmul (equalizerLeftRetractionR R A D) a (fun b n => by
    change (show D.module from restrictedScalarAction R A D.module (a * b) n) =
      a • (show D.module from restrictedScalarAction R A D.module b n)
    rw [restrictedScalarAction_apply, restrictedScalarAction_apply]
    exact (mul_smul a b (show D.module from n))) x

/-- The `A`-linear retraction agrees with its `R`-linear underlying map. -/
private theorem equalizerLeftRetraction_apply (D : DescentData.{u, v, w} R A)
    (x : A ⊗[R] restrictModule R A D.module) :
    equalizerLeftRetraction R A D x = equalizerLeftRetractionR R A D x := rfl

/-- The retraction `a ⊗ n ↦ a • n` landing in the universe-lifted first term of the
equalizer diagram. -/
private def equalizerLeftRetractionLift (D : DescentData.{u, v, w} R A) :
    (A ⊗[R] restrictModule R A D.module) →ₗ[A] ULift.{v} D.module where
  toFun x := ULift.up (equalizerLeftRetraction R A D x)
  map_add' x y := congrArg ULift.up ((equalizerLeftRetraction R A D).map_add x y)
  map_smul' a x := congrArg ULift.up ((equalizerLeftRetraction R A D).map_smul a x)

/-- The multiplication map `a ⊗ b ↦ a * b` on `A ⊗[R] A`, promoted to an `A`-linear map. -/
private def equalizerScalarProduct : (A ⊗[R] A) →ₗ[A] A where
  toFun := equalizerScalarProductR R A
  map_add' x y := (equalizerScalarProductR R A).map_add x y
  map_smul' a x := map_smul_of_tmul (equalizerScalarProductR R A) a (fun b c => mul_assoc a b c) x

/-- The `R`-linear retraction `(a ⊗ b) ⊗ n ↦ (a * b) ⊗ n` of the parallel arrows. -/
private def equalizerRightRetractionR (D : DescentData.{u, v, w} R A) :
    ((A ⊗[R] A) ⊗[R] restrictModule R A D.module) →ₗ[R]
      (A ⊗[R] restrictModule R A D.module) :=
  TensorProduct.map ((equalizerScalarProduct R A).restrictScalars R) LinearMap.id

/-- The retraction `(a ⊗ b) ⊗ n ↦ (a * b) ⊗ n`, promoted to an `A`-linear map. -/
private def equalizerRightRetraction (D : DescentData.{u, v, w} R A) :
    ((A ⊗[R] A) ⊗[R] restrictModule R A D.module) →ₗ[A]
      (A ⊗[R] restrictModule R A D.module) where
  toFun x := equalizerRightRetractionR R A D x
  map_add' x y := (equalizerRightRetractionR R A D).map_add x y
  map_smul' a x := map_smul_of_tmul (equalizerRightRetractionR R A D) a (fun p n => by
    change equalizerRightRetractionR R A D ((a • p) ⊗ₜ[R] n) =
      a • equalizerRightRetractionR R A D (p ⊗ₜ[R] n)
    simp only [equalizerRightRetractionR, TensorProduct.map_tmul,
      LinearMap.restrictScalars_apply, smul_tmul']
    rw [(equalizerScalarProduct R A).map_smul]) x

/-- The canonical `A`-linear lifts of the three displayed formulas. -/
structure CanonicalArrows (D : DescentData.{u, v, w} R A) where
  /-- The `A`-linear lift of `n ↦ θ(n ⊗ 1)`. -/
  comparison : ULift.{v} D.module →ₗ[A]
    (A ⊗[R] restrictModule R A D.module)
  /-- The `A`-linear lift of the transition pulled back in positions `1, 2`. -/
  transition : (A ⊗[R] restrictModule R A D.module) →ₗ[A]
    ((A ⊗[R] A) ⊗[R] restrictModule R A D.module)
  /-- The `A`-linear lift of `a ⊗ n ↦ (a ⊗ 1) ⊗ n`. -/
  unit : (A ⊗[R] restrictModule R A D.module) →ₗ[A]
    ((A ⊗[R] A) ⊗[R] restrictModule R A D.module)
  /-- The lift of the comparison map computes the displayed formula. -/
  comparison_spec : ∀ n : D.module,
    comparison (ULift.up n) = descentComparisonLeft R A D n
  /-- The lift of the first parallel arrow restricts to the displayed formula. -/
  transition_spec : transition.restrictScalars R = transition12AfterUnit R A D
  /-- The lift of the second parallel arrow restricts to the displayed formula. -/
  unit_spec : unit.restrictScalars R = rightUnitBaseChange R A D

/-- Each of the three displayed `R`-linear formulas is in fact `A`-linear for the actions
through the first tensor factor. -/
theorem canonicalArrows_nonempty
    (D : DescentData.{u, v, w} R A) : Nonempty (CanonicalArrows R A D) := by
  refine ⟨{
    comparison := {
      toFun := fun x => descentComparisonLeft R A D x.down
      map_add' := fun x y => descentComparisonLeft_add R A D x.down y.down
      map_smul' := fun a x => descentComparisonLeft_smul R A D a x.down
    }
    transition := {
      toFun := fun x => transition12AfterUnit R A D x
      map_add' := by
        intro x y
        simp [transition12AfterUnit]
      map_smul' := fun a x => map_smul_of_tmul (transition12AfterUnit R A D) a
        (fun b n => assoc_symm_first_smul R A D.module a b (D.transition (n ⊗ₜ[R] (1 : A)))) x
    }
    unit := {
      toFun := fun x => rightUnitBaseChange R A D x
      map_add' := by
        intro x y
        simp [rightUnitBaseChange]
      map_smul' := fun a x => map_smul_of_tmul (rightUnitBaseChange R A D) a (fun b n => rfl) x
    }
    comparison_spec _ := rfl
    transition_spec := rfl
    unit_spec := rfl
  }⟩

/-- The first canonical arrow in the equalizer diagram of a module descent datum. -/
noncomputable def descentComparisonHom (D : DescentData.{u, v, w} R A) :
    ULift.{v} D.module →ₗ[A] (A ⊗[R] restrictModule R A D.module) :=
  (Classical.choice (canonicalArrows_nonempty R A D)).comparison

/-- The first parallel arrow in the equalizer diagram of a module descent datum. -/
noncomputable def transition12AfterUnitHom (D : DescentData.{u, v, w} R A) :
    (A ⊗[R] restrictModule R A D.module) →ₗ[A]
      ((A ⊗[R] A) ⊗[R] restrictModule R A D.module) :=
  (Classical.choice (canonicalArrows_nonempty R A D)).transition

/-- The second parallel arrow in the equalizer diagram of a module descent datum. -/
noncomputable def rightUnitBaseChangeHom (D : DescentData.{u, v, w} R A) :
    (A ⊗[R] restrictModule R A D.module) →ₗ[A]
      ((A ⊗[R] A) ⊗[R] restrictModule R A D.module) :=
  (Classical.choice (canonicalArrows_nonempty R A D)).unit

/-- The first canonical arrow sends `n` to the transition applied to `n ⊗ 1`. -/
theorem descentComparisonHom_apply (D : DescentData.{u, v, w} R A)
    (n : D.module) :
    descentComparisonHom R A D (ULift.up n) =
      descentComparisonLeft R A D n :=
  (Classical.choice (canonicalArrows_nonempty R A D)).comparison_spec n

/-- The first parallel arrow restricts to the transition pulled back in positions `1, 2`
after adjoining a unit. -/
theorem transition12AfterUnitHom_restrictScalars
    (D : DescentData.{u, v, w} R A) :
    (transition12AfterUnitHom R A D).restrictScalars R = transition12AfterUnit R A D :=
  (Classical.choice (canonicalArrows_nonempty R A D)).transition_spec

/-- The second parallel arrow restricts to `a ⊗ n ↦ (a ⊗ 1) ⊗ n`. -/
theorem rightUnitBaseChangeHom_restrictScalars
    (D : DescentData.{u, v, w} R A) :
    (rightUnitBaseChangeHom R A D).restrictScalars R = rightUnitBaseChange R A D :=
  (Classical.choice (canonicalArrows_nonempty R A D)).unit_spec

/-- Collapse `n ⊗ a` to `a • n`. -/
private def sourceUnitCollapse (D : DescentData.{u, v, w} R A) :
    (restrictModule R A D.module ⊗[R] A) →ₗ[R] restrictModule R A D.module :=
  (equalizerLeftRetractionR R A D).comp
    (TensorProduct.comm R (restrictModule R A D.module) A).toLinearMap

/-- The collapse map is a retraction of `n ↦ n ⊗ 1`. -/
private theorem sourceUnitCollapse_tmul (D : DescentData.{u, v, w} R A)
    (n : restrictModule R A D.module) :
    sourceUnitCollapse R A D (n ⊗ₜ[R] (1 : A)) = n := by
  simp [sourceUnitCollapse, equalizerLeftRetractionR,
    TensorProduct.comm_tmul, TensorProduct.lift.tmul]

/-- The first displayed formula is injective, because `n ↦ n ⊗ 1` is split and the
transition is an isomorphism. -/
private theorem descentComparisonLeft_injective (D : DescentData.{u, v, w} R A) :
    Function.Injective (descentComparisonLeft R A D) := by
  intro x y h
  have hθ : D.transition (x ⊗ₜ[R] (1 : A)) =
      D.transition (y ⊗ₜ[R] (1 : A)) := by
    simpa [descentComparisonLeft, transitionRestrictScalars_apply] using h
  have hxy := congrArg (sourceUnitCollapse R A D) (D.transition.injective hθ)
  have hx := sourceUnitCollapse_tmul R A D (show restrictModule R A D.module from x)
  have hy := sourceUnitCollapse_tmul R A D (show restrictModule R A D.module from y)
  rwa [hx, hy] at hxy

/-- Adjoining a unit on the right and then regrouping is the second parallel arrow. -/
private theorem rightComm_unit (D : DescentData.{u, v, w} R A)
    (x : A ⊗[R] restrictModule R A D.module) :
    (TensorProduct.rightComm R A (restrictModule R A D.module) A)
        (x ⊗ₜ[R] (1 : A)) = rightUnitBaseChange R A D x := by
  induction x using TensorProduct.induction_on with
  | zero => simp [rightUnitBaseChange]
  | add x y hx hy => rw [add_tmul, map_add, hx, hy, map_add]
  | tmul a n =>
      simp [rightUnitBaseChange, TensorProduct.rightComm_tmul,
        TensorProduct.map_tmul, TensorProduct.mk_apply]

/-- The two parallel arrows agree on the image of the first arrow. This is the cocycle
condition evaluated at `(n ⊗ 1) ⊗ 1`. -/
private theorem descentComparison_cocycle (D : DescentData.{u, v, w} R A)
    (n : D.module) :
    transition12AfterUnit R A D (descentComparisonLeft R A D n) =
      rightUnitBaseChange R A D (descentComparisonLeft R A D n) := by
  have h := congrArg (fun f => f ((n ⊗ₜ[R] (1 : A)) ⊗ₜ[R] (1 : A))) D.cocycle
  change transition12 R A D.module D.transition
      ((transition01 R A D.module D.transition)
        ((n ⊗ₜ[R] (1 : A)) ⊗ₜ[R] (1 : A))) =
    transition02 R A D.module D.transition
      ((n ⊗ₜ[R] (1 : A)) ⊗ₜ[R] (1 : A)) at h
  rw [transition01, LinearMap.rTensor_tmul] at h
  change transition12AfterUnit R A D (D.transition (n ⊗ₜ[R] (1 : A))) =
    (TensorProduct.rightComm R A (restrictModule R A D.module) A)
      (D.transition (n ⊗ₜ[R] (1 : A)) ⊗ₜ[R] (1 : A)) at h
  rw [rightComm_unit] at h
  simpa [descentComparisonLeft, transitionRestrictScalars_apply] using h

/-- The right retraction splits the second parallel arrow. -/
private theorem equalizerRightRetraction_unit (D : DescentData.{u, v, w} R A)
    (x : A ⊗[R] restrictModule R A D.module) :
    equalizerRightRetractionR R A D (rightUnitBaseChange R A D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp [rightUnitBaseChange, equalizerRightRetractionR]
  | add x y hx hy => simp [hx, hy]
  | tmul a n =>
      show (a * 1) ⊗ₜ[R] n = a ⊗ₜ[R] n
      simp

/-- Regrouping and then contracting the first two factors is the action on the first
factor. -/
private theorem equalizerRightRetraction_assoc (D : DescentData.{u, v, w} R A)
    (a : A) (x : A ⊗[R] restrictModule R A D.module) :
    equalizerRightRetractionR R A D
        ((TensorProduct.assoc R A A (restrictModule R A D.module)).symm
          (a ⊗ₜ[R] x)) = a • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp [equalizerRightRetractionR]
  | add x y hx hy => rw [tmul_add, map_add, map_add, hx, hy, smul_add]
  | tmul b n =>
      show (a * b) ⊗ₜ[R] n = a • (b ⊗ₜ[R] n)
      simp [smul_tmul']

/-- The right retraction carries the first parallel arrow to the first arrow precomposed
with the left retraction. -/
private theorem equalizerRightRetraction_transition (D : DescentData.{u, v, w} R A)
    (x : A ⊗[R] restrictModule R A D.module) :
    equalizerRightRetractionR R A D (transition12AfterUnit R A D x) =
      descentComparisonLeft R A D (equalizerLeftRetractionR R A D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp [transition12AfterUnit, descentComparisonLeft]
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy, map_add]
      exact (descentComparisonLeft_add R A D _ _).symm
  | tmul a n =>
      show equalizerRightRetractionR R A D
          ((TensorProduct.assoc R A A (restrictModule R A D.module)).symm
            (a ⊗ₜ[R] D.transition (n ⊗ₜ[R] (1 : A)))) =
        descentComparisonLeft R A D (a • n)
      rw [equalizerRightRetraction_assoc]
      exact (descentComparisonLeft_smul R A D a n).symm

/-- The left retraction splits the first arrow. -/
private theorem descentComparison_unit (D : DescentData.{u, v, w} R A)
    (n : D.module) :
    equalizerLeftRetractionR R A D (descentComparisonLeft R A D n) = n := by
  have hc := descentComparison_cocycle R A D n
  have ht := equalizerRightRetraction_transition R A D
    (descentComparisonLeft R A D n)
  have hg := equalizerRightRetraction_unit R A D
    (descentComparisonLeft R A D n)
  have h := congrArg (equalizerRightRetractionR R A D) hc
  rw [ht, hg] at h
  exact descentComparisonLeft_injective R A D h

/-- Pointwise form of `transition12AfterUnitHom_restrictScalars`. -/
private theorem transition12AfterUnitHom_apply (D : DescentData.{u, v, w} R A)
    (x : A ⊗[R] restrictModule R A D.module) :
    transition12AfterUnitHom R A D x = transition12AfterUnit R A D x := by
  have h := congrArg (fun f : (A ⊗[R] restrictModule R A D.module) →ₗ[R]
      ((A ⊗[R] A) ⊗[R] restrictModule R A D.module) => f x)
    (transition12AfterUnitHom_restrictScalars R A D)
  simpa using h

/-- Pointwise form of `rightUnitBaseChangeHom_restrictScalars`. -/
private theorem rightUnitBaseChangeHom_apply (D : DescentData.{u, v, w} R A)
    (x : A ⊗[R] restrictModule R A D.module) :
    rightUnitBaseChangeHom R A D x = rightUnitBaseChange R A D x := by
  have h := congrArg (fun f : (A ⊗[R] restrictModule R A D.module) →ₗ[R]
      ((A ⊗[R] A) ⊗[R] restrictModule R A D.module) => f x)
    (rightUnitBaseChangeHom_restrictScalars R A D)
  simpa using h

/-- **Stacks Project, Tag 08WZ.** The canonically associated diagram is a split equalizer of
`A`-modules. -/
@[stacks 08WZ]
theorem isSplitEqualizer_descentComparison
    (D : DescentData.{u, v, w} R A) :
    Nonempty (IsSplitEqualizer
      (ModuleCat.ofHom (transition12AfterUnitHom R A D))
      (ModuleCat.ofHom (rightUnitBaseChangeHom R A D))
      (ModuleCat.ofHom (descentComparisonHom R A D))) := by
  let ι := ModuleCat.ofHom (descentComparisonHom R A D)
  let f := ModuleCat.ofHom (transition12AfterUnitHom R A D)
  let g := ModuleCat.ofHom (rightUnitBaseChangeHom R A D)
  let r := ModuleCat.ofHom (equalizerLeftRetractionLift R A D)
  let t := ModuleCat.ofHom (equalizerRightRetraction R A D)
  refine ⟨{
    leftRetraction := r
    rightRetraction := t
    condition := by
      apply ModuleCat.hom_ext
      refine LinearMap.ext fun z => ?_
      show transition12AfterUnitHom R A D (descentComparisonHom R A D z) =
        rightUnitBaseChangeHom R A D (descentComparisonHom R A D z)
      rw [descentComparisonHom_apply, transition12AfterUnitHom_apply,
        rightUnitBaseChangeHom_apply]
      exact descentComparison_cocycle R A D z.down
    ι_leftRetraction := by
      apply ModuleCat.hom_ext
      refine LinearMap.ext fun z => ?_
      cases z with
      | up n =>
          show ULift.up (equalizerLeftRetraction R A D
            (descentComparisonHom R A D (ULift.up n))) = ULift.up n
          rw [descentComparisonHom_apply]
          congr 1
          exact descentComparison_unit R A D n
    bottom_rightRetraction := by
      apply ModuleCat.hom_ext
      refine LinearMap.ext fun x => ?_
      show equalizerRightRetraction R A D
        (rightUnitBaseChangeHom R A D x) = x
      rw [rightUnitBaseChangeHom_apply]
      exact equalizerRightRetraction_unit R A D x
    top_rightRetraction := by
      apply ModuleCat.hom_ext
      refine LinearMap.ext fun x => ?_
      show equalizerRightRetraction R A D
          (transition12AfterUnitHom R A D x) =
        descentComparisonHom R A D (equalizerLeftRetractionLift R A D x)
      rw [transition12AfterUnitHom_apply, equalizerLeftRetractionLift, descentComparisonHom_apply]
      show equalizerRightRetractionR R A D (transition12AfterUnit R A D x) =
        descentComparisonLeft R A D (equalizerLeftRetraction R A D x)
      rw [equalizerLeftRetraction_apply]
      exact equalizerRightRetraction_transition R A D x
  }⟩

/-- The equalizer inclusion of Tag 08WZ is injective, being a limit cone leg. -/
theorem descentComparisonHom_injective (D : DescentData.{u, v, w} R A) :
    Function.Injective (descentComparisonHom R A D) := by
  have hmono : Mono (ModuleCat.ofHom (descentComparisonHom R A D) :
      ModuleCat.of A (ULift.{v} D.module) ⟶
        ModuleCat.of A (A ⊗[R] restrictModule R A D.module)) :=
    CategoryTheory.Limits.Fork.IsLimit.mono
      (Classical.choice (isSplitEqualizer_descentComparison R A D)).isEqualizer
  exact (ModuleCat.mono_iff_injective
    (ModuleCat.ofHom (descentComparisonHom R A D))).mp hmono

/-- **Stacks Project, Tag 08X1.** Character duality turns the descent equalizer into a split
coequalizer. -/
@[stacks 08X1]
theorem isSplitCoequalizer_characterModule_descentComparison
    (D : DescentData.{u, v, w} R A) :
    Nonempty (IsSplitCoequalizer
      (ModuleCat.ofHom (CharacterModule.dual (transition12AfterUnitHom R A D)))
      (ModuleCat.ofHom (CharacterModule.dual (rightUnitBaseChangeHom R A D)))
      (ModuleCat.ofHom (CharacterModule.dual (descentComparisonHom R A D)))) :=
  characterDual_isSplitCoequalizer (Classical.choice (isSplitEqualizer_descentComparison R A D))

end ModuleCat.DescentData
