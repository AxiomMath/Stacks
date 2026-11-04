module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictColimits
public import StacksFrontier.AlgebraicGeometry.Constructions.PullbackTwistSectionMul

/-!
# The regrouping square can be solved downwards as well as upwards

`Stacks.AlgebraicGeometry.PullbackTwistSectionMul.pullback_twistSectionMul` restricts
multiplication by a degree-one form on a twist to a hyperplane, on one hypothesis: a family
`θ_d : g^*𝒪(d) ≅ 𝒪(d)` of identifications of the twists satisfying the **regrouping square**

`g^*(𝒪(d) ⊗ 𝒪(1) ≅ 𝒪(d+1)) ≫ θ_{d+1} = (01CD) ≫ (θ_d ⊗ θ_1) ≫ (𝒪(d) ⊗ 𝒪(1) ≅ 𝒪(d+1))`

in the degree in question. `…PullbackTwistSectionMul.exists_pullbackTwistIso_succ` solves that
square for `θ_{d+1}` given `θ_d`, so a family over `{d₀, d₀+1, …}` is available for any base
degree; and that file's implementation notes record that the step going the other way — `θ_d`
from `θ_{d+1}` — "would need `θ_d` to be extracted from `θ_d ⊗ θ_1`, i.e. the functor
`- ⊗ 𝒪_{ℙᵐ}(1)` to be full on the hom-set in question. That is true … but it is stated for
`Stacks.SheafOfModules.TensorPower.tensorRightFunctor`, a different spelling of the tensor
product from the one used here, and the bridge is not available."

This file supplies the bridge and the step. [Stacks, Tag 08A7] needs the family over **all** of
`ℤ`, the restriction sequences being needed at every twist, so the downward step is exactly what
was missing.

## Main results

* `Stacks.AlgebraicGeometry.PullbackTwistRegrouping.whiskerRight_eq_tensorRightModules`: **the
  bridge.** Right whiskering by `ℬ` in the monoidal structure of [Stacks, Tag 01CA] is the action
  on morphisms of `…HyperplaneTwistSequence.tensorRightModules X ℬ`, which is
  `Stacks.SheafOfModules.TensorPower.tensorRightFunctor`.
* `…PullbackTwistRegrouping.exists_iso_whiskerRight_eq`: **tensoring with an invertible module is
  full on isomorphisms** — any isomorphism `𝒜 ⊗ ℬ ≅ 𝒞 ⊗ ℬ` with `ℬ` invertible is `θ ▷ ℬ` for an
  isomorphism `θ : 𝒜 ≅ 𝒞`.
* `…PullbackTwistRegrouping.exists_pullbackTwistIso_pred`: **the regrouping square of degree
  `(d, 1)` determines `θ_d` from `θ_{d+1}` and `θ_1`.**

## The mathematics

Only the bridge. Tensoring on the right by an invertible module is an equivalence
(`Stacks.RelativeVeryAmple.isEquivalence_tensorRightFunctor_of_isInvertibleModule`, which is
[Stacks, Tag 01CU]'s own hypothesis in the other of the library's two forms), hence full and
faithful; a full functor hits `Ξ` with some `θ`, and a faithful one reflects the invertibility of
`Ξ`, so `θ` is an isomorphism. The one thing to check is that the functor that is an equivalence
is the one whose action on morphisms is `▷`, and that is
`Stacks.SheafOfModules.Strict.whiskerRight_eq_sheafTensor`: both are the sheafification of the
objectwise `v ⊗ 𝟙`.

The downward step then reads the regrouping square as an equation for `θ_d ▷ g^*𝒪(1)`: writing
`θ_d ⊗ θ_1` as `(θ_d ▷ g^*𝒪(1)) ≫ (𝒪(d) ◁ θ_1)` and moving every other arrow — all of them
isomorphisms — to the other side leaves exactly that, and `g^*𝒪(1)` is invertible by
[Stacks, Tag 0B8L].

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 08A7](https://stacks.math.columbia.edu/tag/08A7)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence (tensorRightModules)
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver twistOverMulIso)
open Stacks.Ample (IsInvertibleModule)
open Stacks.RelativeVeryAmple (pullbackTensorModulesIso)

universe u

namespace Stacks.AlgebraicGeometry.PullbackTwistRegrouping

attribute [local instance] Stacks.AlgebraicGeometry.PullbackSectionMul.schemeTensorStrict

/-! ### Right whiskering is the right-tensor functor of [Stacks, Tag 01CU] -/

/-- **Right whiskering by `ℬ` in the monoidal structure of [Stacks, Tag 01CA] is the action on
morphisms of `Stacks.AlgebraicGeometry.HyperplaneTwistSequence.tensorRightModules X ℬ`**, i.e. of
`Stacks.SheafOfModules.TensorPower.tensorRightFunctor`. Both are the sheafification of the
objectwise `v ⊗ 𝟙`; this is `Stacks.SheafOfModules.Strict.whiskerRight_eq_sheafTensor` read at the
`X.Modules` spelling. -/
theorem whiskerRight_eq_tensorRightModules (X : Scheme.{u}) (B : X.Modules) {A C : X.Modules}
    (v : A ⟶ C) : v ▷ B = (tensorRightModules X B).map v :=
  Stacks.SheafOfModules.Strict.whiskerRight_eq_sheafTensor X.sheaf v B

/-- **Tensoring with an invertible module is full on isomorphisms.** Every isomorphism
`Ξ : 𝒜 ⊗ ℬ ≅ 𝒞 ⊗ ℬ` with `ℬ` invertible is `θ ▷ ℬ` for an isomorphism `θ : 𝒜 ≅ 𝒞`.

Tensoring on the right by an invertible module is an equivalence
(`Stacks.RelativeVeryAmple.isEquivalence_tensorRightFunctor_of_isInvertibleModule`), hence full
and faithful: fullness produces a morphism `v` with `v ▷ ℬ = Ξ`, and faithfulness upgrades it to
an isomorphism, `Ξ` being one. -/
theorem exists_iso_whiskerRight_eq (X : Scheme.{u}) (B : X.Modules) [IsInvertibleModule X B]
    {A C : X.Modules} (Ξ : A ⊗ B ≅ C ⊗ B) : ∃ θ : A ≅ C, θ.hom ▷ B = Ξ.hom := by
  have : (tensorRightModules X B).IsEquivalence :=
    Stacks.RelativeVeryAmple.isEquivalence_tensorRightFunctor_of_isInvertibleModule X B
  obtain ⟨v, hv⟩ := (tensorRightModules X B).map_surjective Ξ.hom
  have : IsIso ((tensorRightModules X B).map v) := by
    rw [hv]; exact ⟨⟨Ξ.inv, Ξ.hom_inv_id, Ξ.inv_hom_id⟩⟩
  have : IsIso v := isIso_of_fully_faithful (tensorRightModules X B) v
  exact ⟨asIso v, (whiskerRight_eq_tensorRightModules X B v).trans hv⟩

/-- Cancelling the isomorphisms in a solved square: pure category theory, isolated because the
concrete instance mixes two presentations of the tensor product and `rw` cannot cross them. -/
private theorem comp_cancel {C : Type*} [Category C] {W U P₁ P Q R : C} (c : W ≅ U)
    (a : W ⟶ P₁) (e : P₁ ⟶ P) (minv : P ⟶ Q) (w' : Q ⟶ R) (w : R ⟶ Q) (mhom : Q ⟶ P)
    (hw : w' ≫ w = 𝟙 Q) (hm : minv ≫ mhom = 𝟙 P) :
    c.hom ≫ ((c.inv ≫ a ≫ e ≫ minv ≫ w') ≫ w) ≫ mhom = a ≫ e := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% hw, hm, Category.comp_id]

/-! ### The regrouping square, solved downwards -/

variable (n m : ℕ) (S : Scheme.{u}) (g : projectiveSpaceOver m S ⟶ projectiveSpaceOver n S)

/-- **The regrouping square of degree `(d, 1)` determines `θ_d` from `θ_{d+1}` and `θ_1`.**

This is the step `Stacks.AlgebraicGeometry.PullbackTwistSectionMul.exists_pullbackTwistIso_succ`
does not do: solving the square for the *lower* degree. Written out, the square says that
`θ_d ▷ g^*𝒪(1)` is a prescribed isomorphism, every other arrow in it being invertible, and
`exists_iso_whiskerRight_eq` solves that for `θ_d` — `g^*𝒪(1)` being invertible by
[Stacks, Tag 0B8L]. Together with the upward step it makes the family available over all of `ℤ`,
which is what the restriction sequences of [Stacks, Tag 08A7] need. -/
theorem exists_pullbackTwistIso_pred (d : ℤ)
    (θd1 : (Scheme.Modules.pullback g).obj (twistOver n S (d + 1)) ≅ twistOver m S (d + 1))
    (θ1 : (Scheme.Modules.pullback g).obj (twistOver n S 1) ≅ twistOver m S 1) :
    ∃ θd : (Scheme.Modules.pullback g).obj (twistOver n S d) ≅ twistOver m S d,
      (Scheme.Modules.pullback g).map (twistOverMulIso n S d 1).hom ≫ θd1.hom =
        (pullbackTensorModulesIso g (twistOver n S d) (twistOver n S 1)).hom ≫
          (θd.hom ⊗ₘ θ1.hom) ≫ (twistOverMulIso m S d 1).hom := by
  let Ξ := (pullbackTensorModulesIso g (twistOver n S d) (twistOver n S 1)).symm ≪≫
    (Scheme.Modules.pullback g).mapIso (twistOverMulIso n S d 1) ≪≫ θd1 ≪≫
    (twistOverMulIso m S d 1).symm ≪≫ whiskerLeftIso (twistOver m S d) θ1.symm
  obtain ⟨θd, hθd⟩ := exists_iso_whiskerRight_eq (projectiveSpaceOver m S)
    ((Scheme.Modules.pullback g).obj (twistOver n S 1))
    (A := (Scheme.Modules.pullback g).obj (twistOver n S d)) (C := twistOver m S d) Ξ
  have h1 : θd.hom ⊗ₘ θ1.hom = Ξ.hom ≫ twistOver m S d ◁ θ1.hom := by
    rw [tensorHom_def, hθd]
    rfl
  refine ⟨θd, Eq.trans ?_ (congrArg (fun z =>
    (pullbackTensorModulesIso g (twistOver n S d) (twistOver n S 1)).hom ≫ z ≫
      (twistOverMulIso m S d 1).hom) h1).symm⟩
  refine (comp_cancel (pullbackTensorModulesIso g (twistOver n S d) (twistOver n S 1))
    ((Scheme.Modules.pullback g).map (twistOverMulIso n S d 1).hom) θd1.hom
    (twistOverMulIso m S d 1).inv (twistOver m S d ◁ θ1.inv) (twistOver m S d ◁ θ1.hom)
    (twistOverMulIso m S d 1).hom ?_ (twistOverMulIso m S d 1).inv_hom_id).symm
  exact (whiskerLeftIso (twistOver m S d) θ1).inv_hom_id

/-! ### The family over all of `ℤ` -/

section Family

open Stacks.AlgebraicGeometry.PullbackTwistSectionMul (exists_pullbackTwistIso_succ)

variable (θ1 : (Scheme.Modules.pullback g).obj (twistOver n S 1) ≅ twistOver m S 1)

/-- The identification in degree zero, solved out of the regrouping square of degree `(0, 1)`. -/
private noncomputable def zeroFam :
    (Scheme.Modules.pullback g).obj (twistOver n S 0) ≅ twistOver m S 0 :=
  (exists_pullbackTwistIso_pred n m S g 0 θ1 θ1).choose

/-- The identifications in the degrees `1, 2, …`, by the upward step. -/
private noncomputable def upFam : (k : ℕ) →
    ((Scheme.Modules.pullback g).obj (twistOver n S ((k : ℤ) + 1)) ≅
      twistOver m S ((k : ℤ) + 1))
  | 0 => θ1
  | k + 1 =>
      (exists_pullbackTwistIso_succ n m S g ((k : ℤ) + 1) (upFam k) θ1).choose

/-- The identifications in the degrees `-1, -2, …`, by the downward step. -/
private noncomputable def downFam : (k : ℕ) →
    ((Scheme.Modules.pullback g).obj (twistOver n S (Int.negSucc k)) ≅
      twistOver m S (Int.negSucc k))
  | 0 => (exists_pullbackTwistIso_pred n m S g (Int.negSucc 0) (zeroFam n m S g θ1) θ1).choose
  | k + 1 =>
      (exists_pullbackTwistIso_pred n m S g (Int.negSucc (k + 1)) (downFam k) θ1).choose

/-- **The identifications of the twists along `g` in every integer degree, satisfying the
regrouping square in every degree.** Degree one is the given `θ1`, the degrees above it come from
`…PullbackTwistSectionMul.exists_pullbackTwistIso_succ` and the degrees below it from
`exists_pullbackTwistIso_pred`. -/
private noncomputable def regroupFam : (d : ℤ) →
    ((Scheme.Modules.pullback g).obj (twistOver n S d) ≅ twistOver m S d)
  | Int.ofNat 0 => zeroFam n m S g θ1
  | Int.ofNat (k + 1) => upFam n m S g θ1 k
  | Int.negSucc k => downFam n m S g θ1 k

/-- **A family of identifications of the twists satisfying the regrouping square in *every*
integer degree, extending a given one in degree one.**

This is the hypothesis `hθ` of
`Stacks.AlgebraicGeometry.PullbackTwistSectionMul.exists_pullback_twistSectionMul`, which that
file's notes record as the only thing between it and an unconditional statement over all of `ℤ`:
the upward step is proved there, and `exists_pullbackTwistIso_pred` above supplies the downward
one, so the family can be built from any single degree in both directions. Degree one is taken as
the anchor, because the square in degree `d` refers to the family's value in degree one, so an
anchor anywhere else would have to satisfy the square at the anchor as well. -/
theorem exists_regroupingFamily :
    ∃ θ : ∀ d : ℤ, (Scheme.Modules.pullback g).obj (twistOver n S d) ≅ twistOver m S d,
      θ 1 = θ1 ∧ ∀ d : ℤ,
        (Scheme.Modules.pullback g).map (twistOverMulIso n S d 1).hom ≫ (θ (d + 1)).hom =
          (pullbackTensorModulesIso g (twistOver n S d) (twistOver n S 1)).hom ≫
            ((θ d).hom ⊗ₘ (θ 1).hom) ≫ (twistOverMulIso m S d 1).hom := by
  refine ⟨regroupFam n m S g θ1, rfl, fun d => ?_⟩
  match d with
  | Int.ofNat 0 => exact (exists_pullbackTwistIso_pred n m S g 0 θ1 θ1).choose_spec
  | Int.ofNat (k + 1) =>
      exact (exists_pullbackTwistIso_succ n m S g ((k : ℤ) + 1)
        (upFam n m S g θ1 k) θ1).choose_spec
  | Int.negSucc 0 =>
      exact (exists_pullbackTwistIso_pred n m S g (Int.negSucc 0)
        (zeroFam n m S g θ1) θ1).choose_spec
  | Int.negSucc (k + 1) =>
      exact (exists_pullbackTwistIso_pred n m S g (Int.negSucc (k + 1))
        (downFam n m S g θ1 k) θ1).choose_spec

end Family

end Stacks.AlgebraicGeometry.PullbackTwistRegrouping

end
