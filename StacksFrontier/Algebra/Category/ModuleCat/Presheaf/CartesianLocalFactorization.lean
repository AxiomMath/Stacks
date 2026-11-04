module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianComposition

/-!
# Being cartesian from local factorizations through cartesian arrows

Let `R` be a presheaf of commutative rings on a category `C` and `M` a presheaf of modules over
it. Write `θ_f : R Y ⊗[R X] M X ⟶ M Y` for the base-change comparison of the restriction map of
`M` along `f : X ⟶ Y` in `Cᵒᵖ`; `M` is *cartesian* over `f` when `θ_f` is bijective.

This file adds two facts to
`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/CartesianComposition.lean`.

* Left cancellation: if `M` is cartesian over `f` and over `f ≫ g`, it is cartesian over `g`.
* Descent from local factorizations: let `φ : z ⟶ x` be an arrow of `C`, and suppose there is a
  finite family `q i : z'ᵢ ⟶ z` along which the ring map `R z ⟶ ∏ R z'ᵢ` is faithfully flat,
  together with factorizations `q i = c i ≫ a i` and `q i ≫ φ = c i ≫ b i` through arrows
  `a i : wᵢ ⟶ z`, `b i : wᵢ ⟶ x`. If `M` is cartesian over every `q i`, `a i` and `b i`, then `M`
  is cartesian over `φ`.

The second is the shape of the argument extending flat base change of a module on an algebraic
stack from flat arrows to all arrows between flat objects: the arrows `q i`, `a i`, `b i` all lie
over flat morphisms of schemes, while `φ` and the `c i` need not.

## Main results

* `Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_comp_left`: left cancellation.
* `Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_factorizations`: descent from local
  factorizations through cartesian arrows.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
-/

@[expose] public section

open CategoryTheory TensorProduct

universe u v r m

namespace Stacks.PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{r}}
  (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))

/-- **Left cancellation of cartesian arrows.** If `M` is cartesian over `f` and over `f ≫ g`, then
it is cartesian over `g`: the comparison over `f ≫ g` is the comparison over `g` after the base
change of the comparison over `f`, which is bijective. -/
theorem isIso_restrictionBaseChange_of_comp_left {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsIso (restrictionBaseChange M f)) (hfg : IsIso (restrictionBaseChange M (f ≫ g))) :
    IsIso (restrictionBaseChange M g) := by
  let : Algebra (R.obj X) (R.obj Y) := (R.map f).hom.toAlgebra
  let : Algebra (R.obj Y) (R.obj Z) := (R.map g).hom.toAlgebra
  let : Algebra (R.obj X) (R.obj Z) := (R.map (f ≫ g)).hom.toAlgebra
  let : IsScalarTower (R.obj X) (R.obj Y) (R.obj Z) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    change (R.map (f ≫ g)).hom a = (R.map g).hom ((R.map f).hom a)
    rw [R.map_comp]
    rfl
  let θ : TensorProduct (R.obj X) (R.obj Y) (M.obj X) →ₗ[R.obj Y] M.obj Y :=
    (restrictionBaseChange M f).hom
  let θg : TensorProduct (R.obj Y) (R.obj Z) (M.obj Y) →ₗ[R.obj Z] M.obj Z :=
    (restrictionBaseChange M g).hom
  let θfg : TensorProduct (R.obj X) (R.obj Z) (M.obj X) →ₗ[R.obj Z] M.obj Z :=
    (restrictionBaseChange M (f ≫ g)).hom
  let c := AlgebraTensorModule.cancelBaseChange (R.obj X) (R.obj Y) (R.obj Z) (R.obj Z)
    (M.obj X)
  have key : ∀ z, θfg (c z) = θg (LinearMap.lTensor (R.obj Z) θ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul d w =>
      induction w using TensorProduct.induction_on with
      | zero => simp only [tmul_zero, map_zero]
      | add w w' hw hw' => simp only [tmul_add, map_add, hw, hw']
      | tmul b x =>
        rw [AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.lTensor_tmul]
        have h1 : θfg ((b • d) ⊗ₜ x) = (b • d) • (M.map (f ≫ g) x : M.obj Z) :=
          restrictionBaseChange_tmul M (f ≫ g) (b • d) x
        have h2 : θ (b ⊗ₜ x) = b • (M.map f x : M.obj Y) := restrictionBaseChange_tmul M f b x
        have h3 : θg (d ⊗ₜ (b • (M.map f x : M.obj Y))) =
            d • (M.map g (b • (M.map f x : M.obj Y)) : M.obj Z) :=
          restrictionBaseChange_tmul M g d (b • (M.map f x : M.obj Y))
        have h4 : (M.map g (b • (M.map f x : M.obj Y)) : M.obj Z) =
            (R.map g).hom b • (M.map g (M.map f x) : M.obj Z) :=
          M.map_smul g b (M.map f x)
        have h5 : (M.map (f ≫ g) x : M.obj Z) = M.map g (M.map f x) := M.map_comp_apply f g x
        rw [h1, h2, h3, h4, h5, smul_smul]
        congr 1
        change (R.map g).hom b * d = d * (R.map g).hom b
        exact mul_comm _ _
  rw [ConcreteCategory.isIso_iff_bijective] at hf hfg ⊢
  change Function.Bijective θg
  have hl : Function.Bijective (LinearMap.lTensor (R.obj Z) θ) :=
    (LinearEquiv.lTensor (R.obj Z) (LinearEquiv.ofBijective θ hf)).bijective
  have hc : (⇑θg) ∘ ⇑(LinearMap.lTensor (R.obj Z) θ) = (⇑θfg) ∘ ⇑c := (funext key).symm
  exact (Function.Bijective.of_comp_iff _ hl).mp (hc ▸ hfg.comp c.bijective)

/-- **Being cartesian over an arrow, from local factorizations through cartesian arrows.** Let
`φ : z ⟶ x` be an arrow of `C`. Suppose given a finite family `q i : z'ᵢ ⟶ z` for which the
product of the ring maps `R z ⟶ R z'ᵢ` is faithfully flat, and factorizations
`q i = c i ≫ a i`, `q i ≫ φ = c i ≫ b i` through arrows `a i : wᵢ ⟶ z` and `b i : wᵢ ⟶ x`. If `M`
is cartesian over every `q i`, `a i` and `b i`, then it is cartesian over `φ`.

By left cancellation `M` is cartesian over each `c i`, hence over `c i ≫ b i = q i ≫ φ`; and
being cartesian over `φ` descends along the faithfully flat family. -/
theorem isIso_restrictionBaseChange_of_factorizations {z x : C} (φ : z ⟶ x)
    {I : Type*} [Finite I] (z' w : I → C) (q : ∀ i, z' i ⟶ z) (c : ∀ i, z' i ⟶ w i)
    (a : ∀ i, w i ⟶ z) (b : ∀ i, w i ⟶ x)
    (hca : ∀ i, c i ≫ a i = q i) (hcb : ∀ i, c i ≫ b i = q i ≫ φ)
    (hff : (RingHom.pi (fun i => (R.map (q i).op).hom)).FaithfullyFlat)
    (hq : ∀ i, IsIso (restrictionBaseChange M (q i).op))
    (ha : ∀ i, IsIso (restrictionBaseChange M (a i).op))
    (hb : ∀ i, IsIso (restrictionBaseChange M (b i).op)) :
    IsIso (restrictionBaseChange M φ.op) := by
  have hc : ∀ i, IsIso (restrictionBaseChange M (c i).op) := fun i =>
    isIso_restrictionBaseChange_of_comp_left M (a i).op (c i).op (ha i)
      (by rw [← op_comp, hca i]; exact hq i)
  refine isIso_restrictionBaseChange_of_faithfullyFlat M φ.op (fun i => Opposite.op (z' i))
    (fun i => (q i).op) hff hq (fun i => ?_)
  rw [← op_comp, ← hcb i, op_comp]
  exact isIso_restrictionBaseChange_comp M _ _ (hb i) (hc i)

end Stacks.PresheafOfModules

end
