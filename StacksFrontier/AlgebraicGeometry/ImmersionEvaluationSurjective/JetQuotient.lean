module

public import StacksFrontier.AlgebraicGeometry.ImmersionEvaluationSurjective.KernelDimension
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Basic

/-!
# The target of the evaluation is the jet quotient of the local ring

The evaluation at `x` of a linear system of sections of an invertible module `ℒ` lands in
`ℒ_x/𝔪_x²ℒ_x`. This file identifies that target with `𝒪_{X,x}/𝔪_x²`, the second-order jets of
the local ring: the stalk of an invertible module is free of rank one, so a trivialization at
`x` carries `𝔪_x²` onto `𝔪_x²ℒ_x`. The isomorphisms are `𝒪_{X,x}`-linear, hence linear over a
base field `k` acting by restriction of scalars along
`Stacks.ImmersionEvaluationSurjective.baseGerm`.

## Main results

* `Stacks.StalkJet.eq_zero_of_smul_germ_basis`: **the germ of the basis section of a
  trivialization is a free generator of the stalk** — it is annihilated by no nonzero element.
* `Stacks.StalkJet.stalkEquiv`: **the stalk of an invertible module is free of rank one**, as the
  `𝒪_{X,x}`-linear isomorphism `𝒪_{X,x} ≃ ℒ_x` given by a trivialization at `x`.
* `Stacks.StalkJet.jetEquiv`: **`𝒪_{X,x}/𝔪_x² ≃ ℒ_x/𝔪_x²ℒ_x`**, the identification of the
  target of the evaluation with the jet quotient of the local ring.
* `Stacks.StalkJet.jetEquivEvalQuotient`: the same reading the target as
  `Stacks.ImmersionEvaluationSurjective.evalQuotient`.
* `Stacks.StalkJet.finrank_evalQuotient_eq_finrank_jetQuotient`: the target of the evaluation
  and `𝒪_{X,x}/𝔪_x²` have the same dimension over the base field.

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace Opposite

universe u

namespace Stacks.StalkJet

open Stacks.ModuleStalk Stacks.NonvanishingOpen Stacks.SectionProduct
open Stacks.ImmersionEvaluationSurjective

variable {X : Scheme.{u}} {M : X.Modules} {V : X.Opens}
  (t : Stacks.SheafDescent.Trivialization X.presheaf M.val V) {x : X} (hx : x ∈ V)

/-- **The germ of the basis section of a trivialization is a free generator of the stalk**: it is
annihilated by no nonzero element of `𝒪_{X,x}`. -/
theorem eq_zero_of_smul_germ_basis (r : X.presheaf.stalk x)
    (h : r • (M.presheaf.germ V x hx).hom (basis t) = 0) : r = 0 := by
  obtain ⟨W, hWV, hxW, a, ha⟩ := X.presheaf.exists_le_germ_eq r hx
  have hres : (M.presheaf.germ W x hxW).hom
      (a • M.presheaf.map (homOfLE hWV).op (basis t)) = 0 := by
    rwa [germ_smul, ha, TopCat.Presheaf.germ_res_apply]
  obtain ⟨W', hxW', iU, iV, e⟩ := M.presheaf.germ_eq x hxW hxW
    (a • M.presheaf.map (homOfLE hWV).op (basis t)) 0 (by rw [hres, map_zero])
  have h1 : triv t (homOfLE hWV) (a • M.presheaf.map (homOfLE hWV).op (basis t)) = a := by
    rw [triv_smul, triv_res_basis, mul_one]
  have h2 := triv_res t (homOfLE hWV) iU (iU ≫ homOfLE hWV)
    (a • M.presheaf.map (homOfLE hWV).op (basis t))
  rw [e, map_zero, h1] at h2
  have h3 : X.presheaf.map iU.op a = 0 := by
    rw [← h2]
    exact (t.θ W' (iU ≫ homOfLE hWV)).map_zero
  rw [← ha, ← TopCat.Presheaf.germ_res_apply X.presheaf iU x hxW' a, h3, map_zero]

/-- **The stalk of an invertible module is free of rank one**: a trivialization through `x`
makes `r ↦ r · basis_x` an isomorphism `𝒪_{X,x} ≃ ℒ_x`. -/
def stalkEquiv : X.presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
    TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x :=
  LinearEquiv.ofBijective
    { toFun := fun r => r • (M.presheaf.germ V x hx).hom (basis t)
      map_add' := fun a b => add_smul a b _
      map_smul' := fun a b => mul_smul a b _ }
    ⟨fun a b hab => by
      have h : (a - b) • (M.presheaf.germ V x hx).hom (basis t) = 0 := by
        rwa [sub_smul, sub_eq_zero]
      exact sub_eq_zero.1 (eq_zero_of_smul_germ_basis t hx _ h),
     fun w => exists_smul_germ_basis t hx w |>.imp fun _ hr => hr.symm⟩

/-- The isomorphism `stalkEquiv` sends `r` to `r` times the germ of the basis section. -/
@[simp]
theorem stalkEquiv_apply (r : X.presheaf.stalk x) :
    stalkEquiv t hx r = r • (M.presheaf.germ V x hx).hom (basis t) :=
  rfl

/-- The free generator carries an ideal of the local ring onto the corresponding submodule of
the stalk. -/
theorem map_stalkEquiv_smul_top (I : Ideal (X.presheaf.stalk x)) :
    Submodule.map (stalkEquiv t hx).toLinearMap (I • (⊤ : Submodule (X.presheaf.stalk x)
        (X.presheaf.stalk x))) =
      I • (⊤ : Submodule (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x)) := by
  rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]

/-- The jet quotient `𝒪_{X,x}/𝔪_x²` of the local ring at `x`, written as the quotient by the
submodule `𝔪_x²·𝒪_{X,x}` so that it matches the shape of `ℒ_x/𝔪_x²ℒ_x`. -/
abbrev jetQuotient (X : Scheme.{u}) (x : X) : Type u :=
  X.presheaf.stalk x ⧸ (maximalIdeal (X.presheaf.stalk x) ^ 2 •
    (⊤ : Submodule (X.presheaf.stalk x) (X.presheaf.stalk x)))

/-- **The jet quotient of the local ring is the target of the evaluation**: a trivialization at
`x` identifies `𝒪_{X,x}/𝔪_x²` with `ℒ_x/𝔪_x²ℒ_x`. -/
def jetEquiv : jetQuotient X x ≃ₗ[X.presheaf.stalk x]
    (TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x ⧸ maximalSqSmul M x) :=
  Submodule.Quotient.equiv _ _ (stalkEquiv t hx)
    (map_stalkEquiv_smul_top t hx (maximalIdeal (X.presheaf.stalk x) ^ 2))

/-- **The jet quotient of the local ring is the target of the evaluation**, read for
`Stacks.ImmersionEvaluationSurjective.evalQuotient`. -/
def jetEquivEvalQuotient {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k)) :
    jetQuotient X x ≃ₗ[X.presheaf.stalk x] evalQuotient f M x :=
  jetEquiv t hx

/-- **The target of the evaluation at any point of an invertible module is isomorphic to the jet
quotient of the local ring there.** -/
theorem nonempty_jetEquivEvalQuotient {k : Type u} [Field k] (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] (f : X ⟶ Spec (CommRingCat.of k)) (y : X) :
    Nonempty (jetQuotient X y ≃ₗ[X.presheaf.stalk y] evalQuotient f M y) := by
  obtain ⟨V, hyV, ⟨t⟩⟩ := Stacks.SectionProduct.exists_trivialization_at M y
  exact ⟨jetEquivEvalQuotient t hyV f⟩

/-- **The dimension of the target of the evaluation is the dimension of `𝒪_{X,x}/𝔪_x²`** over
the base field, which acts on `𝒪_{X,x}/𝔪_x²` through
`Stacks.ImmersionEvaluationSurjective.baseGerm`. -/
theorem finrank_evalQuotient_eq_finrank_jetQuotient {k : Type u} [Field k] (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] (f : X ⟶ Spec (CommRingCat.of k)) (y : X) :
    letI : Module k (jetQuotient X y) := Module.compHom _ (baseGerm f y)
    Module.finrank k (evalQuotient f M y) = Module.finrank k (jetQuotient X y) := by
  let : Module k (jetQuotient X y) := Module.compHom _ (baseGerm f y)
  let : Module k (X.presheaf.stalk y) := (baseGerm f y).toModule
  have : IsScalarTower k (X.presheaf.stalk y) (jetQuotient X y) :=
    ⟨fun c r m => mul_smul (baseGerm f y c) r m⟩
  have : IsScalarTower k (X.presheaf.stalk y) (evalQuotient f M y) :=
    ⟨fun c r m => mul_smul (baseGerm f y c) r m⟩
  obtain ⟨e⟩ := nonempty_jetEquivEvalQuotient M f y
  exact ((e.restrictScalars k).finrank_eq).symm

end Stacks.StalkJet

end
