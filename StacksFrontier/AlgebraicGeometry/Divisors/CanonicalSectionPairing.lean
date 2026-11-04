module

public import StacksFrontier.AlgebraicGeometry.Divisors.IdealActionFactorization
public import StacksFrontier.AlgebraicGeometry.TensorPowerCoherence.Basic

/-!
# The canonical section and the evaluation pairing of a divisor twist

Let `X` be a scheme and `D ⊆ X` an effective Cartier divisor, with ideal sheaf
`ℐ_D = 𝒪_X(-D)`, invertible sheaf `𝒪_X(D) = ℐ_D^∨` and canonical section `1_D ∈ Γ(X, 𝒪_X(D))`.
There are two ways to turn a local section `μ ⊗ s` of `𝒪_X(D) ⊗_{𝒪_X} ℐ_D` into a section of
`𝒪_X(D)`: push `s` into `𝒪_X` along the ideal inclusion `ι : ℐ_D ⟶ 𝒪_X` and multiply `μ` by
the resulting scalar, or evaluate `μ` on `s` and multiply the canonical section `1_D` by the
resulting scalar. This file proves that the two agree,

`ι(s) · μ = μ(s) · 1_D`,

as an identity of morphisms `𝒪_X(D) ⊗_{𝒪_X} ℐ_D ⟶ 𝒪_X(D)` in `X.Modules`.

## Main results

* `Stacks.Divisors.tensorRightMap_canonicalSectionHom_comp_evaluation`: the evaluation pairing
  applied to `1_D` in its first slot is the ideal inclusion, `ev(r · 1_D ⊗ s) = r · ι(s)`.
* `Stacks.Divisors.tensorLeftMap_idealSheafInclusion_comp_tensorRightUnitor`: **`ι(s)·μ` and
  `μ(s)·1_D` are the same morphism** `𝒪_X(D) ⊗_{𝒪_X} ℐ_D ⟶ 𝒪_X(D)`.

The general monoidal input is isolated in `Stacks.Monoidal`:

* `Stacks.Monoidal.whiskerLeft_rightUnitor_eq_whiskerRight_leftUnitor`: in a braided monoidal
  category, a morphism `g : B ⟶ 𝟙` to the unit acts the same way in either slot of `B ⊗ B` as
  soon as `β_ B B = 𝟙`.
* `Stacks.Monoidal.whiskerLeft_rightUnitor_eq_comp` : the identity above, in an arbitrary
  symmetric monoidal category, for an object `I` whose self-braiding is trivial and which
  carries a trivializing pairing with `L`.

## Implementation notes

**Where invertibility of `ℐ_D` is used, and why it has to be.** The identity is *false* for a
general dual pair: with `V` of rank two and `μ`, `ι` two independent functionals, `ι(s)μ` and
`μ(s)ι` are different elements of `V^∨`. What makes it true here is that `ℐ_D` is invertible, so
`ℐ_D ⊗ ℐ_D` has trivial self-braiding
(`Stacks.SheafOfModules.Invertible.tensorProductBraiding_self`, which is the one step of
[Stacks, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU) that is not formal), and that is
exactly what `Stacks.Monoidal.whiskerLeft_rightUnitor_eq_whiskerRight_leftUnitor` consumes: the
difference between the two sides is the transposition of the two `ℐ_D` slots. Invertibility
enters twice more, in the inessential sense that it is needed to *state* the identity —
`Stacks.SheafOfModules.Scheme.evaluationIso` is an isomorphism — and to cancel the tensor factor
`ℐ_D`, which is what makes `· ⊗ ℐ_D` faithful
(`Stacks.SheafOfModules.Invertible.cancel_tensor_right`).

**The decomposition.** `tensorRightMap_canonicalSectionHom_comp_evaluation` is the definitional
half: both sides are computed on local pure tensors, where the evaluation pairing is
`Stacks.SheafOfModules.evalSection` and the canonical section is the restricted ideal inclusion,
so the identity is `ev(r · ι|_U ⊗ s) = r · ι(s)` and needs no geometry. The main result is then
pure monoidal algebra on top of it, and that is where the braiding is used.

**Which monoidal structure.** `Stacks.SheafOfModules.sheafTensorMonoidal`, the
structure whose tensor product is the tensor product sheaf of
[Stacks, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA) on the nose and whose constraints
are the four maps of Tag 01CU. It is activated as a local instance below, because
`AlgebraicGeometry.Scheme.Modules.tensorLeftMap`,
`AlgebraicGeometry.Scheme.Modules.tensorRightMap` and
`AlgebraicGeometry.Scheme.Modules.tensorRightUnitor` are then `◁`, `▷` and `ρ_` by `rfl`, which
is what lets the generic lemmas of `Stacks.Monoidal` apply to the statements as spelled. The
instance has `O` and `hO` as explicit arguments, so `attribute [local instance]` does not fire
on it; it is re-exported here at a scheme instead.

## References

* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
* [Stacks Project, Tag 0G5G](https://stacks.math.columbia.edu/tag/0G5G)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory BraidedCategory Opposite TopologicalSpace
open scoped TensorProduct

universe v u

namespace Stacks.Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **Two morphisms to the unit object can be applied in either order.** For `f : A ⟶ 𝟙` and
`g : B ⟶ 𝟙`, applying `f` and then `g` to `A ⊗ B` agrees with applying `g` and then `f`: both
composites are `f ⊗ g` followed by the common unitor of the unit. -/
theorem whiskerRight_leftUnitor_comp {A B : C} (f : A ⟶ 𝟙_ C) (g : B ⟶ 𝟙_ C) :
    f ▷ B ≫ (λ_ B).hom ≫ g = A ◁ g ≫ (ρ_ A).hom ≫ f := by
  rw [← leftUnitor_naturality, ← rightUnitor_naturality, ← whisker_exchange_assoc, unitors_equal]

/-- Contracting the `B` slot of `A ⊗ B` against `g : B ⟶ 𝟙` and contracting the second `B` slot
of `(A ⊗ B) ⊗ B` against `g` give the same morphism `(A ⊗ B) ⊗ B ⟶ A ⊗ B`, provided `g` does not
distinguish the two slots of `B ⊗ B`. -/
theorem whiskerRight_whiskerLeft_rightUnitor {B : C} (g : B ⟶ 𝟙_ C) (A : C)
    (h : B ◁ g ≫ (ρ_ B).hom = g ▷ B ≫ (λ_ B).hom) :
    (A ◁ g ≫ (ρ_ A).hom) ▷ B = (A ⊗ B) ◁ g ≫ (ρ_ (A ⊗ B)).hom := by
  have key := congrArg (fun k : B ⊗ B ⟶ B => (α_ A B B).hom ≫ A ◁ k) h
  simp only [whiskerLeft_comp] at key
  rw [← associator_naturality_right_assoc, ← associator_naturality_middle_assoc] at key
  have e₁ : (α_ A (𝟙_ C) B).hom ≫ A ◁ (λ_ B).hom = (ρ_ A).hom ▷ B := by monoidal
  have e₂ : (α_ A B (𝟙_ C)).hom ≫ A ◁ (ρ_ B).hom = (ρ_ (A ⊗ B)).hom := by monoidal
  rw [e₁, e₂] at key
  rw [comp_whiskerRight]
  exact key.symm

variable [BraidedCategory C]

/-- **An object with trivial self-braiding does not distinguish its two tensor slots.** If
`β_ B B = 𝟙` then a morphism `g : B ⟶ 𝟙` to the unit object contracts either slot of `B ⊗ B` to
the same morphism `B ⊗ B ⟶ B`. -/
theorem whiskerLeft_rightUnitor_eq_whiskerRight_leftUnitor {B : C} (g : B ⟶ 𝟙_ C)
    (hb : (β_ B B).hom = 𝟙 (B ⊗ B)) :
    B ◁ g ≫ (ρ_ B).hom = g ▷ B ≫ (λ_ B).hom :=
  calc B ◁ g ≫ (ρ_ B).hom = ((β_ B B).hom ≫ B ◁ g) ≫ (ρ_ B).hom := by
        rw [hb, Category.id_comp]
    _ = (g ▷ B ≫ (β_ (𝟙_ C) B).hom) ≫ (ρ_ B).hom := by
        rw [braiding_naturality_left (Y := 𝟙_ C) g B]
    _ = g ▷ B ≫ (λ_ B).hom := by rw [Category.assoc, braiding_rightUnitor]

/-- **Multiplication by a functional on a tensor inverse is evaluation followed by the dual
functional.** Let `I` be an object of a braided monoidal category with trivial self-braiding
`β_ I I = 𝟙` and let `ev : L ⊗ I ≅ 𝟙` be a trivializing pairing, so that `L` is a tensor inverse
of `I`. Given `iota : I ⟶ 𝟙` and `c : 𝟙 ⟶ L` paired by `ev` in the sense of `hc`, multiplying
by `iota` on `L ⊗ I` is evaluation followed by multiplication by `c`.

The hypothesis `hfaithful` says that `· ▷ I` is faithful on morphisms out of `L ⊗ I`; for an
invertible `I` it is supplied by cancelling the tensor factor. -/
theorem whiskerLeft_rightUnitor_eq_comp {I L : C} (ev : L ⊗ I ≅ 𝟙_ C) (iota : I ⟶ 𝟙_ C)
    (c : 𝟙_ C ⟶ L) (hb : (β_ I I).hom = 𝟙 (I ⊗ I))
    (hfaithful : ∀ {p q : L ⊗ I ⟶ L}, p ▷ I = q ▷ I → p = q)
    (hc : c ▷ I ≫ ev.hom = (λ_ I).hom ≫ iota) :
    L ◁ iota ≫ (ρ_ L).hom = ev.hom ≫ c := by
  refine hfaithful ((cancel_mono ev.hom).mp ?_)
  calc (L ◁ iota ≫ (ρ_ L).hom) ▷ I ≫ ev.hom
      = (L ⊗ I) ◁ iota ≫ (ρ_ (L ⊗ I)).hom ≫ ev.hom := by
        rw [whiskerRight_whiskerLeft_rightUnitor iota L
          (whiskerLeft_rightUnitor_eq_whiskerRight_leftUnitor iota hb), Category.assoc]
    _ = ev.hom ▷ I ≫ (λ_ I).hom ≫ iota := (whiskerRight_leftUnitor_comp ev.hom iota).symm
    _ = ev.hom ▷ I ≫ c ▷ I ≫ ev.hom := by rw [hc]
    _ = (ev.hom ≫ c) ▷ I ≫ ev.hom := by rw [comp_whiskerRight, Category.assoc]

end Stacks.Monoidal

namespace Stacks.Divisors

open Stacks.SheafOfModules (evalSection evaluation tensorPt)
open Stacks.SheafOfModules (sheafTensorMonoidal sheafTensorSymmetric)
open Stacks.SheafOfModules.Invertible (tensorProductLeftUnitor)

/-- The monoidal structure of Tag 05NA on the `𝒪_X`-modules of a scheme, as an instance. -/
noncomputable local instance schemeModulesMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules :=
  sheafTensorMonoidal X.sheaf.obj X.ringCatSheaf.property

/-- The symmetry of Tag 01CU on the `𝒪_X`-modules of a scheme, as an instance. -/
noncomputable local instance schemeModulesSymmetric (X : Scheme.{u}) :
    SymmetricCategory X.Modules :=
  sheafTensorSymmetric X.sheaf.obj X.ringCatSheaf.property

/-- The monoidal structure on presheaves of `𝒪_X`-modules, which the tensor product sheaf is
the sheafification of. -/
noncomputable local instance schemePresheafModulesMonoidal (X : Scheme.{u}) :
    MonoidalCategory (PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  Stacks.SheafOfModules.monoidalCategoryPresheafOfModules X.sheaf.obj X.ringCatSheaf.property

variable {X : Scheme.{u}}

/-- The ideal sheaf of an effective Cartier divisor is invertible in the sense of
`Stacks.SheafOfModules.IsInvertible`. This is `Stacks.Divisors.isTensorInvertible_negativeTwist`
registered as an instance, which is what makes
`Stacks.SheafOfModules.Scheme.evaluationIso` applicable to `ℐ_D` in a statement. -/
local instance stacksIsInvertible_negativeTwist' (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] :
    Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property (negativeTwist' D) :=
  isTensorInvertible_negativeTwist D

/-- **Two morphisms out of a tensor product sheaf agreeing on local pure tensors are equal.**
Every section of `A ⊗ B` is locally a finite sum of images of pure tensors under the
sheafification unit, and `Stacks.SheafOfModules.hom_ext_toSheafify` reduces an equality of
morphisms to those images; the reduction from an arbitrary element of the presheaf tensor
product to a pure tensor is `TensorProduct.ext'`. -/
private theorem hom_ext_tensorPt {A B E : X.Modules}
    (f g : Scheme.Modules.tensorObj A B ⟶ E)
    (h : ∀ (V : (Opens X)ᵒᵖ) (a : A.val.obj V) (b : B.val.obj V),
      (f.val.app V).hom (tensorPt X.sheaf.obj X.ringCatSheaf.property A B V a b) =
        (g.val.app V).hom (tensorPt X.sheaf.obj X.ringCatSheaf.property A B V a b)) :
    f = g := by
  have key : Stacks.SheafOfModules.TensorSheafification.toSheafify X.sheaf.obj
        X.ringCatSheaf.property (A.val ⊗ B.val) ≫
      (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf
            X.sheaf.obj X.ringCatSheaf.property) ⋙
          PresheafOfModules.restrictScalars
            (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.sheaf.obj
              X.ringCatSheaf.property).obj)).map f =
      Stacks.SheafOfModules.TensorSheafification.toSheafify X.sheaf.obj
        X.ringCatSheaf.property (A.val ⊗ B.val) ≫
      (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf
            X.sheaf.obj X.ringCatSheaf.property) ⋙
          PresheafOfModules.restrictScalars
            (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.sheaf.obj
              X.ringCatSheaf.property).obj)).map g :=
    PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (TensorProduct.ext' (h V))
  exact Stacks.SheafOfModules.hom_ext_toSheafify X.sheaf.obj X.ringCatSheaf.property f g
    fun V t => PresheafOfModules.hom_congr_apply key V t

/-- **The evaluation pairing of `𝒪_X(D)` with `ℐ_D` at the canonical section, on a local pure
tensor.** Multiplication by `1_D` sends `r` to `r · ι|_V`, the pairing evaluates that functional
on `s`, and both steps are `Stacks.SheafOfModules.evalSection` of the restricted ideal
inclusion; so the value is `r · ι(s)`, which is also what the left unit constraint followed by
the ideal inclusion gives. -/
private theorem evaluation_canonicalSectionHom_tmul (D : X.IdealSheafData) (W : Opens X)
    (r : (structureSheafRing X.toRingedSpace).obj.obj (op W))
    (s : (negativeTwist' D).val.obj (op W)) :
    ((evaluation X.sheaf.obj X.ringCatSheaf.property (negativeTwist' D)).val.app (op W)).hom
        (((Scheme.Modules.tensorRightMap (canonicalSectionHom D)
            (negativeTwist' D)).val.app (op W)).hom
          (tensorPt X.sheaf.obj X.ringCatSheaf.property (SheafOfModules.unit X.ringCatSheaf)
            (negativeTwist' D) (op W) r s)) =
      ((idealSheafInclusion D).val.app (op W)).hom
        (((tensorProductLeftUnitor X.sheaf.obj X.ringCatSheaf.property
            (negativeTwist' D)).hom.val.app (op W)).hom
          (tensorPt X.sheaf.obj X.ringCatSheaf.property (SheafOfModules.unit X.ringCatSheaf)
            (negativeTwist' D) (op W) r s)) := by
  have hwhisker : ((Scheme.Modules.tensorRightMap (canonicalSectionHom D)
        (negativeTwist' D)).val.app (op W)).hom
          (tensorPt X.sheaf.obj X.ringCatSheaf.property
            (SheafOfModules.unit X.ringCatSheaf) (negativeTwist' D) (op W) r s) =
      tensorPt X.sheaf.obj X.ringCatSheaf.property (invertibleSheaf' D)
        (negativeTwist' D) (op W) (r • canonicalSectionComponent D W) s :=
    Stacks.SheafOfModules.sheafify_map_toSheafify_app X.sheaf.obj X.ringCatSheaf.property
      ((canonicalSectionHom D).val ▷ (negativeTwist' D).val) (op W) (r ⊗ₜ s)
  have hunitor : ((tensorProductLeftUnitor X.sheaf.obj X.ringCatSheaf.property
        (negativeTwist' D)).hom.val.app (op W)).hom
          (tensorPt X.sheaf.obj X.ringCatSheaf.property
            (SheafOfModules.unit X.ringCatSheaf) (negativeTwist' D) (op W) r s) = r • s :=
    Stacks.SheafOfModules.tensorSheafLeftUnitor_hom_val_app_tmul X.sheaf.obj
      X.ringCatSheaf.property (negativeTwist' D) (op W) r s
  have heval : ((evaluation X.sheaf.obj X.ringCatSheaf.property
        (negativeTwist' D)).val.app (op W)).hom
        (tensorPt X.sheaf.obj X.ringCatSheaf.property (invertibleSheaf' D)
          (negativeTwist' D) (op W) (r • canonicalSectionComponent D W) s) =
      evalSection X.sheaf.obj (negativeTwist' D).val
        (SheafOfModules.unit X.ringCatSheaf).val (op W)
        (r • canonicalSectionComponent D W) s :=
    Stacks.SheafOfModules.evaluation_tensorPt X.sheaf.obj X.ringCatSheaf.property
      (negativeTwist' D) (op W) (r • canonicalSectionComponent D W) s
  rw [hwhisker, hunitor, heval, map_smul]
  exact Stacks.SheafOfModules.evalSection_smul_left X.sheaf.obj (negativeTwist' D).val
    (SheafOfModules.unit X.ringCatSheaf).val (op W) r (canonicalSectionComponent D W) s

/-- **The evaluation pairing of `𝒪_X(D)` with `ℐ_D`, read at the canonical section.** Pairing
`r · 1_D` against a local section `s` of `ℐ_D` gives `r · ι(s)`, where `ι : ℐ_D ⟶ 𝒪_X` is the
ideal inclusion. Equivalently, multiplication by `1_D` followed by the evaluation pairing is the
ideal inclusion.

Nothing here uses that `D` is an effective Cartier divisor: both sides are computed on local
pure tensors, where the pairing is `Stacks.SheafOfModules.evalSection` and the canonical section
is the restriction of the ideal inclusion. -/
theorem tensorRightMap_canonicalSectionHom_comp_evaluation (D : X.IdealSheafData) :
    Scheme.Modules.tensorRightMap (canonicalSectionHom D) (negativeTwist' D) ≫
        evaluation X.sheaf.obj X.ringCatSheaf.property (negativeTwist' D) =
      (tensorProductLeftUnitor X.sheaf.obj X.ringCatSheaf.property (negativeTwist' D)).hom ≫
        idealSheafInclusion D :=
  hom_ext_tensorPt _ _ fun V r s => evaluation_canonicalSectionHom_tmul D V.unop r s

/-- **`ι(s) · μ = μ(s) · 1_D`.** For an effective Cartier divisor `D` on a scheme `X`, the two
morphisms `𝒪_X(D) ⊗_{𝒪_X} ℐ_D ⟶ 𝒪_X(D)` — multiply the first factor by the image of the second
under the ideal inclusion `ι : ℐ_D ⟶ 𝒪_X`, or evaluate the first factor on the second and
multiply the canonical section `1_D` by the result — are equal.

This is where invertibility of `ℐ_D` is consumed: the two sides differ by the transposition of
the two `ℐ_D` slots in `(𝒪_X(D) ⊗ ℐ_D) ⊗ ℐ_D`, and that transposition is the identity because
the self-braiding of an invertible sheaf is trivial
(`Stacks.SheafOfModules.Invertible.tensorProductBraiding_self`). For a dual pair of rank two the
identity fails. -/
theorem tensorLeftMap_idealSheafInclusion_comp_tensorRightUnitor (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] :
    Scheme.Modules.tensorLeftMap (invertibleSheaf' D) (idealSheafInclusion D) ≫
        (Scheme.Modules.tensorRightUnitor (invertibleSheaf' D)).hom =
      (Stacks.SheafOfModules.Scheme.evaluationIso X (negativeTwist' D)).hom ≫
        canonicalSectionHom D := by
  have _ : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (negativeTwist' D) := isInvertible_negativeTwist D
  -- the evaluation pairing with the factors in the order the cancellation lemma wants
  have swapIso : Scheme.Modules.tensorObj (negativeTwist' D) (invertibleSheaf' D) ≅
      𝟙_ X.Modules :=
    BraidedCategory.braiding (C := X.Modules) (negativeTwist' D) (invertibleSheaf' D) ≪≫
      (Stacks.SheafOfModules.Scheme.evaluationIso X (negativeTwist' D) :
        Scheme.Modules.tensorObj (invertibleSheaf' D) (negativeTwist' D) ≅ 𝟙_ X.Modules)
  have hcancel : ∀ {p q : Scheme.Modules.tensorObj (invertibleSheaf' D) (negativeTwist' D) ⟶
        (invertibleSheaf' D : X.Modules)},
      Scheme.Modules.tensorRightMap p (negativeTwist' D) =
        Scheme.Modules.tensorRightMap q (negativeTwist' D) → p = q :=
    fun {_ _} h => Stacks.SheafOfModules.Invertible.cancel_tensor_right swapIso _ _ h
  have hbraiding : (BraidedCategory.braiding (C := X.Modules)
      (negativeTwist' D) (negativeTwist' D)).hom =
      𝟙 (Scheme.Modules.tensorObj (negativeTwist' D) (negativeTwist' D)) :=
    congrArg Iso.hom (Stacks.SheafOfModules.Invertible.tensorProductBraiding_self
      X.sheaf.obj X.ringCatSheaf.property (negativeTwist' D))
  let evIso : MonoidalCategory.tensorObj (C := X.Modules) (invertibleSheaf' D)
      (negativeTwist' D) ≅ 𝟙_ X.Modules :=
    Stacks.SheafOfModules.Scheme.evaluationIso X (negativeTwist' D)
  exact Stacks.Monoidal.whiskerLeft_rightUnitor_eq_comp (C := X.Modules)
    (I := negativeTwist' D) (L := invertibleSheaf' D) evIso
    (idealSheafInclusion D) (canonicalSectionHom D) hbraiding hcancel
    (tensorRightMap_canonicalSectionHom_comp_evaluation D)

end Stacks.Divisors

end
