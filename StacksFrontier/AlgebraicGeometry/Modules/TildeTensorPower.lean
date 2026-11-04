module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraBundleStalk
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.AffineTensor

/-!
# Tensor powers of associated sheaves on an affine scheme

For a module `M` over a commutative ring `R` and `n : ℕ`, the sheaf associated to the `n`-fold
tensor power `M ⊗ ⋯ ⊗ M` is canonically the `n`-fold tensor power, in the sense of Stacks
Section 17.21, of the associated sheaf of `M` on `Spec R`.

## Main definitions

* `AlgebraicGeometry.specTildeAlgebras`: the tensor algebra of the sheaf associated to `M` on
  `Spec R`, with its exterior and symmetric quotients — the bundle
  `SheafOfModules.ringedSpaceAlgebras` at `Spec R`.
* `AlgebraicGeometry.specTildeTensorPower`: the `n`-fold tensor power of that sheaf.
* `AlgebraicGeometry.tildeTensorPowerSection`: the tensor product of the global sections
  associated to a finite family of elements of `M`, which is the pure tensor the comparison is
  pinned on.
* `AlgebraicGeometry.tildeTensorPowerStepIso`: the recursion step of the comparison.
* `AlgebraicGeometry.tildeTensorPowerIso`: the comparison itself.

## Main results

* `AlgebraicGeometry.tildeTensorPowerIso_hom_tprod`: the comparison carries the global section
  associated to a pure tensor to the tensor product of the associated global sections. Together
  with `tildeTensorPowerSection` this pins the comparison down, including the empty tensor in
  degree zero, where the value is the unit of the structure sheaf.
* `AlgebraicGeometry.tildeTensorPowerIso_natural`: the comparison is natural in `M`. The map on
  the right is the degree-`n` component of a unital homomorphism of graded algebra sheaves
  extending `tilde.map f` on degree-one generators; the universal property of the tensor algebra
  makes such a homomorphism unique, so the statement quantified over it is a statement about the
  canonical one.

## Implementation notes

Tensor powers of modules are Mathlib's `TensorPower`; tensor powers of sheaves of modules are
`SheafOfModules.tensorPower`, whose degree-zero piece is the structure sheaf, whose degree-one
piece is the sheaf itself and whose higher pieces are built with
`Stacks.SheafOfModules.Tensor.sheafTensor`. The comparison is therefore a two-step recursion, with
`AlgebraicGeometry.tildeTensorIso` — the tensor-product part of this tag, on the Zariski site of
`Spec R` — supplying the step.

Two tensor products of sheaves of modules meet in that step: `AlgebraicGeometry.specTensorSheaf`,
the sheafification of the sectionwise tensor product that `tildeTensorIso` lands in, and
`Stacks.SheafOfModules.Tensor.sheafTensor`, which the tensor powers are built from. They are the
same sheafification of the same presheaf of modules, but not the same spelling of it, and
rewriting across the identification is what makes this elaboration expensive. The identification
is therefore absorbed once, into the result type of `tildeTensorPowerStepIso` and into the
statements of the private lemmas feeding it, and every step below is composed with `Eq.trans`
and `congrArg` rather than rewritten. That is the only reason the proofs are written in term
style; it is also why no elaboration option is needed.

`tildeTensorPowerIso` recurses through the named `tildeTensorPowerStepIso` rather than inlining
its body, so that the three unfolding equations hold by `rfl` at a cost the elaborator can pay —
unfolding an inlined step forces the comparison of the two tensor-product spellings at every
degree at once.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

-- `(Spec R).ringCatSheaf` is a `TopCat.Sheaf`, a plain `def` for `CategoryTheory.Sheaf`;
-- projecting a sheaf of modules over it is type-correct only once that abbreviation unfolds,
-- and until it does the rewrites below do not fire. Same precedent as
-- `StacksFrontier/AlgebraicGeometry/Schemes/ZariskiAndSeparation/AffineTensor.lean`.
attribute [local implicit_reducible] TopCat.Sheaf AlgebraicGeometry.Scheme.Modules

universe u v w

/-- The tensor algebra of the sheaf associated to `M` on `Spec R`, with its exterior and
symmetric quotients. -/
noncomputable def specTildeAlgebras (R : CommRingCat.{u}) (M : ModuleCat.{u} R) :
    SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥(Spec R)) (tilde M) :=
  SheafOfModules.ringedSpaceAlgebras (Spec R).toRingedSpace (tilde M)

/-- The `n`-fold tensor power of the sheaf associated to `M` on `Spec R`. -/
abbrev specTildeTensorPower (R : CommRingCat.{u}) (M : ModuleCat.{u} R) (n : ℕ) :
    (Spec R).Modules :=
  SheafOfModules.tensorPower (Opens.grothendieckTopology ↥(Spec R)) (tilde M) n

/-- The whole affine scheme, as an object of the site of open subsets of `Spec R`. -/
abbrev specGlobalOpen (R : CommRingCat.{u}) : (Opens ↥(Spec R))ᵒᵖ := op ⊤

/-- The tensor product of the global sections corresponding to a finite family of elements of
an affine module. -/
noncomputable def tildeTensorPowerSection (R : CommRingCat.{u}) (M : ModuleCat.{u} R) :
    (n : ℕ) → (Fin n → M) → (specTildeTensorPower R M n).val.obj (specGlobalOpen R)
  | 0, _ =>
      (((specTildeAlgebras R M).tensorPieceIso 0).hom.val.app (specGlobalOpen R))
        ((specTildeAlgebras R M).tensor.one.eval (specGlobalOpen R))
  | 1, a => (tilde.toOpen M ⊤).hom (a 0)
  | n + 2, a =>
      ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf ((Spec R).toRingedSpace.sheaf))
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ((Spec R).toRingedSpace.sheaf)).obj)).unit.app
        (PresheafOfModules.tensorObj ((tilde M)).val ((specTildeTensorPower R M (n + 1))).val)).app
          (specGlobalOpen R)
        ((tilde.toOpen M ⊤).hom (a 0) ⊗ₜ[
            (Spec R).toRingedSpace.sheaf.obj.obj (specGlobalOpen R)]
          tildeTensorPowerSection R M (n + 1) fun i => a i.succ)

/-- The zeroth tensor power of a module is the ring. -/
noncomputable abbrev tensorPowerEquivZero (R : CommRingCat.{u}) (M : ModuleCat.{u} R) :
    TensorPower R 0 M ≃ₗ[R] R :=
  PiTensorProduct.isEmptyEquiv (Fin 0) (R := R) (s := fun _ => M)

/-- The first tensor power of a module is the module. -/
noncomputable abbrev tensorPowerEquivOne (R : CommRingCat.{u}) (M : ModuleCat.{u} R) :
    TensorPower R 1 M ≃ₗ[R] M :=
  PiTensorProduct.subsingletonEquiv (R := R) (s := fun _ => M) (0 : Fin 1)

/-- A tensor power of degree at least two splits off its first factor. -/
noncomputable def tensorPowerStepEquiv (R : CommRingCat.{u}) (M : ModuleCat.{u} R) (n : ℕ) :
    TensorPower R (n + 2) M ≃ₗ[(R : Type u)]
      TensorProduct (R : Type u) (M : Type u) (TensorPower R (n + 1) M) :=
  ((TensorPower.mulEquiv (R := (R : Type u)) (M := (M : Type u)) (n := 1) (m := n + 1)).trans
      (TensorPower.cast (R : Type u) (M : Type u)
        (show 1 + (n + 1) = n + 2 by omega))).symm.trans
    (TensorProduct.congr (tensorPowerEquivOne R M)
      (LinearEquiv.refl (R : Type u) (TensorPower R (n + 1) M)))

/-- The recursion step of the affine tensor-power comparison: the degree-one factor splits off,
tag 01I8's tensor-product comparison identifies the associated sheaf of the split tensor
product, and the comparison in degree `k + 1` is tensored in.

The two tensor products of sheaves of modules involved — `AlgebraicGeometry.specTensorSheaf`,
the sheafification of the sectionwise tensor product used by tag 01I8, and
`Stacks.SheafOfModules.Tensor.sheafTensor`, the one the tensor powers of Section 17.21 are built
from — are the same sheafification of the same presheaf, and the identification is absorbed
into this definition's result type so that nothing below has to rewrite across it. -/
noncomputable def tildeTensorPowerStepIso (R : CommRingCat.{u}) (M : ModuleCat.{u} R) (k : ℕ)
    (e : tilde (ModuleCat.of R (TensorPower R (k + 1) M)) ≅
      specTildeTensorPower R M (k + 1)) :
    tilde (ModuleCat.of R (TensorPower R (k + 2) M)) ≅ specTildeTensorPower R M (k + 2) := by
  change tilde (ModuleCat.of R (TensorPower R (k + 2) M)) ≅
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((Spec R).toRingedSpace).presheaf, ((Spec R).toRingedSpace).IsSheaf⟩).obj
      (tilde M)).obj (specTildeTensorPower R M (k + 1))
  let split : tilde (ModuleCat.of R (M ⊗[R] TensorPower R (k + 1) M)) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((Spec R).toRingedSpace).presheaf, ((Spec R).toRingedSpace).IsSheaf⟩).obj
        (tilde M)).obj (tilde (ModuleCat.of R (TensorPower R (k + 1) M))) :=
    tildeTensorIso R M (ModuleCat.of R (TensorPower R (k + 1) M))
  exact (tilde.functor R).mapIso (tensorPowerStepEquiv R M k).toModuleIso ≪≫ split ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((Spec R).toRingedSpace).presheaf, ((Spec R).toRingedSpace).IsSheaf⟩).obj
      (tilde M)).mapIso e

/-- **Stacks Project, Tag 01I8 (tensor-power part).** The associated sheaf of a tensor power is
canonically the tensor power of the associated sheaf. -/
@[stacks 01I8 "tensor_power"]
noncomputable def tildeTensorPowerIso (R : CommRingCat.{u}) (M : ModuleCat.{u} R) :
    (n : ℕ) → (tilde (ModuleCat.of R (TensorPower R n M)) ≅ specTildeTensorPower R M n)
  | 0 => Functor.mapIso (tilde.functor R) (tensorPowerEquivZero R M).toModuleIso
  | 1 => Functor.mapIso (tilde.functor R) (tensorPowerEquivOne R M).toModuleIso
  | k + 2 => tildeTensorPowerStepIso R M k (tildeTensorPowerIso R M (k + 1))

private lemma tildeTensorPowerIso_zero (R : CommRingCat.{u}) (M : ModuleCat.{u} R) :
    tildeTensorPowerIso R M 0 =
      Functor.mapIso (tilde.functor R) (tensorPowerEquivZero R M).toModuleIso := rfl

private lemma tildeTensorPowerIso_one (R : CommRingCat.{u}) (M : ModuleCat.{u} R) :
    tildeTensorPowerIso R M 1 =
      Functor.mapIso (tilde.functor R) (tensorPowerEquivOne R M).toModuleIso := rfl

private lemma tildeTensorPowerIso_add_two (R : CommRingCat.{u}) (M : ModuleCat.{u} R) (k : ℕ) :
    tildeTensorPowerIso R M (k + 2) =
      tildeTensorPowerStepIso R M k (tildeTensorPowerIso R M (k + 1)) := rfl

private lemma tensorPowerStepEquiv_tprod (R : CommRingCat.{u}) (M : ModuleCat.{u} R) (n : ℕ)
    (a : Fin (n + 2) → M) :
    tensorPowerStepEquiv R M n (PiTensorProduct.tprod R a) =
      a 0 ⊗ₜ[R] (PiTensorProduct.tprod R fun i : Fin (n + 1) => a i.succ) := by
  simp [tensorPowerStepEquiv, TensorPower.mulEquiv, TensorPower.cast,
    tensorPowerEquivOne, PiTensorProduct.tmulEquiv]
  congr 1

private lemma tildeMap_toOpen_top_apply {R : CommRingCat.{u}} {X Y : ModuleCat.{u} R}
    (f : X ⟶ Y) (x : X) :
    (tilde.map f).val.app (op ⊤) ((tilde.toOpen X ⊤).hom x) =
      (tilde.toOpen Y ⊤).hom (f.hom x) :=
  congrArg (fun g => g.hom x) (tilde.toOpen_map_app f ⊤)

/-- The affine tensor comparison of tag 01I8, with the sheafification unit spelled as the
unit of the tensor product of sheaves of modules. -/
private lemma tildeTensorIso_app_tmul (R : CommRingCat.{u}) (M N : ModuleCat.{u} R) (m : M)
    (n : N) :
    (tildeTensorIso R M N).hom.val.app (specGlobalOpen R)
        ((tilde.toOpen (M ⊗ N) ⊤).hom (TensorProduct.tmul R m n)) =
      ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf ((Spec R).toRingedSpace.sheaf))
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ((Spec R).toRingedSpace.sheaf)).obj)).unit.app
        (PresheafOfModules.tensorObj ((tilde M)).val ((tilde N)).val)).app (specGlobalOpen R)
        ((tilde.toOpen M ⊤).hom m ⊗ₜ[
            (Spec R).toRingedSpace.sheaf.obj.obj (specGlobalOpen R)]
          (tilde.toOpen N ⊤).hom n) :=
  tildeTensorIso_hom_tmul R M N m n

/-- Naturality of the sheafification unit of the tensor product of sheaves of modules. -/
private lemma tensorSheafificationUnit_natural {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {Osharp : Sheaf J CommRingCat.{w}}
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
    {F G F' G' : SheafOfModules.{w} (Sheaf.toRingCat J Osharp)}
    (φ : ((F, G) : SheafOfModules.{w} (Sheaf.toRingCat J Osharp) ×
      SheafOfModules.{w} (Sheaf.toRingCat J Osharp)) ⟶ (F', G')) (U : Cᵒᵖ)
    (z : (PresheafOfModules.tensorObj F.val G.val).obj U) :
    ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp)).map φ).val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
          (PresheafOfModules.tensorObj F.val G.val)).app U z) =
      ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
        (PresheafOfModules.tensorObj F'.val G'.val)).app U
        ((PresheafOfModules.tensorHom φ.1.val φ.2.val).app U z) :=
  (congrArg (fun tensorMap => tensorMap.val.app U
      (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
        (PresheafOfModules.tensorObj F.val G.val)).app U z))
    (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map Osharp φ.1 φ.2)).trans
      (PresheafOfModules.unit_naturality_apply
        (R := Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
        (α := 𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)
        (PresheafOfModules.tensorHom φ.1.val φ.2.val) U z)

private lemma sheafIso_inv_app_hom_app {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {O : Sheaf J RingCat.{w}} {F G : SheafOfModules.{w} O}
    (e : F ≅ G) (U : Cᵒᵖ) (x : F.val.obj U) :
    (e.inv.val.app U) ((e.hom.val.app U) x) = x :=
  congrArg (fun k : F.val.obj U ⟶ F.val.obj U => k x)
    (congrArg (fun k : F ⟶ F => k.val.app U) e.hom_inv_id)

/-- If an isomorphism of sheaves of modules carries `x` to `y`, then `x` is the inverse's value
at `y`. -/
private lemma sheafIso_eq_inv_app_of_hom_app_eq {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {O : Sheaf J RingCat.{w}} {F G : SheafOfModules.{w} O}
    (e : F ≅ G) (U : Cᵒᵖ) {x : F.val.obj U} {y : G.val.obj U} (h : (e.hom.val.app U) x = y) :
    x = (e.inv.val.app U) y :=
  (sheafIso_inv_app_hom_app e U x).symm.trans (congrArg (e.inv.val.app U) h)

private lemma map_cast {ι : Sort*} {A B : ι → Sort*} (f : ∀ i, A i → B i) {i j : ι} (h : i = j)
    (x : A i) : f j (Eq.mp (congrArg A h) x) = Eq.mp (congrArg B h) (f i x) := by
  cases h
  rfl

/-- The value of `tilde.toOpen` at `1` is the unit section of the structure sheaf. -/
private lemma tilde_toOpen_top_one (R : CommRingCat.{u}) :
    (tilde.toOpen (ModuleCat.of R R) ⊤).hom (1 : R) =
      (1 : (Spec R).toRingedSpace.sheaf.obj.obj (specGlobalOpen R)) :=
  StructureSheaf.const_one ⊤

/-- The associated sheaf of a linear equivalence, on the image of a global section. -/
private lemma tilde_mapIso_toOpen_top_apply {R : CommRingCat.{u}} {A B : Type u}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] (e : A ≃ₗ[R] B) (x : A) :
    (Functor.mapIso (tilde.functor R) e.toModuleIso).hom.val.app (specGlobalOpen R)
        ((tilde.toOpen (ModuleCat.of R A) ⊤).hom x) =
      (tilde.toOpen (ModuleCat.of R B) ⊤).hom (e x) :=
  tildeMap_toOpen_top_apply e.toModuleIso.hom x

/-- The tensor comparison of tag 01I8, followed by tensoring with a comparison in the second
argument, on a pure tensor. -/
private lemma tildeTensorIso_tensorSheaf_step (R : CommRingCat.{u}) (M P : ModuleCat.{u} R)
    (Q : (Spec R).Modules) (e : tilde P ≅ Q) (m : M) (p : P) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((Spec R).toRingedSpace.sheaf)).obj
      (tilde M)).map e.hom).val.app (specGlobalOpen R)
        ((tildeTensorIso R M P).hom.val.app (specGlobalOpen R)
          ((tilde.toOpen (M ⊗ P) ⊤).hom (TensorProduct.tmul R m p))) =
      ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf ((Spec R).toRingedSpace.sheaf))
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ((Spec R).toRingedSpace.sheaf)).obj)).unit.app
        (PresheafOfModules.tensorObj ((tilde M)).val Q.val)).app (specGlobalOpen R)
        ((tilde.toOpen M ⊤).hom m ⊗ₜ[
            (Spec R).toRingedSpace.sheaf.obj.obj (specGlobalOpen R)]
          e.hom.val.app (specGlobalOpen R) ((tilde.toOpen P ⊤).hom p)) := by
  rw [tildeTensorIso_app_tmul]
  refine (PresheafOfModules.unit_naturality_apply
    (R := Stacks.SheafOfModules.Tensor.ringSheaf (Spec R).toRingedSpace.sheaf)
    (α := 𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (Spec R).toRingedSpace.sheaf).obj)
    (PresheafOfModules.tensorHom (𝟙 (tilde M).val) e.hom.val)
    (specGlobalOpen R) _).trans ?_
  exact congrArg _ (PresheafOfModules.tensorHom_tmul _ _ _ _ _)

/-- The recursion step on pure tensors. -/
private lemma tildeTensorPowerStepIso_hom_tprod (R : CommRingCat.{u}) (M : ModuleCat.{u} R)
    (k : ℕ) (e : tilde (ModuleCat.of R (TensorPower R (k + 1) M)) ≅
      specTildeTensorPower R M (k + 1)) (a : Fin (k + 2) → M) :
    (tildeTensorPowerStepIso R M k e).hom.val.app (specGlobalOpen R)
        ((tilde.toOpen (ModuleCat.of R (TensorPower R (k + 2) M)) ⊤).hom
          (PiTensorProduct.tprod R a)) =
      ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf ((Spec R).toRingedSpace.sheaf))
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ((Spec R).toRingedSpace.sheaf)).obj)).unit.app
        (PresheafOfModules.tensorObj ((tilde M)).val ((specTildeTensorPower R M (k + 1))).val)).app
          (specGlobalOpen R)
        ((tilde.toOpen M ⊤).hom (a 0) ⊗ₜ[
            (Spec R).toRingedSpace.sheaf.obj.obj (specGlobalOpen R)]
          e.hom.val.app (specGlobalOpen R)
            ((tilde.toOpen (ModuleCat.of R (TensorPower R (k + 1) M)) ⊤).hom
              (PiTensorProduct.tprod R fun i : Fin (k + 1) => a i.succ))) := by
  have hstart : (tildeTensorPowerStepIso R M k e).hom.val.app (specGlobalOpen R)
      ((tilde.toOpen (ModuleCat.of R (TensorPower R (k + 2) M)) ⊤).hom
        (PiTensorProduct.tprod R a)) =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((Spec R).toRingedSpace.sheaf)).obj (tilde M)).map e.hom).val.app (specGlobalOpen R)
        ((tildeTensorIso R M (ModuleCat.of R (TensorPower R (k + 1) M))).hom.val.app
          (specGlobalOpen R)
          ((tilde.map (tensorPowerStepEquiv R M k).toModuleIso.hom).val.app
            (specGlobalOpen R)
            ((tilde.toOpen (ModuleCat.of R (TensorPower R (k + 2) M)) ⊤).hom
              (PiTensorProduct.tprod R a)))) := rfl
  refine hstart.trans ?_
  rw [tildeMap_toOpen_top_apply,
    show (tensorPowerStepEquiv R M k).toModuleIso.hom.hom (PiTensorProduct.tprod R a) =
        TensorProduct.tmul R (a 0)
          (PiTensorProduct.tprod R fun i : Fin (k + 1) => a i.succ) from
      tensorPowerStepEquiv_tprod R M k a]
  exact tildeTensorIso_tensorSheaf_step R M (ModuleCat.of R (TensorPower R (k + 1) M))
    (specTildeTensorPower R M (k + 1)) e (a 0) _

/-- **Stacks Project, Tag 01I8 (tensor-power part).** The canonical affine tensor-power
comparison carries a pure tensor to the tensor product of its associated global sections. -/
@[stacks 01I8 "tensor_power"]
theorem tildeTensorPowerIso_hom_tprod (R : CommRingCat.{u}) (M : ModuleCat.{u} R) (n : ℕ)
    (a : Fin n → M) :
    (tildeTensorPowerIso R M n).hom.val.app (specGlobalOpen R)
        ((tilde.toOpen (ModuleCat.of R (TensorPower R n M)) ⊤).hom
          (PiTensorProduct.tprod R a)) =
      tildeTensorPowerSection R M n a := by
  induction n using Nat.twoStepInduction with
  | zero =>
      rw [tildeTensorPowerIso_zero]
      refine (tilde_mapIso_toOpen_top_apply (tensorPowerEquivZero R M) _).trans ?_
      have htarget : tildeTensorPowerSection R M 0 a =
          (((specTildeAlgebras R M).tensorPieceIso 0).hom.val.app (specGlobalOpen R))
            ((specTildeAlgebras R M).tensor.one.eval (specGlobalOpen R)) := rfl
      rw [htarget, (specTildeAlgebras R M).tensorPieceIso_zero (specGlobalOpen R)]
      exact (congrArg _ (PiTensorProduct.isEmptyEquiv_apply_tprod (Fin 0) a)).trans
        (tilde_toOpen_top_one R)
  | one =>
      rw [tildeTensorPowerIso_one]
      refine (tilde_mapIso_toOpen_top_apply (tensorPowerEquivOne R M) _).trans ?_
      exact congrArg (fun z => (tilde.toOpen M ⊤).hom z)
        (PiTensorProduct.subsingletonEquiv_apply_tprod (0 : Fin 1) a)
  | more n _ ihSucc =>
      rw [tildeTensorPowerIso_add_two, tildeTensorPowerStepIso_hom_tprod,
        ihSucc fun i => a i.succ]
      rfl

section Naturality

variable (R : CommRingCat.{u}) {M N : ModuleCat.{u} R} (f : M ⟶ N)
  (g : SheafOfModules.GradedAlgebra.UnitalHom
    (specTildeAlgebras R M).tensor (specTildeAlgebras R N).tensor)

/-- The degree-one generators are carried to each other, which is the hypothesis of
`tildeTensorPowerSection_natural` read on a global section. -/
private lemma unitalHom_tensorGenerator_toOpen
    (hg : (specTildeAlgebras R M).tensorGenerator ≫ g.app 1 =
      tilde.map f ≫ (specTildeAlgebras R N).tensorGenerator) (m : M) :
    (g.app 1).val.app (specGlobalOpen R)
        ((specTildeAlgebras R M).tensorGenerator.val.app (specGlobalOpen R)
          ((tilde.toOpen M ⊤).hom m)) =
      (specTildeAlgebras R N).tensorGenerator.val.app (specGlobalOpen R)
        ((tilde.toOpen N ⊤).hom (f.hom m)) := by
  refine (congrArg (fun k : tilde M ⟶ (specTildeAlgebras R N).tensor.piece 1 =>
    k.val.app (specGlobalOpen R) ((tilde.toOpen M ⊤).hom m)) hg).trans ?_
  exact congrArg ((specTildeAlgebras R N).tensorGenerator.val.app (specGlobalOpen R))
    (tildeMap_toOpen_top_apply f m)

/-- The degree-one identification of the tensor algebra undoes the degree-one generator. -/
private lemma tensorPieceIso_hom_generator_apply (M : ModuleCat.{u} R)
    (x : (tilde M).val.obj (specGlobalOpen R)) :
    ((specTildeAlgebras R M).tensorPieceIso 1).hom.val.app (specGlobalOpen R)
        ((specTildeAlgebras R M).tensorGenerator.val.app (specGlobalOpen R) x) = x :=
  congrArg (fun k : tilde M ⟶ tilde M => k.val.app (specGlobalOpen R) x)
    (specTildeAlgebras R M).tensorPieceIso_one

/-- The degree-zero case of `tildeTensorPowerSection_natural`. -/
private lemma tildeTensorPowerSection_natural_zero (a : Fin 0 → M) :
    ((specTildeAlgebras R N).tensorPieceIso 0).hom.val.app (specGlobalOpen R)
        ((g.app (0 : ℕ)).val.app (specGlobalOpen R)
          (((specTildeAlgebras R M).tensorPieceIso 0).inv.val.app (specGlobalOpen R)
            (tildeTensorPowerSection R M 0 a))) =
      tildeTensorPowerSection R N 0 fun i => f.hom (a i) :=
  (congrArg (fun y => ((specTildeAlgebras R N).tensorPieceIso 0).hom.val.app
      (specGlobalOpen R) ((g.app 0).val.app (specGlobalOpen R) y))
    (sheafIso_inv_app_hom_app ((specTildeAlgebras R M).tensorPieceIso 0) (specGlobalOpen R)
      ((specTildeAlgebras R M).tensor.one.eval (specGlobalOpen R)))).trans
    (congrArg (fun y => ((specTildeAlgebras R N).tensorPieceIso 0).hom.val.app
      (specGlobalOpen R) y) (g.map_one (specGlobalOpen R)))

/-- The degree-one case of `tildeTensorPowerSection_natural`. -/
private lemma tildeTensorPowerSection_natural_one
    (hg : (specTildeAlgebras R M).tensorGenerator ≫ g.app 1 =
      tilde.map f ≫ (specTildeAlgebras R N).tensorGenerator) (a : Fin 1 → M) :
    ((specTildeAlgebras R N).tensorPieceIso 1).hom.val.app (specGlobalOpen R)
        ((g.app (1 : ℕ)).val.app (specGlobalOpen R)
          (((specTildeAlgebras R M).tensorPieceIso 1).inv.val.app (specGlobalOpen R)
            (tildeTensorPowerSection R M 1 a))) =
      tildeTensorPowerSection R N 1 fun i => f.hom (a i) := by
  have hgenM : ((specTildeAlgebras R M).tensorPieceIso 1).inv.val.app (specGlobalOpen R)
        ((tilde.toOpen M ⊤).hom (a 0)) =
      (specTildeAlgebras R M).tensorGenerator.val.app (specGlobalOpen R)
        ((tilde.toOpen M ⊤).hom (a 0)) :=
    (sheafIso_eq_inv_app_of_hom_app_eq ((specTildeAlgebras R M).tensorPieceIso 1)
      (specGlobalOpen R) (tensorPieceIso_hom_generator_apply R M _)).symm
  refine ((congrArg (fun y => ((specTildeAlgebras R N).tensorPieceIso 1).hom.val.app
      (specGlobalOpen R) ((g.app 1).val.app (specGlobalOpen R) y)) hgenM).trans ?_)
  refine ((congrArg (fun y => ((specTildeAlgebras R N).tensorPieceIso 1).hom.val.app
      (specGlobalOpen R) y)
    (unitalHom_tensorGenerator_toOpen R f g hg (a 0))).trans ?_)
  exact tensorPieceIso_hom_generator_apply R N _

/-- The recursion step of `tildeTensorPowerSection_natural`. -/
private lemma tildeTensorPowerSection_natural_add_two
    (hg : (specTildeAlgebras R M).tensorGenerator ≫ g.app 1 =
      tilde.map f ≫ (specTildeAlgebras R N).tensorGenerator) (n : ℕ) (a : Fin (n + 2) → M)
    (ih : ((specTildeAlgebras R N).tensorPieceIso (n + 1)).hom.val.app (specGlobalOpen R)
        ((g.app ((n + 1 : ℕ) : ℤ)).val.app (specGlobalOpen R)
          (((specTildeAlgebras R M).tensorPieceIso (n + 1)).inv.val.app (specGlobalOpen R)
            (tildeTensorPowerSection R M (n + 1) fun i => a i.succ))) =
      tildeTensorPowerSection R N (n + 1) fun i => f.hom (a i.succ)) :
    ((specTildeAlgebras R N).tensorPieceIso (n + 2)).hom.val.app (specGlobalOpen R)
        ((g.app ((n + 2 : ℕ) : ℤ)).val.app (specGlobalOpen R)
          (((specTildeAlgebras R M).tensorPieceIso (n + 2)).inv.val.app (specGlobalOpen R)
            (tildeTensorPowerSection R M (n + 2) a))) =
      tildeTensorPowerSection R N (n + 2) fun i => f.hom (a i) := by
  have hInv : ((specTildeAlgebras R M).tensorPieceIso (n + 2)).inv.val.app (specGlobalOpen R)
        (tildeTensorPowerSection R M (n + 2) a) =
      Eq.mp (congrArg (fun k : ℤ =>
          (((specTildeAlgebras R M).tensor.piece k).val.obj (specGlobalOpen R) : Type u))
        (show 1 + ((n + 1 : ℕ) : ℤ) = ((n + 2 : ℕ) : ℤ) by omega))
        (((specTildeAlgebras R M).tensor.mul 1 ((n + 1 : ℕ) : ℤ)).app (specGlobalOpen R)
          ((specTildeAlgebras R M).tensorGenerator.val.app (specGlobalOpen R)
            ((tilde.toOpen M ⊤).hom (a 0)))
          (((specTildeAlgebras R M).tensorPieceIso (n + 1)).inv.val.app (specGlobalOpen R)
            (tildeTensorPowerSection R M (n + 1) fun i => a i.succ))) :=
    (sheafIso_eq_inv_app_of_hom_app_eq ((specTildeAlgebras R M).tensorPieceIso (n + 2))
      (specGlobalOpen R)
      ((specTildeAlgebras R M).tensorPieceIso_mul_left n (specGlobalOpen R)
        ((tilde.toOpen M ⊤).hom (a 0))
        (tildeTensorPowerSection R M (n + 1) fun i => a i.succ))).symm
  have htail : (g.app ((n + 1 : ℕ) : ℤ)).val.app (specGlobalOpen R)
        (((specTildeAlgebras R M).tensorPieceIso (n + 1)).inv.val.app (specGlobalOpen R)
          (tildeTensorPowerSection R M (n + 1) fun i => a i.succ)) =
      ((specTildeAlgebras R N).tensorPieceIso (n + 1)).inv.val.app (specGlobalOpen R)
        (tildeTensorPowerSection R N (n + 1) fun i => f.hom (a i.succ)) :=
    sheafIso_eq_inv_app_of_hom_app_eq ((specTildeAlgebras R N).tensorPieceIso (n + 1))
      (specGlobalOpen R) ih
  have hmul : (g.app (1 + ((n + 1 : ℕ) : ℤ))).val.app (specGlobalOpen R)
        (((specTildeAlgebras R M).tensor.mul 1 ((n + 1 : ℕ) : ℤ)).app (specGlobalOpen R)
          ((specTildeAlgebras R M).tensorGenerator.val.app (specGlobalOpen R)
            ((tilde.toOpen M ⊤).hom (a 0)))
          (((specTildeAlgebras R M).tensorPieceIso (n + 1)).inv.val.app (specGlobalOpen R)
            (tildeTensorPowerSection R M (n + 1) fun i => a i.succ))) =
      ((specTildeAlgebras R N).tensor.mul 1 ((n + 1 : ℕ) : ℤ)).app (specGlobalOpen R)
        ((specTildeAlgebras R N).tensorGenerator.val.app (specGlobalOpen R)
          ((tilde.toOpen N ⊤).hom (f.hom (a 0))))
        (((specTildeAlgebras R N).tensorPieceIso (n + 1)).inv.val.app (specGlobalOpen R)
          (tildeTensorPowerSection R N (n + 1) fun i => f.hom (a i.succ))) :=
    (g.map_mul 1 ((n + 1 : ℕ) : ℤ) (specGlobalOpen R)
        ((specTildeAlgebras R M).tensorGenerator.val.app (specGlobalOpen R)
          ((tilde.toOpen M ⊤).hom (a 0)))
        (((specTildeAlgebras R M).tensorPieceIso (n + 1)).inv.val.app (specGlobalOpen R)
          (tildeTensorPowerSection R M (n + 1) fun i => a i.succ))).trans
      (congrArg₂ (fun x y => ((specTildeAlgebras R N).tensor.mul 1 ((n + 1 : ℕ) : ℤ)).app
          (specGlobalOpen R) x y)
        (unitalHom_tensorGenerator_toOpen R f g hg (a 0)) htail)
  rw [hInv, map_cast (fun k => (g.app k).val.app (specGlobalOpen R))
      (show 1 + ((n + 1 : ℕ) : ℤ) = ((n + 2 : ℕ) : ℤ) by omega), hmul]
  exact (specTildeAlgebras R N).tensorPieceIso_mul_left n (specGlobalOpen R)
    ((tilde.toOpen N ⊤).hom (f.hom (a 0)))
    (tildeTensorPowerSection R N (n + 1) fun i => f.hom (a i.succ))

/-- The global sections attached to a finite family of module elements are carried to each
other by any unital graded-algebra map extending `tilde.map f` on degree-one generators. -/
private theorem tildeTensorPowerSection_natural
    (hg : (specTildeAlgebras R M).tensorGenerator ≫ g.app 1 =
      tilde.map f ≫ (specTildeAlgebras R N).tensorGenerator) :
    ∀ (n : ℕ) (a : Fin n → M),
      ((specTildeAlgebras R N).tensorPieceIso n).hom.val.app (specGlobalOpen R)
          ((g.app (n : ℤ)).val.app (specGlobalOpen R)
            (((specTildeAlgebras R M).tensorPieceIso n).inv.val.app (specGlobalOpen R)
              (tildeTensorPowerSection R M n a))) =
        tildeTensorPowerSection R N n fun i => f.hom (a i) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => exact tildeTensorPowerSection_natural_zero R f g
  | one => exact tildeTensorPowerSection_natural_one R f g hg
  | more n _ ihSucc => exact fun a =>
      tildeTensorPowerSection_natural_add_two R f g hg n a (ihSucc fun i => a i.succ)

/-- `tildeTensorPowerIso_natural` evaluated on a pure tensor, which is what the adjunction
reduces it to. -/
private lemma tildeTensorPowerIso_natural_apply
    (hg : (specTildeAlgebras R M).tensorGenerator ≫ g.app 1 =
      tilde.map f ≫ (specTildeAlgebras R N).tensorGenerator) (n : ℕ) (a : Fin n → M) :
    (tildeTensorPowerIso R N n).hom.val.app (specGlobalOpen R)
        ((tilde.map (ModuleCat.ofHom (PiTensorProduct.map (fun _ : Fin n => f.hom)))).val.app
          (specGlobalOpen R)
          ((tilde.toOpen (ModuleCat.of R (TensorPower R n M)) ⊤).hom
            (PiTensorProduct.tprod R a))) =
      ((specTildeAlgebras R N).tensorPieceIso n).hom.val.app (specGlobalOpen R)
        ((g.app (n : ℤ)).val.app (specGlobalOpen R)
          (((specTildeAlgebras R M).tensorPieceIso n).inv.val.app (specGlobalOpen R)
            ((tildeTensorPowerIso R M n).hom.val.app (specGlobalOpen R)
              ((tilde.toOpen (ModuleCat.of R (TensorPower R n M)) ⊤).hom
                (PiTensorProduct.tprod R a))))) := by
  have h1 : (tildeTensorPowerIso R N n).hom.val.app (specGlobalOpen R)
        ((tilde.map (ModuleCat.ofHom (PiTensorProduct.map (fun _ : Fin n => f.hom)))).val.app
          (specGlobalOpen R)
          ((tilde.toOpen (ModuleCat.of R (TensorPower R n M)) ⊤).hom
            (PiTensorProduct.tprod R a))) =
      tildeTensorPowerSection R N n fun i => f.hom (a i) :=
    (congrArg ((tildeTensorPowerIso R N n).hom.val.app (specGlobalOpen R))
        ((tildeMap_toOpen_top_apply
            (ModuleCat.ofHom (PiTensorProduct.map (fun _ : Fin n => f.hom)))
            (PiTensorProduct.tprod R a)).trans
          (congrArg ((tilde.toOpen (ModuleCat.of R (TensorPower R n N)) ⊤).hom)
            (PiTensorProduct.map_tprod (fun _ : Fin n => f.hom) a)))).trans
      (tildeTensorPowerIso_hom_tprod R N n fun i => f.hom (a i))
  have h2 := congrArg (fun y => ((specTildeAlgebras R N).tensorPieceIso n).hom.val.app
      (specGlobalOpen R) ((g.app (n : ℤ)).val.app (specGlobalOpen R)
        (((specTildeAlgebras R M).tensorPieceIso n).inv.val.app (specGlobalOpen R) y)))
    (tildeTensorPowerIso_hom_tprod R M n a)
  exact h1.trans ((tildeTensorPowerSection_natural R f g hg n a).symm.trans h2.symm)

/-- **Stacks Project, Tag 01I8 (tensor-power part).** Naturality of the affine tensor-power
comparison. The right-hand map is the degree-`n` component of a unital graded-algebra map
extending `tilde.map f` on degree-one generators; the universal property of the tensor algebra
makes such a map unique, so quantifying over it is a statement about the canonical one. -/
@[stacks 01I8 "tensor_power"]
theorem tildeTensorPowerIso_natural
    (hg : (specTildeAlgebras R M).tensorGenerator ≫ g.app 1 =
      tilde.map f ≫ (specTildeAlgebras R N).tensorGenerator) (n : ℕ) :
    tilde.map (ModuleCat.ofHom (PiTensorProduct.map (fun _ : Fin n => f.hom))) ≫
        (tildeTensorPowerIso R N n).hom =
      (tildeTensorPowerIso R M n).hom ≫ ((specTildeAlgebras R M).tensorPieceIso n).inv ≫
        g.app (n : ℤ) ≫ ((specTildeAlgebras R N).tensorPieceIso n).hom := by
  apply ((tilde.adjunction (R := R)).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply PiTensorProduct.ext
  ext a
  exact tildeTensorPowerIso_natural_apply R f g hg n a

/-- The canonical unital homomorphism of tensor algebra sheaves induced by `f`: the one the
universal property of `(specTildeAlgebras R M).tensor` produces from `tilde.map f`. The tensor
algebra imposes no condition on the degree-one generator, so no side condition is needed. -/
noncomputable def specTildeTensorAlgebraMap :
    SheafOfModules.GradedAlgebra.UnitalHom
      (specTildeAlgebras R M).tensor (specTildeAlgebras R N).tensor :=
  (specTildeAlgebras R M).tensor_isTensorAlgebra.isUniversal.desc
    (specTildeAlgebras R N).tensor
    (tilde.map f ≫ (specTildeAlgebras R N).tensorGenerator) trivial

/-- The canonical tensor-algebra map extends `tilde.map f` on the degree-one generators, which is
the hypothesis `tildeTensorPowerIso_natural` quantifies over. -/
theorem specTildeTensorAlgebraMap_app_one :
    (specTildeAlgebras R M).tensorGenerator ≫ (specTildeTensorAlgebraMap R f).app 1 =
      tilde.map f ≫ (specTildeAlgebras R N).tensorGenerator :=
  (specTildeAlgebras R M).tensor_isTensorAlgebra.isUniversal.desc_extends
    (specTildeAlgebras R N).tensor
    (tilde.map f ≫ (specTildeAlgebras R N).tensorGenerator) trivial

/-- **Stacks Project, Tag 01I8 (tensor-power part).** Naturality of the affine tensor-power
comparison against the canonical induced map, rather than against a hypothesised one: this is
`tildeTensorPowerIso_natural` instantiated at `specTildeTensorAlgebraMap`, the unital
graded-algebra map the universal property of the tensor algebra provides. The left-hand map is
the associated sheaf of `PiTensorProduct.map`, the `n`-fold tensor power of `f`. -/
@[stacks 01I8 "tensor_power"]
theorem tildeTensorPowerIso_natural_piTensorProductMap (n : ℕ) :
    tilde.map (ModuleCat.ofHom (PiTensorProduct.map (fun _ : Fin n => f.hom))) ≫
        (tildeTensorPowerIso R N n).hom =
      (tildeTensorPowerIso R M n).hom ≫ ((specTildeAlgebras R M).tensorPieceIso n).inv ≫
        (specTildeTensorAlgebraMap R f).app (n : ℤ) ≫
          ((specTildeAlgebras R N).tensorPieceIso n).hom :=
  tildeTensorPowerIso_natural R f (specTildeTensorAlgebraMap R f)
    (specTildeTensorAlgebraMap_app_one R f) n

end Naturality

end AlgebraicGeometry

end
