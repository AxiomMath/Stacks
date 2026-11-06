module

public import Mathlib.Algebra.Category.Ring.Under.Limits
public import StacksFrontier.RingTheory.TensorProduct.TensorPi

/-!
# Base change along a flat, finitely presented ring map preserves all limits

For `S` a finitely presented `R`-module, `CommRingCat.tensorProd R S` preserves products indexed
by an arbitrary type (Stacks Tag 059K). If `S` is moreover flat over `R`, it preserves all limits,
and so does `CategoryTheory.Under.pushout f` for a flat `f : R ⟶ S` making `S` a finitely
presented `R`-module.

## Main results

* `CommRingCat.Under.preservesLimitsOfShape_discrete_tensorProd`: `CommRingCat.tensorProd R S`
  preserves products indexed by an arbitrary type when `S` is a finitely presented `R`-module.
* `CommRingCat.Under.preservesLimits_tensorProd`: it preserves all limits when `S` is moreover
  flat.
* `CommRingCat.Under.preservesLimits_pushout`: the same for `CategoryTheory.Under.pushout f`.

## References

* [Stacks Project, Tag 059K](https://stacks.math.columbia.edu/tag/059K)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace CommRingCat.Under

variable {R S : CommRingCat.{u}} [Algebra R S] {ι : Type u} (P : ι → CategoryTheory.Under R)

/-- The two fans on `i ↦ S ⊗[R] P i` agree for an arbitrary index type when `S` is a finitely
presented `R`-module. -/
def tensorProductFanIsoOfFinitePresentation [Module.FinitePresentation R S] :
    tensorProductFan S P ≅ tensorProductFan' S P :=
  Fan.ext (Algebra.TensorProduct.piRightOfFinitePresentation R S S
    (fun i ↦ (P i).right)).toUnder <| fun i ↦ by
  dsimp only [tensorProductFan, Fan.mk_pt, fan_mk_proj, tensorProductFan']
  apply CommRingCat.mkUnder_ext
  intro c
  induction c with
  | tmul x f =>
    simp only [AlgHom.toUnder_right, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
      Pi.evalAlgHom_apply, CategoryTheory.Under.comp_right, comp_apply,
      AlgEquiv.toUnder_hom_right_apply,
      Algebra.TensorProduct.piRightOfFinitePresentation_tmul]
  | add x y hx hy => simp_all

/-- The fan on `i ↦ S ⊗[R] P i` with vertex `S ⊗[R] ∀ i, P i` is limiting for an arbitrary index
type when `S` is a finitely presented `R`-module. -/
def tensorProductFanIsLimitOfFinitePresentation [Module.FinitePresentation R S] :
    IsLimit (tensorProductFan S P) :=
  (IsLimit.equivIsoLimit (tensorProductFanIsoOfFinitePresentation P)).symm
    (piFanIsLimit _)

/-- `CommRingCat.tensorProd R S` sends the canonical fan on `P` to a limit fan, for an arbitrary
index type, when `S` is a finitely presented `R`-module. -/
def piFanTensorProductIsLimitOfFinitePresentation [Module.FinitePresentation R S] :
    IsLimit ((tensorProd R S).mapCone (piFan P)) :=
  (isLimitMapConeFanMkEquiv (tensorProd R S) P _).symm <|
    tensorProductFanIsLimitOfFinitePresentation P

/-- `CommRingCat.tensorProd R S` preserves the product of an arbitrary family when `S` is a
finitely presented `R`-module. -/
instance preservesLimit_discreteFunctor_tensorProd [Module.FinitePresentation R S] :
    PreservesLimit (Discrete.functor P) (tensorProd R S) :=
  preservesLimit_of_preserves_limit_cone (piFanIsLimit P)
    (piFanTensorProductIsLimitOfFinitePresentation P)

/-- `CommRingCat.tensorProd R S` preserves all products indexed by `ι` when `S` is a finitely
presented `R`-module — with no finiteness hypothesis on `ι`. -/
instance preservesLimitsOfShape_discrete_tensorProd [Module.FinitePresentation R S] :
    PreservesLimitsOfShape (Discrete ι) (tensorProd R S) :=
  preservesLimitsOfShape_of_discrete (tensorProd R S)

/-- **Base change along a flat, finitely presented ring map preserves all limits**:
`CommRingCat.tensorProd R S` preserves all limits when `S` is a flat and finitely presented
`R`-module. -/
lemma preservesLimits_tensorProd [Module.Flat R S] [Module.FinitePresentation R S] :
    PreservesLimitsOfSize.{u, u} (tensorProd R S) :=
  preservesLimits_of_preservesEqualizers_and_products (tensorProd R S)

/-- **`Under.pushout f` preserves all limits** when `f` is flat and makes its target a finitely
presented module over its source. -/
lemma preservesLimits_pushout {R S : CommRingCat.{u}} (f : R ⟶ S)
    (hflat : RingHom.Flat f.hom)
    (hfp : letI : Algebra R S := f.hom.toAlgebra; Module.FinitePresentation R S) :
    PreservesLimitsOfSize.{u, u} (CategoryTheory.Under.pushout f) :=
  let : Algebra R S := f.hom.toAlgebra
  have : Module.Flat R S := hflat
  have : Module.FinitePresentation R S := hfp
  have : PreservesLimitsOfSize.{u, u} (tensorProd R S) := preservesLimits_tensorProd
  preservesLimits_of_natIso (F := tensorProd R S) (tensorProdIsoPushout R S)

end CommRingCat.Under

end
