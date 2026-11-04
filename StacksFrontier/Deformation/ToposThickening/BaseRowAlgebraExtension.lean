module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingInverseImageKernel
public import StacksFrontier.Deformation.AlgebraExtension.InducedKernelMap
public import StacksFrontier.Deformation.ToposThickening.ExtensionProblem

/-!
# The lower row of a square-zero extension problem as an extension of algebras

A square-zero extension problem `S` of ringed topoi ([Stacks Project, Tag 08UF]) over
`f : X ⟶ B` has, on `X`, the lower row `0 → f⁻¹𝒥 → f⁻¹𝒪_{B'} → f⁻¹𝒪_B → 0`: the inverse image
of the base thickening, with its ideal `f⁻¹𝒥 = S.I`. This file reads that row as an extension of
`f⁻¹𝒪_{B'}`-algebras of `f⁻¹𝒪_B` by `S.I`
(`Deformation.ToposThickening.RingedToposExtensionProblem.baseRowExtension`).

For two problems over the same morphism `f` and a map `φ : 𝒪_{B'_S} ⟶ 𝒪_{B'_T}` of thickened
bases over `𝒪_B`, the inverse image `f⁻¹φ` is then a homomorphism of middle terms over `f⁻¹𝒪_B`,
and so induces a map of ideals `S.I ⟶ T.I` (`Deformation.AlgebraExtension.inducedKernelMap`):
the map `ι` along which a solution of `T` is read over the thickened base of `S`
(`RingedToposExtensionProblem.CompatibleFirstOrderThickening.restrictBase`).

## Main definitions

* `Deformation.ToposThickening.RingedToposExtensionProblem.baseRowExtension`: the lower row of `S`
  as an extension of `f⁻¹𝒪_{B'}`-algebras of `f⁻¹𝒪_B` by `S.I`.

## References

* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor
  isLocallySurjective_inverseImageCommRingFunctor_map)

universe v u w v' u' w'

namespace Deformation.ToposThickening.RingedToposExtensionProblem

variable {X : RingedTopos.{v, u, w}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (S : RingedToposExtensionProblem X B)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The product of two sections of `f⁻¹𝒪_{B'}` killed by the inverse image of the base
reduction is zero. -/
theorem baseRow_mul_eq_zero (U : X.Cᵒᵖ)
    (a b : ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U)
    (ha : ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U a = 0)
    (hb : ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U b = 0) :
    a * b = 0 := by
  obtain ⟨m, hm, -⟩ := S.idealUniversal U b hb
  rw [← hm]
  refine ((S.idealInclusion.val.app U).hom.map_smul' a m).symm.trans ?_
  have h0 : (show ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
      ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O)).obj.obj U from
        ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U a) = 0 := ha
  change (S.idealInclusion.val.app U).hom
      ((show ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
      ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O)).obj.obj U from
        ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U a) •
        (show S.I.val.obj U from m)) = 0
  rw [h0, zero_smul]
  exact map_zero _

/-- **The lower row of `S` as an extension of algebras**: `f⁻¹𝒪_{B'} ⟶ f⁻¹𝒪_B`, the inverse
image of the base reduction, with kernel the ideal `f⁻¹𝒥 = S.I`, as an extension of
`f⁻¹𝒪_{B'}`-algebras. -/
def baseRowExtension :
    Deformation.AlgebraExtension (J := X.J)
      ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction) S.I where
  extension := (inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension
  reduction := (inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction
  locallySurjective := isLocallySurjective_inverseImageCommRingFunctor_map S.f.toToposHom
    S.baseReduction S.baseLocallySurjective
  squareZero U := by
    rw [pow_two, eq_bot_iff]
    exact Ideal.mul_le.2 fun a ha b hb => (Ideal.mem_bot).2 (S.baseRow_mul_eq_zero U a b ha hb)
  algebraMap := 𝟙 _
  algebraMap_reduction := Category.id_comp _
  kernelInclusion := S.idealInclusion
  kernelZero := S.idealZero
  kernelUniversal := S.idealUniversal

/-- The inclusion of the kernel of `S.baseRowExtension` sends a section `a` of `S.I` to its
image under `S.idealInclusion`. -/
theorem baseRowExtension_incl {U : X.Cᵒᵖ} (a : S.I.val.obj U) :
    S.baseRowExtension.incl a =
      (show ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U from
        S.idealInclusion.val.app U a) :=
  rfl

end Deformation.ToposThickening.RingedToposExtensionProblem

end
