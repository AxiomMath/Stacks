module

public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionBaseChange
public import StacksFrontier.CategoryTheory.Sites.Modules.QuotientRingSheafRecognition

/-!
# The universal property of the base change of a solution

Let `X'` be a solution over `t₁` of the deformation problem of **Stacks 08U7** and `X'_2` its base
change along `h' : S'₂ ⟶ S'₁` (`DeformationSolution.baseChange`). Any solution `Y'` over `t₂`
receiving from `𝒪_{X'}` a morphism of extended structure sheaves compatible with the reductions,
inducing `ν` on ideals and compatible with the algebra structures through `h'` is isomorphic to
`X'_2`.

The comparison is the universal property of the square-zero pushout `𝒪_{X'} ⊔_{𝒢₁} 𝒢₂`: the
given morphism and the inclusion of `𝒢₂` into `𝒪_{Y'}` together define a ring homomorphism out of
`𝒪_{X'} ⋉ 𝒢₂` killing the graph of `ν`, hence a morphism out of the pushout; it is a morphism of
extensions of `(f ∘ t₂)⁻¹𝒪_{S'₂}`-algebras because the descended algebra structure is determined
by its values on the fibre product from which it is descended.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension.pushCoeffDesc`: the
  morphism out of the pushout `𝒪_{X'} ⊔_{𝒢₁} 𝒢₂` determined by a morphism of extensions inducing
  `ν` on ideals.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.isomorphic_baseChange_of_hom`:
  **the universal property of base change.**

## References

* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
* [Stacks Project, Tag 08UA](https://stacks.math.columbia.edu/tag/08UA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction PresheafOfModules
open Stacks.Sites.SqZeroPushout
open Stacks.Sheaves.Differentials (sqZeroExtSheaf sqZeroExtSheafInl sqZeroExtSheafProj)
open Stacks.Sites.Conormal (IdealRestriction kernelIdeal kernelIdeal_le_comap hom_of_comp_eq
  presentationScalar)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

namespace AlgebraSquareZeroExtension

variable {X T T₂ : RingedSpace.{u, u}} {g : X ⟶ T} {g₂ : X ⟶ T₂}
  {G₁ G₂ : SheafOfModules.{u} (ringSheaf (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  (P : AlgebraSquareZeroExtension g G₁) (ν : G₁ ⟶ G₂)
  {P₂ : AlgebraSquareZeroExtension g₂ G₂} (hP₂ : P₂.IdealBijective)
  (θ : P.sheaf ⟶ P₂.sheaf) (hred : θ ≫ P₂.reduction = P.reduction)
  (hideal : ∀ (V : (Opens X.carrier)ᵒᵖ) (y : ↥(kernelIdeal P.reduction.hom V)),
    P₂.ideal.app V ⟨θ.hom.app V y, kernelIdeal_le_comap _ _ θ.hom (hom_of_comp_eq hred) V y.2⟩ =
      ν.val.app V (P.ideal.app V y))

/-- The ring component `r` of a section `(r, n)` of `𝒪_{X'} ⋉ 𝒢₂`. -/
abbrev fstR (U : (Opens X.carrier)ᵒᵖ)
    (w : ↥((modules.{u} (restrictAlong.{u} P.reduction G₂)).sqZeroExtObj U)) :
    ↥(P.sheaf.obj.obj U) :=
  sqZeroExtFst (M := modules.{u} (restrictAlong.{u} P.reduction G₂)) w

/-- The module component `n` of a section `(r, n)` of `𝒪_{X'} ⋉ 𝒢₂`, as a section of `𝒢₂`. -/
abbrev sndG (U : (Opens X.carrier)ᵒᵖ)
    (w : ↥((modules.{u} (restrictAlong.{u} P.reduction G₂)).sqZeroExtObj U)) :
    ↥(G₂.val.obj U) :=
  sqZeroExtSnd (M := modules.{u} (restrictAlong.{u} P.reduction G₂)) w

variable (U : (Opens X.carrier)ᵒᵖ)
  (w w' : ↥((modules.{u} (restrictAlong.{u} P.reduction G₂)).sqZeroExtObj U))

/-- The ring component of a sum is the sum of the ring components. -/
theorem fstR_add : fstR P U (w + w') = fstR P U w + fstR P U w' := rfl

/-- The ring component of a product is the product of the ring components. -/
theorem fstR_mul : fstR P U (w * w') = fstR P U w * fstR P U w' := rfl

/-- The ring component of `0` is `0`. -/
theorem fstR_zero : fstR (G₂ := G₂) P U 0 = 0 := rfl

/-- The ring component of `1` is `1`. -/
theorem fstR_one : fstR (G₂ := G₂) P U 1 = 1 := rfl

/-- The module component of a sum is the sum of the module components. -/
theorem sndG_add : sndG P U (w + w') = sndG P U w + sndG P U w' := rfl

/-- The module component of `0` is `0`. -/
theorem sndG_zero : sndG (G₂ := G₂) P U 0 = 0 := rfl

/-- The module component of `1` is `0`. -/
theorem sndG_one : sndG (G₂ := G₂) P U 1 = 0 := rfl

/-- The module component of a product: `(r, n) * (r', n')` has module component
`r • n' + r' • n`. -/
theorem sndG_mul : sndG P U (w * w') =
    presentationScalar P.reduction U (fstR P U w) • sndG P U w' +
      presentationScalar P.reduction U (fstR P U w') • sndG P U w := rfl

/-- The value `θ(r) + n` of a section `(r, n)` of `𝒪_{X'} ⋉ 𝒢₂`. -/
def descValue : ↥(P₂.sheaf.obj.obj U) :=
  θ.hom.app U (fstR P U w) + P₂.idealIncl hP₂ U (sndG P U w)

/-- `descValue` is additive. -/
theorem descValue_add :
    descValue P hP₂ θ U (w + w') = descValue P hP₂ θ U w + descValue P hP₂ θ U w' := by
  unfold descValue
  rw [fstR_add, sndG_add, map_add, P₂.idealIncl_add hP₂]
  abel

/-- `descValue` sends `0` to `0`. -/
theorem descValue_zero : descValue P hP₂ θ U 0 = 0 := by
  unfold descValue
  rw [fstR_zero, sndG_zero, map_zero, P₂.idealIncl_zero hP₂, add_zero]

/-- `descValue` sends `1` to `1`. -/
theorem descValue_one : descValue P hP₂ θ U 1 = 1 := by
  unfold descValue
  rw [fstR_one, sndG_one, map_one, P₂.idealIncl_zero hP₂, add_zero]

include hred in
/-- `descValue` is multiplicative. -/
theorem descValue_mul :
    descValue P hP₂ θ U (w * w') = descValue P hP₂ θ U w * descValue P hP₂ θ U w' := by
  have hsc : ∀ r : ↥(P.sheaf.obj.obj U),
      presentationScalar P₂.reduction U (θ.hom.app U r) = presentationScalar P.reduction U r :=
    fun r => congrArg (fun k => (k.hom.app U) r) hred
  unfold descValue
  rw [fstR_mul, sndG_mul, map_mul, P₂.idealIncl_add hP₂, add_mul, mul_add,
    mul_add, P₂.idealIncl_mul_idealIncl hP₂, add_zero, P₂.mul_idealIncl hP₂, hsc,
    mul_comm (P₂.idealIncl hP₂ U _) (θ.hom.app U _), P₂.mul_idealIncl hP₂, hsc]
  abel

/-- The ring homomorphism `(r, n) ↦ θ(r) + n` out of `𝒪_{X'} ⋉ 𝒢₂`. -/
def descSqZero :
    sqZeroExtSheaf.{u} (K := Opens.grothendieckTopology X.carrier) P.sheaf
      (restrictAlong.{u} P.reduction G₂) ⟶ P₂.sheaf :=
  ⟨{ app := fun U => CommRingCat.ofHom
        (R := ↥((modules.{u} (restrictAlong.{u} P.reduction G₂)).sqZeroExtObj U))
        (S := ↥(P₂.sheaf.obj.obj U))
        { toFun := descValue P hP₂ θ U
          map_one' := descValue_one P hP₂ θ U
          map_mul' := descValue_mul P hP₂ θ hred U
          map_zero' := descValue_zero P hP₂ θ U
          map_add' := descValue_add P hP₂ θ U }
     naturality := fun U V i => CommRingCat.hom_ext (RingHom.ext fun w => by
        change θ.hom.app V ((P.sheaf.obj.map i).hom (fstR P U w)) +
            P₂.idealIncl hP₂ V (G₂.val.map i (sndG P U w)) =
          (P₂.sheaf.obj.map i).hom (θ.hom.app U (fstR P U w) + P₂.idealIncl hP₂ U (sndG P U w))
        rw [map_add, P₂.idealIncl_map hP₂, NatTrans.naturality_apply θ.hom i]) }⟩

/-- The section map of `descSqZero` is `descValue`. -/
theorem descSqZero_app (U : (Opens X.carrier)ᵒᵖ)
    (w : ↥((modules.{u} (restrictAlong.{u} P.reduction G₂)).sqZeroExtObj U)) :
    (descSqZero P hP₂ θ hred).hom.app U w = descValue P hP₂ θ U w :=
  rfl

include hideal in
/-- `(r, n) ↦ θ(r) + n` kills the graph `{(g, -ν(g))}` of `ν`. -/
theorem sectionIdeal_le_ker_descSqZero (V : (Opens X.carrier)ᵒᵖ) :
    Stacks.Sites.sectionIdeal (graphIdealSubsheaf.{u} P.reduction (restrictAlong.{u} P.reduction G₂)
      (coeffPushoutData P ν)) V ≤ RingHom.ker ((descSqZero P hP₂ θ hred).hom.app V).hom := by
  rintro w ⟨y, rfl⟩
  change θ.hom.app V (y : ↥(P.sheaf.obj.obj V)) +
    P₂.idealIncl hP₂ V (-(ν.val.app V (P.ideal.app V y))) = 0
  have h1 : θ.hom.app V (y : ↥(P.sheaf.obj.obj V)) =
      P₂.idealIncl hP₂ V (ν.val.app V (P.ideal.app V y)) := by
    rw [← hideal V y, P₂.idealIncl_ideal hP₂]
  rw [h1, ← P₂.idealIncl_add hP₂, add_neg_cancel, P₂.idealIncl_zero hP₂]

/-- **The morphism out of the pushout `𝒪_{X'} ⊔_{𝒢₁} 𝒢₂`** determined by a morphism `θ` of
extensions inducing `ν` on ideals: `[(r, n)] ↦ θ(r) + n`. -/
def pushCoeffDesc : (P.pushCoeff ν).sheaf ⟶ P₂.sheaf :=
  Stacks.Sites.quotientRingSheafDesc (descSqZero P hP₂ θ hred)
    (graphIdealSubsheaf.{u} P.reduction (restrictAlong.{u} P.reduction G₂) (coeffPushoutData P ν))
    (sectionIdeal_le_ker_descSqZero P ν hP₂ θ hred hideal)

/-- `pushCoeffDesc` sends the class of `(r, n)` to `θ(r) + n`. -/
theorem pushCoeffDesc_app_pushoutMk (U : (Opens X.carrier)ᵒᵖ)
    (w : ↥((modules.{u} (restrictAlong.{u} P.reduction G₂)).sqZeroExtObj U)) :
    (pushCoeffDesc P ν hP₂ θ hred hideal).hom.app U
        ((pushoutMk.{u} P.reduction (restrictAlong.{u} P.reduction G₂)
          (coeffPushoutData P ν)).hom.app U w) = descValue P hP₂ θ U w :=
  Stacks.Sites.quotientRingSheafDesc_app_apply (descSqZero P hP₂ θ hred)
    (graphIdealSubsheaf.{u} P.reduction (restrictAlong.{u} P.reduction G₂) (coeffPushoutData P ν))
    (sectionIdeal_le_ker_descSqZero P ν hP₂ θ hred hideal) U w

/-- `pushCoeffDesc` restricts to `θ` on `𝒪_{X'}`. -/
theorem pushCoeffInl_comp_pushCoeffDesc :
    P.pushCoeffInl ν ≫ pushCoeffDesc P ν hP₂ θ hred hideal = θ := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => CommRingCat.hom_ext
    (RingHom.ext fun r => ?_)))
  change (pushCoeffDesc P ν hP₂ θ hred hideal).hom.app U
      ((pushoutMk.{u} P.reduction (restrictAlong.{u} P.reduction G₂)
        (coeffPushoutData P ν)).hom.app U (sqZeroExtMk r 0)) = θ.hom.app U r
  refine (pushCoeffDesc_app_pushoutMk P ν hP₂ θ hred hideal U _).trans ?_
  change θ.hom.app U r + P₂.idealIncl hP₂ U 0 = θ.hom.app U r
  rw [P₂.idealIncl_zero hP₂, add_zero]

/-- On the image of a section `n` of `𝒢₂`, `pushCoeffDesc` is the inclusion of `n` into the ideal
of `P₂`. -/
theorem pushCoeffDesc_pushoutInr (U : (Opens X.carrier)ᵒᵖ) (n : ↥(G₂.val.obj U)) :
    (pushCoeffDesc P ν hP₂ θ hred hideal).hom.app U
        (pushoutInr.{u} P.reduction (restrictAlong.{u} P.reduction G₂) (coeffPushoutData P ν) U n) =
      P₂.idealIncl hP₂ U n := by
  refine (pushCoeffDesc_app_pushoutMk P ν hP₂ θ hred hideal U _).trans ?_
  change θ.hom.app U 0 + P₂.idealIncl hP₂ U n = _
  rw [map_zero, zero_add]

/-- `pushCoeffDesc` is compatible with the reductions. -/
theorem pushCoeffDesc_comp_reduction :
    pushCoeffDesc P ν hP₂ θ hred hideal ≫ P₂.reduction = (P.pushCoeff ν).reduction := by
  have := isLocallySurjective_pushoutMk.{u} P.reduction (restrictAlong.{u} P.reduction G₂)
    (coeffPushoutData P ν)
  refine Stacks.Sites.RingDescent.hom_ext_of_isLocallySurjective
    (pushoutMk.{u} P.reduction (restrictAlong.{u} P.reduction G₂) (coeffPushoutData P ν)) ?_
  refine Eq.trans ?_ (pushoutMk_comp_pushoutProj.{u} _ _ _).symm
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => CommRingCat.hom_ext
    (RingHom.ext fun w => ?_)))
  change (P₂.reduction.hom.app U).hom ((pushCoeffDesc P ν hP₂ θ hred hideal).hom.app U
      ((pushoutMk.{u} P.reduction (restrictAlong.{u} P.reduction G₂)
        (coeffPushoutData P ν)).hom.app U w)) = (P.reduction.hom.app U).hom (fstR P U w)
  refine (congrArg (P₂.reduction.hom.app U).hom
    (pushCoeffDesc_app_pushoutMk P ν hP₂ θ hred hideal U w)).trans ?_
  change (P₂.reduction.hom.app U).hom (θ.hom.app U (fstR P U w) +
    P₂.idealIncl hP₂ U (sndG P U w)) = _
  rw [map_add, P₂.reduction_idealIncl hP₂, add_zero]
  exact congrArg (fun k => (k.hom.app U).hom (fstR P U w)) hred

/-- `pushCoeffDesc` induces the identity of `𝒢₂` on the square-zero ideals. -/
theorem pushCoeffDesc_ideal (V : (Opens X.carrier)ᵒᵖ)
    (y : ↥(kernelIdeal (P.pushCoeff ν).reduction.hom V)) :
    P₂.ideal.app V ⟨(pushCoeffDesc P ν hP₂ θ hred hideal).hom.app V y,
        kernelIdeal_le_comap _ _ _
          (hom_of_comp_eq (pushCoeffDesc_comp_reduction P ν hP₂ θ hred hideal)) V y.2⟩ =
      (P.pushCoeff ν).ideal.app V y := by
  have hy := P.pushCoeff_ideal_app_eq ν V y
  have h1 : (pushCoeffDesc P ν hP₂ θ hred hideal).hom.app V y =
      P₂.idealIncl hP₂ V ((P.pushCoeff ν).ideal.app V y) :=
    (congrArg _ hy).trans (pushCoeffDesc_pushoutInr P ν hP₂ θ hred hideal V _)
  refine Eq.trans ?_ (P₂.ideal_idealIncl hP₂ V ((P.pushCoeff ν).ideal.app V y))
  exact congrArg (P₂.ideal.app V) (Subtype.ext h1)

end AlgebraSquareZeroExtension

namespace DeformationSolution

variable {X S S₁ S₂ : RingedSpace.{u, u}} {t₂ : S ⟶ S₂} {h' : S₂ ⟶ S₁} {f : X ⟶ S}
  {G₁ G₂ : SheafOfModules.{u} (ringSheaf (J := Opens.grothendieckTopology X.carrier) X.sheaf)}

section Core

variable {ht₁ : IsFirstOrderThickening (t₂ ≫ h')}
  {c₁ : (modulePullback f).obj ((modulePullback (t₂ ≫ h')).obj
    (AlgebraicGeometry.SheafOfModules.idealSheaf (t₂ ≫ h'))) ⟶ G₁}
  (c₂ : (modulePullback f).obj ((modulePullback t₂).obj
    (AlgebraicGeometry.SheafOfModules.idealSheaf t₂)) ⟶ G₂)
  (ν : G₁ ⟶ G₂) (hν : baseChangeIdealMap f h' rfl ≫ c₂ = c₁ ≫ ν)
  (Q : DeformationSolution (t₂ ≫ h') ht₁ f G₁ c₁) (ht₂ : IsFirstOrderThickening t₂)
  (Q₂ : DeformationSolution t₂ ht₂ f G₂ c₂)
  (θ₂ : Q.toAlgebraExtension.sheaf ⟶ Q₂.toAlgebraExtension.sheaf)
  (hred : θ₂ ≫ Q₂.toAlgebraExtension.reduction = Q.toAlgebraExtension.reduction)
  (hideal : ∀ (V : (Opens X.carrier)ᵒᵖ) (y : ↥(kernelIdeal Q.toAlgebraExtension.reduction.hom V)),
    Q₂.toAlgebraExtension.ideal.app V
        ⟨θ₂.hom.app V y, kernelIdeal_le_comap _ _ θ₂.hom (hom_of_comp_eq hred) V y.2⟩ =
      ν.val.app V (Q.toAlgebraExtension.ideal.app V y))
  (hbase : Q.toAlgebraExtension.adjointBase ≫ (TopCat.Sheaf.pushforward CommRingCat.{u}
      (f ≫ (t₂ ≫ h')).hom.base).map θ₂ =
    thickeningSharp h' ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} h'.hom.base).map
      Q₂.toAlgebraExtension.adjointBase)

include hbase in
/-- The comparison out of the pushout is compatible with the descended algebra structure. -/
theorem base_comp_pushCoeffDesc :
    (Q.coreExtension c₂ ν hν ht₂).base ≫
        Q.toAlgebraExtension.pushCoeffDesc ν Q₂.toAlgebraExtension_idealBijective θ₂ hred hideal =
      Q₂.toAlgebraExtension.base := by
  set P := Q.toAlgebraExtension.pushCoeff ν
  set ψ := Q.toAlgebraExtension.pushCoeffDesc ν Q₂.toAlgebraExtension_idealBijective θ₂ hred hideal
  have hQ₂ := Q₂.toAlgebraExtension_idealBijective
  have hP := Q.toAlgebraExtension.pushCoeff_idealBijective ν
  have hcomp := pushCoeff_ideal_adjointBase c₂ ν hν Q
  have := BaseChange.isIso_base ht₂.1 ht₁.1
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology S₁.carrier)
      (BaseChange.sharp₁ t₂ h').hom := isLocallySurjective_thickeningSharp (t₂ ≫ h') ht₁.1
  have := Stacks.Sites.SqZeroPullback.isLocallySurjective_fibreSnd (BaseChange.sharp₁ t₂ h')
    (BaseChange.sharp₂ t₂ h')
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    (f ≫ t₂).hom.base).homEquiv _ _).injective
  refine ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    (f ≫ t₂).hom.base).homEquiv_naturality_right _ _).trans ?_
  refine (congrArg (· ≫ _) (BaseChange.adjointBaseHom_base₂ c₂ P hP hcomp ht₂.1 ht₁.1)).trans ?_
  refine BaseChange.pushforward_map_injective_ofIso h' ?_
  refine ((TopCat.Sheaf.pushforward CommRingCat.{u} h'.hom.base).map_comp _ _).trans ?_
  refine (congrArg (· ≫ _)
    (BaseChange.pushforward_map_adjointBase₂ c₂ P hP hcomp ht₂.1 ht₁.1)).trans ?_
  refine Stacks.Sites.RingDescent.hom_ext_of_isLocallySurjective
    (Stacks.Sites.SqZeroPullback.fibreSnd (BaseChange.sharp₁ t₂ h') (BaseChange.sharp₂ t₂ h')) ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (BaseChange.fibreSnd_comp_descHom c₂ P hP hcomp ht₁.1)).trans ?_
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V => CommRingCat.hom_ext
    (RingHom.ext fun z => ?_)))
  have hadj : P.adjointBase = Q.toAlgebraExtension.adjointBase ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} (f ≫ (t₂ ≫ h')).hom.base).map
        (Q.toAlgebraExtension.pushCoeffInl ν) :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      (f ≫ (t₂ ≫ h')).hom.base).homEquiv_naturality_right _ _
  have hinl : ∀ (U : (Opens X.carrier)ᵒᵖ) (r : ↥(Q.toAlgebraExtension.sheaf.obj.obj U)),
      ψ.hom.app U ((Q.toAlgebraExtension.pushCoeffInl ν).hom.app U r) = θ₂.hom.app U r :=
    fun U r => congrArg (fun k => k.hom.app U r)
      (Q.toAlgebraExtension.pushCoeffInl_comp_pushCoeffDesc ν hQ₂ θ₂ hred hideal)
  have hincl : ∀ (U : (Opens X.carrier)ᵒᵖ) (n : ↥(G₂.val.obj U)),
      ψ.hom.app U (P.idealIncl hP U n) = Q₂.toAlgebraExtension.idealIncl hQ₂ U n := by
    intro U n
    have h := Q.toAlgebraExtension.pushCoeffDesc_ideal ν hQ₂ θ₂ hred hideal U
      ⟨P.idealIncl hP U n, P.idealIncl_mem hP U n⟩
    exact (Q₂.toAlgebraExtension.idealIncl_eq_of_ideal_eq hQ₂ U
      ⟨ψ.hom.app U (P.idealIncl hP U n), _⟩ n (h.trans (P.ideal_idealIncl hP U n))).symm
  change ψ.hom.app _ (BaseChange.adj P V (BaseChange.fst V z) +
      P.idealIncl hP _ (BaseChange.diffValue c₂ V z)) =
    (Q₂.toAlgebraExtension.adjointBase.hom.app _).hom (BaseChange.snd V z)
  have hP_adj : BaseChange.adj P V (BaseChange.fst V z) =
      (Q.toAlgebraExtension.pushCoeffInl ν).hom.app _
        ((Q.toAlgebraExtension.adjointBase.hom.app V).hom (BaseChange.fst V z)) :=
    congrArg (fun k => (k.hom.app V).hom (BaseChange.fst V z)) hadj
  rw [map_add, hP_adj]
  refine (congrArg₂ (· + ·) (hinl _ _) (hincl _ _)).trans ?_
  have hs : BaseChange.snd V z = BaseChange.hmap V (BaseChange.fst V z) + BaseChange.diff V z :=
    (add_sub_cancel _ _).symm
  have hb : (Q₂.toAlgebraExtension.adjointBase.hom.app _).hom
      (BaseChange.hmap V (BaseChange.fst V z)) =
      θ₂.hom.app _ ((Q.toAlgebraExtension.adjointBase.hom.app V).hom (BaseChange.fst V z)) :=
    (congrArg (fun k => (k.hom.app V).hom (BaseChange.fst V z)) hbase).symm
  have hd : (Q₂.toAlgebraExtension.adjointBase.hom.app _).hom (BaseChange.diff V z) =
      Q₂.toAlgebraExtension.idealIncl hQ₂ _ (BaseChange.diffValue c₂ V z) := by
    exact (Q₂.toAlgebraExtension.idealIncl_eq_of_ideal_eq hQ₂ _
      ⟨_, Q₂.toAlgebraExtension.adjointBase_mem_kernelIdeal _ _ (BaseChange.diff_mem V z)⟩ _
      (Q₂.toAlgebraExtension_ideal_adjointBase _ _ (BaseChange.diff_mem V z))).symm
  have hsum : (Q₂.toAlgebraExtension.adjointBase.hom.app _).hom (BaseChange.snd V z) =
      (Q₂.toAlgebraExtension.adjointBase.hom.app _).hom (BaseChange.hmap V (BaseChange.fst V z)) +
        (Q₂.toAlgebraExtension.adjointBase.hom.app _).hom (BaseChange.diff V z) :=
    (congrArg (Q₂.toAlgebraExtension.adjointBase.hom.app _).hom hs).trans (map_add _ _ _)
  exact (congrArg₂ (· + ·) hb.symm hd.symm).trans hsum.symm

include hred hideal hbase in
/-- **The universal property of base change**, over `t₁ = t₂ ≫ h'`. -/
theorem isomorphic_baseChangeCore_of_hom :
    Isomorphic Q₂ (Q.baseChangeCore c₂ ν hν ht₂) := by
  have hQ₂ := Q₂.toAlgebraExtension_idealBijective
  have hE : (Q.coreExtension c₂ ν hν ht₂).toPresented.extClass =
      Q₂.toAlgebraExtension.toPresented.extClass :=
    AlgebraSquareZeroExtension.extClass_eq_extClass_of_hom (Q.coreExtension c₂ ν hν ht₂)
      Q₂.toAlgebraExtension (Q.toAlgebraExtension.pushCoeffDesc ν hQ₂ θ₂ hred hideal)
      (base_comp_pushCoeffDesc c₂ ν hν Q ht₂ Q₂ θ₂ hred hideal hbase)
      (Q.toAlgebraExtension.pushCoeffDesc_comp_reduction ν hQ₂ θ₂ hred hideal)
      (Q.toAlgebraExtension.pushCoeffDesc_ideal ν hQ₂ θ₂ hred hideal)
  obtain ⟨θ', hb', hr', hi'⟩ :=
    AlgebraSquareZeroExtension.exists_hom_toAlgebraExtension_toDeformationSolution
      (Q.coreExtension_idealBijective c₂ ν hν ht₂) ht₂
      (Q.coreExtension_ideal_adjointBase c₂ ν hν ht₂)
  have hE' : (Q.coreExtension c₂ ν hν ht₂).toPresented.extClass =
      (Q.baseChangeCore c₂ ν hν ht₂).extClass :=
    AlgebraSquareZeroExtension.extClass_eq_extClass_of_hom (Q.coreExtension c₂ ν hν ht₂)
      (Q.baseChangeCore c₂ ν hν ht₂).toAlgebraExtension θ' hb' hr' hi'
  exact (extClass_eq_extClass_iff_isomorphic Q₂ (Q.baseChangeCore c₂ ν hν ht₂)).1
    (hE.symm.trans hE')

end Core

variable {t₁ : S ⟶ S₁} {ht₁ : IsFirstOrderThickening t₁}
  {c₁ : (modulePullback f).obj ((modulePullback t₁).obj
    (AlgebraicGeometry.SheafOfModules.idealSheaf t₁)) ⟶ G₁}

/-- **The universal property of the base change of a solution along `h'`.** Let `Y'` be a
solution over `t₂` and `θ₂ : 𝒪_{X'} ⟶ 𝒪_{Y'}` a morphism of extended structure sheaves on `X`
which is compatible with the reductions, induces `ν` on the square-zero ideals, and is compatible
with the algebra structures through `h'` (in the adjoint form of
`DeformationSolution.adjointBase_comp_baseChangeHom`). Then `Y'` is isomorphic to the base change
of `X'`. -/
theorem isomorphic_baseChange_of_hom (Q : DeformationSolution t₁ ht₁ f G₁ c₁)
    (ht₂ : IsFirstOrderThickening t₂)
    (c₂ : (modulePullback f).obj ((modulePullback t₂).obj
      (AlgebraicGeometry.SheafOfModules.idealSheaf t₂)) ⟶ G₂)
    (h' : S₂ ⟶ S₁) (comm : t₂ ≫ h' = t₁) (ν : G₁ ⟶ G₂)
    (hν : baseChangeIdealMap f h' comm ≫ c₂ = c₁ ≫ ν)
    (Q₂ : DeformationSolution t₂ ht₂ f G₂ c₂)
    (θ₂ : Q.toAlgebraExtension.sheaf ⟶ Q₂.toAlgebraExtension.sheaf)
    (hred : θ₂ ≫ Q₂.toAlgebraExtension.reduction = Q.toAlgebraExtension.reduction)
    (hideal : ∀ (V : (Opens X.carrier)ᵒᵖ)
      (y : ↥(kernelIdeal Q.toAlgebraExtension.reduction.hom V)),
      Q₂.toAlgebraExtension.ideal.app V
          ⟨θ₂.hom.app V y, kernelIdeal_le_comap _ _ θ₂.hom (hom_of_comp_eq hred) V y.2⟩ =
        ν.val.app V (Q.toAlgebraExtension.ideal.app V y))
    (hbase : Q.toAlgebraExtension.adjointBase ≫ (TopCat.Sheaf.pushforward CommRingCat.{u}
        (f ≫ t₁).hom.base).map θ₂ =
      thickeningSharp h' ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} h'.hom.base).map
          Q₂.toAlgebraExtension.adjointBase ≫ eqToHom (by subst comm; rfl)) :
    Isomorphic Q₂ (Q.baseChange ht₂ c₂ h' comm ν hν) := by
  subst comm
  exact isomorphic_baseChangeCore_of_hom c₂ ν hν Q ht₂ Q₂ θ₂ hred hideal
    (hbase.trans ((Category.assoc _ _ _).symm.trans (Category.comp_id _)))

end DeformationSolution

end AlgebraicGeometry.RingedSpaceThickening

end
