module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAdmissibleTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeAdmissible
public import
  StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategoryLocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeDifferentialGradedModuleToposPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedModule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedResolutionLeft
public import StacksCore.Algebra.Homology.QuasiIso
public import StacksCore.Tactic.StacksAttribute

/-!
# Good acyclic right differential graded modules

Let `(C, O)` be a ringed site, let `A` be a sheaf of differential graded `O`-algebras on it and
let `P` be a good acyclic right differential graded `A`-module. Then:

1. `P ⊗_A N` is acyclic for every left differential graded `A`-module `N`;
2. for a base change along a continuous functor of sites and a homomorphism `φ : A → A'` of
   differential graded algebras, the pullback `f^*P` is good, and it is acyclic as soon as it is
   identified with `f⁻¹P ⊗_{f⁻¹A} A'` for a good acyclic module `f⁻¹P` on the second site.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.PullbackAcyclicityData`: an identification
  `f^*P ≅ f⁻¹P ⊗_{f⁻¹A} A'` of the pullback with a relative tensor product, where `f⁻¹P` is a
  good acyclic differential graded module over an algebra `f⁻¹A` on the second site.

## Main results

* `SheafOfModules.DifferentialGradedModule.acyclic_dgTensor_of_isKFlat_of_acyclic`: a K-flat
  acyclic right differential graded module tensored with an arbitrary left differential graded
  module is acyclic.
* `SheafOfModules.DifferentialGradedModule.acyclic_dgTensor_of_isGood_of_acyclic` and
  `SheafOfModules.DifferentialGradedModule.acyclic_dgTensor_of_isGoodToposBaseChange_of_acyclic`:
  the same statement for a good acyclic module, goodness being
  `SheafOfModules.DifferentialGradedModule.IsGood`, respectively
  `SheafOfModules.IsGoodToposBaseChange`.
* `SheafOfModules.DifferentialGradedModule.acyclic_pullback_of_isGood_of_acyclic`: given
  `PullbackAcyclicityData`, the pullback of a good acyclic module is acyclic.
* `SheafOfModules.DifferentialGradedModule.isGood_pullback_of_isGood`: the pullback of a good
  module is good.

## Implementation notes

The homogeneous pieces of the algebra and of the modules share one universe.

## References

* [Stacks Project, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t m v u m₁ v₁ u₁ m₂ v₂ u₂

namespace SheafOfModules

namespace DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] [HasWeakSheafify J (Type m)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  {Osharp : Sheaf J CommRingCat.{t}}

/-! ### A left module read twice across the opposite algebra -/

variable {R : Sheaf J RingCat.{t}} {B : DifferentialGradedAlgebra.{t, m} R}

/-- An integer multiple commutes with a heterogeneous equality between two sections of the pieces
of one graded family. -/
theorem _root_.SheafOfModules.LeftDifferentialGradedModule.heq_zsmul_of_heq (X : ℤ → Type*)
    [∀ k, AddCommGroup (X k)] {k k' : ℤ} (hk : k = k') {a : X k} {b : X k'} (hab : a ≍ b)
    (s : ℤ) : s • a ≍ s • b := by
  subst hk
  cases eq_of_heq hab
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] [HasWeakSheafify J (Type m)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}] in
/-- Reading a left differential graded `B`-module as a right `B.op`-module and back gives the
module one started from: the two Koszul signs cancel. -/
theorem _root_.SheafOfModules.LeftDifferentialGradedModule.opRight_unopLeft
    (N : LeftDifferentialGradedModule.{t, m, m} B) : N.opRight.unopLeft = N := by
  have hmul : ∀ (n p : ℤ), N.opRight.unopLeft.mul n p = N.mul n p := by
    intro n p
    refine Stacks.BilinearMap.ext fun U α x => eq_of_heq ?_
    refine (DifferentialGradedModule.unopLeftMul_app_heq N.opRight n p U α x).trans ?_
    refine (LeftDifferentialGradedModule.heq_zsmul_of_heq (fun k => (N.complex.X k).val.obj U)
      (Int.add_comm p n) (N.opRightMul_app_heq p n U x α) (Int.negOnePow (n * p) : ℤ)).trans ?_
    rw [smul_smul, negOnePow_mul_negOnePow, one_smul]
    exact HEq.rfl
  obtain ⟨c, mul, h₁, h₂, h₃⟩ := N
  have : (LeftDifferentialGradedModule.mk c mul h₁ h₂ h₃).opRight.unopLeft.mul = mul :=
    funext fun n => funext fun p => hmul n p
  change LeftDifferentialGradedModule.mk c _ _ _ _ = _
  congr

variable {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}

/-! ### The tensor product with a good acyclic module -/

/-- If `P` is a K-flat acyclic right differential graded `A`-module, then `P ⊗_A N` is acyclic
for every left differential graded `A`-module `N`. -/
theorem acyclic_dgTensor_of_isKFlat_of_acyclic {P : DifferentialGradedModule.{t, m, m} A}
    (hP : RelativeTensor.IsKFlat P) (hPac : P.complex.Acyclic)
    (N : LeftDifferentialGradedModule.{t, m, m} A) :
    (RelativeTensor.dgTensor P N).Acyclic := by
  obtain ⟨X, χ, hχ, -, hX⟩ := exists_flat_quasiIso (A := A.op) N.opRight
  have hses := (isAdmissibleShortExact_conePackage χ).dgTensor_shortExact P.opLeft
  have h₃ : (RelativeTensor.dgTensor (shift X) P.opLeft).Acyclic :=
    isKFlat_shift X hX P.opLeft hPac
  have hcone : (cone χ).complex.Acyclic := (acyclic_cone_iff_quasiIso _ χ).2 hχ
  have h₂ : (RelativeTensor.dgTensor (cone χ) P.opLeft).Acyclic := fun i =>
    (_root_.exactAt_iff_of_quasiIsoAt (RelativeTensor.dgTensorOpIso P (cone χ)).hom i).2
      (hP (cone χ).unopLeft hcone i)
  have h₁ : (RelativeTensor.dgTensor N.opRight P.opLeft).Acyclic :=
    hses.acyclic_X₁ (quasiIso_of_acyclic _ h₂ h₃)
  have h := RelativeTensor.acyclic_dgTensor_of_acyclic_dgTensor_op P N.opRight h₁
  rwa [LeftDifferentialGradedModule.opRight_unopLeft] at h

/-- If `P` is a good (in the sense of `SheafOfModules.DifferentialGradedModule.IsGood`) acyclic
right differential graded `A`-module, then `P ⊗_A N` is acyclic for every left differential
graded `A`-module `N`. -/
theorem acyclic_dgTensor_of_isGood_of_acyclic
    {P : DifferentialGradedModule.{t, m, m} A} (hP : IsGood.{t, m, v, u, m₁, v₁, u₁} P)
    (hPac : P.complex.Acyclic) (N : LeftDifferentialGradedModule.{t, m, m} A) :
    (RelativeTensor.dgTensor P N).Acyclic :=
  acyclic_dgTensor_of_isKFlat_of_acyclic hP.isKFlat hPac N

/-! ### The pullback of a good acyclic module -/

section Pullback

variable {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁}
  [J₁.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] [HasWeakSheafify J₁ (Type m₁)]
  [J₁.WEqualsLocallyBijective AddCommGrpCat.{m₁}] [HasSheafify J₁ AddCommGrpCat.{m₁}]
  {Osharp₁ : Sheaf J₁ CommRingCat.{t}} {w₁ : C ⥤ C₁}
  {ρ₁ : (toRingCat J Osharp).obj ⟶ w₁.op ⋙ (toRingCat J₁ Osharp₁).obj}
  {A₁ : DifferentialGradedAlgebra.{t, m₁} (toRingCat J₁ Osharp₁)}
  {φ₁ : DifferentialGradedAlgebra.SemilinearHom w₁ ρ₁ A A₁}

/-- An identification `f^*P ≅ f⁻¹P ⊗_{f⁻¹A} A'` of the pullback of `P` with a relative tensor
product: a sheaf of differential graded algebras `f⁻¹A` on the second site, a good acyclic right
differential graded `f⁻¹A`-module `f⁻¹P`, a left differential graded `f⁻¹A`-module `A'`, and an
isomorphism of complexes from the pullback of `P` to `f⁻¹P ⊗_{f⁻¹A} A'`. -/
structure PullbackAcyclicityData
    (PD : PullbackData.{t, m₁, m₁, v₁, u₁, m, m, v, u} φ₁)
    (P : DifferentialGradedModule.{t, m, m} A) where
  /-- The inverse image `f⁻¹A`, a sheaf of differential graded algebras on the second site. -/
  invAlg : DifferentialGradedAlgebra.{t, m₁} (toRingCat J₁ Osharp₁)
  /-- The inverse image `f⁻¹P`, a right differential graded `f⁻¹A`-module. -/
  invObj : DifferentialGradedModule.{t, m₁, m₁} invAlg
  /-- `A'` as a left differential graded `f⁻¹A`-module. -/
  coeff : LeftDifferentialGradedModule.{t, m₁, m₁} invAlg
  /-- `f⁻¹P` is acyclic. -/
  acyclic_invObj : invObj.complex.Acyclic
  /-- `f⁻¹P` is good. -/
  isGood_invObj : IsGood.{t, m₁, v₁, u₁, m₁, v₁, u₁} invObj
  /-- The isomorphism `f^*P ≅ f⁻¹P ⊗_{f⁻¹A} A'`. -/
  iso : (PD.obj P).complex ≅ RelativeTensor.dgTensor invObj coeff

omit [HasWeakSheafify J (Type m)] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasSheafify J AddCommGrpCat.{m}] in
/-- Given an identification `f^*P ≅ f⁻¹P ⊗_{f⁻¹A} A'` with `f⁻¹P` good and acyclic, the
pullback `f^*P` of `P` along a morphism of ringed sites and a homomorphism of differential
graded algebras is acyclic. -/
theorem acyclic_pullback_of_isGood_of_acyclic
    {PD : PullbackData.{t, m₁, m₁, v₁, u₁, m, m, v, u} φ₁}
    {P : DifferentialGradedModule.{t, m, m} A} (data : PullbackAcyclicityData PD P) :
    (PD.obj P).complex.Acyclic := by
  exact fun i => (_root_.exactAt_iff_of_quasiIsoAt data.iso.hom i).2
    (acyclic_dgTensor_of_isKFlat_of_acyclic data.isGood_invObj.isKFlat data.acyclic_invObj
      data.coeff i)

omit [HasWeakSheafify J (Type m)] [HasWeakSheafify J₁ (Type m₁)] in
/-- The pullback of a good right differential graded module along a morphism of ringed sites
and a homomorphism of differential graded algebras is good, provided the unit of the pullback
data is universal for every further base change. Goodness of `P` is assumed with the universes
of both the second and the third site. -/
theorem isGood_pullback_of_isGood {P : DifferentialGradedModule.{t, m, m} A}
    (hP₁ : IsGood.{t, m, v, u, m₁, v₁, u₁} P) (hP₂ : IsGood.{t, m, v, u, m₂, v₂, u₂} P)
    (PD : PullbackData.{t, m₁, m₁, v₁, u₁, m, m, v, u} φ₁)
    (huniv : ∀ {C₂ : Type u₂} [Category.{v₂} C₂] {J₂ : GrothendieckTopology C₂}
      [J₂.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
      {Osharp₂ : Sheaf J₂ CommRingCat.{t}} {w₂ : C₁ ⥤ C₂}
      {ρ₂ : (toRingCat J₁ Osharp₁).obj ⟶ w₂.op ⋙ (toRingCat J₂ Osharp₂).obj}
      {A₂ : DifferentialGradedAlgebra.{t, m₂} (toRingCat J₂ Osharp₂)}
      (φ₂ : DifferentialGradedAlgebra.SemilinearHom w₂ ρ₂ A₁ A₂)
      (M : DifferentialGradedModule.{t, m, m} A)
      (N : DifferentialGradedModule.{t, m₂, m₂} A₂), (PD.unit M).IsUniversal φ₂ N) :
    IsGood.{t, m₁, v₁, u₁, m₂, v₂, u₂} (PD.obj P) := by
  have h := hP₁.baseChange w₁ ρ₁ A₁ φ₁ PD
  refine ⟨h.1, h.2, ?_⟩
  intro C₂ _ J₂ _ _ _ Osharp₂ w₂ ρ₂ A₂ φ₂ PD₂
  exact hP₂.baseChange (w₁ ⋙ w₂) (compRingMap w₂ ρ₂ w₁ ρ₁) A₂ (φ₁.trans φ₂)
    { obj := fun M ↦ PD₂.obj (PD.obj M)
      unit := fun M ↦ PD₂.transUnit PD M
      isPullback := fun M ↦ PD₂.transIsPullback PD (fun M N ↦ huniv φ₂ M N) M }

end Pullback

/-! ### Goodness in the sense of `IsGoodToposBaseChange` -/

section ToposGood

universe w

variable {Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, w}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [HasSheafify Y.J (Type w)]
  {A₀ : DifferentialGradedAlgebra.{w, w} (toRingCat Y.J Y.O)}

/-- If `P` is a good (in the sense of `SheafOfModules.IsGoodToposBaseChange`) acyclic right
differential graded `A₀`-module, then `P ⊗_{A₀} N` is acyclic for every left differential graded
`A₀`-module `N`. -/
theorem acyclic_dgTensor_of_isGoodToposBaseChange_of_acyclic
    {P : DifferentialGradedModule.{w, w, w} A₀} (hP : IsGoodToposBaseChange.{w, v₁, u₁} P)
    (hPac : P.complex.Acyclic) (N : LeftDifferentialGradedModule.{w, w, w} A₀) :
    (RelativeTensor.dgTensor P N).Acyclic :=
  acyclic_dgTensor_of_isKFlat_of_acyclic hP.isKFlat hPac N

end ToposGood

end DifferentialGradedModule

end SheafOfModules
