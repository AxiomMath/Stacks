module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderIdealAffine
public import StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderStructureTopSplitting

/-!
# Integrability of the canonical connection on an affine object

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], let `F` be a sheaf
of `𝒪_{X/S}`-modules on the big crystalline site, let `(U, T, δ)` be an object of `CRIS(X/S)`, and
write `D = Γ(T, 𝒪_T)`, `Ω = Γ(T, Ω_{T/S,δ})`, `Ω² = Γ(T, Ω²_{T/S,δ})` and `M = F(U, T, δ)`.

`Crystalline.GlobalCrystallineSituation.crystalConnectionTensor_comp_self_eq_zero` proves
`∇ ∘ ∇ = 0` from two inputs: the degree-one identification
`Crystalline.GlobalCrystallineSituation.FirstOrderIdealBaseChange`, which is what gives `∇` the
target `Ω ⊗_D M` at all, and injectivity of the degree-two canonical map
`Crystalline.GlobalCrystallineSituation.diffAction₂`.  On an object with affine ambient scheme and
quasi-coherent `F_T` the first is now a theorem for a sheaf crystal,
`Crystalline.GlobalCrystallineSituation.firstOrderIdealBaseChangeOfIsSheafCrystal`.  This module
supplies the second, and with it the integrability clause.

## The shape of the argument

`Crystalline.GlobalCrystallineSituation.SecondOrderAffine.bijective_extensionSectionsMap` says
that on an affine object

`D'' ⊗_D M ⟶ F(U, T'', δ'')`,   `t ⊗ s ↦ t · q₀^* s`

is bijective, `D'' = Γ(T'', 𝒪_{T''})`.  The splitting
`𝒪_{T''} = 𝒪_T ⊕ Ω_{T/S,δ} ⊕ Ω_{T/S,δ} ⊕ Ω²_{T/S,δ}` of [Stacks, Remark 60.14.5, Tag 07J3] is a
splitting of `D''` as a `D`-module through `q₀`, because `q₀` is the inclusion `b ↦ (b, 0, 0, 0)`
of the first summand and the three others are ideals on which `D` then acts coordinatewise.  So
it induces a splitting

`D'' ⊗_D M ≅ M ⊕ (Ω ⊗_D M) ⊕ (Ω ⊗_D M) ⊕ (Ω² ⊗_D M)`

under which the base change above is exactly the degree-two base-change map
`Crystalline.GlobalCrystallineSituation.secondOrderSectionsMap`.  Hence that map is bijective, its
restriction `Crystalline.GlobalCrystallineSituation.diffAction₂` to the top summand is injective,
and `∇ ∘ ∇ = 0`.

The splitting itself is unconditional: no crystal hypothesis, no quasi-coherence, no affineness.
Affineness enters only through the base change.

## On the hypotheses

The conclusion is stated for an object whose ambient scheme is affine and with `F_T`
quasi-coherent, and carries no `@[stacks]` attribute for that reason: [Stacks, Tag 07J6] is
stated for every object of `CRIS(X/S)`, and affineness of the object is a hypothesis the source
does not impose.  It is not a gap in the argument but a feature of the spelling: at global
sections the degree-one identification `Ω ⊗_D M ≅ ker(i^* : F(U, T', δ') ⟶ M)` that gives `∇` its
target is **false** on a non-affine object, by the `ℙ¹` counterexample recorded in the module
documentation of `StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealSheaf.lean`, so there
is no connection at global sections there to be integrable.  The identification that does hold on
every object is the one at the level of *sheaves* of `𝒪_T`-modules,
`Crystalline.GlobalCrystallineSituation.isIso_firstOrderKernelComparison_of_isSheafCrystal`, whose
degree-two companion is
`Crystalline.GlobalCrystallineSituation.mono_secondOrderTensorComparison`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.SecondOrderAffine.splitTensorEquiv` — the splitting of
  `D'' ⊗_D M` into its four summands.

## Main results

* `...SecondOrderAffine.bijective_secondOrderSectionsMap_iff_bijective_extensionSectionsMap`
  — the degree-two base-change map of [Stacks, Tag 07J3] and the base change of the sections along
  `q₀` are bijective together.  Unconditional.
* `Crystalline.GlobalCrystallineSituation.SecondOrderAffine.injective_secondOrderSectionsMap` —
  **the degree-two base-change map is injective** for a sheaf crystal on an affine object with
  `F_T` quasi-coherent, and
  `Crystalline.GlobalCrystallineSituation.SecondOrderAffine.injective_diffAction₂` — so is the
  degree-two canonical map.
* `...SecondOrderAffine.crystalConnectionTensor_comp_self_eq_zero_of_isSheafCrystal`
  — **`∇ ∘ ∇ = 0`** for a sheaf crystal on an affine object with `F_T` quasi-coherent, with both
  inputs of the reduction discharged.

## References

* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J5](https://stacks.math.columbia.edu/tag/07J5)
* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace PresheafOfModules
open scoped AlgebraicGeometry TensorProduct ChangeOfRings

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

namespace SecondOrderAffine

/-! ### Three more identities in the abstract second-order extension

They are proved in the abstract setting rather than in the crystalline one for the reason
recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Crystalline/SecondOrderThickeningSections.lean`: over a section
ring of the crystalline site the module structures are reached through `inferInstanceAs`, and
`rw` does not see through that. -/

section SecondOrderExt

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  {M₁ M₂ N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
  {q : Stacks.BilinearMap M₁ M₂ N} {X : Cᵒᵖ}

/-- **The first middle coordinate of `(a, 0, 0, 0) · y` is `a · (first middle coordinate of
y)`.**  The Leibniz term of the second factor contributes nothing, the first middle coordinate of
`(a, 0, 0, 0)` vanishing. -/
theorem secondOrderExtLeft_incl_mul (a : ↑(R.obj X)) (y : SecondOrderExt q X) :
    secondOrderExtLeft (secondOrderExtMk (q := q) a 0 0 0 * y) = a • secondOrderExtLeft y := by
  rw [secondOrderExtLeft_mul, secondOrderExtFst_mk, secondOrderExtLeft_mk, smul_zero, add_zero]

/-- **The second middle coordinate of `(a, 0, 0, 0) · y` is `a · (second middle coordinate of
y)`.** -/
theorem secondOrderExtRight_incl_mul (a : ↑(R.obj X)) (y : SecondOrderExt q X) :
    secondOrderExtRight (secondOrderExtMk (q := q) a 0 0 0 * y) = a • secondOrderExtRight y := by
  rw [secondOrderExtRight_mul, secondOrderExtFst_mk, secondOrderExtRight_mk, smul_zero, add_zero]

/-- **A section of a second-order extension is the sum of its four coordinates**, each read
through the corresponding summand. -/
theorem secondOrderExt_coords_sum (y : SecondOrderExt q X) :
    secondOrderExtMk (q := q) (secondOrderExtFst y) 0 0 0 +
          secondOrderExtMk (q := q) 0 (secondOrderExtLeft y) 0 0 +
        secondOrderExtMk (q := q) 0 0 (secondOrderExtRight y) 0 +
      secondOrderExtMk (q := q) 0 0 0 (secondOrderExtTop y) = y := by
  refine secondOrderExt_ext ?_ ?_ ?_ ?_ <;> simp

end SecondOrderExt

variable {S : GlobalCrystallineSituation.{u}}
  (M : SheafOfModules.{u} (crystallineStructureSheaf S)) (A : Thickening S)

/-! ### The four coordinates of a section of `𝒪_{T''}`

Each is the corresponding coordinate of the abstract second-order extension, ascribed to the type
the crystalline spelling names it with: the carriers agree, but elaborating a coordinate on its
own produces the abstract type, whose scalar actions are not the ones instance search finds from
`Crystalline.GlobalCrystallineSituation.crysSheafRing` and the two form modules.  Every lemma
about them is closed by `rfl`. -/

/-- The first coordinate of a section of `𝒪_{T''}`, as a section of `𝒪_T`. -/
def fstPart (t : crysSheafRing S (secondOrderThickeningObject S A)) : crysSheafRing S A :=
  secondOrderExtFst t

/-- The first middle coordinate of a section of `𝒪_{T''}`, as a one-form. -/
def leftPart (t : crysSheafRing S (secondOrderThickeningObject S A)) : crysDiffSections A :=
  secondOrderExtLeft t

/-- The second middle coordinate of a section of `𝒪_{T''}`, as a one-form. -/
def rightPart (t : crysSheafRing S (secondOrderThickeningObject S A)) : crysDiffSections A :=
  secondOrderExtRight t

/-- The top coordinate of a section of `𝒪_{T''}`, as a two-form. -/
def topPart (t : crysSheafRing S (secondOrderThickeningObject S A)) : crysSecondFormSections A :=
  secondOrderExtTop t

/-! ### The splitting of the sections of `𝒪_{T''}` as a module over the sections of `𝒪_T` -/

/-- **A two-form read as a section of `𝒪_{T''}`, linearly in the two-form.**  The scalars of
`Γ(T, 𝒪_T)` act on `Γ(T'', 𝒪_{T''})` through `q₀`, and `q₀(b) · η = b η`. -/
def topSectionLinear :
    crysSecondFormSections A →ₗ[crysSheafRing S A]
      crysSheafRing S (secondOrderThickeningObject S A) where
  toFun := secondOrderTopSection A
  map_add' := secondOrderTopSection_add A
  map_smul' b η :=
    ((secondOrderTopSection_mul_crysSheafRingMap_q₀ A η b).symm.trans
      (mul_comm _ _)).trans (crysSheafRing_smul_def A b (secondOrderTopSection A η)).symm

/-- `topSectionLinear` sends a two-form `η` to `secondOrderTopSection A η`. -/
@[simp]
theorem topSectionLinear_apply (η : crysSecondFormSections A) :
    topSectionLinear A η = secondOrderTopSection A η := rfl

/-- **A one-form read as a section of `𝒪_{T''}` in the first middle summand, linearly in the
one-form.** -/
def leftSectionLinear :
    crysDiffSections A →ₗ[crysSheafRing S A]
      crysSheafRing S (secondOrderThickeningObject S A) where
  toFun := secondOrderLeftSection A
  map_add' := secondOrderLeftSection_add A
  map_smul' b ω :=
    ((secondOrderLeftSection_mul_crysSheafRingMap_q₀ A ω b).symm.trans
      (mul_comm _ _)).trans (crysSheafRing_smul_def A b (secondOrderLeftSection A ω)).symm

/-- `leftSectionLinear` sends a one-form `ω` to `secondOrderLeftSection A ω`. -/
@[simp]
theorem leftSectionLinear_apply (ω : crysDiffSections A) :
    leftSectionLinear A ω = secondOrderLeftSection A ω := rfl

/-- **A one-form read as a section of `𝒪_{T''}` in the second middle summand, linearly in the
one-form.** -/
def rightSectionLinear :
    crysDiffSections A →ₗ[crysSheafRing S A]
      crysSheafRing S (secondOrderThickeningObject S A) where
  toFun := secondOrderRightSection A
  map_add' := secondOrderRightSection_add A
  map_smul' b ω :=
    ((secondOrderRightSection_mul_crysSheafRingMap_q₀ A ω b).symm.trans
      (mul_comm _ _)).trans (crysSheafRing_smul_def A b (secondOrderRightSection A ω)).symm

/-- `rightSectionLinear` sends a one-form `ω` to `secondOrderRightSection A ω`. -/
@[simp]
theorem rightSectionLinear_apply (ω : crysDiffSections A) :
    rightSectionLinear A ω = secondOrderRightSection A ω := rfl

/-- **The first coordinate of a section of `𝒪_{T''}`, as a map of `Γ(T, 𝒪_T)`-modules.**  It is
linear and not only semilinear because the scalars act through `q₀`, which is the inclusion of the
first summand. -/
def fstPartLinear :
    crysSheafRing S (secondOrderThickeningObject S A) →ₗ[crysSheafRing S A]
      crysSheafRing S A where
  toFun := fstPart A
  map_add' t t' := secondOrderExtFst_add t t'
  map_smul' _ _ := rfl

/-- `fstPartLinear` sends a section of `𝒪_{T''}` to its first coordinate. -/
@[simp]
theorem fstPartLinear_apply (t : crysSheafRing S (secondOrderThickeningObject S A)) :
    fstPartLinear A t = fstPart A t := rfl

/-- **The first middle coordinate of a section of `𝒪_{T''}`, as a map of
`Γ(T, 𝒪_T)`-modules.** -/
def leftPartLinear :
    crysSheafRing S (secondOrderThickeningObject S A) →ₗ[crysSheafRing S A]
      crysDiffSections A where
  toFun := leftPart A
  map_add' t t' := secondOrderExtLeft_add t t'
  map_smul' b t := secondOrderExtLeft_incl_mul b t

/-- `leftPartLinear` sends a section of `𝒪_{T''}` to its first middle coordinate. -/
@[simp]
theorem leftPartLinear_apply (t : crysSheafRing S (secondOrderThickeningObject S A)) :
    leftPartLinear A t = leftPart A t := rfl

/-- **The second middle coordinate of a section of `𝒪_{T''}`, as a map of
`Γ(T, 𝒪_T)`-modules.** -/
def rightPartLinear :
    crysSheafRing S (secondOrderThickeningObject S A) →ₗ[crysSheafRing S A]
      crysDiffSections A where
  toFun := rightPart A
  map_add' t t' := secondOrderExtRight_add t t'
  map_smul' b t := secondOrderExtRight_incl_mul b t

/-- `rightPartLinear` sends a section of `𝒪_{T''}` to its second middle coordinate. -/
@[simp]
theorem rightPartLinear_apply (t : crysSheafRing S (secondOrderThickeningObject S A)) :
    rightPartLinear A t = rightPart A t := rfl

/-- **The top coordinate of a section of `𝒪_{T''}`, as a map of `Γ(T, 𝒪_T)`-modules.** -/
def topPartLinear :
    crysSheafRing S (secondOrderThickeningObject S A) →ₗ[crysSheafRing S A]
      crysSecondFormSections A where
  toFun := topPart A
  map_add' t t' := secondOrderExtTop_add t t'
  map_smul' b t := secondOrderExtTop_incl_mul b t

/-- `topPartLinear` sends a section of `𝒪_{T''}` to its top coordinate. -/
@[simp]
theorem topPartLinear_apply (t : crysSheafRing S (secondOrderThickeningObject S A)) :
    topPartLinear A t = topPart A t := rfl

/-- **The splitting `𝒪_{T''}(T'') = Γ(T, 𝒪_T) ⊕ Ω ⊕ Ω ⊕ Ω²` of [Stacks, Tag 07J3]**, written as
the statement that the four coordinates recover the section. -/
theorem q₀_add_leftSection_add_rightSection_add_topSection
    (t : crysSheafRing S (secondOrderThickeningObject S A)) :
    crysSheafRingMap (secondOrderThickeningSiteQ₀ S A) (fstPart A t) +
          secondOrderLeftSection A (leftPart A t) +
        secondOrderRightSection A (rightPart A t) +
      secondOrderTopSection A (topPart A t) = t :=
  secondOrderExt_coords_sum t

/-! ### The four coordinates of the four summands -/

/-- The first coordinate of `1` is `1`. -/
@[simp] theorem fstPart_one : fstPart A (1 : crysSheafRing S (secondOrderThickeningObject S A)) =
    1 := rfl

/-- The first middle coordinate of `1` is `0`. -/
@[simp] theorem leftPart_one : leftPart A (1 : crysSheafRing S (secondOrderThickeningObject S A)) =
    0 := rfl

/-- The second middle coordinate of `1` is `0`. -/
@[simp] theorem rightPart_one :
    rightPart A (1 : crysSheafRing S (secondOrderThickeningObject S A)) = 0 := rfl

/-- The top coordinate of `1` is `0`. -/
@[simp] theorem topPart_one : topPart A (1 : crysSheafRing S (secondOrderThickeningObject S A)) =
    0 := rfl

/-- The first coordinate of a section of the first middle summand is `0`. -/
@[simp] theorem fstPart_leftSection (ω : crysDiffSections A) :
    fstPart A (secondOrderLeftSection A ω) = 0 := rfl

/-- The first middle coordinate of `secondOrderLeftSection A ω` is `ω`. -/
@[simp] theorem leftPart_leftSection (ω : crysDiffSections A) :
    leftPart A (secondOrderLeftSection A ω) = ω := rfl

/-- The second middle coordinate of a section of the first middle summand is `0`. -/
@[simp] theorem rightPart_leftSection (ω : crysDiffSections A) :
    rightPart A (secondOrderLeftSection A ω) = 0 := rfl

/-- The top coordinate of a section of the first middle summand is `0`. -/
@[simp] theorem topPart_leftSection (ω : crysDiffSections A) :
    topPart A (secondOrderLeftSection A ω) = 0 := rfl

/-- The first coordinate of a section of the second middle summand is `0`. -/
@[simp] theorem fstPart_rightSection (ω : crysDiffSections A) :
    fstPart A (secondOrderRightSection A ω) = 0 := rfl

/-- The first middle coordinate of a section of the second middle summand is `0`. -/
@[simp] theorem leftPart_rightSection (ω : crysDiffSections A) :
    leftPart A (secondOrderRightSection A ω) = 0 := rfl

/-- The second middle coordinate of `secondOrderRightSection A ω` is `ω`. -/
@[simp] theorem rightPart_rightSection (ω : crysDiffSections A) :
    rightPart A (secondOrderRightSection A ω) = ω := rfl

/-- The top coordinate of a section of the second middle summand is `0`. -/
@[simp] theorem topPart_rightSection (ω : crysDiffSections A) :
    topPart A (secondOrderRightSection A ω) = 0 := rfl

/-- The first coordinate of a section of the top summand is `0`. -/
@[simp] theorem fstPart_topSection (η : crysSecondFormSections A) :
    fstPart A (secondOrderTopSection A η) = 0 := rfl

/-- The first middle coordinate of a section of the top summand is `0`. -/
@[simp] theorem leftPart_topSection (η : crysSecondFormSections A) :
    leftPart A (secondOrderTopSection A η) = 0 := rfl

/-- The second middle coordinate of a section of the top summand is `0`. -/
@[simp] theorem rightPart_topSection (η : crysSecondFormSections A) :
    rightPart A (secondOrderTopSection A η) = 0 := rfl

/-- The top coordinate of `secondOrderTopSection A η` is `η`. -/
@[simp] theorem topPart_topSection (η : crysSecondFormSections A) :
    topPart A (secondOrderTopSection A η) = η := rfl

/-! ### The splitting of the base change -/

/-- The reading of the top summand of the splitting of [Stacks, Tag 07J3] inside the base change,
`Ω² ⊗_D M ⟶ D'' ⊗_D M`. -/
def topTensorMap :
    crysSecondFormSections A ⊗[crysSheafRing S A] M.val.obj (op A) →ₗ[crysSheafRing S A]
      crysSheafRing S (secondOrderThickeningObject S A) ⊗[crysSheafRing S A]
        M.val.obj (op A) :=
  TensorProduct.map (topSectionLinear A) LinearMap.id

/-- `topTensorMap` on a pure tensor `η ⊗ s` reads the two-form `η` in the top summand. -/
@[simp]
theorem topTensorMap_tmul (η : crysSecondFormSections A) (s : M.val.obj (op A)) :
    topTensorMap M A (η ⊗ₜ[crysSheafRing S A] s) =
      secondOrderTopSection A η ⊗ₜ[crysSheafRing S A] s :=
  TensorProduct.map_tmul _ _ η s

/-- The reading of the first middle summand of the splitting inside the base change. -/
def leftTensorMap :
    crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A) →ₗ[crysSheafRing S A]
      crysSheafRing S (secondOrderThickeningObject S A) ⊗[crysSheafRing S A]
        M.val.obj (op A) :=
  TensorProduct.map (leftSectionLinear A) LinearMap.id

/-- `leftTensorMap` on a pure tensor `ω ⊗ s` reads `ω` in the first middle summand. -/
@[simp]
theorem leftTensorMap_tmul (ω : crysDiffSections A) (s : M.val.obj (op A)) :
    leftTensorMap M A (ω ⊗ₜ[crysSheafRing S A] s) =
      secondOrderLeftSection A ω ⊗ₜ[crysSheafRing S A] s :=
  TensorProduct.map_tmul _ _ ω s

/-- The reading of the second middle summand of the splitting inside the base change. -/
def rightTensorMap :
    crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A) →ₗ[crysSheafRing S A]
      crysSheafRing S (secondOrderThickeningObject S A) ⊗[crysSheafRing S A]
        M.val.obj (op A) :=
  TensorProduct.map (rightSectionLinear A) LinearMap.id

/-- `rightTensorMap` on a pure tensor `ω ⊗ s` reads `ω` in the second middle summand. -/
@[simp]
theorem rightTensorMap_tmul (ω : crysDiffSections A) (s : M.val.obj (op A)) :
    rightTensorMap M A (ω ⊗ₜ[crysSheafRing S A] s) =
      secondOrderRightSection A ω ⊗ₜ[crysSheafRing S A] s :=
  TensorProduct.map_tmul _ _ ω s

/-- **The splitting of [Stacks, Tag 07J3], read on the base change of the sections**: the map

`M × (Ω ⊗_D M) × (Ω ⊗_D M) × (Ω² ⊗_D M) ⟶ D'' ⊗_D M`,
`(s, z₁, z₂, w) ↦ 1 ⊗ s + z₁ + z₂ + w`,

each of the last three summands read through the corresponding summand of `𝒪_{T''}`. -/
def splitTensor :
    M.val.obj (op A) ×
        ((crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) ×
          ((crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) ×
            (crysSecondFormSections A ⊗[crysSheafRing S A] M.val.obj (op A)))) →+
      crysSheafRing S (secondOrderThickeningObject S A) ⊗[crysSheafRing S A]
        M.val.obj (op A) :=
  AddMonoidHom.mk'
    (fun x ↦ (1 : crysSheafRing S (secondOrderThickeningObject S A)) ⊗ₜ[crysSheafRing S A] x.1 +
      leftTensorMap M A x.2.1 + rightTensorMap M A x.2.2.1 + topTensorMap M A x.2.2.2)
    (fun x y ↦ by
      change (1 : crysSheafRing S (secondOrderThickeningObject S A)) ⊗ₜ[crysSheafRing S A]
            (x.1 + y.1) + leftTensorMap M A (x.2.1 + y.2.1) +
          rightTensorMap M A (x.2.2.1 + y.2.2.1) + topTensorMap M A (x.2.2.2 + y.2.2.2) = _
      rw [TensorProduct.tmul_add, map_add, map_add, map_add]
      abel)

/-- The splitting of the base change, on a quadruple. -/
@[simp]
theorem splitTensor_apply (s : M.val.obj (op A))
    (z₁ z₂ : crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A))
    (w : crysSecondFormSections A ⊗[crysSheafRing S A] M.val.obj (op A)) :
    splitTensor M A (s, z₁, z₂, w) =
      (1 : crysSheafRing S (secondOrderThickeningObject S A)) ⊗ₜ[crysSheafRing S A] s +
        leftTensorMap M A z₁ + rightTensorMap M A z₂ + topTensorMap M A w := rfl

/-- **The inverse of the splitting
`Crystalline.GlobalCrystallineSituation.SecondOrderAffine.splitTensor`**: a pure tensor `t ⊗ s`
goes to the quadruple of its four coordinates under the splitting of [Stacks, Tag 07J3]. -/
def splitTensorInv :
    crysSheafRing S (secondOrderThickeningObject S A) ⊗[crysSheafRing S A]
        M.val.obj (op A) →ₗ[crysSheafRing S A]
      M.val.obj (op A) ×
        ((crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) ×
          ((crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) ×
            (crysSecondFormSections A ⊗[crysSheafRing S A] M.val.obj (op A)))) :=
  LinearMap.prod
    ((TensorProduct.lid (crysSheafRing S A) (M.val.obj (op A))).toLinearMap ∘ₗ
      TensorProduct.map (fstPartLinear A) LinearMap.id)
    (LinearMap.prod (TensorProduct.map (leftPartLinear A) LinearMap.id)
      (LinearMap.prod (TensorProduct.map (rightPartLinear A) LinearMap.id)
        (TensorProduct.map (topPartLinear A) LinearMap.id)))

/-- The inverse of the splitting, on a pure tensor. -/
@[simp]
theorem splitTensorInv_tmul (t : crysSheafRing S (secondOrderThickeningObject S A))
    (s : M.val.obj (op A)) :
    splitTensorInv M A (t ⊗ₜ[crysSheafRing S A] s) =
      (fstPart A t • s, leftPart A t ⊗ₜ[crysSheafRing S A] s,
        rightPart A t ⊗ₜ[crysSheafRing S A] s, topPart A t ⊗ₜ[crysSheafRing S A] s) := rfl

/-- Two additive maps out of a tensor product agree if they agree on pure tensors. -/
private theorem tensor_addHom_apply_eq {R P Q N : Type*} [CommSemiring R] [AddCommMonoid P]
    [Module R P] [AddCommMonoid Q] [Module R Q] [AddCommMonoid N] {f g : P ⊗[R] Q →+ N}
    (h : ∀ p q, f (p ⊗ₜ[R] q) = g (p ⊗ₜ[R] q)) (z : P ⊗[R] Q) : f z = g z :=
  z.inductionOn (motive := fun z ↦ f z = g z) h
    fun _ _ hx hy ↦ by rw [map_add, map_add, hx, hy]

/-- The inverse of the splitting undoes the first middle summand. -/
theorem splitTensorInv_leftTensorMap
    (z : crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) :
    splitTensorInv M A (leftTensorMap M A z) = (0, z, 0, 0) :=
  tensor_addHom_apply_eq
    (f := (splitTensorInv M A).toAddMonoidHom.comp (↑(leftTensorMap M A)))
    (g := (AddMonoidHom.inr _ _).comp (AddMonoidHom.inl _ _))
    (fun _ _ ↦ by simp [splitTensorInv_tmul]) _

/-- The inverse of the splitting undoes the second middle summand. -/
theorem splitTensorInv_rightTensorMap
    (z : crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) :
    splitTensorInv M A (rightTensorMap M A z) = (0, 0, z, 0) :=
  tensor_addHom_apply_eq
    (f := (splitTensorInv M A).toAddMonoidHom.comp (↑(rightTensorMap M A)))
    (g := (AddMonoidHom.inr _ _).comp ((AddMonoidHom.inr _ _).comp (AddMonoidHom.inl _ _)))
    (fun _ _ ↦ by simp [splitTensorInv_tmul]) _

/-- The inverse of the splitting undoes the top summand. -/
theorem splitTensorInv_topTensorMap
    (w : crysSecondFormSections A ⊗[crysSheafRing S A] M.val.obj (op A)) :
    splitTensorInv M A (topTensorMap M A w) = (0, 0, 0, w) :=
  tensor_addHom_apply_eq
    (f := (splitTensorInv M A).toAddMonoidHom.comp (↑(topTensorMap M A)))
    (g := (AddMonoidHom.inr _ _).comp ((AddMonoidHom.inr _ _).comp (AddMonoidHom.inr _ _)))
    (fun _ _ ↦ by simp [splitTensorInv_tmul]) _

/-- **The splitting of [Stacks, Tag 07J3] on the base change of the sections**, as an additive
equivalence

`M × (Ω ⊗_D M) × (Ω ⊗_D M) × (Ω² ⊗_D M) ≃+ D'' ⊗_D M`.

Unconditional: no crystal hypothesis, no quasi-coherence, no affineness. -/
def splitTensorEquiv :
    M.val.obj (op A) ×
        ((crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) ×
          ((crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) ×
            (crysSecondFormSections A ⊗[crysSheafRing S A] M.val.obj (op A)))) ≃+
      crysSheafRing S (secondOrderThickeningObject S A) ⊗[crysSheafRing S A]
        M.val.obj (op A) where
  toFun := splitTensor M A
  invFun := splitTensorInv M A
  map_add' := map_add (splitTensor M A)
  left_inv x := by
    obtain ⟨s, z₁, z₂, w⟩ := x
    rw [splitTensor_apply, map_add, map_add, map_add, splitTensorInv_tmul,
      splitTensorInv_leftTensorMap, splitTensorInv_rightTensorMap, splitTensorInv_topTensorMap,
      fstPart_one, leftPart_one, rightPart_one, topPart_one, one_smul,
      TensorProduct.zero_tmul, TensorProduct.zero_tmul]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp
  right_inv t := by
    induction t using TensorProduct.inductionOn with
    | tmul t s =>
        rw [splitTensorInv_tmul, splitTensor_apply, leftTensorMap_tmul, rightTensorMap_tmul,
          topTensorMap_tmul, ← TensorProduct.smul_tmul, crysSheafRing_smul_def, mul_one,
          ← TensorProduct.add_tmul, ← TensorProduct.add_tmul, ← TensorProduct.add_tmul,
          q₀_add_leftSection_add_rightSection_add_topSection]
    | add t t' ht ht' => rw [map_add, map_add, ht, ht']

/-! ### The two base-change maps agree -/

/-- The degree-two canonical map into the first middle summand, on a pure tensor. -/
theorem diffActionLeft_tmul (ω : crysDiffSections A) (s : M.val.obj (op A)) :
    diffActionLeft M A (ω ⊗ₜ[crysSheafRing S A] s) =
      secondOrderLeftSection A ω •
        moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) s :=
  TensorProduct.liftAddHom_tmul _ _ ω s

/-- The degree-two canonical map into the second middle summand, on a pure tensor. -/
theorem diffActionRight_tmul (ω : crysDiffSections A) (s : M.val.obj (op A)) :
    diffActionRight M A (ω ⊗ₜ[crysSheafRing S A] s) =
      secondOrderRightSection A ω •
        moduleSiteRestrict M (secondOrderThickeningSiteQ₀ S A) s :=
  TensorProduct.liftAddHom_tmul _ _ ω s

/-- **On the first middle summand the base change of the sections is the canonical map into that
summand.** -/
theorem extensionSectionsMap_leftTensorMap
    (z : crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) :
    extensionSectionsMap M A (leftTensorMap M A z) = diffActionLeft M A z :=
  tensor_addHom_apply_eq
    (f := (extensionSectionsMap M A).comp (↑(leftTensorMap M A)))
    (g := diffActionLeft M A) (fun _ _ ↦ by simp [diffActionLeft_tmul]) _

/-- **On the second middle summand the base change of the sections is the canonical map into that
summand.** -/
theorem extensionSectionsMap_rightTensorMap
    (z : crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) :
    extensionSectionsMap M A (rightTensorMap M A z) = diffActionRight M A z :=
  tensor_addHom_apply_eq
    (f := (extensionSectionsMap M A).comp (↑(rightTensorMap M A)))
    (g := diffActionRight M A) (fun _ _ ↦ by simp [diffActionRight_tmul]) _

/-- **On the top summand the base change of the sections is the degree-two canonical map of
[Stacks, Tag 07J6].** -/
theorem extensionSectionsMap_topTensorMap
    (w : crysSecondFormSections A ⊗[crysSheafRing S A] M.val.obj (op A)) :
    extensionSectionsMap M A (topTensorMap M A w) = diffAction₂ M A w :=
  tensor_addHom_apply_eq
    (f := (extensionSectionsMap M A).comp (↑(topTensorMap M A)))
    (g := diffAction₂ M A) (fun _ _ ↦ by simp [diffAction₂_tmul]) _

/-- **The degree-two base-change map on global sections of
`Crystalline.GlobalCrystallineSituation.secondOrderSectionsMap` is the base change of the sections
along `q₀`**, read through the splitting
`𝒪_{T''}(T'') = Γ(T, 𝒪_T) ⊕ Ω ⊕ Ω ⊕ Ω²` of [Stacks, Tag 07J3]. -/
theorem extensionSectionsMap_splitTensorEquiv
    (x : M.val.obj (op A) ×
      ((crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) ×
        ((crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) ×
          (crysSecondFormSections A ⊗[crysSheafRing S A] M.val.obj (op A))))) :
    extensionSectionsMap M A (splitTensorEquiv M A x) = secondOrderSectionsMap M A x := by
  obtain ⟨s, z₁, z₂, w⟩ := x
  change extensionSectionsMap M A (splitTensor M A (s, z₁, z₂, w)) = _
  rw [splitTensor_apply, map_add, map_add, map_add, extensionSectionsMap_tmul,
    extensionSectionsMap_leftTensorMap, extensionSectionsMap_rightTensorMap,
    extensionSectionsMap_topTensorMap, one_smul, secondOrderSectionsMap_apply]

/-- **The bijectivity of the degree-two base-change map of [Stacks, Tag 07J3] is the bijectivity
of the base change of the sections along `q₀`.**  Unconditional: the two maps differ by the
additive equivalence that the splitting
`𝒪_{T''}(T'') = Γ(T, 𝒪_T) ⊕ Ω ⊕ Ω ⊕ Ω²` induces. -/
theorem bijective_secondOrderSectionsMap_iff_bijective_extensionSectionsMap :
    Function.Bijective (secondOrderSectionsMap M A) ↔
      Function.Bijective (extensionSectionsMap M A) := by
  have hfun : (secondOrderSectionsMap M A : _ → _) =
      (extensionSectionsMap M A) ∘ (splitTensorEquiv M A) :=
    funext fun x ↦ (extensionSectionsMap_splitTensorEquiv M A x).symm
  have hinv : (extensionSectionsMap M A : _ → _) =
      (secondOrderSectionsMap M A) ∘ (splitTensorEquiv M A).symm := by
    refine funext fun t ↦ ?_
    change _ = secondOrderSectionsMap M A ((splitTensorEquiv M A).symm t)
    rw [← extensionSectionsMap_splitTensorEquiv M A, AddEquiv.apply_symm_apply]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [hinv]
    exact h.comp (splitTensorEquiv M A).symm.bijective
  · rw [hfun]
    exact h.comp (splitTensorEquiv M A).bijective

/-! ### Integrability on an affine object -/

section Affine

variable [IsAffine A.thickening.target.scheme] [(ambientSchemeModules M A).IsQuasicoherent]

/-- **The degree-two base-change map of [Stacks, Tag 07J3] is bijective** for a crystal on an
object whose ambient scheme is affine and with `F_T` quasi-coherent: the sections of `F` over the
second-order universal thickening are the base change of the sections over the object.  This is
the degree-two analogue of
`Crystalline.GlobalCrystallineSituation.bijective_firstOrderSectionsMap_of_isSheafCrystal`. -/
theorem bijective_secondOrderSectionsMap (hM : IsSheafCrystal M) :
    Function.Bijective (secondOrderSectionsMap M A) :=
  (bijective_secondOrderSectionsMap_iff_bijective_extensionSectionsMap M A).mpr
    (bijective_extensionSectionsMap M A hM)

/-- **The degree-two base-change map of [Stacks, Tag 07J3] is injective** for a crystal on an
object whose ambient scheme is affine and with `F_T` quasi-coherent.  This is the degree-two input
of clause C5 of [Stacks, Tag 07J6], obtained from the source's own crystal hypothesis rather than
assumed. -/
theorem injective_secondOrderSectionsMap (hM : IsSheafCrystal M) :
    Function.Injective (secondOrderSectionsMap M A) :=
  (bijective_secondOrderSectionsMap M A hM).injective

/-- **The degree-two canonical map of [Stacks, Tag 07J6] is injective** for a crystal on an object
whose ambient scheme is affine and with `F_T` quasi-coherent, being the restriction of the
degree-two base-change map to the top summand.  This is what lets the outcome of the source's
integrability computation be read inside `Ω² ⊗_D M`. -/
theorem injective_diffAction₂ (hM : IsSheafCrystal M) :
    Function.Injective (diffAction₂ M A) :=
  injective_diffAction₂_of_injective M A (injective_secondOrderSectionsMap M A hM)

/-- **Integrability of the canonical connection of [Stacks, Lemma 60.15.1, Tag 07J6], for a
sheaf crystal on an object with affine ambient scheme.**  The connection
`∇(s) = p₁^* s - p₀^* s` of [Stacks, Tag 07J2], read inside `Ω ⊗_D M` through the degree-one
identification `Crystalline.GlobalCrystallineSituation.firstOrderIdealBaseChangeOfIsSheafCrystal`,
composes with its own degree-one extension `∇(ω ⊗ s) = ∇(s) ∧ ω + (d ω) ⊗ s` of §07J5 to zero.

Both inputs of
`Crystalline.GlobalCrystallineSituation.crystalConnectionTensor_comp_self_eq_zero` are theorems
here: the degree-one identification is
`Crystalline.GlobalCrystallineSituation.firstOrderIdealBaseChangeOfIsSheafCrystal` and the
degree-two injectivity is
`Crystalline.GlobalCrystallineSituation.SecondOrderAffine.injective_diffAction₂`.  The hypotheses
are the crystal condition, which is the source's own, together with affineness of the ambient
scheme of the object, which is not: the source states the clause for every object, and the reason
this spelling needs an affine one is recorded in the module documentation.  No `@[stacks]`
attribute, for that reason. -/
theorem crystalConnectionTensor_comp_self_eq_zero_of_isSheafCrystal (hM : IsSheafCrystal M)
    (s : M.val.obj (op A)) :
    extendedConnectionTensor M A (firstOrderIdealBaseChangeOfIsSheafCrystal M A hM)
        (crystalConnectionTensor M A (firstOrderIdealBaseChangeOfIsSheafCrystal M A hM) s) = 0 :=
  crystalConnectionTensor_comp_self_eq_zero M A
    (firstOrderIdealBaseChangeOfIsSheafCrystal M A hM) (injective_diffAction₂ M A hM) s

end Affine

end SecondOrderAffine

end Crystalline.GlobalCrystallineSituation

end

end
