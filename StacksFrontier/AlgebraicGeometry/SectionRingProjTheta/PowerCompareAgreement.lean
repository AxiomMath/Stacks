module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjTheta.SectionRingComparison
public import StacksFrontier.AlgebraicGeometry.Constructions.CoherentMulSections
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Recursion
public import StacksFrontier.AlgebraicGeometry.GradedSectionRing.CoherentNormalisation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence

/-!
# The two comparisons of the tensor-power families of an invertible sheaf of modules agree

Let `𝒪` be a sheaf of commutative rings on a site and `L` an invertible sheaf of `𝒪`-modules.
The iterated tensor products `Stacks.TensorPowers.natTensorPow` of `L` are compared with the
integer tensor powers `Stacks.SheafOfModules.TensorPower.tensorPower` of [Stacks, Tag 01CU] in
nonnegative degree by `Stacks.SectionRingProjTheta.powIso`, built from
`Stacks.PowerFamilyBridge.natIso`, and by `Stacks.SheafOfModules.Invertible.tensorPowerCompare`,
built from `Stacks.Monoidal.PowerSystem.compare`. The two comparisons are the same isomorphism.

## Main results

* `Stacks.SectionRingProjTheta.powIso_eq_tensorPowerCompare`: the two comparisons agree in every
  nonnegative degree.
* `Stacks.SectionRingProjTheta.powIso_succ` and
  `Stacks.SheafOfModules.Invertible.tensorPowerCompare_succ`: the successor clauses of the two
  comparisons — one more copy of `L` whiskered in, then the successor comparison of Tag 01CU's
  powers.
* `Stacks.SheafOfModules.Invertible.tensorIso_eq_tensorObjIso`: the two identifications
  `AlgebraicGeometry.SheafOfModules.tensorIso` and `Stacks.SheafOfModules.tensorObjIso` of a
  monoidal tensor product of sheaves of modules with the tensor product sheaf of [Stacks, Tag
  01CA] agree.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory Category MonoidalCategory Limits Opposite
open Stacks.SheafOfModules.TensorSheafification
open Stacks.TensorPowers (natTensorPow)

universe v u w

namespace Stacks.Monoidal

/-- A whiskering, an identity and a tensor product with an identity compose to the whiskering of
the composite. -/
theorem whiskerRightIso_trans_tensorIso_refl {D : Type u} [Category.{v} D] [MonoidalCategory D]
    {A B E T : D} (a : A ≅ B) (b : B ≅ E) (G : D) (X : E ⊗ G ≅ T) :
    whiskerRightIso a G ≪≫ (Iso.refl (B ⊗ G)).symm ≪≫ tensorIso b (Iso.refl G) ≪≫ X
      = whiskerRightIso (a ≪≫ b) G ≪≫ X :=
  Iso.ext <| by simp only [Iso.trans_hom, Iso.symm_hom, Iso.refl_inv, whiskerRightIso_hom,
    tensorIso_hom, Iso.refl_hom, tensorHom_id, Category.id_comp, Category.assoc, comp_whiskerRight]

end Stacks.Monoidal

namespace Stacks.SheafOfModules.Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.braidedCategory

/-- **The identification of the localized tensor product with the tensor product sheaf, on
components.** `AlgebraicGeometry.SheafOfModules.tensorIso` is the tensor product of the inverses
of the two sheafification counits followed by the monoidality isomorphism
`Stacks.SheafInternalHom.tensorSheafifyIso` of sheafification. -/
theorem tensorIso_hom_eq (F G : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :
    (AlgebraicGeometry.SheafOfModules.tensorIso 𝒪 h𝒪 F G).hom
      = ((Stacks.SheafOfModules.sheafifyValIso 𝒪 h𝒪 F).inv ⊗ₘ
            (Stacks.SheafOfModules.sheafifyValIso 𝒪 h𝒪 G).inv) ≫
          ((Stacks.SheafInternalHom.tensorSheafifyIso 𝒪 h𝒪 F.val).app G.val).hom := by
  simp only [AlgebraicGeometry.SheafOfModules.tensorIso, SheafInternalHom.tensorLeftIso,
    structureSheaf_obj, Functor.id_obj, SheafInternalHom.sheafifyCounitIso, sheafifyValIso,
    Iso.app_inv]
  rfl

/-- **The two identifications of a tensor product of sheaves of modules with the tensor product
sheaf of [Stacks, Tag 01CA] agree.** `AlgebraicGeometry.SheafOfModules.tensorIso` is stated for
`Stacks.SheafInternalHom.monoidalCategory` and `Stacks.SheafOfModules.tensorObjIso` for
`Stacks.SheafOfModules.monoidalCategory`. -/
theorem tensorIso_eq_tensorObjIso (F G : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :
    AlgebraicGeometry.SheafOfModules.tensorIso 𝒪 h𝒪 F G
      = Stacks.SheafOfModules.tensorObjIso 𝒪 h𝒪 F G :=
  Iso.ext ((tensorIso_hom_eq 𝒪 h𝒪 F G).trans
    (Stacks.SheafOfModules.tensorObjIso_hom_eq 𝒪 h𝒪 F G).symm)

variable (L : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))
  [AlgebraicGeometry.SheafOfModules.IsInvertible 𝒪 h𝒪 L]

open Stacks.SheafOfModules.TensorPower (tensorPower)

/-- **The successor clause of the comparison of the iterated tensor products with the integer
tensor powers of [Stacks, Tag 01CU].** The comparison in degree `k + 1` is the comparison in
degree `k` whiskered by one more copy of `L`, followed by the successor comparison of Tag 01CU's
powers read through the identification of the tensor product with the tensor product sheaf. -/
theorem tensorPowerCompare_succ (k : ℕ) :
    tensorPowerCompare 𝒪 h𝒪 L (k + 1)
      = whiskerRightIso (tensorPowerCompare 𝒪 h𝒪 L k) L ≪≫
          Stacks.SheafOfModules.tensorObjIso 𝒪 h𝒪 (tensorPower 𝒪 h𝒪 L (k : ℤ)) L ≪≫
          tensorPowerSuccIso 𝒪 h𝒪 L (k : ℤ) :=
  @Stacks.Monoidal.whiskerRightIso_trans_tensorIso_refl _ _
    (Stacks.SheafOfModules.monoidalCategory 𝒪 h𝒪) _ _ _ _
    (natTensorPowUnitShift 𝒪 h𝒪 L k) (natTensorPowCompare 𝒪 h𝒪 L k) L
    (Stacks.SheafOfModules.tensorObjIso 𝒪 h𝒪 (tensorPower 𝒪 h𝒪 L (k : ℤ)) L ≪≫
      tensorPowerSuccIso 𝒪 h𝒪 L (k : ℤ))

end Stacks.SheafOfModules.Invertible

namespace Stacks.SectionRingProjTheta

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.braidedCategory

variable (L : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))
  [AlgebraicGeometry.SheafOfModules.IsInvertible 𝒪 h𝒪 L]

open AlgebraicGeometry.SheafOfModules (tensorIso)
open Stacks.SheafOfModules.TensorPower (tensorPower)

/-- **The successor clause of the section-ring bridge's comparison of the two tensor-power
families.** `powIso` in degree `k + 1` is `powIso` in degree `k` whiskered by one more copy of
`L`, followed by the successor comparison of Tag 01CU's powers read through
`AlgebraicGeometry.SheafOfModules.tensorIso`. -/
theorem powIso_succ (k : ℕ) :
    powIso 𝒪 h𝒪 L (k + 1)
      = whiskerRightIso (powIso 𝒪 h𝒪 L k) L ≪≫
          tensorIso 𝒪 h𝒪 (tensorPower 𝒪 h𝒪 L (k : ℤ)) L ≪≫
          Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso 𝒪 h𝒪 L (k : ℤ) := rfl

/-- **The two comparisons of the iterated tensor products of an invertible sheaf of modules with
the integer tensor powers of [Stacks, Tag 01CU] are the same isomorphism, in every nonnegative
degree.** On one side `powIso`, built from `Stacks.PowerFamilyBridge.natIso`; on the other
`Stacks.SheafOfModules.Invertible.tensorPowerCompare`, the comparison of the two power
systems. -/
theorem powIso_eq_tensorPowerCompare : ∀ n : ℕ,
    powIso 𝒪 h𝒪 L n = Stacks.SheafOfModules.Invertible.tensorPowerCompare 𝒪 h𝒪 L n
  | 0 => rfl
  | n + 1 => by
      rw [powIso_succ, Stacks.SheafOfModules.Invertible.tensorPowerCompare_succ,
        powIso_eq_tensorPowerCompare n,
        Stacks.SheafOfModules.Invertible.tensorIso_eq_tensorObjIso,
        Stacks.SheafOfModules.Invertible.tensorPowerSuccIso_eq_tensorPowerSuccIso]
      rfl

end Stacks.SectionRingProjTheta

end
