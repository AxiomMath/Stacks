module

public import StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.Reseat
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.MulIsomorphism
public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.Evaluation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridgeSuccIso

/-!
# The two trivialisations of `L ⊗ L^{⊗ -1}` are the same multiplication

Tag 0B3V's inverse-line factor is pinned, on one side, against
`Stacks.ProjBundleInverseBaseChange.negOneMulIso'` and, on the other, against
`Stacks.SheafOfModules.Invertible.mulNegOneIso`. Both trivialise `L ⊗ L^{⊗ -1}`, both are built
out of Tag 01CU's successor comparison and the commutativity constraint of the tensor product
sheaf, and they were built independently: `negOneMulIso'` reads the successor comparison in the
order `L^{⊗ -1} ⊗ L` and brings `L ⊗ L^{⊗ -1}` to it by the braiding, while `mulNegOneIso`
braids first, in the degrees `(1, -1)`, and corrects the first factor by `L ≅ L^{⊗ 1}` on each
side. **This file identifies them.**

## Main results

* `Stacks.SheafOfModules.Invertible.tensorProductBraiding_naturality`: the commutativity
  constraint of the tensor product sheaf of [Stacks, Tag 01CA] is natural in both variables at
  once. The repository had the symmetry (`tensorProductBraiding_hom_comp`) and the self-braiding
  of an invertible module, but not naturality.
* `Stacks.SheafOfModules.Invertible.tensorProductBraiding_tensorPowerOneIso`: **the braiding in
  degrees `(1, -1)`, conjugated by `L ≅ L^{⊗ 1}`, is the braiding at `L`.** Naturality in both
  variables moves the conjugation across the braiding, where the two copies of `L ≅ L^{⊗ 1}`
  then meet in the same factor and cancel.
* `Stacks.SheafOfModules.Invertible.mulNegOneIso_hom_eq`: **Tag 01CU's multiplication at
  `(1, -1)`, read on `L ⊗ L^{⊗ -1}`, is the braiding followed by the successor comparison and
  the reindexing** — the `L ≅ L^{⊗ 1}` conjugation of
  `Stacks.SheafOfModules.Invertible.tensorPowerMulIsoNegOne` contributes nothing.
* `Stacks.SheafOfModules.Invertible.negOneMulIso_tail_eq`: the same composite written with the
  step maps of the *other* development of the integer tensor powers, which is the one
  `negOneMulIso'` is built from.
* `Stacks.ProjBundleInverseBaseChange.negOneMulIso'_eq`: **the identification.**
  `negOneMulIso'`, whose source and target are the tensor product and the unit of
  `Stacks.SheafInternalHom.monoidalCategory`, is `mulNegOneIso` conjugated by
  `AlgebraicGeometry.SheafOfModules.tensorIso` on its source and
  `AlgebraicGeometry.SheafOfModules.unitIso` on its target — that is, by exactly the comparisons
  `CategoryTheory.MonoidalCategory.reseatIso` and `ε` of
  `StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.Reseat`.

## Route

The identification is available on sections
(`Stacks.ProjectiveBundleConormal.sectionMulNegOne_eq_negOneMulIso`), but it is not obtained by
promoting that from sections to morphisms: **no section is needed.** The whole content is
the naturality of the braiding of the tensor product sheaf, and that is one application of
`CategoryTheory.BraidedCategory.braiding_naturality` to the *presheaves* underneath: both
`tensorProductBraiding` and `tensorProductIso` are `Stacks.SheafOfModules.Invertible.sheafify`
applied to a morphism of presheaves of modules, so a `change` into that spelling followed by
`CategoryTheory.Functor.map_comp` reduces naturality at the sheaf level to naturality at the
presheaf level, where it is a Mathlib lemma. No descent to sections, and no braiding of sheaves
of modules — the presheaf braiding is the only one that enters.

Two crossings are paid on the way, and neither is a `rfl` that `rw` can take:

* The two developments of the integer tensor powers of Tag 01CU — the one under
  `Stacks.SheafOfModules.Invertible` and the one under `Stacks.SheafOfModules.TensorPower` —
  build their successor and reindexing comparisons from their own copies of the iterate
  calculus. `mulNegOneIso` uses the first and `negOneMulIso'` the second. The bridges
  `Stacks.SheafOfModules.Invertible.tensorPowerSuccIso_eq` and `tensorPowerReindex_eq` are what
  cross them.
* `Stacks.SheafOfModules.TensorPower.tensorPower 𝒪 h𝒪 L 0` and `SheafOfModules.unit` are equal
  by `rfl`, so `negOneMulIso`'s closing `eqToHom` is the identity by proof irrelevance — but the
  two objects are not *syntactically* equal, so a goal mentioning both is not type-correct at
  `implicit` transparency and neither `rw [Category.comp_id]` nor `simp` will remove it. It is
  removed by `tailAux`, over a bare category, where `exact` checks the crossing at default
  transparency instead.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory MonoidalCategory AlgebraicGeometry
open Stacks.SheafOfModules.TensorSheafification Stacks.TensorPowers Stacks.SheafOfModules
open Stacks.SheafOfModules.TensorPower
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)

universe v u w

namespace Stacks.SheafOfModules.Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The commutativity constraint of the tensor product sheaf is natural in both variables at
once.** Tensoring a pair of isomorphisms and then braiding is braiding and then tensoring the
pair the other way round.

`Stacks.SheafOfModules.Invertible.tensorProductBraiding` and `tensorProductIso` are both
`Stacks.SheafOfModules.TensorSheafification.sheafify` applied to a morphism of the underlying
presheaves of modules, so this is `CategoryTheory.BraidedCategory.braiding_naturality` for
presheaves of modules carried through that functor. -/
theorem tensorProductBraiding_naturality
    {M M' N N' : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)} (e : M ≅ M') (f : N ≅ N') :
    (tensorProductIso 𝒪 h𝒪 e f).hom ≫ (tensorProductBraiding 𝒪 h𝒪 M' N').hom =
      (tensorProductBraiding 𝒪 h𝒪 M N).hom ≫ (tensorProductIso 𝒪 h𝒪 f e).hom := by
  let : MonoidalCategory (PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := 𝒪)
  let : SymmetricCategory (PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj) :=
    PresheafOfModulesOfCommRing.symmetricCategory (R := 𝒪)
  show (sheafify 𝒪 h𝒪).map (e.hom.val ⊗ₘ f.hom.val) ≫
      (sheafify 𝒪 h𝒪).map (β_ M'.val N'.val).hom =
    (sheafify 𝒪 h𝒪).map (β_ M.val N.val).hom ≫
      (sheafify 𝒪 h𝒪).map (f.hom.val ⊗ₘ e.hom.val)
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg _ (BraidedCategory.braiding_naturality _ _)

variable (L : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))
  [AlgebraicGeometry.SheafOfModules.IsInvertible 𝒪 h𝒪 L]

/-- **The braiding of `L^{⊗ 1} ⊗ L^{⊗ -1}`, conjugated by `L ≅ L^{⊗ 1}` on the way in and on
the way out, is the braiding of `L ⊗ L^{⊗ -1}`.** This is the conjugation that
`Stacks.SheafOfModules.Invertible.tensorPowerMulIsoNegOne` carries, because Tag 01CU's
multiplication is indexed by degrees and `L` itself is not one; naturality of the braiding in
both variables puts the two copies of `L ≅ L^{⊗ 1}` in the same tensor factor, where they
cancel. -/
theorem tensorProductBraiding_tensorPowerOneIso :
    tensorProductIso 𝒪 h𝒪 (tensorPowerOneIso 𝒪 h𝒪 L).symm
          (Iso.refl (tensorPower 𝒪 h𝒪 L (-1))) ≪≫
        tensorProductBraiding 𝒪 h𝒪 (tensorPower 𝒪 h𝒪 L 1) (tensorPower 𝒪 h𝒪 L (-1)) ≪≫
          tensorProductIso 𝒪 h𝒪 (Iso.refl (tensorPower 𝒪 h𝒪 L (-1)))
            (tensorPowerOneIso 𝒪 h𝒪 L) =
      tensorProductBraiding 𝒪 h𝒪 L (tensorPower 𝒪 h𝒪 L (-1)) := by
  refine Iso.ext ?_
  rw [Iso.trans_hom, Iso.trans_hom, ← Category.assoc, tensorProductBraiding_naturality,
    Category.assoc, ← Iso.trans_hom, ← tensorProductIso_trans]
  simp [tensorProductIso_refl]

/-- Replacing the last factor of a three-step composite by an identified composite, over a bare
category. -/
private theorem appendAux {D : Type*} [Category D] {A B E F G : D}
    (a : A ⟶ B) (b : B ⟶ E) (c : E ⟶ F) (u : F ⟶ G) (m : A ⟶ F)
    (h : a ≫ b ≫ c = m) : a ≫ b ≫ c ≫ u = m ≫ u := by
  rw [← h]; simp

/-- **Tag 01CU's multiplication `L ⊗ L^{⊗ -1} ≅ 𝒪` is the braiding followed by the successor
comparison and the reindexing.** `Stacks.SheafOfModules.Invertible.mulNegOneIso` is
`tensorPowerMulIsoNegOne` precomposed with `L ≅ L^{⊗ 1}` in the first factor, and
`tensorPowerMulIsoNegOne` braids in degrees `(1, -1)` and then undoes that comparison in the
second factor; by `tensorProductBraiding_tensorPowerOneIso` the three steps together are the
braiding at `L`.

The reindexing's target is `L^{⊗ 0}`, which is `SheafOfModules.unit` by `rfl`; that is why no
`eqToHom` appears here and one does in `Stacks.ProjBundleInverseBaseChange.negOneMulIso`. -/
theorem mulNegOneIso_hom_eq :
    (mulNegOneIso 𝒪 h𝒪 L).hom =
      (tensorProductBraiding 𝒪 h𝒪 L (tensorPower 𝒪 h𝒪 L (-1))).hom ≫
        (tensorPowerSuccIso 𝒪 h𝒪 L (-1)).hom ≫
          (tensorPowerReindex 𝒪 h𝒪 L (show (-1 : ℤ) + 1 = 0 by omega)).hom := by
  refine Eq.trans (show (mulNegOneIso 𝒪 h𝒪 L).hom =
      (tensorProductIso 𝒪 h𝒪 (tensorPowerOneIso 𝒪 h𝒪 L).symm
          (Iso.refl (tensorPower 𝒪 h𝒪 L (-1)))).hom ≫
        (tensorProductBraiding 𝒪 h𝒪 (tensorPower 𝒪 h𝒪 L 1)
          (tensorPower 𝒪 h𝒪 L (-1))).hom ≫
          (tensorProductIso 𝒪 h𝒪 (Iso.refl (tensorPower 𝒪 h𝒪 L (-1)))
            (tensorPowerOneIso 𝒪 h𝒪 L)).hom ≫
            ((tensorPowerSuccIso 𝒪 h𝒪 L (-1)).hom ≫
              (tensorPowerReindex 𝒪 h𝒪 L (show (-1 : ℤ) + 1 = 0 by omega)).hom) from rfl) ?_
  exact appendAux _ _ _ _ _
    (congrArg Iso.hom (tensorProductBraiding_tensorPowerOneIso 𝒪 h𝒪 L))

/-- `Stacks.SheafOfModules.Invertible.mulNegOneIso_hom_eq` with the braiding and the two step
maps written in the vocabulary `Stacks.ProjBundleInverseBaseChange.negOneMulIso` is built from:
`Stacks.SheafOfModules.tensorSheafBraiding`, which is `tensorProductBraiding` by definition, and
the successor and reindexing comparisons of the `Stacks.SheafOfModules.TensorPower` development
of Tag 01CU, which agree with this one's by
`Stacks.SheafOfModules.Invertible.tensorPowerSuccIso_eq` and `tensorPowerReindex_eq`. -/
theorem negOneMulIso_tail_eq :
    (tensorSheafBraiding 𝒪 h𝒪 L (TensorPower.tensorPower 𝒪 h𝒪 L (-1))).hom ≫
        (TensorPower.tensorPowerSuccIso 𝒪 h𝒪 L (-1)).hom ≫
          (TensorPower.tensorPowerReindex 𝒪 h𝒪 L (show (-1 : ℤ) + 1 = 0 by omega)).hom =
      (mulNegOneIso 𝒪 h𝒪 L).hom := by
  rw [mulNegOneIso_hom_eq, tensorPowerSuccIso_eq, tensorPowerReindex_eq]
  rfl

end Stacks.SheafOfModules.Invertible

namespace Stacks.ProjBundleInverseBaseChange

open Stacks.SheafOfModules.Invertible

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (L : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))
  [Stacks.SheafOfModules.IsInvertible 𝒪 h𝒪 L]

/-- Replacing the head of a composite by an identified composite, dropping an identity and
cancelling the meeting isomorphism of the two trivialisations, over a bare category.
`Stacks.ProjBundleInverseBaseChange.negOneMulIso'` crosses to the tensor product sheaf, braids,
crosses back, and then `negOneMulIso` crosses forward again, so `x.inv` and `x.hom` stand next to
each other in the middle of the composite.

The identity is passed as a hypothesis, and this is a separate step rather than a
`simp only [Iso.inv_hom_id_assoc]` in the application, for the reason that applies to every such
crossing: the two objects the identity sits between, `L^{⊗ 0}` and `SheafOfModules.unit`, are equal
only by `rfl`, and the composite names both the
tensor product of `Stacks.SheafInternalHom.monoidalCategory` and
`Stacks.SheafOfModules.Tensor.sheafTensor`'s value, so it is not type-correct at `implicit`
transparency and neither `rw` nor `simp` can act on it — not even `CategoryTheory.Iso.trans_hom`,
which silently does not fire. Stated over a bare category, there is a single `Category` instance
and the cancellation is available again. -/
private theorem tailCancelAux {D : Type*} [Category D] {A B E F G H I : D} (t : A ⟶ B)
    (a : B ⟶ E) (x : F ≅ E) (b : E ⟶ G) (c : G ⟶ H) (i : H ⟶ H) (u : H ⟶ I) (m : B ⟶ H)
    (hi : i = 𝟙 H) (h : a ≫ b ≫ c = m) :
    t ≫ a ≫ x.inv ≫ x.hom ≫ b ≫ c ≫ i ≫ u = t ≫ m ≫ u := by
  rw [Iso.inv_hom_id_assoc, hi, Category.id_comp, appendAux a b c u m h]

/-- **The left trivialisation of Tag 01CU's `(-1)`st tensor power is Tag 01CU's multiplication
at `(1, -1)`.**

`Stacks.ProjBundleInverseBaseChange.negOneMulIso'` trivialises `L ⊗ L^{⊗ -1}` with its source
and target taken at the tensor product and the unit of
`Stacks.SheafInternalHom.monoidalCategory`;
`Stacks.SheafOfModules.Invertible.mulNegOneIso` trivialises the same product with its source
taken at `Stacks.SheafOfModules.TensorSheafification.tensorSheaf` and its target at
`SheafOfModules.unit`. This says the second is the first, conjugated by
`AlgebraicGeometry.SheafOfModules.tensorIso` and
`AlgebraicGeometry.SheafOfModules.unitIso` — which are
`CategoryTheory.MonoidalCategory.reseatIso` and the unit comparison `ε` of the re-seating that
`StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.Reseat` identifies the monoidal
structure of the conormal construction by.

So the two pins of Tag 0B3V's inverse-line factor —
`Stacks.ProjBundleInverseBaseChange.inverseQuotientBaseChangeIso_evaluation`, stated against
`negOneMulIso'`, and
`Stacks.ProjectiveBundleConormal.inverseTwistBundleBaseChangeIso_tensorHom_comp`, stated against
`Stacks.ProjectiveBundleConormal.invertibleEvaluation`, which *is* `mulNegOneIso` — are pins
against one and the same pairing.

Both sides are a braiding followed by the successor comparison in degree `-1`; the only
discrepancy is the conjugation by `L ≅ L^{⊗ 1}` that the degree-indexed multiplication carries,
and `Stacks.SheafOfModules.Invertible.mulNegOneIso_hom_eq` is where it cancels. -/
theorem negOneMulIso'_eq :
    negOneMulIso' 𝒪 h𝒪 L =
      AlgebraicGeometry.SheafOfModules.tensorIso 𝒪 h𝒪 L (TensorPower.tensorPower 𝒪 h𝒪 L (-1)) ≪≫
        mulNegOneIso 𝒪 h𝒪 L ≪≫ (AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).symm := by
  refine Iso.ext ?_
  exact tailCancelAux
    (AlgebraicGeometry.SheafOfModules.tensorIso 𝒪 h𝒪 L
      (TensorPower.tensorPower 𝒪 h𝒪 L (-1))).hom
    (tensorSheafBraiding 𝒪 h𝒪 L (TensorPower.tensorPower 𝒪 h𝒪 L (-1))).hom
    (AlgebraicGeometry.SheafOfModules.tensorIso 𝒪 h𝒪
      (TensorPower.tensorPower 𝒪 h𝒪 L (-1)) L)
    (TensorPower.tensorPowerSuccIso 𝒪 h𝒪 L (-1)).hom
    (TensorPower.tensorPowerReindex 𝒪 h𝒪 L (show (-1 : ℤ) + 1 = 0 by omega)).hom
    (eqToIso (TensorPower.tensorPower_zero 𝒪 h𝒪 L)).hom
    (AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).symm.hom
    (mulNegOneIso 𝒪 h𝒪 L).hom rfl (negOneMulIso_tail_eq 𝒪 h𝒪 L)

end Stacks.ProjBundleInverseBaseChange

end
