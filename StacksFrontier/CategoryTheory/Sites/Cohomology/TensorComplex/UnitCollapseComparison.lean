module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCompositionUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DiagonalUnitality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorRightUnitor
import StacksCore.Tactic.StacksAttribute

/-! # The two collapses of the total tensor product against the structure sheaf agree

Let `(C, O)` be a ringed site and `W` a complex of `O`-modules. This development builds the
total tensor product of `W` with the structure sheaf placed in degree zero twice, and
trivialises it twice:

* `AlgebraicGeometry.RingedSite.tensorTotalStructureSheafCollapse`, the morphism
  `Tot(W ⊗_O O[0]) ⟶ W` out of `AlgebraicGeometry.RingedSite.tensorTotal` — which totalises the
  bicomplex of presheaf tensor products and sheafifies afterwards — built as the composition
  morphism of Stacks 0A91 at `K = L = O[0]`. This is the collapse the unit law of the derived
  composition morphism of Stacks 0A98 is proved against.
* `Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections`, the isomorphism
  `Tot(W ⊗_O O[0]) ≅ W` out of `Stacks.SheafOfModules.Tensor.tensorComplex` — which sheafifies
  degreewise and totalises afterwards — built as the single-row comparison
  `CochainComplex.KFlatBifunctor.totalSingleIso` followed by the termwise unit law. This is the
  collapse the unit law `Stacks.SheafOfModules.DerivedTensorProduct.unitIso` of the derived
  tensor product is built on.

The two live over different objects, so they cannot be equal on the nose; the comparison of the
two total complexes is `AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex`. This file
proves that the two collapses agree across it, so that a composite written against either one
can be rewritten against the other.

The section "What this file does not contain" of
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/DerivedCompositionUnit.lean` records
this as unproved separate work: "The collapse `tensorTotalStructureSheafCollapse` is not
compared with `Stacks.SheafOfModules.tensorComplexUnitIso` ... Both collapses are isomorphisms
and both are inverse to formation of the pure tensor with `1`, so they agree; but
`tensorComplexUnitIso` is assembled from `CochainComplex.KFlatBifunctor.totalSingleIso` and
`Stacks.SheafOfModules.rowComplexUnitIso` and has no description on local sections, and
supplying one is a separate piece of work." That description is the first result below.

## Main results

* `Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections_inv_f`: **the missing degreewise
  description of the second collapse.** In degree `n` the inverse of the unit law is the
  degreewise right unit constraint read backwards, followed by the inclusion of the summand of
  bidegree `(n, 0)` — the only summand of total degree `n` that does not vanish.
* `AlgebraicGeometry.RingedSite.tensorComplexUnitIsoFreeSections_inv_val_app`: the same on local
  sections, where it is formation of the pure tensor with the unit section.
* `RingedSite.tensorComplexUnitIsoFreeSections_inv_comp_tensorTotalIsoTensorComplex_inv`: **the
  two collapses agree, read backwards**: the pure tensor with `1` of the second construction,
  carried along the comparison of the two total complexes, is the pure tensor with `1` of the
  first, `AlgebraicGeometry.RingedSite.tensorTotalStructureSheafUnit`.
* `AlgebraicGeometry.RingedSite.tensorTotalStructureSheafCollapse_eq`: **the two collapses
  agree**, in the form a rewrite consumes: the collapse of Stacks 0A91 is the comparison of the
  two total complexes followed by the unit law of the tensor product.
* `AlgebraicGeometry.RingedSite.tensorTotalUnitIso_eq`: the same as an equality of
  isomorphisms.

## Implementation notes

Nothing here is a new construction, and no total-complex bookkeeping is redone. The degreewise
description of the second collapse is the summandwise description
`Stacks.Sheaves.DerivedPullback.totalSingleIso_inv_f` of the single-row comparison for an
arbitrary additive bifunctor, together with the observation that the termwise unit law is the
degreewise one in each degree. The comparison of the two collapses is then the degreewise
collapse `AlgebraicGeometry.RingedSite.unitRightComponent` — which is *defined* as the right
unit constraint read backwards, the summand inclusion, and the comparison of the two total
complexes, in that order — together with
`AlgebraicGeometry.RingedSite.diagonalTensorUnit_f`, which identifies it with the diagonal of
Stacks 0A93 at the structure sheaf followed by evaluation at the unit section. That composite
is `AlgebraicGeometry.RingedSite.tensorTotalStructureSheafUnit`, whose inverse is the collapse
of Stacks 0A91 by `AlgebraicGeometry.RingedSite.tensorTotalUnitIso`. So the whole file is an
identity between morphisms already in the library.

The degreewise right unit constraint is spelled
`Stacks.SheafOfModules.Tensor.sheafTensorUnitIsoRight`, which is the same term as
`Stacks.SheafOfModules.sheafTensorUnitIsoFreeSections` — the constraint
`tensorComplexUnitIsoFreeSections` is itself built from — by `rfl`; the first spelling is used
because it is the one carrying the local-section formulas
(`AlgebraicGeometry.RingedSite.sheafTensorUnitIsoRight_inv_apply`) and the one
`unitRightComponent` is stated with.

The proofs are chains of `Eq.trans` and `congrArg` rather than rewrites. In
`CochainComplex (SheafOfModules …)` the two spellings of the total tensor complex are
definitionally equal only at default transparency, so a composite carrying both is a term in
which `rw` and `simp only` cannot find `Category.assoc`; term-mode chains are checked at the
transparency where the seam is invisible.

## References

* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 0A93](https://stacks.math.columbia.edu/tag/0A93)
* [Stacks Project, Tag 0A98](https://stacks.math.columbia.edu/tag/0A98)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe v u w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (S : Sheaf J CommRingCat.{w}) [HasSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(Tensor.sheafTensor.{u, v, w} S).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, v, w} S).obj M).Additive]
  [∀ (K L : CochainComplex (_root_.SheafOfModules.{w} (Tensor.ringSheaf S)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Tensor.sheafTensor S) (ComplexShape.up ℤ)]

section

omit [∀ M : _root_.SheafOfModules.{w} (Tensor.ringSheaf S),
    ((Tensor.sheafTensor.{u, v, w} S).obj M).Additive]
  [∀ (K L : CochainComplex (_root_.SheafOfModules.{w} (Tensor.ringSheaf S)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Tensor.sheafTensor.{u, v, w} S) (ComplexShape.up ℤ)]

/-- The termwise unit law `(p ↦ K^p ⊗_O O) ≅ K` in a single degree is the degreewise unit law
of the tensor product there. This is `rowComplexUnitIso_hom_f` of
`DerivedPullback/DerivedPullbackTensorRightUnitor.lean` (in
`StacksFrontier/CategoryTheory/Sites/Cohomology/`) at a free universe of the sections, and with
the right unit constraint spelled as the plain composite
`Stacks.SheafOfModules.Tensor.sheafTensorUnitIsoRight` rather than through the re-seated
monoidal structure. -/
private lemma rowComplexUnitIsoFreeSections_hom_f
    (K : CochainComplex (_root_.SheafOfModules.{w} (Tensor.ringSheaf S)) ℤ) (n : ℤ) :
    (rowComplexUnitIsoFreeSections S K).hom.f n =
      (Tensor.sheafTensorUnitIsoRight.{u, v, w} S (K.X n)).hom := Category.comp_id _

/-- The termwise unit law read backwards in a single degree. -/
private lemma rowComplexUnitIsoFreeSections_inv_f
    (K : CochainComplex (_root_.SheafOfModules.{w} (Tensor.ringSheaf S)) ℤ) (n : ℤ) :
    (rowComplexUnitIsoFreeSections S K).inv.f n =
      (Tensor.sheafTensorUnitIsoRight.{u, v, w} S (K.X n)).inv :=
  congrArg Iso.inv
    (Iso.ext (rowComplexUnitIsoFreeSections_hom_f S K n) :
      (HomologicalComplex.eval (_root_.SheafOfModules.{w} (Tensor.ringSheaf S))
          (ComplexShape.up ℤ) n).mapIso (rowComplexUnitIsoFreeSections S K) =
        Tensor.sheafTensorUnitIsoRight.{u, v, w} S (K.X n))

end

/-- **The inverse of the unit law `Tot(K ⊗_O O[0]) ≅ K` of Tag 06YM, in a single degree**: it is
the degreewise right unit constraint read backwards, followed by the inclusion of the summand of
bidegree `(n, 0)`.

This is the description on a summand that `tensorComplexUnitIsoFreeSections` was lacking. Its
two halves are the summandwise description `Stacks.Sheaves.DerivedPullback.totalSingleIso_inv_f`
of the single-row comparison for an arbitrary additive bifunctor — whose transport of the
degree-zero term of `O[0]` to `O` is an identity, that degree being zero — and the degreewise
form of the termwise unit law. -/
lemma tensorComplexUnitIsoFreeSections_inv_f
    (K : CochainComplex (_root_.SheafOfModules.{w} (Tensor.ringSheaf S)) ℤ) (n : ℤ) :
    (tensorComplexUnitIsoFreeSections S K).inv.f n =
      (Tensor.sheafTensorUnitIsoRight.{u, v, w} S (K.X n)).inv ≫
        HomologicalComplex.ιMapBifunctor K
          ((HomologicalComplex.single (_root_.SheafOfModules.{w} (Tensor.ringSheaf S))
            (ComplexShape.up ℤ) 0).obj (_root_.SheafOfModules.unit (Tensor.ringSheaf S)))
          (Tensor.sheafTensor S) (ComplexShape.up ℤ) n 0 n (add_zero n) := by
  have hmap : ((Tensor.sheafTensor.{u, v, w} S).obj (K.X n)).map
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
          (_root_.SheafOfModules.unit (Tensor.ringSheaf S))).inv =
      𝟙 (((Tensor.sheafTensor.{u, v, w} S).obj (K.X n)).obj
        (_root_.SheafOfModules.unit (Tensor.ringSheaf S))) :=
    CategoryTheory.Functor.map_id _ _
  refine (congrArg (· ≫ _) (rowComplexUnitIsoFreeSections_inv_f S K n)).trans
    (congrArg (_ ≫ ·) ?_)
  exact (Stacks.Sheaves.DerivedPullback.totalSingleIso_inv_f (Tensor.sheafTensor.{u, v, w} S) K
    (_root_.SheafOfModules.unit (Tensor.ringSheaf S)) n).trans
    ((congrArg (· ≫ _) hmap).trans (Category.id_comp _))

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSite

open Stacks.SheafOfModules.Tensor

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

variable (X : RingedSite.{u, u, u})
  [(sheafTensor.{u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u} X.O) (ComplexShape.up ℤ)]
  (W : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **The inverse of the unit law `Tot(W ⊗_O O[0]) ≅ W` on local sections**: it carries a
homogeneous local section `w` of degree `n` to the local pure tensor `w ⊗ 1`.

This is `Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections_inv_f` read on sections, the
right unit constraint read backwards being formation of the pure tensor with the unit section
(`AlgebraicGeometry.RingedSite.sheafTensorUnitIsoRight_inv_apply`) and the pure tensor of
`Stacks.SheafOfModules.Tensor.tensorComplex` being the sheafification unit followed by the
inclusion of a summand. -/
lemma tensorComplexUnitIsoFreeSections_inv_val_app (n : ℤ) (U : X.C)
    (w : (W.X n).val.obj (op U)) :
    (((Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections X.O W).inv.f n).val.app (op U)) w =
      tensorComplexSection X n 0 n (add_zero n) w (structureSheafOne X U) :=
  (congrArg (fun z : W.X n ⟶ ((((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj W).obj
        (structureSheafComplex X)).X n) => z.val.app (op U) w)
      (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections_inv_f X.O W n)).trans
    (congrArg ((HomologicalComplex.ιMapBifunctor W (structureSheafComplex X)
        (sheafTensor.{u, u, u} X.O) (ComplexShape.up ℤ) n 0 n (add_zero n)).val.app (op U))
      (sheafTensorUnitIsoRight_inv_apply X (W.X n) (op U) w))

/-- **The two collapses of `Tot(W ⊗_O O[0])` agree, read backwards.** The inverse of the unit
law of `Stacks.SheafOfModules.Tensor.tensorComplex`, followed by the comparison of the two total
tensor complexes, is the pure tensor with the unit section
`AlgebraicGeometry.RingedSite.tensorTotalStructureSheafUnit` — the diagonal morphism of
Stacks 0A93 at the structure sheaf followed by evaluation at the unit section.

Degreewise the left-hand side is
`AlgebraicGeometry.RingedSite.unitRightComponent`, by
`Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections_inv_f`, and
`AlgebraicGeometry.RingedSite.diagonalTensorUnit_f` identifies that with the right-hand side. -/
theorem tensorComplexUnitIsoFreeSections_inv_comp_tensorTotalIsoTensorComplex_inv :
    (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections X.O W).inv ≫
        (tensorTotalIsoTensorComplex X W (structureSheafComplex X)).inv =
      tensorTotalStructureSheafUnit X W := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine Eq.trans (show ((Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections X.O W).inv ≫
      (tensorTotalIsoTensorComplex X W (structureSheafComplex X)).inv).f n =
        (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections X.O W).inv.f n ≫
          (tensorTotalIsoTensorComplex X W (structureSheafComplex X)).inv.f n from rfl) ?_
  refine Eq.trans (congrArg
    (fun z => z ≫ (tensorTotalIsoTensorComplex X W (structureSheafComplex X)).inv.f n)
    (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections_inv_f X.O W n)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact (diagonalTensorUnit_f X (A := W) n).symm

/-- **The two collapses of `Tot(W ⊗_O O[0])` agree.** The collapse
`AlgebraicGeometry.RingedSite.tensorTotalStructureSheafCollapse` — the composition morphism of
Stacks 0A91 at `K = L = O[0]`, against which the unit law of the derived composition morphism of
Stacks 0A98 is proved — is the comparison of the two total tensor complexes followed by the unit
law `Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections` of the tensor product, on which the
unit law `Stacks.SheafOfModules.DerivedTensorProduct.unitIso` of the derived tensor product is
built.

This is the form a rewrite consumes: it replaces a composite written against the first collapse
by one written against the second. Both collapses are inverse to formation of the pure tensor
with `1`, and `tensorComplexUnitIsoFreeSections_inv_comp_tensorTotalIsoTensorComplex_inv` says
so; what remains is to invert. -/
theorem tensorTotalStructureSheafCollapse_eq :
    tensorTotalStructureSheafCollapse X W =
      (tensorTotalIsoTensorComplex X W (structureSheafComplex X)).hom ≫
        (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections X.O W).hom :=
  congrArg Iso.inv
    (Iso.ext (tensorComplexUnitIsoFreeSections_inv_comp_tensorTotalIsoTensorComplex_inv X W).symm :
      tensorTotalUnitIso X W =
        (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections X.O W).symm ≪≫
          (tensorTotalIsoTensorComplex X W (structureSheafComplex X)).symm)

/-- **The two collapses of `Tot(W ⊗_O O[0])` agree, as isomorphisms.**
`AlgebraicGeometry.RingedSite.tensorTotalUnitIso` is the unit law
`Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections` of the tensor product read backwards,
followed by the comparison of the two total tensor complexes read backwards. -/
theorem tensorTotalUnitIso_eq :
    tensorTotalUnitIso X W =
      (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections X.O W).symm ≪≫
        (tensorTotalIsoTensorComplex X W (structureSheafComplex X)).symm :=
  Iso.ext (tensorComplexUnitIsoFreeSections_inv_comp_tensorTotalIsoTensorComplex_inv X W).symm

end AlgebraicGeometry.RingedSite

end
