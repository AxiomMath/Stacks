module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Filtered
public import Mathlib.CategoryTheory.Products.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# A direct sum of flat sheaves of modules is flat

Flatness of a sheaf of modules `F` over a sheaf of commutative rings `O` on a site is
exactness of the endofunctor `· ⊗_O F` of `Mod(O)`. This file shows that an arbitrary
direct sum of flat sheaves of modules is flat.

## Main results

* `Stacks.SheafOfModules.FlatCoproduct.isFlat_coproduct`: an arbitrary coproduct of flat sheaves of
  modules is
  flat.
* `Stacks.SheafOfModules.FlatCoproduct.isFlat_colimit`: a colimit of flat sheaves of modules along
  any shape whose
  colimits are exact is flat. For a filtered shape this is Stacks 05NG.

## Implementation notes

Flatness and the colimit argument use the native bifunctor
`Stacks.SheafOfModules.Tensor.sheafTensor` directly, with its right-hand argument fixed.
The monoidal closed structure supplies colimit preservation of that same tensor data;
no comparison between duplicate fixed-factor sheaf functors is used.
The presheaf-level compatibility lemmas below remain separate from this argument.

Preservation of colimits is used in the *second* variable: it says that `· ⊗_O ·` is, as a
functor of its right-hand argument into endofunctors of `Mod(O)`, colimit-preserving, so
that `· ⊗_O (⨁ F i)` is the coproduct of the endofunctors `· ⊗_O F i`. A coproduct of
exact functors is exact because coproducts in `Mod(O)` are exact: filtered colimits of
sheaves of modules are exact (`AlgebraicGeometry.SheafOfModules.instAB5SheafOfModules`,
Tag 03DB), and AB5 implies AB4.

## References

* [Stacks Project, Tag 03EU](https://stacks.math.columbia.edu/tag/03EU)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u w

namespace Stacks.SheafOfModules.FlatCoproduct

open AlgebraicGeometry.SheafOfModules

/-! ### Comparison of the two tensor products -/

section Presheaf

variable {C : Type u} [Category.{v} C]

/-- The objectwise tensor product of presheaves of modules used by the definition of
flatness agrees with the tensor product of Mathlib's monoidal structure on presheaves of
modules: both send an object `X` of the site to `G(X) ⊗_{O(X)} F(X)`, with the same
restriction maps, so the comparison is the identity in each degree. -/
def tensorObjIso (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (G F : PresheafOfModules.{w} (ringPresheaf O)) :
    PresheafOfModules.tensorObj G F ≅ G ⊗ F :=
  _root_.PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
    intro X Y f
    simp only [Iso.refl_hom]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl)

/-- `tensorObjIso` is natural in the left-hand factor, so the two objectwise tensor
endofunctors `· ⊗ F` of presheaves of modules are isomorphic. -/
def tensorRightIso (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (F : PresheafOfModules.{w} (ringPresheaf O)) :
    PresheafOfModules.tensorRight F ≅ (curriedTensor _).flip.obj F :=
  NatIso.ofComponents (fun G ↦ tensorObjIso O G F) (by
    intro G H φ
    apply _root_.PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl)

end Presheaf

section Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})] in
/-- Flatness of a sheaf of modules, restated for `Stacks.SheafOfModules.Tensor.sheafTensor`. -/
lemma isFlat_iff_exactFunctor_sheafTensor (O : Sheaf J CommRingCat.{max u v})
    (F : _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    IsFlat F ↔
      exactFunctor (_root_.SheafOfModules.{max u v} (Tensor.ringSheaf O)) _
        ((Tensor.sheafTensor.{u, v, max u v, max u v, max u v} O).flip.obj F) :=
  Iff.rfl

/-- `· ⊗_O ·`, viewed as a functor of its right-hand argument into endofunctors of
`Mod(O)`, preserves colimits: colimits in a functor category are computed pointwise, and
pointwise this is the statement that each `G ⊗_O ·` preserves colimits, which holds
because `Mod(O)` is monoidal closed. -/
instance preservesColimitsOfShape_sheafTensor_flip (O : Sheaf J CommRingCat.{max u v})
    (K : Type*) [Category K] :
    PreservesColimitsOfShape K
      (Tensor.sheafTensor.{u, v, max u v, max u v, max u v} O).flip :=
  preservesColimitsOfShape_of_evaluation
    (Tensor.sheafTensor.{u, v, max u v, max u v, max u v} O).flip
    K fun G ↦ by
    rw [flip_comp_evaluation]
    exact ⟨fun {diagram} ↦ _root_.SheafOfModules.preservesColimitsOfSize_sheafTensor_obj
      O G diagram⟩

end Sheaf

/-! ### A colimit of exact functors is exact -/

section ExactColimit

variable {A : Type*} [Category* A] {I : Type*} [Category* I]

/-- If colimits of shape `I` in `A` are exact, then a colimit of a diagram of exact
endofunctors of `A` is exact. Exactness of a functor into `A` is detected pointwise, and
the colimit of a diagram of functors is the pointwise colimit. -/
lemma exactFunctor_colimit [HasColimitsOfShape I A] [HasExactColimitsOfShape I A]
    (T : I ⥤ A ⥤ A) (hT : ∀ i, exactFunctor A A (T.obj i)) :
    exactFunctor A A (colimit T) := by
  let : PreservesFiniteLimits (colim : (I ⥤ A) ⥤ A) :=
    HasExactColimitsOfShape.preservesFiniteLimits (J := I) (C := A)
  let : PreservesFiniteLimits T.flip :=
    preservesFiniteLimits_of_evaluation _ fun i ↦ ((exactFunctor_iff _).1 (hT i)).1
  let : PreservesFiniteColimits T.flip :=
    preservesFiniteColimits_of_evaluation _ fun i ↦ ((exactFunctor_iff _).1 (hT i)).2
  exact (exactFunctor_iff _).2
    ⟨preservesFiniteLimits_of_natIso (colimitIsoFlipCompColim T).symm,
      preservesFiniteColimits_of_natIso (colimitIsoFlipCompColim T).symm⟩

end ExactColimit

/-! ### Direct sums of flat sheaves of modules -/

section Main

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]

/-! Each of the following is seated as a named declaration rather than left to instance
synthesis: the search chains `SheafOfModules → PresheafOfModules → AddCommGrpCat` and
`Abelian → HasFiniteLimits → HasFiniteProducts` both exhaust the heartbeat limit when
nested inside the search for `AB4OfSize`. -/

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}] in
/-- Presheaves of modules have colimits indexed by the module universe. -/
lemma hasColimitsOfSize_presheafOfModules (R : Sheaf J RingCat.{max u v}) :
    HasColimitsOfSize.{max u v, max u v} (PresheafOfModules.{max u v} R.obj) := by
  infer_instance

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})] in
/-- Sheaves of modules have colimits indexed by the module universe. -/
lemma hasColimitsOfSize_sheafOfModules (R : Sheaf J RingCat.{max u v}) :
    HasColimitsOfSize.{max u v, max u v} (_root_.SheafOfModules.{max u v} R) :=
  let _ := hasColimitsOfSize_presheafOfModules R
  inferInstance

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})] in
/-- Sheaves of modules have coproducts indexed by the module universe. -/
lemma hasColimitsOfShape_discrete (R : Sheaf J RingCat.{max u v}) (ι : Type (max u v)) :
    HasColimitsOfShape (Discrete ι) (_root_.SheafOfModules.{max u v} R) :=
  let _ := hasColimitsOfSize_sheafOfModules R
  inferInstance

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})] in
/-- Sheaves of modules have finite biproducts, being an abelian category. -/
lemma hasFiniteBiproducts_sheafOfModules (R : Sheaf J RingCat.{max u v}) :
    HasFiniteBiproducts (_root_.SheafOfModules.{max u v} R) :=
  let _ : Abelian (_root_.SheafOfModules.{max u v} R) := instAbelianSheafOfModules R
  HasFiniteBiproducts.of_hasFiniteProducts

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})] in
/-- Coproducts of sheaves of modules indexed by the module universe are exact: filtered
colimits of sheaves of modules are exact (Tag 03DB) and AB5 implies AB4. -/
lemma hasExactColimitsOfShape_discrete (R : Sheaf J RingCat.{max u v})
    (ι : Type (max u v)) :
    HasExactColimitsOfShape (Discrete ι) (_root_.SheafOfModules.{max u v} R) := by
  let _ : Abelian (_root_.SheafOfModules.{max u v} R) := instAbelianSheafOfModules R
  let _ := hasColimitsOfSize_sheafOfModules R
  let _ := hasFiniteBiproducts_sheafOfModules R
  let _ : AB5OfSize.{max u v, max u v} (_root_.SheafOfModules.{max u v} R) :=
    instAB5SheafOfModules R
  let _ : AB4OfSize.{max u v} (_root_.SheafOfModules.{max u v} R) :=
    AB4.of_AB5 (_root_.SheafOfModules.{max u v} R)
  exact AB4OfSize.ofShape ι

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})] in
  /-- A colimit of flat sheaves of modules along a shape with exact colimits is flat. -/
  private theorem isFlat_colimit_of_exactColimits {O : Sheaf J CommRingCat.{max u v}}
      {I : Type*} [Category I]
      [HasColimitsOfShape I
        (_root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
      [HasExactColimitsOfShape I
        (_root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
      (F : I ⥤ _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (hF : ∀ i, IsFlat (F.obj i)) :
      IsFlat (colimit F) := by
    have hcol := exactFunctor_colimit
      (F ⋙ (Tensor.sheafTensor.{u, v, max u v, max u v, max u v} O).flip)
      fun i ↦ (isFlat_iff_exactFunctor_sheafTensor O (F.obj i)).1 (hF i)
    have := (preservesColimitsOfShape_sheafTensor_flip O I).preservesColimit (K := F)
    rw [isFlat_iff_exactFunctor_sheafTensor]
    exact (exactFunctor _ _).prop_of_iso
      (preservesColimitIso (Tensor.sheafTensor.{u, v, max u v, max u v, max u v} O).flip F).symm
      hcol

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})] in
/-- **A direct sum of flat sheaves of modules is flat.** -/
@[stacks 03EU]
theorem isFlat_coproduct {O : Sheaf J CommRingCat.{max u v}} {ι : Type (max u v)}
    (F : ι → _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hF : ∀ i, IsFlat (F i)) :
    IsFlat (∐ F) := by
  let _ := hasColimitsOfShape_discrete (Stacks.SheafOfModules.Tensor.ringSheaf O) ι
  let _ := hasExactColimitsOfShape_discrete (Stacks.SheafOfModules.Tensor.ringSheaf O) ι
  exact isFlat_colimit_of_exactColimits (Discrete.functor F) fun i ↦ hF i.as

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})] in
/-- **A colimit of flat sheaves of modules along a shape whose colimits are exact is flat.**
For a filtered shape the exactness hypothesis is automatic from AB5 (Tag 03DB), which is the
form Stacks 05NG takes; the coproduct case above is the same argument at a discrete shape,
where exactness instead comes from AB4. -/
theorem isFlat_colimit {O : Sheaf J CommRingCat.{max u v}} {I : Type*} [Category I]
    [HasColimitsOfShape I
      (_root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
    [HasExactColimitsOfShape I
      (_root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
    (F : I ⥤ _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hF : ∀ i, IsFlat (F.obj i)) :
    IsFlat (colimit F) :=
  isFlat_colimit_of_exactColimits F hF

end Main

end Stacks.SheafOfModules.FlatCoproduct
