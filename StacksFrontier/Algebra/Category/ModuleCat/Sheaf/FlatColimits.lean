module

public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPreservesColimits
public import StacksFrontier.CategoryTheory.Functor.Bifunctor
import StacksCore.Tactic.StacksAttribute

/-!
# Colimits and direct sums of flat sheaves of modules

A filtered colimit of flat sheaves of modules over a sheaf of commutative rings on a site is
flat, and so is an arbitrary direct sum. Flatness of `F` means that `G ↦ G ⊗ F` is an exact
endofunctor of sheaves of modules (Stacks 03ER(3)), so the statement is that an exact functor
is obtained as a filtered colimit, respectively a direct sum, of exact functors.

The proof is the one in the source. Tensoring on the right assembles into a functor from the
index category to endofunctors of sheaves of modules, and the colimit of that diagram is the
tensor functor of the colimit: this is where Stacks 05NB enters, through
`Stacks.SheafOfModules.TensorColimits.tensorLeft_preservesColimits`, evaluated at each sheaf
of modules. Filtered colimits of sheaves of modules are exact, because they are exact for
presheaves and sheafification is a left adjoint, so a filtered colimit of exact functors is
exact.

For direct sums the argument is the same twice over. A finite direct sum of exact functors is
exact because finite biproducts are exact, which gives the finite case; an arbitrary coproduct
is the filtered colimit of its finite subcoproducts, so the general case follows from the
finite one and the filtered-colimit case. The passage from a diagram of sheaves to a diagram of
tensor functors is the native tensor bifunctor with its arguments flipped, which is additive in
the tensoring sheaf and therefore commutes with the finite direct sums involved.

## Main results

* `Stacks.SheafOfModules.FlatColimits.isFlat_colimit`: a filtered colimit of flat sheaves of
  modules is flat.
* `Stacks.SheafOfModules.FlatColimits.isFlat_coproduct`: an arbitrary direct sum of flat
  sheaves of modules is flat; `isFlat_coproduct_finite` is the finite case.
* `Stacks.SheafOfModules.FlatColimits.exact_colimit_of_exact_functors`: in a category with
  exact filtered colimits, a filtered colimit of exact endofunctors is exact.
* `Stacks.SheafOfModules.FlatColimits.exact_colimit_of_exact_finite_family`: in a preadditive
  category with finite biproducts, a finite direct sum of exact endofunctors is exact.

## Implementation notes

The tensor product used is the native sheaf tensor bifunctor
`Stacks.SheafOfModules.Tensor.sheafTensor`, which sheafifies the objectwise tensor product and
in terms of which flatness is defined. `tensorColimitDiagram` uses it with its arguments
flipped, and `tensorColimitCoconeIsColimit` identifies its colimit by evaluating at each sheaf
of modules and appealing to Stacks 05NB.

This is both halves of Stacks 05NG, the filtered-colimit clause and the direct-sum clause. The
presheaf-level analogue is Stacks 03EU, `Stacks.isFlat_colimit`; that is a different statement
(presheaves of modules over a presheaf of rings, and the presheaf-level `IsFlat`), not a
duplicate.

## References

* [Stacks Project, Tag 03EU](https://stacks.math.columbia.edu/tag/03EU)
* [Stacks Project, Tag 05NG](https://stacks.math.columbia.edu/tag/05NG)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w z

namespace Stacks.SheafOfModules.FlatColimits

open AlgebraicGeometry.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
  [HasWeakSheafify J AddCommGrpCat.{z}]

/-- If `colim` preserves finite limits, a colimit of exact endofunctors is exact. -/
private theorem exactFunctor_colimit_of_exact {A : Type*} [Category* A]
    {I : Type*} [Category* I] [HasColimitsOfShape I A]
    [PreservesFiniteLimits (colim : (I ⥤ A) ⥤ A)] (T : I ⥤ A ⥤ A)
    (hT : ∀ i, exactFunctor A A (T.obj i)) :
    exactFunctor A A (colimit T) := by
  let : PreservesFiniteLimits T.flip :=
    preservesFiniteLimits_of_evaluation _ (fun i => (hT i).1)
  let : PreservesFiniteColimits T.flip :=
    preservesFiniteColimits_of_evaluation _ (fun i => (hT i).2)
  exact ⟨preservesFiniteLimits_of_natIso (colimitIsoFlipCompColim T).symm,
    preservesFiniteColimits_of_natIso (colimitIsoFlipCompColim T).symm⟩

/-- In a category with exact filtered colimits, a filtered colimit of exact endofunctors is
exact. -/
theorem exact_colimit_of_exact_functors {A : Type*} [Category* A]
    {I : Type*} [Category* I] [IsFiltered I] [HasColimitsOfShape I A]
    [HasExactColimitsOfShape I A] (T : I ⥤ A ⥤ A)
    (hT : ∀ i, exactFunctor A A (T.obj i)) :
    exactFunctor A A (colimit T) :=
  let : PreservesFiniteLimits (colim : (I ⥤ A) ⥤ A) :=
    HasExactColimitsOfShape.preservesFiniteLimits (J := I) (C := A)
  exactFunctor_colimit_of_exact T hT

/-- In a preadditive category with finite biproducts, a finite direct sum of exact endofunctors
is exact. Unlike `exact_colimit_of_exact_functors` the index category is discrete rather than
filtered, and exactness of the colimit comes from exactness of finite biproducts instead. -/
theorem exact_colimit_of_exact_finite_family {A : Type*} [Category* A]
    [HasFiniteProducts A] [HasFiniteCoproducts A] [Preadditive A]
    {ι : Type*} [Finite ι] (T : ι → A ⥤ A) (hT : ∀ i, exactFunctor A A (T i)) :
    exactFunctor A A (colimit (Discrete.functor T)) := by
  have : HasFiniteBiproducts A := HasFiniteBiproducts.of_hasFiniteProducts
  exact exactFunctor_colimit_of_exact _ fun i => hT i.as

section TensorColimitHelpers

variable (O : Sheaf J CommRingCat.{w})

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- A *finite* direct sum of flat sheaves of modules is flat: tensoring with it is the finite
direct sum of the tensor functors, which is exact because finite biproducts are. -/
theorem isFlat_coproduct_finite {ι : Type z} [Finite ι]
    (F : ι → _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hF : ∀ i, IsFlat (F i)) :
    IsFlat (∐ F) := by
  let M := _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)
  let S : M ⥤ M ⥤ M := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} O).flip
  let T : ι → M ⥤ M := fun i => S.obj (F i)
  let eD : Discrete.functor T ≅ Discrete.functor F ⋙ S :=
    Discrete.natIso fun _ => Iso.refl _
  exact (exactFunctor M M).prop_of_iso (preservesColimitIso S (Discrete.functor F)).symm
    ((exactFunctor M M).prop_of_iso (HasColimit.isoOfNatIso eD)
      (exact_colimit_of_exact_finite_family T fun i => hF i))

/-- The diagram of tensor endofunctors attached to a diagram of sheaves of modules. -/
noncomputable def tensorColimitDiagram {I : Type z} [Category.{z} I]
    (F : I ⥤ _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    I ⥤ (_root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O) ⥤
      _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  F ⋙ (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} O).flip

/-- The cocone on `tensorColimitDiagram` with vertex the tensor functor of the colimit. -/
noncomputable def tensorColimitCocone {I : Type z} [Category.{z} I]
    (F : I ⥤ _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    Cocone (tensorColimitDiagram O F) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} O).flip.mapCocone
    (colimit.cocone F)

/-- Tensoring commutes with the colimit: the cocone of `tensorColimitCocone` is a colimit,
by Stacks 05NB applied at each sheaf of modules. -/
noncomputable def tensorColimitCoconeIsColimit {I : Type z}
    [Category.{z} I] [IsFiltered I]
    (F : I ⥤ _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    IsColimit (tensorColimitCocone O F) := by
  apply evaluationJointlyReflectsColimits
  intro G
  let L : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O) ⥤
      _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} O).obj G
  letI : PreservesColimitsOfSize.{z, z} L :=
    Stacks.SheafOfModules.TensorColimits.tensorLeft_preservesColimits.{u, v, w, z, z} J O G
  exact isColimitOfPreserves L (colimit.isColimit F)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
private theorem exact_tensorColimitDiagram_colimit
    {I : Type z} [Category.{z} I] [IsFiltered I]
    (F : I ⥤ _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hF : ∀ i, IsFlat (F.obj i)) :
    exactFunctor (_root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (_root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (colimit (tensorColimitDiagram O F)) := by
  let A := _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)
  let : HasSheafify J AddCommGrpCat.{z} := hasSheafify_of_locallyBijective (J := J)
  let : HasExactColimitsOfShape I
      (_root_.PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj) :=
    HasExactColimitsOfShape.domain_of_functor I
      (_root_.PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
  let : (_root_.SheafOfModules.forget.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙
      _root_.PresheafOfModules.restrictScalars
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).Full :=
    (_root_.PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).fullyFaithfulROfIsIsoCounit.full
  let : (_root_.SheafOfModules.forget.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙
      _root_.PresheafOfModules.restrictScalars
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).Faithful :=
    (_root_.PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).fullyFaithfulROfIsIsoCounit.faithful
  let : HasExactColimitsOfShape I A :=
    Adjunction.hasExactColimitsOfShape
      (_root_.PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)) I
  exact exact_colimit_of_exact_functors (tensorColimitDiagram O F) fun i => hF i

end TensorColimitHelpers

/-- **Stacks Project, Tag 03EU part (2), filtered colimits.** A filtered colimit of flat
sheaves of modules is flat. -/
@[stacks 03EU "part (2), filtered colimits", stacks 05NG "filtered_colimits_flat"]
theorem isFlat_colimit {O : Sheaf J CommRingCat.{w}}
    {I : Type z} [Category.{z} I] [IsFiltered I]
    (F : I ⥤ _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hF : ∀ i, IsFlat (F.obj i)) :
    IsFlat (colimit F) := by
  let A := _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)
  exact (exactFunctor A A).prop_of_iso
    (IsColimit.coconePointUniqueUpToIso (colimit.isColimit (tensorColimitDiagram O F))
      (tensorColimitCoconeIsColimit O F))
    (exact_tensorColimitDiagram_colimit O F hF)

/-- **Stacks Project, Tag 03EU part (2), direct sums.** An arbitrary direct sum of flat sheaves
of modules is flat. An arbitrary coproduct is the filtered colimit of its finite subcoproducts,
so this follows from the finite case `isFlat_coproduct_finite` and the filtered-colimit case
`isFlat_colimit`. -/
@[stacks 03EU "part (2), direct sums", stacks 05NG "direct_sums_flat"]
theorem isFlat_coproduct {O : Sheaf J CommRingCat.{w}} {ι : Type z}
    (F : ι → _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hF : ∀ i, IsFlat (F i)) :
    IsFlat (∐ F) := by
  let M := _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)
  let D : Finset (Discrete ι) ⥤ M :=
    CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor F)
  have hD (s : Finset (Discrete ι)) : IsFlat (D.obj s) := by
    dsimp only [D, CoproductsFromFiniteFiltered.liftToFinsetObj]
    exact isFlat_coproduct_finite O (fun x : s => F x.val.as) fun x => hF x.val.as
  let e : colimit D ≅ ∐ F :=
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit D)
      (CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone F)
  exact (exactFunctor M M).prop_of_iso
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} O).flip.mapIso e)
    (isFlat_colimit (O := O) D hD)

end Stacks.SheafOfModules.FlatColimits

end
