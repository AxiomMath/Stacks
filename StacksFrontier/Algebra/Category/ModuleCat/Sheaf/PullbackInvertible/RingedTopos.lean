module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnit
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModules
public import StacksCore.Tactic.StacksAttribute

/-!
# The pullback of an invertible module along a morphism of ringed topoi

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and let `L` be an
invertible sheaf of `O_D`-modules, that is, one whose tensor functor is an equivalence
(`Stacks.SheafOfModules.IsInvertible`, Tag 01CS). **Stacks 0B8P** says that the pullback `f^*L`
of Tag 03D6 part (2) is an invertible sheaf of `O_C`-modules.

The proof is the one in the Stacks Project, with the three inputs it names. Invertibility is
equivalent to the existence of a tensor inverse (`isInvertible_iff_exists_tensor_iso_unit`,
Tag 0B8K, the ringed-site form of the Tag 0B8N used by the source), so choose `N` with
`L ⊗_{O_D} N ≅ O_D`. Pullback commutes with the tensor product
(`Stacks.SheafOfModules.pullbackTensorIso`, Tag 03EL) and carries the structure sheaf to the
structure sheaf (`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso`), so

`f^*L ⊗_{O_C} f^*N ≅ f^*(L ⊗_{O_D} N) ≅ f^*O_D ≅ O_C`,

and Tag 0B8K applies again, on `(Sh(C), O_C)` this time.

## Main definitions

There are no new definitions.

## Main results

* `Stacks.SheafOfModules.isInvertible_pullbackModules_obj`: **Stacks 0B8P**, the pullback of an
  invertible sheaf of modules along a morphism of ringed topoi is invertible. It is an instance,
  so invertibility of a pullback is found by instance search.
* `Stacks.SheafOfModules.isInvertible_pullbackModules_obj_ringedToposHom`: the same statement
  for a morphism of ringed topoi in the two-field sense of Tag 01D3 part (2).

## Implementation notes

`pullbackModules` is constructed over the four-field
`Stacks.Sheaves.RingedToposModules.RingedToposHom`, which stores both forms of the structure map
at the `RingCat` level, while Tag 01D3 part (2) defines the two-field
`AlgebraicGeometry.RingedToposHom`. The two data are equivalent and
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom` is the passage, so the second result
is the first read along that passage; both carry the tag.

The tensor product of Tag 03EL is spelled
`Stacks.SheafOfModules.Tensor.sheafTensor`, while Tag 0B8K is phrased with
`Stacks.SheafOfModules.tensorLeftFunctor` over
`Stacks.SheafOfModules.TensorSheafification.structureSheaf`. On objects the two agree by
definition, as `Stacks.SheafOfModules.TensorSheafification.tensorSheafBifunctor_obj_eq_tensorSheaf`
records, so no comparison isomorphism is inserted between them.

## References

* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules

universe w w' v u v' u'

namespace Stacks.SheafOfModules

variable {X : AlgebraicGeometry.RingedTopos.{v, u, w}}
  {Y : AlgebraicGeometry.RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]

/-- **Stacks Project, Tag 0B8P.** The pullback of an invertible module along a morphism of
ringed topoi is invertible. -/
@[stacks 0B8P, instance]
theorem isInvertible_pullbackModules_obj (f : RingedToposHom X Y)
    (L : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    [hL : IsInvertible Y.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property L] :
    IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
      ((f.pullbackModules).obj L) := by
  obtain ⟨N, ⟨e⟩⟩ := (isInvertible_iff_exists_tensor_iso_unit
    (hO := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property) L).mp hL
  refine (isInvertible_iff_exists_tensor_iso_unit
    (hO := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)
    ((f.pullbackModules).obj L)).mpr ⟨(f.pullbackModules).obj N, ⟨?_⟩⟩
  exact ((pullbackTensorIso f).app (L, N)).symm ≪≫ (f.pullbackModules).mapIso e ≪≫
    (pullbackModulesObjUnitIso f).symm

/-- **Stacks Project, Tag 0B8P** for a morphism of ringed topoi in the two-field sense of Tag
01D3 part (2): the pullback of an invertible module is invertible. -/
@[stacks 0B8P]
theorem isInvertible_pullbackModules_obj_ringedToposHom
    (f : AlgebraicGeometry.RingedToposHom X Y)
    (L : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    [IsInvertible Y.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property L] :
    IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
      ((f.toRingedToposModulesHom.pullbackModules).obj L) :=
  isInvertible_pullbackModules_obj f.toRingedToposModulesHom L

end Stacks.SheafOfModules

end
