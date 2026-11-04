module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import StacksCore.Algebra.Homology.TotalComplex
public import StacksFrontier.Algebra.Homology.ComplexShapeSignsNat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsTensorConstant

/-!
# The tensor product of abelian groups as a bifunctor

`AddCommGrpCat` carries a tensor product `A ⊗_ℤ B`, but this Mathlib pin gives it no monoidal
structure: the only monoidal structure on `AddCommGrpCat` it supplies is the *cartesian* one
(`Mathlib.Algebra.Category.Grp.CartesianMonoidal`, where `A ⊗ B = A × B`), and
`Mathlib.Algebra.Category.Grp.ZModuleEquivalence` records transporting the tensor product from
`ModuleCat ℤ` as a TODO.  The tensor product is available as a bifunctor
`AddCommGrpCat ⥤ AddCommGrpCat ⥤ AddCommGrpCat`, `Stacks.EtaleCohomology.TensorConstant.tensorBif`;
this module supplies the instances a homological consumer needs: that it preserves zero
morphisms in each variable, and that the total complex of its action on two `ℕ`-indexed cochain
complexes exists.

That last instance is the point of the module.  Without it
`CategoryTheory.Functor.map₂HomologicalComplex` cannot be applied, so an `ℕ`-indexed cochain
complex of abelian groups has no tensor product with another, and the generic wedge filtration of
`StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.WedgeImageSystem` — which is
stated for an arbitrary bifunctor on an arbitrary abelian category precisely so that it can be
used here — cannot be instantiated.  The completed de Rham complexes of the crystalline chapter,
[Stacks, Tag 07LD] and [Stacks, Tag 07LG], are complexes of `AddCommGrpCat`: their terms are
completed tensor products and their differentials are additive but not linear, so
`Crystalline.CompletedDeRham.complex` lands in `CochainComplex AddCommGrpCat ℕ` and nothing
finer.  The wedge of a form against an element of such a term is biadditive, so it factors
through the tensor product of abelian groups, the bifunctor used here.

## Main definitions

* `AddCommGrpCat.tensorIntBifunctorNat`: the tensor product of abelian groups,
  `Stacks.EtaleCohomology.TensorConstant.tensorBif`, read on `ℕ`-indexed cochain complexes, by
  total complexes.

## Main results

* `AddCommGrpCat.hasMapBifunctorNat`: **the total complex of the tensor product of two
  `ℕ`-indexed cochain complexes of abelian groups exists.**  In each total degree only the
  finitely many pairs `(p, q)` with `p + q = n` contribute, and `AddCommGrpCat` has finite
  coproducts.

## Implementation notes

The bifunctor is `A ↦ (M ↦ A ⊗_ℤ M)`, so its first variable is the one acted on by
`LinearMap.rTensor` and its second by `LinearMap.lTensor`.  Both variables range over
`AddCommGrpCat.{w}` for a single `w`: `A ⊗[ℤ] M` is formed from two types in one universe, and
`AddCommGrpCat.{w}` is the category of groups in that universe.  A consumer whose two complexes
live in different universes must raise both to their maximum first; the crystalline complexes do
this already, their terms being objects of `AddCommGrpCat.{max v w}`.

The bifunctor itself is `Stacks.EtaleCohomology.TensorConstant.tensorBif` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsTensorConstant`, with the functor
`Stacks.EtaleCohomology.TensorConstant.tensorConstLeft` of tensoring by a fixed group; this module
adds what a homological consumer needs on top of it.

## References

* [Stacks Project, Tag 012Z](https://stacks.math.columbia.edu/tag/012Z), the total complex
* [Stacks Project, Lemma 60.19.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe w

namespace AddCommGrpCat

open Stacks.EtaleCohomology.TensorConstant

/-! ### The bifunctor -/

/-- The value of the bifunctor on a pure tensor, in the first variable. -/
@[simp] public theorem tensorBif_map_app_apply {A B : AddCommGrpCat.{w}} (f : A ⟶ B)
    (M : AddCommGrpCat.{w}) (a : A) (m : M) :
    ((tensorBif.map f).app M).hom (a ⊗ₜ[ℤ] m) = f.hom a ⊗ₜ[ℤ] m := rfl

/-- The value of the bifunctor on a pure tensor, in the second variable. -/
@[simp] public theorem tensorBif_obj_map_apply (A : AddCommGrpCat.{w})
    {M N : AddCommGrpCat.{w}} (f : M ⟶ N) (a : A) (m : M) :
    ((tensorBif.obj A).map f).hom (a ⊗ₜ[ℤ] m) = a ⊗ₜ[ℤ] f.hom m := rfl

/-- The tensor product of abelian groups is additive in its first variable. -/
public instance additive_tensorBif : tensorBif.{w}.Additive where
  map_add {_ _ f g} := NatTrans.ext (funext fun _ =>
    tensorConstLeft_hom_ext (fun a m => by
      change (f.hom a + g.hom a) ⊗ₜ[ℤ] m = f.hom a ⊗ₜ[ℤ] m + g.hom a ⊗ₜ[ℤ] m
      exact TensorProduct.add_tmul _ _ m))

/-- Tensoring by a fixed abelian group preserves the zero morphism, which is what the action of a
bifunctor on homological complexes requires. -/
public instance preservesZeroMorphisms_tensorBif_obj (A : AddCommGrpCat.{w}) :
    (tensorBif.obj A).PreservesZeroMorphisms :=
  inferInstanceAs (tensorConstLeft (A : Type w)).PreservesZeroMorphisms

/-! ### The total complex over `ℕ` -/

/-- **The total complex of the tensor product of two `ℕ`-indexed cochain complexes of abelian
groups exists**: in each total degree only the finitely many pairs `(p, q)` with `p + q = n`
contribute, and `AddCommGrpCat` has finite coproducts. -/
public instance hasMapBifunctorNat (K₁ K₂ : CochainComplex AddCommGrpCat.{w} ℕ) :
    HomologicalComplex.HasMapBifunctor K₁ K₂ tensorBif.{w} (ComplexShape.up ℕ) :=
  HomologicalComplex₂.hasTotal_of_finite _ _ (fun n => Set.Finite.subset
    (Set.Finite.ofFinset (Finset.antidiagonal n) (fun _ => Finset.mem_antidiagonal))
    (fun _ h => h.1))

/-- The tensor product of abelian groups, as a bifunctor on `ℕ`-indexed cochain complexes. -/
public abbrev tensorIntBifunctorNat :
    CochainComplex AddCommGrpCat.{w} ℕ ⥤ CochainComplex AddCommGrpCat.{w} ℕ ⥤
      CochainComplex AddCommGrpCat.{w} ℕ :=
  tensorBif.map₂HomologicalComplex (ComplexShape.up ℕ) (ComplexShape.up ℕ)
    (ComplexShape.up ℕ)

end AddCommGrpCat

end
