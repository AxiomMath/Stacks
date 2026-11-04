module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackExistence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOnKFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorAlongASiteMorphism
public import StacksFrontier.CategoryTheory.Sites.Modules.Gate18.FlatTensorProduct

/-!
# Flatness of total tensor complexes, at any universes

On a site `(C, J)` whose objects and morphisms lie in arbitrary universes, with coefficients in
a third universe: a coproduct of flat modules indexed by a small type is flat, the total complex
of a bounded-above double complex of flat modules has flat terms, and so has the total tensor
complex `Tot(K ⊗ L)` of two complexes of flat modules. These are the statements of
`DerivedPullbackOnKFlatComplexes.lean` without its single-universe restriction.

## References

* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Sheaves.DerivedPullback.KFlatPullback

namespace Stacks.Sheaves.DerivedPullback

universe u

/-! ## Flatness of the terms of a total complex -/

section Flat

universe v' u' w'

-- The sections universe `w'` is independent of the two site universes, so Mathlib's
-- size-restricted instances do not supply the sheaf-condition composition through which
-- `Stacks.SheafOfModules.Tensor.ringSheaf` and `IsFlat` are stated.
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{w'}] [J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (O : Sheaf J CommRingCat.{w'})

/-- **A direct sum of flat sheaves of modules indexed by a type in the lowest universe is
flat.** This is Stacks 05NG after reindexing along `Equiv.ulift`: the statement there has the
index type in the universe of the sections, and the direct sums appearing in a total complex
are indexed by a subtype of `ℤ × ℤ`. -/
theorem isFlat_coproduct_of_smallIndex_general {ι : Type}
    (F : ι → SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', w'} O))
    [HasCoproduct F]
    (hF : ∀ i, AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', w', w'} (O := O) (F i)) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', w', w'} (O := O) (∐ F) := by
  let G : ULift.{w'} ι →
      SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', w'} O) :=
    fun i => F i.down
  let _ : HasCoproduct G :=
    hasCoproduct_of_equiv_of_iso F G Equiv.ulift (fun _ => Iso.refl _)
  refine Stacks.SheafOfModules.FlatRetract.isFlat_of_iso O ?_
    (Stacks.SheafOfModules.FlatColimits.isFlat_coproduct (O := O) G (fun i => hF i.down))
  exact
    { hom := Sigma.desc fun i => Sigma.ι F i.down
      inv := Sigma.desc fun i => Sigma.ι G (ULift.up i)
      hom_inv_id := by apply colimit.hom_ext; rintro ⟨i⟩; simp [G]
      inv_hom_id := by apply colimit.hom_ext; rintro ⟨i⟩; simp [G] }

/-- **Every term of the total complex of a bicomplex of flat sheaves of modules is flat.** The
term in total degree `n` is the direct sum of the bidegrees `(p, q)` with `p + q = n`. -/
theorem isFlat_total_general
    (Z : HomologicalComplex₂ (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [Z.HasTotal (ComplexShape.up ℤ)]
    (hflat : ∀ p q, AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', w', w'}
      (O := O) ((Z.X p).X q))
    (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', w', w'} (O := O)
      ((Z.total (ComplexShape.up ℤ)).X n) :=
  isFlat_coproduct_of_smallIndex_general O _ (fun j => hflat j.val.1 j.val.2)

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w', w'} O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w', w'} O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor O)
      (ComplexShape.up ℤ)]

/-- **The total tensor complex of two complexes with flat terms has flat terms.** Each bidegree
`K^p ⊗_O L^q` is flat by Stacks 0G6Q and the term in total degree `n` is their direct sum. -/
theorem isFlat_tensorComplex_X_general
    (K L : CochainComplex (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (hK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', w', w'} (O := O) (K.X i))
    (hL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', w', w'} (O := O) (L.X i))
    (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', w', w'} (O := O)
      ((((Stacks.SheafOfModules.Tensor.tensorComplex O).obj K).obj L).X n) :=
  isFlat_total_general O
    ((((Stacks.SheafOfModules.Tensor.sheafTensor O).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L)
    (fun p q => Stacks.SheafOfModules.FlatTensor.isFlat_tensor (K.X p) (L.X q) (hK p) (hL q)) n

end Flat

end Stacks.Sheaves.DerivedPullback

end
