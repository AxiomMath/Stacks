module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Homology.KFlat.Bifunctor
public import StacksCore.Tactic.StacksAttribute

@[expose] public section

/-!
# K-flatness in distinguished triangles of complexes of sheaves

For a ringed site `(C, O)`, K-flatness of complexes of `O`-modules satisfies the
two-out-of-three property in distinguished triangles of the homotopy category `K(Mod(O))`.

## Main results

* `Stacks.SheafOfModules.kFlat_of_second_third`: the first vertex is K-flat if the other two are.
* `Stacks.SheafOfModules.kFlat_of_first_third`: the second vertex is K-flat if the other two are.
* `Stacks.SheafOfModules.kFlat_of_first_second`: the third vertex is K-flat if the other two are.

## Implementation notes

The three implications are stated separately so each can be applied directly.  The vertices of
the triangle are complexes of sheaves of modules over the given ring sheaf, and K-flatness uses
their total tensor complex `Stacks.SheafOfModules.Tensor.tensorComplex` (Stacks Tag 06YM), spelled
  through
`CochainComplex.KFlatBifunctor.KFlat` at the tensor bifunctor
  `Stacks.SheafOfModules.Tensor.sheafTensor`.  That
predicate unfolds definitionally to the Stacks Tag 06YN one, "`Tot(F ⊗_O K)` is acyclic for every
acyclic `F`", so the two may be used interchangeably and a conversion between them is `rfl`.

The additivity of `⊗_O` in each variable and the existence of the total complexes are carried
as instance hypotheses, exactly as in Stacks Tag 06YM.  `HasSheafify` (rather than merely
`HasWeakSheafify`) is assumed because it is what makes `Mod(O)` abelian, and abelianness of
`Mod(O)` is the ambient structure the proof runs in: both a distinguished triangle of
`K(Mod(O))` and the triangulated subcategory of acyclic objects live there.

**Universe constraint.**  `Stacks.SheafOfModules.Tensor.sheafTensor` forces the universe of the
  sections of the
ring sheaf to agree with the universe of the sections of the module sheaves, and both to be at
least the universe of the site; the free parameter above that is `w`.  So the statements here
are the ringed-site statements read at a ring-and-module universe `max u v w`, rather than at
independent ring and module universes.  The constraint comes from the monoidal structure on
presheaves of modules, which `Stacks.SheafOfModules.Tensor.presheafTensor` uses, and is not
  introduced here.

The proof is `CochainComplex.KFlatBifunctor.kFlat_obj₁_of_distTriang` and its two siblings,
applied to `F = ⊗_O`.  The mathematical input is that `Tot(F ⊗_O -)` is an exact functor of
triangulated categories for a fixed acyclic `F`, which is Stacks Tag 06YM, Statement 1.

## References

* [The Stacks Project, Tag 07A3](https://stacks.math.columbia.edu/tag/07A3)
-/

open CategoryTheory CategoryTheory.Limits Pretriangulated

noncomputable section

universe v u w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (R : Sheaf J CommRingCat.{max u v w})
variable [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, max u v w, max u v w} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, max u v w, max u v w} R).obj
    M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-- In a distinguished triangle, the first complex is K-flat if the second and
third are K-flat. -/
@[stacks 07A3 "first vertex"]
theorem kFlat_of_second_third
    {K₁ K₂ K₃ : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ}
    (f : (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K₁ ⟶
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K₂)
    (g : (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K₂ ⟶
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K₃)
    (h : (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K₃ ⟶
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K₁)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang _)
    (h₂ : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor R) K₂)
    (h₃ : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor R) K₃) :
    CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor R) K₁ :=
  CochainComplex.KFlatBifunctor.kFlat_obj₁_of_distTriang _ f g h hT h₂ h₃

/-- In a distinguished triangle, the second complex is K-flat if the first
and third are K-flat. -/
@[stacks 07A3 "second vertex"]
theorem kFlat_of_first_third
    {K₁ K₂ K₃ : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ}
    (f : (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K₁ ⟶
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K₂)
    (g : (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K₂ ⟶
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K₃)
    (h : (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K₃ ⟶
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K₁)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang _)
    (h₁ : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor R) K₁)
    (h₃ : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor R) K₃) :
    CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor R) K₂ :=
  CochainComplex.KFlatBifunctor.kFlat_obj₂_of_distTriang _ f g h hT h₁ h₃

/-- In a distinguished triangle, the third complex is K-flat if the first
and second are K-flat. -/
@[stacks 07A3 "third vertex"]
theorem kFlat_of_first_second
    {K₁ K₂ K₃ : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ}
    (f : (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K₁ ⟶
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K₂)
    (g : (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K₂ ⟶
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K₃)
    (h : (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K₃ ⟶
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K₁)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang _)
    (h₁ : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor R) K₁)
    (h₂ : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor R) K₂) :
    CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor R) K₃ :=
  CochainComplex.KFlatBifunctor.kFlat_obj₃_of_distTriang _ f g h hT h₁ h₂

end Stacks.SheafOfModules

end
