module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkTensor
public import StacksFrontier.CategoryTheory.Sites.Point.ModuleStalkDerived
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Iso
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat

/-!
# Stalks of sequential colimits of bounded above complexes of flat modules are K-flat

Let `(C, J, O)` be a ringed site and `Φ` a point of it.  If a complex of `O`-modules is a
sequential colimit of strictly bounded above complexes with flat terms — the shape of the
resolutions of Stacks 06YS built in this development — then its stalk at `Φ` is a K-flat complex
of modules over the stalk ring `O_Φ`: the stalk functor commutes with the colimit, carries each
stage to a bounded above complex of flat `O_Φ`-modules (Stacks 05VB), which is K-flat by
Stacks 064K, and a filtered colimit of K-flat complexes is K-flat by Stacks 06Y3.

## Main results

* `Stacks.kFlat_mapHomologicalComplex_sheafModuleFiber_colimit`: the statement above.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 05VB](https://stacks.math.columbia.edu/tag/05VB)
* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
* [Stacks Project, Tag 06Y3](https://stacks.math.columbia.edu/tag/06Y3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (Φ : J.Point.{w}) (O : Sheaf J CommRingCat.{w})
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- **The stalk of a sequential colimit of strictly bounded above complexes with flat terms is
K-flat.** -/
theorem kFlat_mapHomologicalComplex_sheafModuleFiber_colimit
    (D : ℕ ⥤ CochainComplex (SheafOfModules.{w} (commRingSheafToRingSheaf O)) ℤ)
    [HasColimit D]
    (hLE : ∀ n : ℕ, ∃ b : ℤ, (D.obj n).IsStrictlyLE b)
    (hflat : ∀ (n : ℕ) (i : ℤ),
      AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := O) ((D.obj n).X i)) :
    CochainComplex.KFlat.{w, w}
      (((sheafModuleFiberOfCommRing Φ O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (colimit D)) := by
  let F := (sheafModuleFiberOfCommRing Φ O).mapHomologicalComplex (ComplexShape.up ℤ)
  have : PreservesColimitsOfShape ℕ (sheafModuleFiberOfCommRing Φ O) := inferInstance
  have : PreservesColimitsOfShape ℕ F := inferInstance
  have hstage : ∀ n : ℕ, CochainComplex.KFlat.{w, w} ((D ⋙ F).obj n) := by
    intro n
    obtain ⟨b, hb⟩ := hLE n
    have : CochainComplex.IsStrictlyLE ((D ⋙ F).obj n) b := by
      rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      exact (sheafModuleFiberOfCommRing Φ O).map_isZero
        ((D.obj n).isZero_of_isStrictlyLE b i hi)
    have : ∀ i : ℤ, Module.Flat ((Φ.presheafFiber (A := CommRingCat.{w})).obj O.obj)
        (((D ⋙ F).obj n).X i) := fun i =>
      isFlatModuleStalk_of_isFlat_freeUniverse O ((D.obj n).X i) Φ (hflat n i)
    exact CochainComplex.KFlat.kFlat_of_flat _ b
  have hcol := CochainComplex.KFlat.kFlat_colimit (D ⋙ F) hstage
  exact CochainComplex.KFlat.of_iso (preservesColimitIso F D).symm hcol

end Stacks

end
