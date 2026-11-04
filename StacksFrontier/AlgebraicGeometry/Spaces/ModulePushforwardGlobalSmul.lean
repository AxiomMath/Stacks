module

public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRingHomSiteSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionLinear
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyPullback

/-!
# Direct image of multiplication by a global function

For a morphism `f : X ⟶ Y` of algebraic spaces, a global function `c` of `Y` and an
`𝒪_X`-module `K`, the direct image of multiplication by the pulled back function `f♯ c` on `K`
is multiplication by `c` on `f_*K`.

## Main results

* `AlgebraicGeometry.Space.modulePushforward_map_globalSmul_globalSectionsRingHomSite`: the direct
  image of multiplication by `f♯ c` is multiplication by `c`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback
open Stacks.Cohomology.SiteModules (globalSmul)

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **The direct image of multiplication by `f♯ c` is multiplication by `c`.** For a morphism
`f : X ⟶ Y` of algebraic spaces, a global function `c` of `Y` and an `𝒪_X`-module `K`, the direct
image along `f` of multiplication by `f♯ c` on `K` is multiplication by `c` on `f_*K`. -/
theorem modulePushforward_map_globalSmul_globalSectionsRingHomSite (f : X ⟶ Y)
    (c : RingCat.sectionsSubring
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj)
    (K : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforward B S hS f).map
        (globalSmul _ (globalSectionsRingHomSite B S hS f c) K) =
      globalSmul _ c ((modulePushforward B S hS f).obj K) := by
  ext V' x
  obtain ⟨V⟩ := V'
  change SmallEtale B S hS Y.1 at V
  refine moduleChartProjection_ext B S hS f V (moduleSetSheaf B S hS X K) (fun j ↦ ?_)
  have hP : PreservesFiniteProducts (smallEtaleDirectImage B S hS f ⋙
      sectionsFunctor.{u} (SmallEtale.topology B S hS Y.1) (op V)) := inferInstance
  have hQ : PreservesFiniteProducts
      (sectionsFunctor.{u} (SmallEtale.topology B S hS X.1) j.right) := inferInstance
  have hR : (SmallEtale.topology B S hS X.1).HasSheafCompose
      (forget RingCat.{u}) := inferInstance
  have hA : (SmallEtale.topology B S hS X.1).HasSheafCompose
      (forget AddCommGrpCat.{u}) := inferInstance
  refine (Functor.natTrans_app_map_apply (moduleChartProjection B S hS f V j)
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
      (globalSmul _ (globalSectionsRingHomSite B S hS f c) K)) x).trans ?_
  refine Eq.trans ?_ (@moduleSMulObj_naturality _ _ _ hR hA
    (structureRingSheaf B S hS X) K _ hP _ hQ
    (moduleChartProjection B S hS f V j)
    (((structureSharp B S hS f).hom.app (op V)).hom (c.1 (op V)) :
      ((smallEtaleDirectImage B S hS f ⋙
        sectionsFunctor.{u} (SmallEtale.topology B S hS Y.1) (op V)).obj
      (structureSetSheaf B S hS X))) x).symm
  rw [moduleChartProjection_app_structureSharp B S hS f V j]
  refine Eq.trans ?_ (sectionsFunctor_map_moduleSMulHom
    (structureRingSheaf B S hS X) K j.right (chartPullback B S hS f V j (c.1 (op V)))
    ((moduleChartProjection B S hS f V j).app (moduleSetSheaf B S hS X K) x)).symm
  have key : chartPullback B S hS f V j (c.1 (op V)) =
      (globalSectionsRingHomSite B S hS f c).1 j.right :=
    (globalSectionsRingHomSite_val_chartPullback B S hS f c V j).symm
  rw [key]
  rfl

end AlgebraicGeometry.Space
