module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackGlobalPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectImages

/-!
# Quasi-coherent modules as colimits of their finite type submodules

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let `G` be
a quasi-coherent `𝒪_F`-module which is the colimit of a diagram of `𝒪_F`-modules of finite
presentation.  This file proves the colimit assertion of **Stacks 0829** for `G`: the canonical
cocone of the finite type quasi-coherent submodules of `G` is a colimit cocone.

## Main results

* `Space.nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone_of_isFinitePresentation`:
  the colimit assertion of Stacks 0829 from a presentation by modules of finite presentation,
  indexed by a category of any size.

## References

* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The colimit assertion of Stacks 0829 from a filtered presentation by modules of finite
presentation.**  If a quasi-coherent `𝒪_F`-module `G` is the colimit of a diagram of
`𝒪_F`-modules of finite presentation, indexed by a category of any size, then the canonical
cocone of its finite type quasi-coherent submodules is a colimit cocone.

This is the source's argument: the images of the stages are finite type quasi-coherent
submodules of `G`, and their supremum is `G` because the legs of a colimit cocone are jointly
epimorphic.  Neither filteredness of the diagram nor any size condition on its index is used;
the directedness of the system of submodules is
`AlgebraicGeometry.Space.isFiltered_finiteTypeQuasicoherentSubobject`. -/
theorem nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone_of_isFinitePresentation
    (G : Modules.{u, u} B S hS F hF) [G.IsQuasicoherentOnSite] {K : Type*} [Category* K]
    (D : K ⥤ Modules.{u, u} B S hS F hF) (φ : D ⟶ (Functor.const K).obj G)
    (hfp : ∀ k, (D.obj k).IsFinitePresentation) (hcol : IsColimit (Cocone.mk G φ)) :
    Nonempty (IsColimit (finiteTypeQuasicoherentSubobjectCocone B S hS F hF G)) := by
  classical
  have hes : EssentiallySmall.{u} (smallEtaleRingedSite B S hS F hF).C := by
    change EssentiallySmall.{u} (SmallEtale B S hS F)
    infer_instance
  have hgr : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS F hF) :=
    SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _
  have hfiltered : IsFiltered (FiniteTypeQuasicoherentSubobject B S hS F hF G) :=
    isFiltered_finiteTypeQuasicoherentSubobject B S hS F hF G
  have himg := iSup_imageSubobject_eq_top_of_isColimit_of_category φ hcol
  have htop : (⨆ H : FiniteTypeQuasicoherentSubobject B S hS F hF G, H.obj) =
      (⊤ : Subobject G) := by
    refine le_antisymm le_top ?_
    rw [← himg]
    refine iSup_le fun k => ?_
    have := hfp k
    have hq : (D.obj k).IsQuasicoherentOnSite :=
      Stacks.SheafOfModules.isQuasicoherentOnSite_of_quasicoherentData
        (SheafOfModules.IsFinitePresentation.exists_quasicoherentData (D.obj k)).choose
    exact le_iSup (fun H : FiniteTypeQuasicoherentSubobject B S hS F hF G => H.obj)
      ⟨imageSubobject (φ.app k), finiteTypeQuasicoherentSubobjectProperty_imageSubobject
        B S hS F hF (φ.app k) hq ‹_› inferInstance⟩
  exact ⟨isColimitSubobjectCocone_of_iSup_eq_top
    (finiteTypeQuasicoherentSubobjectProperty B S hS F hF G) htop⟩

end AlgebraicGeometry.Space

end
