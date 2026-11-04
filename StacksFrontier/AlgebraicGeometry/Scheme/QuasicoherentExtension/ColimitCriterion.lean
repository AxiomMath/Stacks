module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjects

/-!
# A quasi-coherent module is the colimit of its finite type submodules as soon as they cover it

Let `F` be a quasi-coherent module on a scheme `X`. Its quasi-coherent submodules of finite type
form a filtered category `AlgebraicGeometry.FiniteTypeQuasicoherentSubobject F`, and
`AlgebraicGeometry.finiteTypeQuasicoherentSubobjectCocone F` is the cocone whose legs are their
inclusions into `F`. This file shows that this cocone is a colimit cocone as soon as the
submodules in question cover `F`, in the sense that their supremum in `Subobject F` is the whole
of `F`.

## Main definitions

* `AlgebraicGeometry.isColimit_finiteTypeQuasicoherentSubobjectCocone_of_iSup_eq_top`: the
  canonical cocone on the finite type quasi-coherent submodules of `F` is a colimit cocone,
  given that their supremum is `⊤`.

## References

* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- The canonical cocone on the diagram of finite type quasi-coherent submodules of a
quasi-coherent module `F` is a colimit cocone, provided those submodules cover `F`, that is,
provided their supremum in `Subobject F` is the top subobject. -/
def isColimit_finiteTypeQuasicoherentSubobjectCocone_of_iSup_eq_top
    {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    (hiSup : (⨆ G : FiniteTypeQuasicoherentSubobject F, G.1) = ⊤) :
    IsColimit (finiteTypeQuasicoherentSubobjectCocone F) := by
  classical
  let P := finiteTypeQuasicoherentSubobjectProperty F
  let J := FiniteTypeQuasicoherentSubobject F
  let D : J ⥤ MonoOver F := P.ι ⋙ Subobject.representative
  let _ : Small.{u} (Subobject F) := inferInstance
  let _ : ObjectProperty.Small.{u} P :=
    ObjectProperty.Small.of_le (P := P) (Q := ⊤) (fun _ _ ↦ trivial)
  let _ : Small.{u} J := inferInstance
  let _ : LocallySmall.{u} (Subobject F) := CategoryTheory.locallySmall_of_thin
  let _ : LocallySmall.{u} J := locallySmall_of_faithful P.ι
  let _ : EssentiallySmall.{u} J := essentiallySmall_of_small_of_locallySmall J
  let eJ : J ≌ SmallModel.{u} J := equivSmallModel J
  let _ : IsFiltered (SmallModel.{u} J) := IsFiltered.of_equivalence eJ
  let Dsmall : SmallModel.{u} J ⥤ MonoOver F := eJ.inverse ⋙ D
  let c : Cocone (D ⋙ MonoOver.forget F) := Cocone.mk (Over.mk (𝟙 F))
    { app := fun G ↦ (MonoOver.forget F).map (MonoOver.leTop (D.obj G))
      naturality := fun G H f ↦ Over.OverMorphism.ext (Subobject.underlying_arrow f.hom) }
  have hiSupSmall : (⨆ G : SmallModel.{u} J, (eJ.inverse.obj G).1) = ⊤ := by
    apply top_unique
    rw [← hiSup]
    refine iSup_le fun G ↦ ?_
    have hG : G.1 = (eJ.inverse.obj (eJ.functor.obj G)).1 :=
      Subobject.skeletal F ⟨P.ι.mapIso (eJ.unitIso.app G)⟩
    rw [hG]
    exact le_iSup (fun G : SmallModel.{u} J ↦ (eJ.inverse.obj G).1) _
  have htopSmall : Subobject.mk (𝟙 F) =
      ⨆ G : SmallModel.{u} J, Subobject.mk (Dsmall.obj G).obj.hom := by
    rw [← Subobject.top_eq_id]
    simpa [Dsmall, D, Subobject.mk_arrow] using hiSupSmall.symm
  let csmall : Cocone (Dsmall ⋙ MonoOver.forget F) := c.whisker eJ.inverse
  have : Mono csmall.pt.hom := inferInstanceAs (Mono (𝟙 F))
  have hcSmall : IsColimit ((Over.forget F).mapCocone csmall) :=
    IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup Dsmall csmall htopSmall
  have hc : IsColimit ((Over.forget F).mapCocone c) :=
    (IsColimit.whiskerEquivalenceEquiv eJ.symm).symm hcSmall
  exact IsColimit.ofIsoColimit hc (Cocone.ext (Iso.refl F) fun G ↦ Category.comp_id G.obj.arrow)

end AlgebraicGeometry

end
