module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.PullbackSections
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleOnSite

/-!
# Transporting a pulled-back section along the pullback-sections presheaf

Let `F` be a module on a scheme `S` and let `a` be a section of `F` over an open `V ⊆ S`. Every
scheme `T ⟶ S` over `S` whose structure morphism factors through `V` receives from `a` a global
section of the pullback of `F` to `T`, namely
`AlgebraicGeometry.Scheme.Modules.pullbackSection` over `⊤`. This file shows that these sections
are compatible with the transition maps of the pullback-sections presheaf of Tag 03DS: the map
`AlgebraicGeometry.pullbackSectionsMap` induced by a morphism of schemes over `S` carries the
section coming from `a` to the section coming from `a`.

The proof is the bookkeeping of the three `pullbackSection` lemmas of
`StacksFrontier.AlgebraicGeometry.PullbackSections.Affine`. Unfolding
`AlgebraicGeometry.pullbackSectionsMap` definitionally exhibits it as the unit of
`g.left⁺ ⊣ (g.left)_*` followed by the comparisons
`AlgebraicGeometry.Scheme.Modules.pullbackComp` and
`AlgebraicGeometry.Scheme.Modules.pullbackCongr`; `pullbackSection_top` turns the unit into a
pulled-back section, `pullbackSection_comp` absorbs the first comparison and
`pullbackSection_congr` the second.

The restriction lemma proved first is the remaining piece of functoriality of `pullbackSection`
in the open set, and is what makes the global-sections statement usable over smaller opens.

## Main results

* `AlgebraicGeometry.Scheme.Modules.pullbackSection_restrict`: restricting the pullback of a
  section to a smaller open is the pullback of the section to that open.
* `AlgebraicGeometry.pullbackSectionsMap_pullbackSection`: the transition maps of the
  pullback-sections presheaf of Tag 03DS carry pulled-back sections to pulled-back sections.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

namespace Scheme.Modules

/-- Restricting the pullback of a section to a smaller open is the pullback of the section to
that open. -/
public theorem pullbackSection_restrict {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : X.Modules) (U : X.Opens) (V W : Y.Opens) (hVU : V ≤ f ⁻¹ᵁ U) (hWV : W ≤ V)
    (a : Γ(F, U)) :
    ((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE hWV).op
        (Scheme.Modules.pullbackSection f F U V hVU a) =
      Scheme.Modules.pullbackSection f F U W (hWV.trans hVU) a :=
  (PresheafOfModules.map_comp_apply ((Scheme.Modules.pullback f).obj F).val
        (homOfLE hVU).op (homOfLE hWV).op
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).val.app (op U) a)).symm.trans
    (PresheafOfModules.congr_map_apply ((Scheme.Modules.pullback f).obj F).val
      (Subsingleton.elim _ _) _)

end Scheme.Modules

/-- The transition map of the pullback-sections presheaf of Tag 03DS carries the pullback of a
section of `F` over an open of `S` containing the image of the structure morphism to the
pullback of the same section. -/
public theorem pullbackSectionsMap_pullbackSection {S : Scheme.{u}} (F : S.Modules)
    {X Y : Over S} (g : X ⟶ Y) (V : S.Opens)
    (hY : (⊤ : Y.left.Opens) ≤ Y.hom ⁻¹ᵁ V) (hX : (⊤ : X.left.Opens) ≤ X.hom ⁻¹ᵁ V)
    (a : Γ(F, V)) :
    pullbackSectionsMap F g (Scheme.Modules.pullbackSection Y.hom F V ⊤ hY a) =
      Scheme.Modules.pullbackSection X.hom F V ⊤ hX a := by
  have hf : (⊤ : X.left.Opens) ≤ g.left ⁻¹ᵁ (⊤ : Y.left.Opens) := by simp
  have hcomp : (⊤ : X.left.Opens) ≤ (g.left ≫ Y.hom) ⁻¹ᵁ V := by rw [Over.w g]; exact hX
  have hunfold : pullbackSectionsMap F g =
      ((Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app
          ((Scheme.Modules.pullback Y.hom).obj F) ≫
        (Scheme.Modules.pushforward g.left).map
          ((Scheme.Modules.pullbackComp g.left Y.hom).hom.app F ≫
            (Scheme.Modules.pullbackCongr (Over.w g)).hom.app F)).app ⊤ ≫
      ((Scheme.Modules.pullback X.hom).obj F).presheaf.map
        (eqToHom (show (⊤ : X.left.Opens) = g.left ⁻¹ᵁ ⊤ by simp)).op := rfl
  rw [hunfold, Scheme.Modules.presheaf_map_top_eq_id g.left _
    ((Scheme.Modules.pullback X.hom).obj F)]
  change (((Scheme.Modules.pullbackCongr (Over.w g)).hom.app F).val.app (op ⊤))
      ((((Scheme.Modules.pullbackComp g.left Y.hom).hom.app F).val.app (op ⊤))
        ((((Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app
            ((Scheme.Modules.pullback Y.hom).obj F)).val.app (op ⊤))
          (Scheme.Modules.pullbackSection Y.hom F V ⊤ hY a))) = _
  rw [← Scheme.Modules.pullbackSection_top g.left
      ((Scheme.Modules.pullback Y.hom).obj F) hf
      (Scheme.Modules.pullbackSection Y.hom F V ⊤ hY a),
    Scheme.Modules.pullbackSection_comp g.left Y.hom F V ⊤ ⊤ hY hf hcomp a,
    Scheme.Modules.pullbackSection_congr (Over.w g) F V ⊤ hcomp hX a]

end AlgebraicGeometry

end
