module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.Topology.Sheaves.Functors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage

/-!
# Global sections of étale sheaves over a closed subscheme

Let `i : Z ⟶ X` be a morphism of schemes. On the Zariski site, restriction of global sections
along `i` is the component at the top open of the unit of the inverse-image/direct-image
adjunction, `zariskiGlobalSectionsMap`.

On the small étale site the inverse image is a left Kan extension along base change
`X.Etale ⥤ Z.Etale` followed by sheafification. The comparison on global sections is the
composite, evaluated at final objects, of the unit of the left Kan extension, restriction along
the unique morphism from the final object of `Z.Etale` to the base change of the final object of
`X.Etale`, and the sheafification map. That composite is
`smallEtaleGlobalSectionsPresheafComparison`; whiskering it between the two identifications of
global sections with sections at a final object gives the natural transformation
`globalSectionsSmallEtaleInverseImageComparison`.

## Main definitions

* `Stacks.EtaleCohomology.zariskiGlobalSectionsMap` — restriction of global sections of a
  Zariski sheaf along a morphism of schemes.
* `Stacks.EtaleCohomology.smallEtaleGlobalSectionsPresheafComparison` — the presheaf-level
  comparison: the unit of the left Kan extension, restriction along `g`, then the sheafification
  map, all evaluated at final objects.
* `Stacks.EtaleCohomology.smallEtaleGlobalSectionsMapAt` — the induced map on étale global
  sections, for a chosen morphism `g` out of the final object.
* `Stacks.EtaleCohomology.globalSectionsSmallEtaleInverseImageComparison` — the canonical
  comparison of étale global sections, together with the equations characterizing it
  componentwise.

## Main results

* `Stacks.EtaleCohomology.smallEtaleGlobalSectionsMapAt_eq` — the map on global sections does
  not depend on the choice of `g`, since that morphism is unique.
* `Stacks.EtaleCohomology.isIso_globalSectionsSmallEtaleInverseImageComparison_iff` — the
  comparison is an isomorphism exactly when every pullback map on global sections is bijective.

## References

* [Stacks Project, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open TopologicalSpace

universe u v

namespace Stacks.EtaleCohomology

/-- Restriction of global sections along a morphism of schemes, using the unit of the sheaf
pullback/pushforward adjunction for the Zariski sites. -/
public def zariskiGlobalSectionsMap {Y X : Scheme.{u}} (f : Y ⟶ X)
    (F : Sheaf (Opens.grothendieckTopology X.carrier) (Type (max (u + 1) v))) :
    F.obj.obj (op ⊤) →
      (((Opens.map f.base).sheafPullback (Type (max (u + 1) v))
        (Opens.grothendieckTopology X.carrier)
        (Opens.grothendieckTopology Y.carrier)).obj F).obj.obj (op ⊤) :=
  (((Opens.map f.base).sheafAdjunctionContinuous
    (Type (max (u + 1) v))
    (Opens.grothendieckTopology X.carrier)
    (Opens.grothendieckTopology Y.carrier)).unit.app F).hom.app (op ⊤)

variable {X Z : Scheme.{u}} (i : Z ⟶ X)

/-- The presheaf-level comparison for the small étale sites: the unit of the left Kan extension
along base change, evaluated at the final object of `X.Etale`, then restriction along
`g : ⊤_ Z.Etale ⟶ (smallEtaleBaseChange i).obj (⊤_ X.Etale)`, then the sheafification map,
evaluated at the final object of `Z.Etale`. -/
public def smallEtaleGlobalSectionsPresheafComparison
    (g : terminal Z.Etale ⟶ (smallEtaleBaseChange i).obj (terminal X.Etale)) :
    (evaluation X.Etaleᵒᵖ (Type (max (u + 1) v))).obj (op (terminal X.Etale)) ⟶
      (smallEtaleBaseChange i).op.lan ⋙
        presheafToSheaf (Scheme.smallEtaleTopology Z) (Type (max (u + 1) v)) ⋙
          sheafToPresheaf (Scheme.smallEtaleTopology Z) (Type (max (u + 1) v)) ⋙
            (evaluation Z.Etaleᵒᵖ (Type (max (u + 1) v))).obj (op (terminal Z.Etale)) :=
  Functor.whiskerRight (smallEtaleBaseChange i).op.lanUnit
      ((evaluation X.Etaleᵒᵖ (Type (max (u + 1) v))).obj (op (terminal X.Etale))) ≫
    Functor.whiskerLeft (smallEtaleBaseChange i).op.lan
      ((evaluation Z.Etaleᵒᵖ (Type (max (u + 1) v))).map g.op ≫
        Functor.whiskerRight
          (sheafificationAdjunction (Scheme.smallEtaleTopology Z)
            (Type (max (u + 1) v))).unit
          ((evaluation Z.Etaleᵒᵖ (Type (max (u + 1) v))).obj (op (terminal Z.Etale))))

/-- The canonical pullback of an étale global section, expressed on final objects by the units
of the left Kan extension and of sheafification. -/
public def smallEtaleGlobalSectionsMapAt
    (g : terminal Z.Etale ⟶ (smallEtaleBaseChange i).obj (terminal X.Etale))
    (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v))) :
    (Sheaf.Γ (Scheme.smallEtaleTopology X) (Type (max (u + 1) v))).obj F ⟶
      (Sheaf.Γ (Scheme.smallEtaleTopology Z) (Type (max (u + 1) v))).obj
        ((smallEtaleInverseImage i).obj F) :=
  ((Sheaf.ΓNatIsoSheafSections (Scheme.smallEtaleTopology X)
    (Type (max (u + 1) v)) terminalIsTerminal).hom.app F) ≫
  (((smallEtaleBaseChange i).op.lanUnit.app F.obj).app (op (terminal X.Etale))) ≫
  (((smallEtaleBaseChange i).op.lan.obj F.obj).map g.op) ≫
  ((toSheafify (Scheme.smallEtaleTopology Z)
    ((smallEtaleBaseChange i).op.lan.obj F.obj)).app (op (terminal Z.Etale))) ≫
  ((Sheaf.ΓNatIsoSheafSections (Scheme.smallEtaleTopology Z)
    (Type (max (u + 1) v)) terminalIsTerminal).inv.app
      ((smallEtaleInverseImage i).obj F))

/-- The comparison on global sections, as a natural transformation of global-sections functors:
the identification of global sections with sections at a final object, the presheaf-level
comparison, and the identification back again. -/
public def smallEtaleGlobalSectionsNatTrans
    (g : terminal Z.Etale ⟶ (smallEtaleBaseChange i).obj (terminal X.Etale)) :
    Sheaf.Γ (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)) ⟶
      smallEtaleInverseImage i ⋙
        Sheaf.Γ (Scheme.smallEtaleTopology Z) (Type (max (u + 1) v)) :=
  (Sheaf.ΓNatIsoSheafSections (Scheme.smallEtaleTopology X)
      (Type (max (u + 1) v)) (T := terminal X.Etale) terminalIsTerminal).hom ≫
    Functor.whiskerLeft
      (sheafToPresheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)))
      (smallEtaleGlobalSectionsPresheafComparison i g) ≫
    Functor.whiskerLeft (smallEtaleInverseImage i)
      (Sheaf.ΓNatIsoSheafSections (Scheme.smallEtaleTopology Z)
        (Type (max (u + 1) v)) (T := terminal Z.Etale) terminalIsTerminal).inv

/-- The natural transformation `smallEtaleGlobalSectionsNatTrans` has, by construction, the
components `smallEtaleGlobalSectionsMapAt`. -/
@[simp]
public theorem smallEtaleGlobalSectionsNatTrans_app
    (g : terminal Z.Etale ⟶ (smallEtaleBaseChange i).obj (terminal X.Etale))
    (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v))) :
    (smallEtaleGlobalSectionsNatTrans i g).app F =
      smallEtaleGlobalSectionsMapAt i g F := rfl

/-- There is exactly one morphism from the final object of `Z.Etale` to the base change of the
final object of `X.Etale`, because the latter is again a final object. -/
public theorem eq_of_hom_terminal_smallEtaleBaseChange
    (g g' : terminal Z.Etale ⟶ (smallEtaleBaseChange i).obj (terminal X.Etale)) : g = g' :=
  (isTerminalSmallEtaleBaseChangeObj i terminalIsTerminal).hom_ext g g'

/-- The map on étale global sections does not depend on the choice of the morphism out of the
final object, since that morphism is unique. -/
public theorem smallEtaleGlobalSectionsMapAt_eq
    (g g' : terminal Z.Etale ⟶ (smallEtaleBaseChange i).obj (terminal X.Etale))
    (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v))) :
    smallEtaleGlobalSectionsMapAt i g F = smallEtaleGlobalSectionsMapAt i g' F := by
  rw [eq_of_hom_terminal_smallEtaleBaseChange i g g']

/-- The canonical comparison of global sections of an étale sheaf with global sections of its
inverse image on `Z`, together with the equations saying that it is, componentwise, the
standard pullback of sections: the unit of the left Kan extension along base change followed by
the sheafification map, evaluated at final objects. -/
public def globalSectionsSmallEtaleInverseImageComparison :
    {η : Sheaf.Γ (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)) ⟶
      smallEtaleInverseImage i ⋙
        Sheaf.Γ (Scheme.smallEtaleTopology Z) (Type (max (u + 1) v)) //
      ∀ (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)))
        (g : terminal Z.Etale ⟶
          (smallEtaleBaseChange i).obj (terminal X.Etale)),
        η.app F = smallEtaleGlobalSectionsMapAt i g F} :=
  ⟨smallEtaleGlobalSectionsNatTrans i
      ((isTerminalSmallEtaleBaseChangeObj i terminalIsTerminal).from _),
    fun F g ↦ smallEtaleGlobalSectionsMapAt_eq i _ g F⟩

/-- The comparison is an isomorphism exactly when every pullback map on global sections is
bijective. -/
public theorem isIso_globalSectionsSmallEtaleInverseImageComparison_iff :
    IsIso (globalSectionsSmallEtaleInverseImageComparison.{u, v} i).val ↔
      ∀ (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)))
        (g : terminal Z.Etale ⟶ (smallEtaleBaseChange i).obj (terminal X.Etale)),
        Function.Bijective (smallEtaleGlobalSectionsMapAt i g F) := by
  rw [NatTrans.isIso_iff_isIso_app]
  refine ⟨fun h F g ↦ ?_, fun h F ↦ ?_⟩
  · rw [← isIso_iff_bijective,
      ← (globalSectionsSmallEtaleInverseImageComparison.{u, v} i).2 F g]
    exact h F
  · rw [(globalSectionsSmallEtaleInverseImageComparison.{u, v} i).2 F
      ((isTerminalSmallEtaleBaseChangeObj i terminalIsTerminal).from _),
      isIso_iff_bijective]
    exact h F _

end Stacks.EtaleCohomology
