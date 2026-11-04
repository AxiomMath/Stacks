module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage

/-!
# Global sections of Zariski and étale sheaves along a morphism of schemes

A continuous functor of sites whose inverse image on sheaves is left adjoint to the restriction
functor induces a comparison map on sections: a section over an object `U` of the source site is
sent, by the unit of the adjunction, to a section of the inverse image over the image of `U`, and
then restricted along any map into that image. When the two sites have terminal objects this is
the comparison map on global sections.

For a morphism of schemes `f : Y ⟶ X` this produces the restriction map
`Γ(X, F) → Γ(Y, f⁻¹F)` for Zariski sheaves and, for the small étale sites, the comparison
`Γ(X, F) → Γ(Z, i⁻¹F)` on étale global sections. These are the two maps compared by Gabber's
theorem on global sections over a closed subscheme.

## Main definitions

* `Stacks.Sites.sectionsPullbackComparison` is the comparison map on sections over a pair of
  objects of the two sites, joined by a morphism into the image of the first.
* `Stacks.Sites.globalSectionsPullbackComparison` is the comparison map on global sections, for
  sites with terminal objects.
* `Stacks.EtaleCohomology.zariskiSectionsComparison` and
  `Stacks.EtaleCohomology.zariskiGlobalSectionsComparison` are the restriction maps on sections
  over the whole space and on global sections of Zariski sheaves along a morphism of schemes.
* `Stacks.EtaleCohomology.smallEtaleInverseImageAdjunction` is the adjunction between inverse
  image and restriction on sheaves of types on the small étale sites.
* `Stacks.EtaleCohomology.isTerminalSmallEtaleBaseChangeObjTerminal` exhibits the base change of
  the terminal object of a small étale site as a terminal object.
* `Stacks.EtaleCohomology.smallEtaleGlobalSectionsComparison` is the comparison map on global
  sections of sheaves on the small étale sites.

## Main results

* `Stacks.Sites.sectionsPullbackComparison_eq_of_isTerminal` and
  `Stacks.Sites.globalSectionsPullbackComparison_eq_of_isTerminal`: when the image of the chosen
  object of the source site is terminal, the comparison does not depend on the chosen morphism,
  so the comparison on global sections is canonical.
* `Stacks.EtaleCohomology.zariskiSectionsComparison_app`: on the Zariski sites the comparison on
  sections over the whole space is the component of the unit of the adjunction at the whole
  space, because the whole space pulls back to the whole space.
* `Stacks.EtaleCohomology.smallEtaleGlobalSectionsComparison_eq`: the comparison on étale global
  sections computed from an arbitrary morphism of terminal objects is the canonical one.
* `Stacks.EtaleCohomology.isIso_zariskiGlobalSectionsComparison_iff_bijective` and
  `Stacks.EtaleCohomology.isIso_smallEtaleGlobalSectionsComparison_iff_bijective`: each
  comparison is an isomorphism exactly when it is bijective on every sheaf, which is the form in
  which the hypothesis and the conclusion of Gabber's theorem are stated.

## Implementation notes

The comparison is built by whiskering the unit of the adjunction with the sections functor and
then restricting along the chosen morphism, so naturality in the sheaf is inherited and no
naturality square has to be checked by hand. The adjunction is an explicit argument rather than
the chosen left adjoint `CategoryTheory.Functor.sheafPullback`, because the inverse image on the
small étale sites is the concrete left Kan extension followed by sheafification, which is only
isomorphic to that chosen left adjoint.

The terminal object of the small étale site of `X` is the identity of `X`, and base change along
`i : Z ⟶ X` preserves it because base change on small étale sites is left exact; this is what
makes the comparison on étale global sections independent of any choice.

## References

* [Stacks Project, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.Sites

section Sections

variable {C : Type*} [Category C] {D : Type*} [Category D] (G : C ⥤ D)
  (A : Type*) [Category A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K] {P : Sheaf J A ⥤ Sheaf K A}

/-- The comparison map on sections induced by a continuous functor of sites `G` together with an
adjunction between an inverse-image functor `P` and restriction along `G`: a section over `U` is
carried by the unit of the adjunction to a section of `P` over `G.obj U`, and then restricted
along a morphism `g : V ⟶ G.obj U`. -/
public def sectionsPullbackComparison (adj : P ⊣ G.sheafPushforwardContinuous A J K)
    {U : C} {V : D} (g : V ⟶ G.obj U) :
    (sheafSections J A).obj (op U) ⟶ P ⋙ (sheafSections K A).obj (op V) :=
  Functor.whiskerRight adj.unit ((sheafSections J A).obj (op U)) ≫
    Functor.whiskerLeft P ((sheafSections K A).map g.op)

/-- The comparison map on sections is the unit of the adjunction over `G.obj U`, restricted along
the chosen morphism. -/
public theorem sectionsPullbackComparison_app
    (adj : P ⊣ G.sheafPushforwardContinuous A J K) {U : C} {V : D} (g : V ⟶ G.obj U)
    (F : Sheaf J A) :
    (sectionsPullbackComparison G A J K adj g).app F =
      (adj.unit.app F).hom.app (op U) ≫ (P.obj F).obj.map g.op :=
  rfl

/-- If the image of `U` is a terminal object, the comparison map on sections does not depend on
the chosen morphism `V ⟶ G.obj U`. -/
public theorem sectionsPullbackComparison_eq_of_isTerminal
    (adj : P ⊣ G.sheafPushforwardContinuous A J K) {U : C} {V : D}
    (hGU : IsTerminal (G.obj U)) (g g' : V ⟶ G.obj U) :
    sectionsPullbackComparison G A J K adj g =
      sectionsPullbackComparison G A J K adj g' := by
  rw [hGU.hom_ext g g']

end Sections

section GlobalSections

variable {C : Type*} [Category C] {D : Type*} [Category D] (G : C ⥤ D)
  (A : Type*) [Category A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K] {P : Sheaf J A ⥤ Sheaf K A}
  [HasWeakSheafify J A] [HasWeakSheafify K A] [HasTerminal C] [HasTerminal D]

/-- The comparison map on global sections induced by a continuous functor of sites and an
adjunction between an inverse-image functor and restriction along it, on sites with terminal
objects. -/
public def globalSectionsPullbackComparison
    (adj : P ⊣ G.sheafPushforwardContinuous A J K) {U : C} {V : D}
    (hU : IsTerminal U) (hV : IsTerminal V) (g : V ⟶ G.obj U) :
    Sheaf.Γ J A ⟶ P ⋙ Sheaf.Γ K A :=
  (Sheaf.ΓNatIsoSheafSections J A hU).hom ≫ sectionsPullbackComparison G A J K adj g ≫
    Functor.whiskerLeft P (Sheaf.ΓNatIsoSheafSections K A hV).inv

/-- The comparison map on global sections is the comparison map on sections over the two terminal
objects, read through the identification of global sections with sections over a terminal
object. -/
public theorem globalSectionsPullbackComparison_app
    (adj : P ⊣ G.sheafPushforwardContinuous A J K) {U : C} {V : D}
    (hU : IsTerminal U) (hV : IsTerminal V) (g : V ⟶ G.obj U) (F : Sheaf J A) :
    (globalSectionsPullbackComparison G A J K adj hU hV g).app F =
      (Sheaf.ΓNatIsoSheafSections J A hU).hom.app F ≫
        (sectionsPullbackComparison G A J K adj g).app F ≫
          (Sheaf.ΓNatIsoSheafSections K A hV).inv.app (P.obj F) :=
  rfl

/-- If the image of the terminal object is terminal, the comparison map on global sections does
not depend on the chosen morphism of terminal objects. -/
public theorem globalSectionsPullbackComparison_eq_of_isTerminal
    (adj : P ⊣ G.sheafPushforwardContinuous A J K) {U : C} {V : D}
    (hU : IsTerminal U) (hV : IsTerminal V) (hGU : IsTerminal (G.obj U))
    (g g' : V ⟶ G.obj U) :
    globalSectionsPullbackComparison G A J K adj hU hV g =
      globalSectionsPullbackComparison G A J K adj hU hV g' := by
  rw [hGU.hom_ext g g']

end GlobalSections

end Stacks.Sites

namespace Stacks.EtaleCohomology

section Zariski

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- Restriction of sections over the whole space along a morphism of schemes, for sheaves of types
on the Zariski sites. -/
public def zariskiSectionsComparison :
    (sheafSections (Opens.grothendieckTopology X.carrier)
        (Type (max (u + 1) v))).obj (op ⊤) ⟶
      (Opens.map f.base).sheafPullback (Type (max (u + 1) v))
          (Opens.grothendieckTopology X.carrier)
          (Opens.grothendieckTopology Y.carrier) ⋙
        (sheafSections (Opens.grothendieckTopology Y.carrier)
          (Type (max (u + 1) v))).obj (op ⊤) :=
  Stacks.Sites.sectionsPullbackComparison (Opens.map f.base) (Type (max (u + 1) v))
    (Opens.grothendieckTopology X.carrier) (Opens.grothendieckTopology Y.carrier)
    ((Opens.map f.base).sheafAdjunctionContinuous (Type (max (u + 1) v))
      (Opens.grothendieckTopology X.carrier) (Opens.grothendieckTopology Y.carrier))
    (homOfLE le_top)

/-- On a Zariski sheaf, restriction of sections over the whole space is the component at the whole
space of the unit of the inverse-image/direct-image adjunction, since the whole space pulls back
to the whole space. -/
public theorem zariskiSectionsComparison_app
    (F : Sheaf (Opens.grothendieckTopology X.carrier) (Type (max (u + 1) v))) :
    (zariskiSectionsComparison.{u, v} f).app F =
      (((Opens.map f.base).sheafAdjunctionContinuous (Type (max (u + 1) v))
        (Opens.grothendieckTopology X.carrier)
        (Opens.grothendieckTopology Y.carrier)).unit.app F).hom.app (op ⊤) := by
  refine (Stacks.Sites.sectionsPullbackComparison_app _ _ _ _ _ _ F).trans ?_
  simp
  rfl

/-- Restriction of global sections along a morphism of schemes, for sheaves of types on the
Zariski sites. -/
public def zariskiGlobalSectionsComparison :
    Sheaf.Γ (Opens.grothendieckTopology X.carrier) (Type (max (u + 1) v)) ⟶
      (Opens.map f.base).sheafPullback (Type (max (u + 1) v))
          (Opens.grothendieckTopology X.carrier)
          (Opens.grothendieckTopology Y.carrier) ⋙
        Sheaf.Γ (Opens.grothendieckTopology Y.carrier) (Type (max (u + 1) v)) :=
  Stacks.Sites.globalSectionsPullbackComparison (Opens.map f.base) (Type (max (u + 1) v))
    (Opens.grothendieckTopology X.carrier) (Opens.grothendieckTopology Y.carrier)
    ((Opens.map f.base).sheafAdjunctionContinuous (Type (max (u + 1) v))
      (Opens.grothendieckTopology X.carrier) (Opens.grothendieckTopology Y.carrier))
    isTerminalTop isTerminalTop (homOfLE le_top)

/-- Restriction of global sections of Zariski sheaves is an isomorphism of functors exactly when
it is bijective on every Zariski sheaf of types. -/
public theorem isIso_zariskiGlobalSectionsComparison_iff_bijective :
    IsIso (zariskiGlobalSectionsComparison.{u, v} f) ↔
      ∀ F : Sheaf (Opens.grothendieckTopology X.carrier) (Type (max (u + 1) v)),
        Function.Bijective ((zariskiGlobalSectionsComparison.{u, v} f).app F) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact forall_congr' fun _ => isIso_iff_bijective _

end Zariski

section SmallEtale

variable {X Z : Scheme.{u}} (i : Z ⟶ X)

/-- Inverse image on sheaves of types on the small étale sites is left adjoint to restriction
along étale base change. -/
public def smallEtaleInverseImageAdjunction :
    smallEtaleInverseImage.{u, v} i ⊣
      (smallEtaleBaseChange i).sheafPushforwardContinuous
        (Type (max (u + 1) v)) (smallEtaleTopology X) (smallEtaleTopology Z) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (smallEtaleBaseChange i) (Type (max (u + 1) v))
    (smallEtaleTopology X) (smallEtaleTopology Z)

/-- Étale base change along a morphism of schemes carries the terminal object of the small étale
site to a terminal object, because it is left exact. -/
public def isTerminalSmallEtaleBaseChangeObjTerminal :
    IsTerminal ((smallEtaleBaseChange i).obj (terminal X.Etale)) :=
  terminalIsTerminal.isTerminalObj _

/-- The comparison map on global sections of sheaves of types on the small étale sites, induced by
inverse image along a morphism of schemes. -/
public def smallEtaleGlobalSectionsComparison :
    Sheaf.Γ (smallEtaleTopology X) (Type (max (u + 1) v)) ⟶
      smallEtaleInverseImage.{u, v} i ⋙
        Sheaf.Γ (smallEtaleTopology Z) (Type (max (u + 1) v)) :=
  Stacks.Sites.globalSectionsPullbackComparison (smallEtaleBaseChange i)
    (Type (max (u + 1) v)) (smallEtaleTopology X) (smallEtaleTopology Z)
    (smallEtaleInverseImageAdjunction.{u, v} i) terminalIsTerminal terminalIsTerminal
    ((isTerminalSmallEtaleBaseChangeObjTerminal i).from _)

/-- The comparison map on étale global sections is canonical: computing it from an arbitrary
morphism from the terminal object of the small étale site of `Z` to the base change of the
terminal object of the small étale site of `X` gives the same natural transformation. -/
public theorem smallEtaleGlobalSectionsComparison_eq
    (g : terminal Z.Etale ⟶ (smallEtaleBaseChange i).obj (terminal X.Etale)) :
    Stacks.Sites.globalSectionsPullbackComparison (smallEtaleBaseChange i)
        (Type (max (u + 1) v)) (smallEtaleTopology X) (smallEtaleTopology Z)
        (smallEtaleInverseImageAdjunction.{u, v} i) terminalIsTerminal terminalIsTerminal g =
      smallEtaleGlobalSectionsComparison.{u, v} i :=
  Stacks.Sites.globalSectionsPullbackComparison_eq_of_isTerminal _ _ _ _ _ _ _
    (isTerminalSmallEtaleBaseChangeObjTerminal i) _ _

/-- The comparison map on étale global sections is an isomorphism exactly when it is bijective on
every sheaf of types on the small étale site. -/
public theorem isIso_smallEtaleGlobalSectionsComparison_iff_bijective :
    IsIso (smallEtaleGlobalSectionsComparison.{u, v} i) ↔
      ∀ F : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v)),
        Function.Bijective ((smallEtaleGlobalSectionsComparison.{u, v} i).app F) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact forall_congr' fun _ => isIso_iff_bijective _

end SmallEtale

end Stacks.EtaleCohomology

end
