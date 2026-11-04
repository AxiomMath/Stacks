module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.Topology.Sheaves.Limits.FilteredColimitSections
public import StacksFrontier.Topology.Sheaves.Sheafify.Stalk

/-!
# Global sections of a filtered colimit of sheaves of sets

Let `X` be a topological space and let `D : I ⥤ TopCat.Sheaf (Type u) X` be a filtered diagram of
sheaves of sets on `X`.  Part (4) of Stacks 009F says that if the whole space has a cofinal system
of finite open coverings whose pairwise intersections are quasi-compact, then the canonical map

`colim_i D_i(U) ⟶ (colim_i D_i)(U)`

is bijective for `U = ⊤`.  That statement is about the explicit model of the colimit used in
`StacksFrontier/Topology/Sheaves/Limits/FilteredColimitSections.lean`: the colimit presheaf and its
sheaf of germs.  This file turns it into the functorial assertion that the global sections functor
preserves such colimits, which is the form a consumer uses.

The translation has two steps.  First, the colimit of `D` in sheaves is the sheafification of the
colimit of the underlying presheaves, so the sheafification cocone
`CategoryTheory.Sheaf.sheafifyCocone` on the presheaf colimit is a colimit cocone; second,
sheafification for the Grothendieck topology of the opens of `X` agrees with the sheaf of germs,
because the comparison map is an isomorphism on all stalks.  Combining the two identifies the
sections of the colimit over `⊤` with the right-hand side of the map of Stacks 009F, and the map
itself with the comparison map of the sections cocone.

## Main definitions

* `DirectedColimitOfSheaves.presheafToSheafIsoSheafify`: sheafification of a presheaf of sets on a
  space, computed for the Grothendieck topology of its opens, is the sheaf of germs.

## Main results

* `DirectedColimitOfSheaves.preservesColimit_sheafSectionsTop`: sections over `⊤` take a filtered
  colimit cocone of sheaves of sets to a colimit cocone of types.
* `DirectedColimitOfSheaves.preservesColimitsOfShape_sheafSectionsTop` and
  `DirectedColimitOfSheaves.preservesColimitsOfShape_globalSections`: the same for every filtered
  diagram of the given shape, for the sections functor at `⊤` and for the global sections functor
  `CategoryTheory.Sheaf.Γ`.

## Implementation notes

The hypothesis is `DirectedColimitOfSheaves.HasFiniteCompactCofinalCovers ⊤`, exactly as stated
for Stacks 009F: every open covering of `⊤` is refined by a finite covering of `⊤` all of whose
pairwise intersections are quasi-compact.  It is not weakened to quasi-compactness of `X`, which is
the hypothesis of part (3) and additionally requires the transition maps to be injective.

The index category is taken in the same universe as the sections of the sheaves, with morphisms
there too.  This is what Stacks 009F needs (its colimit presheaf is formed in that universe) and
what makes `Type u` have the colimits at issue.

`CategoryTheory.Sheaf.Γ` is the right adjoint of the constant sheaf functor, which on a site with
a terminal object is the sections functor at that object; here the terminal object is `⊤`.  The
statement for `Sheaf.Γ` is obtained from the one for sections at `⊤` along
`CategoryTheory.Sheaf.ΓNatIsoSheafSections`, so it does not depend on which instance provides the
global sections functor.

## References

* [Stacks Project, Tag 009F](https://stacks.math.columbia.edu/tag/009F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace DirectedColimitOfSheaves

variable {X : TopCat.{u}}

/-- **Sheafification of a presheaf of sets on a space is the sheaf of germs.**  The sheafification
of the Grothendieck topology of the opens of `X` and the sheaf of germs both receive the unit map
from `P`, and both units are isomorphisms on every stalk, so the comparison map between them is an
isomorphism of sheaves. -/
noncomputable def presheafToSheafIsoSheafify (P : TopCat.Presheaf (Type u) X) :
    (presheafToSheaf (Opens.grothendieckTopology ↑X) (Type u)).obj P ≅ P.sheafify := by
  let J := Opens.grothendieckTopology ↑X
  let adj := sheafificationAdjunction J (Type u)
  let θ : (presheafToSheaf J (Type u)).obj P ⟶ P.sheafify :=
    (adj.homEquiv P P.sheafify).symm P.toSheafify
  have htri : toSheafify J P ≫ θ.hom = P.toSheafify :=
    (adj.homEquiv P P.sheafify).apply_symm_apply P.toSheafify
  haveI : IsIso θ := by
    have (x : X) : IsIso ((TopCat.Presheaf.stalkFunctor (Type u) x).map θ.hom) := by
      have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (Type u) P
      have hc : IsIso (((TopCat.Presheaf.stalkFunctor (Type u) x).map (toSheafify J P)) ≫
          ((TopCat.Presheaf.stalkFunctor (Type u) x).map θ.hom)) := by
        rw [← Functor.map_comp, htri]
        exact stalkFunctor_map_toSheafify_isIso P x
      exact (isIso_comp_left_iff _ _).mp hc
    exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso θ
  exact asIso θ

variable {I : Type u} [Category.{u} I] [IsFiltered I] (D : I ⥤ TopCat.Sheaf (Type u) X)

/-- **Stacks 009F (4) for the sheafification cocone.**  Sections over `⊤` carry the canonical
colimit cocone of `D` — the sheafification of the colimit cocone of the underlying presheaves — to
a colimit cocone of types.

Sections over `⊤` of the colimit presheaf already form the colimit of the sections, since colimits
of presheaves are pointwise; the map from there to the sections of the sheafification is the
canonical map of Stacks 009F, which part (4) shows to be bijective. -/
noncomputable def isColimit_sheafSectionsTop_sheafifyCocone
    (hX : HasFiniteCompactCofinalCovers (X := X) ⊤) :
    IsColimit (((sheafSections (Opens.grothendieckTopology ↑X) (Type u)).obj (op ⊤)).mapCocone
      (CategoryTheory.Sheaf.sheafifyCocone (colimit.cocone (presheafSystem D)))) := by
  let P := presheafSystem D
  let E := (evaluation ((Opens ↑X)ᵒᵖ) (Type u)).obj (op ⊤)
  let cP := colimit.cocone P
  let c := CategoryTheory.Sheaf.sheafifyCocone cP
  let Γ := (sheafSections (Opens.grothendieckTopology ↑X) (Type u)).obj (op ⊤)
  let θ := presheafToSheafIsoSheafify cP.pt
  let eθ := (Γ.mapIso θ).toEquiv
  let ψ := canonicalMap D ⊤
  let e : (E.mapCocone cP).pt ≃ (Γ.mapCocone c).pt := (Equiv.ofBijective ψ
    (bijective_canonicalMap_of_hasFiniteCompactCofinalCovers D ⊤ hX)).trans eθ.symm
  have hL := Functor.coconeTypesEquiv_symm_apply_pt (P ⋙ E) (E.mapCocone cP)
  have hR := Functor.coconeTypesEquiv_symm_apply_pt (D ⋙ Γ) (Γ.mapCocone c)
  let e' : ((P ⋙ E).coconeTypesEquiv.symm (E.mapCocone cP)).pt ≃
      ((D ⋙ Γ).coconeTypesEquiv.symm (Γ.mapCocone c)).pt :=
    ((Equiv.cast hL).trans e).trans (Equiv.cast hR.symm)
  refine ((Types.isColimit_iff_coconeTypesIsColimit (Γ.mapCocone c)).2 ?_).some
  apply ((Types.isColimit_iff_coconeTypesIsColimit (E.mapCocone cP)).1
    ⟨isColimitOfPreserves E (colimit.isColimit P)⟩).of_equiv e'
  intro j x
  apply eθ.injective
  refine Eq.trans ?_ (eθ.apply_symm_apply (ψ (E.map (cP.ι.app j) x))).symm
  change θ.hom.hom.app (op ⊤) ((c.ι.app j).hom.app (op ⊤) x) =
    cP.pt.toSheafify.app (op ⊤) ((cP.ι.app j).app (op ⊤) x)
  have htri : toSheafify (Opens.grothendieckTopology ↑X) cP.pt ≫ θ.hom.hom = cP.pt.toSheafify :=
    ((sheafificationAdjunction (Opens.grothendieckTopology ↑X) (Type u)).homEquiv cP.pt
      cP.pt.sheafify).apply_symm_apply cP.pt.toSheafify
  exact (congrArg (fun q => θ.hom.hom.app (op ⊤) (q.app (op ⊤) x))
      (CategoryTheory.Sheaf.sheafifyCocone_ι_app_val cP j)).trans
    (congrArg (fun q => q.app (op ⊤) ((cP.ι.app j).app (op ⊤) x)) htri)

/-- **Global sections of a filtered colimit of sheaves of sets**, for a fixed diagram: sections
over `⊤` take any colimit cocone of `D` to a colimit cocone of types, when every open covering of
the space is refined by a finite one with quasi-compact pairwise intersections.  This is Stacks
009F (4) read functorially. -/
theorem preservesColimit_sheafSectionsTop (hX : HasFiniteCompactCofinalCovers (X := X) ⊤) :
    PreservesColimit D ((sheafSections (Opens.grothendieckTopology ↑X) (Type u)).obj (op ⊤)) :=
  preservesColimit_of_preserves_colimit_cocone
    (CategoryTheory.Sheaf.isColimitSheafifyCocone (colimit.cocone (presheafSystem D))
      (colimit.isColimit (presheafSystem D)))
    (isColimit_sheafSectionsTop_sheafifyCocone D hX)

variable (I) in
/-- Sections over `⊤` preserve all filtered colimits of the given shape, when every open covering
of the space is refined by a finite one with quasi-compact pairwise intersections. -/
theorem preservesColimitsOfShape_sheafSectionsTop
    (hX : HasFiniteCompactCofinalCovers (X := X) ⊤) :
    PreservesColimitsOfShape I
      ((sheafSections (Opens.grothendieckTopology ↑X) (Type u)).obj (op ⊤)) :=
  ⟨fun {D} => preservesColimit_sheafSectionsTop D hX⟩

variable (I) in
/-- **The global sections functor preserves filtered colimits of sheaves of sets** on a space
every open covering of which is refined by a finite one with quasi-compact pairwise intersections.
The global sections functor of a site with a terminal object is the sections functor at that
object, here `⊤`. -/
theorem preservesColimitsOfShape_globalSections
    (hX : HasFiniteCompactCofinalCovers (X := X) ⊤) :
    PreservesColimitsOfShape I (Sheaf.Γ (Opens.grothendieckTopology ↑X) (Type u)) :=
  have := preservesColimitsOfShape_sheafSectionsTop (X := X) I hX
  preservesColimitsOfShape_of_natIso
    (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology ↑X) (Type u)
      (isTerminalTop (α := Opens ↑X))).symm

end DirectedColimitOfSheaves

end
