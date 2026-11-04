module

public import Mathlib.Geometry.RingedSpace.Stalks

/-!
# Stalks of the restriction of a presheaf to an open subspace

Let `X` be a topological space, let `U ⊆ X` be open with inclusion `j : U → X`, and let `P` be a
presheaf on `X`. The naive restriction of `P` to `U` is the presheaf `W ↦ P(j(W))`, that is, the
composite of `P` with the opposite of the functor `Opens U ⥤ Opens X` taking an open of `U` to
its image. Its stalk at a point `u` of `U` is the stalk of `P` at `j u`.

## Main results

* `TopCat.Presheaf.stalkRestrictIso`: the isomorphism `(j⁻¹P)_u ≅ P_{j u}`.
* `TopCat.Presheaf.stalkRestrictIso_germ`: it matches germs.
* `TopCat.Presheaf.stalkRestrictIso_naturality`: it is natural in the presheaf.
* `TopCat.Presheaf.isIso_stalkFunctor_map_whiskerLeft_iff`: a morphism of presheaves on `X`
  induces an isomorphism on the stalk at `u ∈ U` of the naive restrictions exactly when it
  induces one on the stalk at `j u`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe v u

namespace TopCat.Presheaf

variable {X : TopCat.{v}} (U : Opens X)

/-- The functor `Opens U ⥤ Opens X` taking an open subset of `U` to its image in `X`. -/
noncomputable abbrev imF : Opens ((Opens.toTopCat X).obj U) ⥤ Opens X :=
  U.isOpenEmbedding.functor

variable {C : Type u} [Category.{v} C] [HasColimits C]

/-- The stalk at `u ∈ U` of the naive restriction `W ↦ P(j(W))` of a presheaf `P` on `X` is the
stalk of `P` at `j u`. -/
noncomputable def stalkRestrictIso (P : TopCat.Presheaf C X) (u : (Opens.toTopCat X).obj U) :
    TopCat.Presheaf.stalk (X := (Opens.toTopCat X).obj U) ((imF U).op ⋙ P) u ≅
      P.stalk (U.inclusion' u) :=
  (⟨X, P⟩ : AlgebraicGeometry.PresheafedSpace C).restrictStalkIso
    (f := U.inclusion') U.isOpenEmbedding u

/-- `stalkRestrictIso` matches germs: the germ at `u` of a section over an open `V ⊆ U` of the
naive restriction is the germ at `j u` of the same section, viewed as a section over `j(V)`. -/
lemma stalkRestrictIso_germ (P : TopCat.Presheaf C X)
    (V : Opens ((Opens.toTopCat X).obj U)) (u : (Opens.toTopCat X).obj U) (hV : u ∈ V) :
    TopCat.Presheaf.germ ((imF U).op ⋙ P) V u hV ≫ (stalkRestrictIso U P u).hom =
      P.germ ((imF U).obj V) (U.inclusion' u) ⟨u, hV, rfl⟩ :=
  AlgebraicGeometry.PresheafedSpace.restrictStalkIso_hom_eq_germ
    (⟨X, P⟩ : AlgebraicGeometry.PresheafedSpace C) U.isOpenEmbedding V u hV

/-- `stalkRestrictIso` is natural in the presheaf. -/
lemma stalkRestrictIso_naturality (P Q : TopCat.Presheaf C X) (φ : P ⟶ Q)
    (u : (Opens.toTopCat X).obj U) :
    (TopCat.Presheaf.stalkFunctor C u).map (Functor.whiskerLeft (imF U).op φ) ≫
        (stalkRestrictIso U Q u).hom =
      (stalkRestrictIso U P u).hom ≫
        (TopCat.Presheaf.stalkFunctor C (U.inclusion' u)).map φ := by
  apply TopCat.Presheaf.stalk_hom_ext ((imF U).op ⋙ P)
  intro V hV
  erw [← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ, Category.assoc,
    stalkRestrictIso_germ, ← Category.assoc, stalkRestrictIso_germ,
    TopCat.Presheaf.stalkFunctor_map_germ]
  rfl

section

set_option backward.isDefEq.respectTransparency false

/-- A morphism of presheaves on `X` induces an isomorphism on the stalk at `u ∈ U` of the naive
restrictions to `U` exactly when it induces one on the stalk at `j u`. -/
lemma isIso_stalkFunctor_map_whiskerLeft_iff (P Q : TopCat.Presheaf C X) (φ : P ⟶ Q)
    (u : (Opens.toTopCat X).obj U) :
    IsIso ((TopCat.Presheaf.stalkFunctor C u).map (Functor.whiskerLeft (imF U).op φ)) ↔
      IsIso ((TopCat.Presheaf.stalkFunctor C (U.inclusion' u)).map φ) := by
  rw [show (TopCat.Presheaf.stalkFunctor C u).map (Functor.whiskerLeft (imF U).op φ)
      = (stalkRestrictIso U P u).hom
        ≫ (TopCat.Presheaf.stalkFunctor C (U.inclusion' u)).map φ
        ≫ (stalkRestrictIso U Q u).inv by
    rw [← Category.assoc, ← stalkRestrictIso_naturality U P Q φ u, Category.assoc,
      Iso.hom_inv_id, Category.comp_id], isIso_comp_left_iff, isIso_comp_right_iff]

end

end TopCat.Presheaf
