module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Point.StalkLeftAdjoint
/-!
# Stalks at a point of a site and their functoriality

Stacks tag 00YH (Lemma 7.37.1): a natural transformation `t : u' ⟶ u` of functors
`C ⥤ Type` induces a natural transformation of stalk functors `(-)_{p'} ⟹ (-)_p`, given on
representatives by `[(U, x', s)] ↦ [(U, t_U x', s)]`.  The stalk of a presheaf `F` at the
point `u` is the colimit of `F` over the category of elements `u.Elements`, whose objects
are the pairs `(U, x)` with `x ∈ u U`; it is `PresheafPushforwardStalkAdjunction.presheafStalk`.
Part 3 records the compatibility of `t` with the bijection `θ^u_U : u U ≃ (h_U)_p` of Stacks
tag 00Y6.  Only the underlying category of the site is used.
-/

@[expose] public section

open CategoryTheory Limits

namespace Stacks.Sites.PointStalk

open PresheafPushforwardStalkAdjunction

universe u
variable {C : Type u} [Category.{u} C]

-- Auxiliary lemmas used to define the stalk transformation.

/-- The neighbourhood diagrams for `p` and `p'` are related through the functor
`CategoryOfElements.map t : u'.Elements ⥤ u.Elements` induced by `t : u' → u`. -/
theorem diag_eq (uu uu' : C ⥤ Type u) (t : uu' ⟶ uu) (F : Cᵒᵖ ⥤ Type u) :
    ((CategoryOfElements.map t).op ⋙ ((CategoryOfElements.π uu).op ⋙ F))
      = ((CategoryOfElements.π uu').op ⋙ F) := by
  rw [← Functor.assoc,
      show (CategoryOfElements.map t).op ⋙ (CategoryOfElements.π uu).op
        = (CategoryOfElements.map t ⋙ CategoryOfElements.π uu).op from rfl,
      CategoryOfElements.map_π]

/-- `F_{p'}` may be read either as the colimit over the neighbourhoods of `p'` or as the
colimit over the neighbourhoods of `p` reindexed along `CategoryOfElements.map t`: by `diag_eq`
the two diagrams are equal, hence so are the colimits.  The `eqToHom` of this equality is the
first factor of `tStalkApp`. -/
theorem stalk_colimit_eq (uu uu' : C ⥤ Type u) (t : uu' ⟶ uu) (F : Cᵒᵖ ⥤ Type u) :
    colimit ((CategoryOfElements.π uu').op ⋙ F)
      = colimit ((CategoryOfElements.map t).op ⋙ ((CategoryOfElements.π uu).op ⋙ F)) := by
  rw [diag_eq]

/-- The component at `F` of the canonical stalk transformation
`t_stalk : F_{p'} → F_p` induced by `t : u' → u`.  Concretely it is the
colimit-comparison map `colimit.pre` along `CategoryOfElements.map t`, i.e. on
representatives `[(U, x', s)] ↦ [(U, t_U(x'), s)]`. -/
noncomputable def tStalkApp (uu uu' : C ⥤ Type u) (t : uu' ⟶ uu) (F : Cᵒᵖ ⥤ Type u) :
    (presheafStalk uu').obj F ⟶ (presheafStalk uu).obj F :=
  eqToHom (stalk_colimit_eq uu uu' t F) ≫
    colimit.pre ((CategoryOfElements.π uu).op ⋙ F) (CategoryOfElements.map t).op

/-- Cocone behaviour of `tStalkApp`: precomposing it with the colimit leg at `j` gives the
leg at `(CategoryOfElements.map t).op.obj j`.  Indeed, up to the `eqToHom` identifying the
two (equal) diagrams, `tStalkApp` is the comparison map `colimit.pre` for the reindexing
functor `(CategoryOfElements.map t).op`, and the `eqToHom` contributes nothing on legs
because it is `colim.map (eqToHom _)`, whose component is `eqToHom_refl = 𝟙`. -/
theorem ι_tStalkApp (uu uu' : C ⥤ Type u) (t : uu' ⟶ uu) (F : Cᵒᵖ ⥤ Type u)
    (j : uu'.Elementsᵒᵖ) :
    colimit.ι ((CategoryOfElements.π uu').op ⋙ F) j ≫ tStalkApp uu uu' t F =
      colimit.ι ((CategoryOfElements.π uu).op ⋙ F) ((CategoryOfElements.map t).op.obj j) := by
  unfold tStalkApp
  have key : eqToHom (stalk_colimit_eq uu uu' t F)
      = colim.map (eqToHom (diag_eq uu uu' t F).symm) := by
    rw [eqToHom_map]
  rw [key, ← Category.assoc, colimit.ι_map, Category.assoc, colimit.ι_pre]
  rw [eqToHom_app]
  simp

/-- Part 2 (Naturality in `F`). For every morphism of presheaves `φ : F → G`, the
square relating `t_stalk` to the functoriality of the stalk commutes; that is, the
components `tStalkApp` assemble into a genuine natural transformation. -/
theorem tStalk_naturality (uu uu' : C ⥤ Type u) (t : uu' ⟶ uu)
    {F G : Cᵒᵖ ⥤ Type u} (φ : F ⟶ G) :
    (presheafStalk uu').map φ ≫ tStalkApp uu uu' t G =
      tStalkApp uu uu' t F ≫ (presheafStalk uu).map φ := by
  refine colimit.hom_ext (F := (CategoryOfElements.π uu').op ⋙ F) fun j => ?_
  rw [presheafStalk_map, presheafStalk_map, ← Category.assoc, ι_colimMap,
      Category.assoc, ι_tStalkApp,
      ← Category.assoc, ι_tStalkApp, ι_colimMap]
  rfl

/-- Tag 00YH, Lemma 7.37.1: the canonical natural transformation of stalk
functors `t_stalk : (-)_{p'} ⟹ (-)_p` induced by `t : u' → u`.  Its components are
`tStalkApp`; naturality is `tStalk_naturality` (part 2). -/
@[stacks 00YH]
noncomputable def tStalk (uu uu' : C ⥤ Type u) (t : uu' ⟶ uu) :
    presheafStalk uu' ⟶ presheafStalk uu where
  app F := tStalkApp uu uu' t F
  naturality _ _ φ := tStalk_naturality uu uu' t φ

/-- Part 1 (Well-defined + defining formula). The stalk transformation acts on a
representative `[(U, x', s)]` by `[(U, x', s)] ↦ [(U, t_U(x'), s)]`; this is `ι_tStalkApp`
at `op ⟨U, x'⟩` applied to `s`, since `(map t).op.obj (op ⟨U, x'⟩)` is `op ⟨U, t.app U x'⟩`.
-/
@[stacks 00YH "(1)"]
theorem tStalkApp_stalkMk (uu uu' : C ⥤ Type u) (t : uu' ⟶ uu) (F : Cᵒᵖ ⥤ Type u)
    (U : C) (x' : uu'.obj U) (s : F.obj (Opposite.op U)) :
    tStalkApp uu uu' t F (stalkMk uu' F U x' s) = stalkMk uu F U (t.app U x') s := by
  have h := ι_tStalkApp uu uu' t F (Opposite.op ⟨U, x'⟩)
  have h2 := ConcreteCategory.congr_hom h s
  exact h2

/-- Part 3 (Compatibility with `t`, the agreement of Tag 00Y6).  Under the
canonical identifications `θ^{u'}_U : u'(U) ≅ (h_U)_{p'}` and
`θ^u_U : u(U) ≅ (h_U)_p`, the map `(t_stalk)_{h_U} : (h_U)_{p'} → (h_U)_p`
corresponds to `t_U : u'(U) → u(U)`.  Since `θ` is `stalkMk … (𝟙 U)`, this is the case
`F := yoneda.obj U`, `s := 𝟙 U` of `tStalkApp_stalkMk`. -/
@[stacks 00YH "(3)"]
theorem tStalkApp_theta (uu uu' : C ⥤ Type u) (t : uu' ⟶ uu) (U : C) (x' : uu'.obj U) :
    tStalkApp uu uu' t (yoneda.obj U) (theta uu' U x') = theta uu U (t.app U x') := by
  unfold theta
  exact tStalkApp_stalkMk uu uu' t (yoneda.obj U) U x' (𝟙 U)

end Stacks.Sites.PointStalk
