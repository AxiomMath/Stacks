module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposTerminalSections
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Global sections of a direct image of sheaves of commutative rings

Let `g : Sh(C) ⟶ Sh(D)` be a morphism of topoi and let `ℱ` be a sheaf of commutative rings on
`C`.  Because `g⁻¹` is left exact it carries the terminal sheaf to the terminal sheaf, so
`Hom(*, g_*ℱ) ≃ Hom(g⁻¹*, ℱ) ≃ Hom(*, ℱ)`: the direct image does not change global sections.
That bijection of *sets* is
`MorphismOfTopoi.pushforwardTerminalHomEquiv`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposTerminalSections.lean`).  This file upgrades
it in two ways, which are exactly what a ringed topos needs.

First, when the site presenting a topos has a terminal object `T`, global sections *are* the
sections over `T`: `Γ(⊤, ℱ) = ℱ(T)`, because the terminal sheaf has a single section over every
object (`CategoryTheory.Sheaf.terminalObjHomEquiv`).

Second, the resulting bijection `(g_*ℱ)(T_D) ≃ ℱ(T_C)` is a ring isomorphism.  This is *not*
automatic: the commutative ring structure on the sections of a direct image is the structure
*transported* along the finite-product-preserving functor `g_* ⋙ Γ(T_D, -)`, by
`Stacks.Sheaves.ToposPullback.pullbackCommRingSheaf` — nothing identifies it with the ring
structure of `ℱ(T_C)` by unfolding, since the two sites are unrelated.  What makes the
comparison a ring map is that the bijection is *natural in the sheaf of sets*: a natural
transformation of finite-product-preserving functors to types is automatically a homomorphism
for the transported operations, by `CategoryTheory.Sheaf.ringAddObj_naturality` and its
siblings.  So the bijection is first assembled into a natural transformation
(`MorphismOfTopoi.pushforwardTerminalSectionsNatTrans`) and only then read as a ring map.

## Main definitions

* `CategoryTheory.Sheaf.terminalObjHomEquiv`: for a site with a terminal object `T`, the
  sections of a sheaf of types over `T` are the morphisms from the terminal sheaf.
* `MorphismOfTopoi.pushforwardTerminalSectionsEquiv` and
  `.pushforwardTerminalSectionsNatTrans`: the bijection `(g_*E)(T_D) ≃ E(T_C)` for a sheaf of
  types, and its packaging as a natural transformation.
* `MorphismOfTopoi.pushforwardCommRingTerminalSectionsRingEquiv` and
  `.pushforwardCommRingTerminalSectionsIso`: **`Γ(⊤, g_*ℱ) ≅ Γ(⊤, ℱ)`** for a sheaf of
  commutative rings, as a `RingEquiv` and as an isomorphism in `CommRingCat`.
* `AlgebraicGeometry.RingedToposHom.globalSectionsMap`: the ring map on global functions
  induced by the structure map of a morphism of ringed topoi.

## Main results

* `CategoryTheory.Sheaf.terminalObjHomEquiv_comp` and
  `MorphismOfTopoi.pushforwardTerminalSectionsEquiv_naturality`: the naturality statements that
  make the comparison a ring map.

## Implementation notes

Both topoi are presented at the *same* universe of sections, `Sheaf J (Type w)` and
`Sheaf K (Type w)`, because the comparison is an isomorphism of objects of one category
`CommRingCat.{w}`; the universes of the two sites are independent.  The four
`GrothendieckTopology.HasSheafCompose` hypotheses are those of
`Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor` and are taken as instance
arguments rather than derived, as everywhere in this part of the development; on a concrete site
they are supplied by the universal instances in
`StacksFrontier/CategoryTheory/Sites/Sheaf/HasSheafComposeForgetRing.lean`.

No declaration here carries a Stacks tag.  Global sections of a sheaf on a site are *defined*
as `Hom(*, ℱ)` by Stacks 06UN, and the discussion following that definition constructs the
pullback map on global sections along a morphism of topoi; but neither the Sites chapter nor
the Modules on Sites chapter states a lemma identifying the global sections of a direct image
with those of the sheaf, nor one computing global sections as the sections over a terminal
object of the site — the only tagged computation of global sections is Stacks 0792, the
equalizer presentation attached to a coequalizer `h_V ⇉ h_U → *`, which is a different
statement.  The declarations below are therefore left untagged.

## References

* [Stacks Project, Tag 00XA](https://stacks.math.columbia.edu/tag/00XA)
* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 06UN](https://stacks.math.columbia.edu/tag/06UN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe w v u v' u'

namespace CategoryTheory.Sheaf

section TerminalObject

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {T : C}

/-- For a site whose underlying category has a terminal object `T`, the sections of a sheaf of
types over `T` are the morphisms into it from the terminal sheaf. -/
noncomputable def terminalObjHomEquiv (hT : IsTerminal T) (E : Sheaf J (Type w)) :
    E.obj.obj (op T) ≃ (⊤_ (Sheaf J (Type w)) ⟶ E) where
  toFun x := constHom (fun X ↦ E.obj.map (hT.from X.unop).op x) (fun {X Y} h ↦ by
    rw [← E.obj.map_comp_apply]
    exact congrArg (fun m ↦ E.obj.map m x) (Quiver.Hom.unop_inj (hT.hom_ext _ _)))
  invFun α := α.hom.app (op T) (terminalSheafSection J (op T))
  left_inv x := by
    change E.obj.map (hT.from T).op x = x
    rw [hT.hom_ext (hT.from T) (CategoryStruct.id T)]
    exact E.obj.map_id_apply _ x
  right_inv α := hom_ext_sections fun X p ↦ by
    rw [sectionsFunctor_map_constHom, map_terminalSheafSection_app α (hT.from X.unop).op]
    exact congrArg _ (eq_terminalSheafSection p).symm

/-- The sections of the morphism out of the terminal sheaf attached to a section over the
terminal object of the site are its restrictions. -/
@[simp]
lemma sectionsFunctor_map_terminalObjHomEquiv (hT : IsTerminal T) {E : Sheaf J (Type w)}
    (x : E.obj.obj (op T)) (X : Cᵒᵖ) (p : (sectionsFunctor J X).obj (⊤_ (Sheaf J (Type w)))) :
    (sectionsFunctor J X).map (terminalObjHomEquiv hT E x) p =
      E.obj.map (hT.from X.unop).op x :=
  rfl

/-- The section over the terminal object of the site attached to a morphism out of the terminal
sheaf. -/
lemma terminalObjHomEquiv_symm_apply (hT : IsTerminal T) {E : Sheaf J (Type w)}
    (α : ⊤_ (Sheaf J (Type w)) ⟶ E) :
    (terminalObjHomEquiv hT E).symm α = α.hom.app (op T) (terminalSheafSection J (op T)) :=
  rfl

/-- `CategoryTheory.Sheaf.terminalObjHomEquiv` is natural: the morphism out of the terminal
sheaf attached to the image of a section is the composite with the morphism of sheaves. -/
lemma terminalObjHomEquiv_comp (hT : IsTerminal T) {E E' : Sheaf J (Type w)}
    (x : E.obj.obj (op T)) (m : E ⟶ E') :
    terminalObjHomEquiv hT E x ≫ m = terminalObjHomEquiv hT E' (m.hom.app (op T) x) :=
  hom_ext_sections fun X p ↦ by
    rw [(sectionsFunctor J X).map_comp_apply, sectionsFunctor_map_terminalObjHomEquiv,
      sectionsFunctor_map_terminalObjHomEquiv, sectionsFunctor_map_apply]
    exact NatTrans.naturality_apply m.hom (hT.from X.unop).op x

/-- `CategoryTheory.Sheaf.terminalObjHomEquiv` is natural, inverse form. -/
lemma terminalObjHomEquiv_symm_comp (hT : IsTerminal T) {E E' : Sheaf J (Type w)}
    (α : ⊤_ (Sheaf J (Type w)) ⟶ E) (m : E ⟶ E') :
    (terminalObjHomEquiv hT E').symm (α ≫ m) =
      m.hom.app (op T) ((terminalObjHomEquiv hT E).symm α) :=
  rfl

end TerminalObject

end CategoryTheory.Sheaf

namespace MorphismOfTopoi

section Sets

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  (g : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))
  {T : C} {T' : D}

/-- The sections of a direct image over the terminal object of the target site are the sections
of the sheaf itself over the terminal object of the source site. -/
noncomputable def pushforwardTerminalSectionsEquiv (hT : IsTerminal T) (hT' : IsTerminal T')
    (E : Sheaf J (Type w)) :
    (g.pushforward.obj E).obj.obj (op T') ≃ E.obj.obj (op T) :=
  (Sheaf.terminalObjHomEquiv hT' (g.pushforward.obj E)).trans
    ((g.pushforwardTerminalHomEquiv E).trans (Sheaf.terminalObjHomEquiv hT E).symm)

/-- `MorphismOfTopoi.pushforwardTerminalSectionsEquiv` written out as the composite of its three
steps. -/
lemma pushforwardTerminalSectionsEquiv_apply (hT : IsTerminal T) (hT' : IsTerminal T')
    (E : Sheaf J (Type w)) (x : (g.pushforward.obj E).obj.obj (op T')) :
    g.pushforwardTerminalSectionsEquiv hT hT' E x =
      (Sheaf.terminalObjHomEquiv hT E).symm (g.pushforwardTerminalHomEquiv E
        (Sheaf.terminalObjHomEquiv hT' (g.pushforward.obj E) x)) :=
  rfl

/-- `MorphismOfTopoi.pushforwardTerminalSectionsEquiv` is natural in the sheaf. -/
lemma pushforwardTerminalSectionsEquiv_naturality (hT : IsTerminal T) (hT' : IsTerminal T')
    {E E' : Sheaf J (Type w)} (m : E ⟶ E')
    (x : (g.pushforward.obj E).obj.obj (op T')) :
    g.pushforwardTerminalSectionsEquiv hT hT' E'
        ((g.pushforward.map m).hom.app (op T') x) =
      m.hom.app (op T) (g.pushforwardTerminalSectionsEquiv hT hT' E x) := by
  rw [pushforwardTerminalSectionsEquiv_apply, pushforwardTerminalSectionsEquiv_apply,
    ← Sheaf.terminalObjHomEquiv_comp hT' x (g.pushforward.map m),
    g.pushforwardTerminalHomEquiv_comp m, Sheaf.terminalObjHomEquiv_symm_comp]

/-- `MorphismOfTopoi.pushforwardTerminalSectionsEquiv`, packaged as a natural transformation of
finite-product-preserving functors from sheaves of sets on the source site to types. This is
the shape in which the transported algebraic structure is compared. -/
noncomputable def pushforwardTerminalSectionsNatTrans (hT : IsTerminal T) (hT' : IsTerminal T') :
    g.pushforward ⋙ Sheaf.sectionsFunctor K (op T') ⟶ Sheaf.sectionsFunctor J (op T) where
  app E := ↾fun x ↦ g.pushforwardTerminalSectionsEquiv hT hT' E x
  naturality E E' m := by
    ext x
    exact g.pushforwardTerminalSectionsEquiv_naturality hT hT' m x

/-- The components of `MorphismOfTopoi.pushforwardTerminalSectionsNatTrans` are the bijections
of `MorphismOfTopoi.pushforwardTerminalSectionsEquiv`. -/
@[simp]
lemma pushforwardTerminalSectionsNatTrans_app_apply (hT : IsTerminal T) (hT' : IsTerminal T')
    (E : Sheaf J (Type w)) (x : (g.pushforward.obj E).obj.obj (op T')) :
    (g.pushforwardTerminalSectionsNatTrans hT hT').app E x =
      g.pushforwardTerminalSectionsEquiv hT hT' E x :=
  rfl

end Sets

section CommRing

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (g : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))
  {T : C} {T' : D}

/-- **The global sections of a direct image are the global sections of the sheaf**, as
commutative rings. -/
noncomputable def pushforwardCommRingTerminalSectionsRingEquiv (hT : IsTerminal T)
    (hT' : IsTerminal T') (O : Sheaf J CommRingCat.{w}) :
    ToType (((pushforwardCommRingFunctor g).obj O).obj.obj (op T')) ≃+*
      ToType (O.obj.obj (op T)) where
  toFun x := (g.pushforwardTerminalSectionsNatTrans hT hT').app
    (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) x
  invFun := (g.pushforwardTerminalSectionsEquiv hT hT'
    (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))).symm
  left_inv x := (g.pushforwardTerminalSectionsEquiv hT hT'
    (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))).left_inv x
  right_inv x := (g.pushforwardTerminalSectionsEquiv hT hT'
    (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))).right_inv x
  map_add' x y :=
    (Sheaf.ringAddObj_naturality ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)
        (g.pushforwardTerminalSectionsNatTrans hT hT') x y).trans
      (Sheaf.sectionsFunctor_map_ringAddHom ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)
        (op T) _ _)
  map_mul' x y :=
    (Sheaf.ringMulObj_naturality ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)
        (g.pushforwardTerminalSectionsNatTrans hT hT') x y).trans
      (Sheaf.sectionsFunctor_map_ringMulHom ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)
        (op T) _ _)

/-- **`Γ(⊤, g_*ℱ) ≅ Γ(⊤, ℱ)`.** For a morphism of topoi `g` presented by sites whose underlying
categories have terminal objects, the global sections of the direct image of a sheaf of
commutative rings are the global sections of the sheaf itself, as an isomorphism in
`CommRingCat`. -/
noncomputable def pushforwardCommRingTerminalSectionsIso (hT : IsTerminal T)
    (hT' : IsTerminal T') (O : Sheaf J CommRingCat.{w}) :
    ((pushforwardCommRingFunctor g).obj O).obj.obj (op T') ≅ O.obj.obj (op T) :=
  (g.pushforwardCommRingTerminalSectionsRingEquiv hT hT' O).toCommRingCatIso

/-- On elements, `MorphismOfTopoi.pushforwardCommRingTerminalSectionsIso` is the bijection
`MorphismOfTopoi.pushforwardTerminalSectionsEquiv` of the underlying sheaves of sets. -/
@[simp]
lemma pushforwardCommRingTerminalSectionsIso_hom_apply (hT : IsTerminal T) (hT' : IsTerminal T')
    (O : Sheaf J CommRingCat.{w})
    (x : ToType (((pushforwardCommRingFunctor g).obj O).obj.obj (op T'))) :
    (g.pushforwardCommRingTerminalSectionsIso hT hT' O).hom.hom x =
      g.pushforwardTerminalSectionsEquiv hT hT'
        (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) x :=
  rfl

end CommRing

end MorphismOfTopoi

namespace AlgebraicGeometry.RingedToposHom

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (f : RingedToposHom X Y) {T : X.C} {T' : Y.C}

/-- **The ring map on global functions induced by a morphism of ringed topoi.** The structure
map `f♯ : O_Y ⟶ f_*O_X` is evaluated over the terminal object of the site presenting the target,
and the result is identified with the global sections of `O_X` by
`MorphismOfTopoi.pushforwardCommRingTerminalSectionsIso`. -/
noncomputable def globalSectionsMap (hT : IsTerminal T) (hT' : IsTerminal T') :
    Y.O.obj.obj (op T') ⟶ X.O.obj.obj (op T) :=
  f.fSharp.hom.app (op T') ≫
    (f.toToposHom.pushforwardCommRingTerminalSectionsIso hT hT' X.O).hom

/-- `AlgebraicGeometry.RingedToposHom.globalSectionsMap` on a global function: evaluate `f♯`
over the terminal object of the target site and transport along the comparison of global
sections. -/
@[simp]
lemma globalSectionsMap_hom_apply (hT : IsTerminal T) (hT' : IsTerminal T')
    (s : ToType (Y.O.obj.obj (op T'))) :
    (f.globalSectionsMap hT hT').hom s =
      f.toToposHom.pushforwardTerminalSectionsEquiv hT hT'
        (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
        ((f.fSharp.hom.app (op T')).hom s) :=
  rfl

end AlgebraicGeometry.RingedToposHom

end
