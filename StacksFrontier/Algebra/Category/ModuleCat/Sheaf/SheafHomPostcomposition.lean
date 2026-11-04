module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomPrecomposition

/-!
# Postcomposition on the internal hom of sheaves of modules

Let `O_X` be a sheaf of commutative rings on a topological space `X` and let `F`, `G`, `G₁` be
sheaves of `O_X`-modules. A map `u : G ⟶ G₁` induces, by postcomposition on sections, a map

`u_* : SheafHom_{O_X}(F, G) ⟶ SheafHom_{O_X}(F, G₁)`

of internal homs. This file constructs it from the characterising data of the two internal homs
alone, and proves that it is covariantly functorial in `u`; it is the companion of
`SheafHom.precomp`, which does the same for the contravariant variable.

## Main definitions

* `SheafHom.postcomp`: the postcomposition map `u_*` of internal homs.

## Main results

* `Stacks.SheafOfModules.restrictOverHom_comp_right`: restriction of maps of restrictions is
  natural in the target.
* `Stacks.SheafOfModules.overSmul_comp`: a morphism of sheaves of modules commutes with
  multiplication by a section of the structure sheaf.
* `SheafHom.eq_of_isPostcomp`: a postcomposition map is unique, so
  `SheafHom.isPostcomp_postcomp` characterises `SheafHom.postcomp`.
* `SheafHom.postcomp_id` and `SheafHom.postcomp_comp`: covariant functoriality.

## References

* [Stacks Project, Tag 01CO](https://stacks.math.columbia.edu/tag/01CO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}

section Restrict

variable (F G : SheafOfModules.{u} (structureSheaf Rc))
  {G₁ : SheafOfModules.{u} (structureSheaf Rc)}

/-- Restriction of maps of restrictions is natural in the target. -/
lemma restrictOverHom_comp_right {U V : Opens X} (hVU : V ≤ U) (u : G ⟶ G₁)
    (f : F.over U ⟶ G.over U) :
    restrictOverHom F G hVU f ≫ u.over V = restrictOverHom F G₁ hVU (f ≫ u.over U) := by
  ext W y
  rfl

/-- **Multiplication by a scalar is natural.** A morphism of sheaves of modules commutes with
multiplication by a section of the structure sheaf, because it is linear. -/
lemma overSmul_comp (U : Opens X) (r : (structureSheaf Rc).obj.obj (op U)) (u : G ⟶ G₁) :
    overSmul G U r ≫ u.over U = u.over U ≫ overSmul G₁ U r := by
  ext W y
  show (u.over U).val.app W ((overSmul G U r).val.app W y) =
    (overSmul G₁ U r).val.app W ((u.over U).val.app W y)
  rw [overSmul_app, overSmul_app]
  exact ((u.over U).val.app W).hom.map_smul _ y

end Restrict

end Stacks.SheafOfModules

namespace SheafHom

open Stacks.SheafOfModules

variable {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}
  {F G G₁ G₂ : SheafOfModules.{u} (structureSheaf Rc)}

/-- **A postcomposition map is unique.** Two morphisms of internal homs which both act on
sections by postcomposition with `u` are equal: the section identifications are bijective. -/
lemma eq_of_isPostcomp {u : G ⟶ G₁} {H : SheafHom Rc F G} {H' : SheafHom Rc F G₁}
    {m m' : H.obj ⟶ H'.obj} (hm : IsPostcomp Rc u H H' m) (hm' : IsPostcomp Rc u H H' m') :
    m = m' := by
  ext U s
  exact (H'.sectionsEquiv U.unop).injective ((hm U.unop s).trans (hm' U.unop s).symm)

/-- **Postcomposition on the internal hom.** A map `u : G ⟶ G₁` of sheaves of modules induces
`u_* : SheafHom_{O_X}(F, G) ⟶ SheafHom_{O_X}(F, G₁)`, acting on sections over every open by
postcomposition with the restriction of `u`. -/
def postcomp (u : G ⟶ G₁) (H : SheafHom Rc F G) (H' : SheafHom Rc F G₁) : H.obj ⟶ H'.obj := by
  let q (U : (Opens X)ᵒᵖ) (s : H.obj.val.obj U) : H'.obj.val.obj (op U.unop) :=
    (H'.sectionsEquiv U.unop).symm (H.sectionsEquiv U.unop s ≫ u.over U.unop)
  have hq_add (U : (Opens X)ᵒᵖ) (s t : H.obj.val.obj U) : q U (s + t) = q U s + q U t := by
    refine Eq.trans (congrArg (H'.sectionsEquiv U.unop).symm
      (Eq.trans (congrArg (· ≫ u.over U.unop) (map_add (H.sectionsEquiv U.unop) s t))
        (Preadditive.add_comp _ _ _ _ _ _))) ?_
    exact map_add (H'.sectionsEquiv U.unop).symm _ _
  let p : H.obj.val.presheaf ⟶ H'.obj.val.presheaf :=
    { app := fun U => AddCommGrpCat.ofHom (AddMonoidHom.mk' (q U) (hq_add U))
      naturality := by
        intro U V f
        ext s
        have hle : V.unop ≤ U.unop := f.unop.le
        have hf : f = (homOfLE hle).op := Subsingleton.elim _ _
        rw [hf]
        change q V (H.obj.val.map (homOfLE hle).op s) =
          H'.obj.val.map (homOfLE hle).op (q U s)
        refine (H'.sectionsEquiv V.unop).injective ?_
        refine Eq.trans ((H'.sectionsEquiv V.unop).apply_symm_apply _) ?_
        refine Eq.trans (congrArg (· ≫ u.over V.unop) (sectionsEquiv_restrict H hle s)) ?_
        refine Eq.trans (restrictOverHom_comp_right F G hle u (H.sectionsEquiv U.unop s)) ?_
        refine Eq.trans (congrArg (restrictOverHom F G₁ hle)
          ((H'.sectionsEquiv U.unop).apply_symm_apply _).symm) ?_
        exact (sectionsEquiv_restrict H' hle (q U s)).symm }
  exact ⟨PresheafOfModules.homMk p (by
    intro U r s
    change q U (r • s) = r • q U s
    refine (H'.sectionsEquiv U.unop).injective ?_
    refine Eq.trans ((H'.sectionsEquiv U.unop).apply_symm_apply _) ?_
    refine Eq.trans (congrArg (· ≫ u.over U.unop) (sectionsEquiv_smul H U.unop r s)) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (H.sectionsEquiv U.unop s ≫ ·)
      (overSmul_comp G U.unop r u)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (· ≫ overSmul G₁ U.unop r)
      ((H'.sectionsEquiv U.unop).apply_symm_apply _).symm) ?_
    exact (sectionsEquiv_smul H' U.unop r (q U s)).symm)⟩

/-- `SheafHom.postcomp` acts on sections by postcomposition, which by
`SheafHom.eq_of_isPostcomp` determines it. -/
lemma isPostcomp_postcomp (u : G ⟶ G₁) (H : SheafHom Rc F G) (H' : SheafHom Rc F G₁) :
    IsPostcomp Rc u H H' (postcomp u H H') := by
  intro U s
  show H'.sectionsEquiv U ((H'.sectionsEquiv U).symm (H.sectionsEquiv U s ≫ u.over U)) = _
  exact (H'.sectionsEquiv U).apply_symm_apply _

/-- The identity induces the identity: postcomposition with `𝟙` on the internal hom of one pair
of modules is the identity. -/
lemma postcomp_id (H : SheafHom Rc F G) : postcomp (𝟙 G) H H = 𝟙 H.obj := by
  refine eq_of_isPostcomp (isPostcomp_postcomp (𝟙 G) H H) (fun U s => ?_)
  show H.sectionsEquiv U s = H.sectionsEquiv U s ≫ SheafOfModules.Hom.over (𝟙 G) U
  exact (Category.comp_id _).symm.trans (congrArg (_ ≫ ·)
    ((SheafOfModules.overFunctor (structureSheaf Rc) U).map_id G).symm)

/-- **Postcomposition is covariantly functorial.** -/
lemma postcomp_comp (u₁ : G ⟶ G₁) (u₂ : G₁ ⟶ G₂) (H : SheafHom Rc F G) (H₁ : SheafHom Rc F G₁)
    (H₂ : SheafHom Rc F G₂) :
    postcomp (u₁ ≫ u₂) H H₂ = postcomp u₁ H H₁ ≫ postcomp u₂ H₁ H₂ := by
  refine eq_of_isPostcomp (isPostcomp_postcomp (u₁ ≫ u₂) H H₂) (fun U s => ?_)
  refine Eq.trans (isPostcomp_postcomp u₂ H₁ H₂ U _) ?_
  refine Eq.trans (congrArg (· ≫ u₂.over U) (isPostcomp_postcomp u₁ H H₁ U s)) ?_
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
    ((SheafOfModules.overFunctor (structureSheaf Rc) U).map_comp u₁ u₂).symm)

/-- A morphism of internal homs acting on sections by postcomposition with `u` is
`SheafHom.postcomp u`. -/
lemma eq_postcomp_of_isPostcomp {u : G ⟶ G₁} {H : SheafHom Rc F G} {H' : SheafHom Rc F G₁}
    {m : H.obj ⟶ H'.obj} (hm : IsPostcomp Rc u H H' m) : m = postcomp u H H' :=
  eq_of_isPostcomp hm (isPostcomp_postcomp u H H')

/-- Postcomposition with `u`, followed by the identification of two internal homs of the same
pair, is postcomposition with `u`. -/
lemma postcomp_comp_id (u : G ⟶ G₁) (H : SheafHom Rc F G) (H₁ H₁' : SheafHom Rc F G₁) :
    postcomp u H H₁ ≫ postcomp (𝟙 G₁) H₁ H₁' = postcomp u H H₁' := by
  rw [← postcomp_comp, Category.comp_id]

/-- The identification of two internal homs of the same pair, followed by postcomposition with
`u`, is postcomposition with `u`. -/
lemma postcomp_id_comp (u : G ⟶ G₁) (H H' : SheafHom Rc F G) (H₁ : SheafHom Rc F G₁) :
    postcomp (𝟙 G) H H' ≫ postcomp u H' H₁ = postcomp u H H₁ := by
  rw [← postcomp_comp, Category.id_comp]

/-- **The internal hom of a pair of sheaves of modules is unique up to a canonical
isomorphism.** Two objects satisfying the characterisation are identified by the morphism which
acts on sections over every open as the identity. -/
def objIso (H H' : SheafHom Rc F G) : H.obj ≅ H'.obj where
  hom := postcomp (𝟙 G) H H'
  inv := postcomp (𝟙 G) H' H
  hom_inv_id := (postcomp_comp_id (𝟙 G) H H' H).trans (postcomp_id H)
  inv_hom_id := (postcomp_comp_id (𝟙 G) H' H H').trans (postcomp_id H')

/-- The forward map of `objIso` is postcomposition with the identity of `G`. -/
@[simp]
lemma objIso_hom (H H' : SheafHom Rc F G) : (objIso H H').hom = postcomp (𝟙 G) H H' := rfl

/-- The inverse map of `objIso` is postcomposition with the identity of `G`. -/
@[simp]
lemma objIso_inv (H H' : SheafHom Rc F G) : (objIso H H').inv = postcomp (𝟙 G) H' H := rfl

end SheafHom

end
