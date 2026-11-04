module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHom

/-!
# Gluing morphisms of presheaves of modules out of the internal hom

Stacks 03EM says that the internal hom `𝓗om_O(F, G)` of Tag 04TT is a sheaf as soon as `G` is
(`internalHom_isSheaf`).  That statement is about a *presheaf of modules*; to use it one needs to
know what its global sections are, and this file supplies the identification: a section of
`internalHom O F G` over every object of the site, compatible with the restriction maps, is the
same thing as a morphism `F ⟶ G`.

With that identification the sheaf condition becomes a gluing principle for morphisms.
If the objects `Y i` cover the final object of the site, then a family of local morphisms
`F|_{Y i} ⟶ G|_{Y i}` agreeing on all common refinements glues to a *unique* morphism `F ⟶ G`
(`existsUnique_hom_of_isCompatible`), and a family of local *isomorphisms* glues to an
isomorphism `F ≅ G` (`exists_iso_of_isCompatible`).

Nothing here fixes a universe: the site `C` has objects in `Type u` and morphisms in `Type v`,
the ring universe of `O` is free, and the module universe `t` of `F` and `G` is free as well.

## Main definitions

* `internalHomEval`: the value of a section of `internalHom O F G` over `U` on a section of `F`
  over `U`, obtained by taking the component at the terminal object `Over.mk (𝟙 U)` of `C/U`.
* `homOfSections` and `sectionsOfHom`: the two directions of the identification, and
  `internalHomSectionsEquiv`, the bijection `(internalHom O F G).sections ≃ (F ⟶ G)` they form.
* `homRestrIso`: an isomorphism `F|_U ≅ G|_U` relocalizes to an isomorphism `F|_V ≅ G|_V`.

## Main results

* `existsUnique_hom_of_isCompatible`: **the gluing form of Stacks 03EM.**  A compatible family of
  morphisms `F|_{Y i} ⟶ G|_{Y i}` on a family of objects covering the final object extends to a
  unique morphism `F ⟶ G`.
* `exists_iso_of_isCompatible`: a compatible family of isomorphisms glues to an isomorphism.  The
  inverses are a compatible family in `internalHom O G F`, and the two composites are pinned down
  by the uniqueness clause applied to the constant family of identities.
* `internalHom_isSheaf_forget`: Stacks 03EM read on the underlying presheaf of types.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 04TT](https://stacks.math.columbia.edu/tag/04TT)
-/

@[expose] public section

open CategoryTheory Opposite

universe v u t w

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat)
  (F G : PresheafOfModules.{t} (Oforget O))

/-- **Evaluation of a section of the internal hom.**  A section of `internalHom O F G` over `U`
is a morphism `F|_U ⟶ G|_U` of presheaves of modules on the slice site `C/U`; it is applied to a
section of `F` over `U` by taking its component at the terminal object `Over.mk (𝟙 U)` of
`C/U`. -/
public noncomputable def internalHomEval (U : Cᵒᵖ) (α : (internalHom O F G).obj U)
    (x : F.obj U) : G.obj U :=
  (α.app (op (Over.mk (𝟙 U.unop)))).hom x

/-- **Evaluation commutes with the restriction maps.**  The two sides differ because
relocalization along `i` sends the terminal object `Over.mk (𝟙 V)` of `C/V` to
`Over.mk (𝟙 V ≫ i)` rather than to `Over.mk i`, so the identification is the naturality square of
`α` along `Over.homMk i : Over.mk (𝟙 V ≫ i) ⟶ Over.mk (𝟙 U)`, which exists because
`i ≫ 𝟙 = 𝟙 ≫ i`. -/
public theorem internalHomEval_naturality {U V : Cᵒᵖ} (i : U ⟶ V)
    (α : (internalHom O F G).obj U) (x : F.obj U) :
    internalHomEval O F G V (ConcreteCategory.hom ((internalHom O F G).map i) α)
        ((F.map i).hom x) =
      (G.map i).hom (internalHomEval O F G U α x) :=
  PresheafOfModules.naturality_apply α
    (Over.homMk i.unop (by simp) :
      Over.mk (𝟙 V.unop ≫ i.unop) ⟶ Over.mk (𝟙 U.unop)).op x

/-- **A compatible family of local morphisms, one over every object, is a morphism.**  The
component at `U` is the evaluation of the section over `U`; its naturality is
`internalHomEval_naturality` combined with the compatibility of the family. -/
public noncomputable def homOfSections (s : (internalHom O F G).sections) : F ⟶ G where
  app U := ModuleCat.ofHom
    { toFun := fun x => internalHomEval O F G U (s.val U) x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun a x =>
        ((s.val U).app (op (Over.mk (𝟙 U.unop)))).hom.map_smul a x }
  naturality {U V} i := by
    ext x
    exact ((congrArg (fun β => internalHomEval O F G V β ((F.map i).hom x))
      (PresheafOfModules.sections_property s i)).symm.trans
      (internalHomEval_naturality O F G i (s.val U) x))

/-- **A morphism restricts to a section of the internal hom over every object.**  The section
over `U` is the restriction `F|_U ⟶ G|_U` of `φ` to the slice site, and its compatibility with
the relocalization maps holds by definition. -/
public noncomputable def sectionsOfHom (φ : F ⟶ G) : (internalHom O F G).sections :=
  PresheafOfModules.sectionsMk (fun U => (restrFun O U.unop).map φ) (fun _ _ _ => rfl)

/-- Evaluating the restrictions of `φ` at the terminal objects of the slice sites returns `φ`. -/
public theorem homOfSections_sectionsOfHom (φ : F ⟶ G) :
    homOfSections O F G (sectionsOfHom O F G φ) = φ := rfl

/-- A section of the internal hom is recovered from the morphism it defines.  The underlying
abelian statement is Mathlib's `CategoryTheory.presheafHomSectionsEquiv`, and
`PresheafOfModules.toPresheaf` is faithful, so the module-valued statement follows from it. -/
public theorem sectionsOfHom_homOfSections (s : (internalHom O F G).sections) :
    sectionsOfHom O F G (homOfSections O F G s) = s := by
  apply PresheafOfModules.sections_ext
  intro U
  apply (PresheafOfModules.toPresheaf (ORestr O U.unop)).map_injective
  exact congrFun (congrArg Subtype.val
    ((presheafHomSectionsEquiv F.presheaf G.presheaf).left_inv
      ⟨fun V => (PresheafOfModules.toPresheaf (ORestr O V.unop)).map (s.val V),
        fun {_ Y} f => congrArg
          (fun α => (PresheafOfModules.toPresheaf (ORestr O Y.unop)).map α) (s.2 f)⟩)) U

/-- **Relocalization of an isomorphism.**  An isomorphism `F|_U ≅ G|_U` restricts along
`f : V ⟶ U` to an isomorphism `F|_V ≅ G|_V`, whose inverse is the restriction of the inverse. -/
public noncomputable def homRestrIso {V U : C} (f : V ⟶ U)
    (e : (restrFun O U).obj F ≅ (restrFun O U).obj G) :
    (restrFun O V).obj F ≅ (restrFun O V).obj G where
  hom := homRestr O F G f e.hom
  inv := homRestr O G F f e.inv
  hom_inv_id := by simp [homRestr]
  inv_hom_id := by simp [homRestr]

/-- **Stacks 03EM on the underlying presheaf of types.**  The forgetful functor of
`AddCommGrpCat` preserves limits, so the sheaf condition for the internal hom passes to the
presheaf of types of its sections. -/
public theorem internalHom_isSheaf_forget {J : GrothendieckTopology C}
    (hG : Presheaf.IsSheaf J G.presheaf) :
    Presheaf.IsSheaf J ((internalHom O F G).presheaf ⋙ CategoryTheory.forget _) :=
  Presheaf.isSheaf_comp_of_isSheaf _ _ _ (internalHom_isSheaf O F G hG)

/-- The restriction map of the presheaf of types of sections of the internal hom is `homRestr`.
This holds by definition. -/
public theorem internalHomForget_map_apply {V U : C} (f : V ⟶ U)
    (α : (restrFun O U).obj F ⟶ (restrFun O U).obj G) :
    ((internalHom O F G).presheaf ⋙ CategoryTheory.forget _).map f.op α =
      homRestr O F G f α := rfl

/-- Relocalizing the identity morphism gives the identity morphism. -/
public theorem homRestr_id {V U : C} (f : V ⟶ U) :
    homRestr O F F f (𝟙 ((restrFun O U).obj F)) = 𝟙 ((restrFun O V).obj F) := by
  simp [homRestr]

/-- **The constant family of identities is a compatible family**, for any family of objects `Y`. -/
public theorem isCompatible_id {I : Type w} (Y : I → C) :
    Presheaf.FamilyOfElementsOnObjects.IsCompatible
      (F := (internalHom O F F).presheaf ⋙ CategoryTheory.forget _)
      (fun i => 𝟙 ((restrFun O (Y i)).obj F)) := by
  intro _ _ _ f g
  rw [internalHomForget_map_apply, internalHomForget_map_apply, homRestr_id, homRestr_id]

/-- **The sections of the internal hom are the morphisms `F ⟶ G`.**  This is the module-valued
counterpart of Mathlib's `CategoryTheory.presheafHomSectionsEquiv`. -/
public noncomputable def internalHomSectionsEquiv :
    (internalHom O F G).sections ≃ (F ⟶ G) where
  toFun := homOfSections O F G
  invFun := sectionsOfHom O F G
  left_inv := sectionsOfHom_homOfSections O F G
  right_inv := homOfSections_sectionsOfHom O F G

/-- **The gluing form of Stacks 03EM.**  Let `Y : I → C` be a family of objects covering the
final object of the site.  A family of morphisms `α i : F|_{Y i} ⟶ G|_{Y i}` which agree after
relocalization to any common refinement extends to a unique morphism `F ⟶ G` restricting to it.

The sheaf hypothesis is Stacks 03EM for the pair `(F, G)`, read on the presheaf of types by
`internalHom_isSheaf_forget`; the gluing of sections is Mathlib's
`CategoryTheory.Presheaf.FamilyOfElementsOnObjects.IsCompatible.existsUnique_section`, and
`internalHomSectionsEquiv` turns the resulting section into the morphism. -/
public theorem existsUnique_hom_of_isCompatible {J : GrothendieckTopology C}
    {I : Type w} {Y : I → C} (hY : J.CoversTop Y)
    (hs : Presheaf.IsSheaf J ((internalHom O F G).presheaf ⋙ CategoryTheory.forget _))
    {α : Presheaf.FamilyOfElementsOnObjects
      ((internalHom O F G).presheaf ⋙ CategoryTheory.forget _) Y}
    (hα : α.IsCompatible) :
    ∃! φ : F ⟶ G, ∀ i, (restrFun O (Y i)).map φ = α i := by
  obtain ⟨t, ht, hu⟩ := hα.existsUnique_section hY hs
  refine ⟨homOfSections O F G t, fun i => ?_, fun φ hφ => ?_⟩
  · exact (congrFun (congrArg Subtype.val (sectionsOfHom_homOfSections O F G t))
      (op (Y i))).trans (ht i)
  · have h : sectionsOfHom O F G φ = t := hu _ (fun i => hφ i)
    exact (homOfSections_sectionsOfHom O F G φ).symm.trans (congrArg (homOfSections O F G) h)

/-- If `F` is a sheaf and `φ ≫ ψ` restricts to the identity on every `Y i`, it is the identity. -/
private theorem comp_eq_id_of_restr_eq_id {J : GrothendieckTopology C}
    {I : Type w} {Y : I → C} (hY : J.CoversTop Y) (hF : Presheaf.IsSheaf J F.presheaf)
    (φ : F ⟶ G) (ψ : G ⟶ F) (h : ∀ i, (restrFun O (Y i)).map (φ ≫ ψ) = 𝟙 _) : φ ≫ ψ = 𝟙 F := by
  obtain ⟨_, -, hu⟩ :=
    existsUnique_hom_of_isCompatible O F F hY (internalHom_isSheaf_forget O F F hF)
      (isCompatible_id O F Y)
  exact (hu _ h).trans (hu _ fun i => (restrFun O (Y i)).map_id _).symm

/-- **A compatible family of local isomorphisms glues to an isomorphism.**

Both `F` and `G` must be sheaves, for four separate uses of the gluing principle: the family of
inverses is a compatible family for `internalHom O G F`, and each of the two composites is
identified with an identity by the uniqueness clause for `internalHom O F F` and for
`internalHom O G G` applied to the constant family of identities. -/
public theorem exists_iso_of_isCompatible {J : GrothendieckTopology C}
    {I : Type w} {Y : I → C} (hY : J.CoversTop Y)
    (hF : Presheaf.IsSheaf J F.presheaf) (hG : Presheaf.IsSheaf J G.presheaf)
    (e : ∀ i, (restrFun O (Y i)).obj F ≅ (restrFun O (Y i)).obj G)
    (he : Presheaf.FamilyOfElementsOnObjects.IsCompatible
      (F := (internalHom O F G).presheaf ⋙ CategoryTheory.forget _) (fun i => (e i).hom)) :
    ∃ φ : F ≅ G, ∀ i, (restrFun O (Y i)).map φ.hom = (e i).hom := by
  have key : ∀ (Z : C) (i j : I) (f : Z ⟶ Y i) (g : Z ⟶ Y j),
      homRestr O F G f (e i).hom = homRestr O F G g (e j).hom := by
    intro Z i j f g
    rw [← internalHomForget_map_apply, ← internalHomForget_map_apply]
    exact he Z i j f g
  have he' : Presheaf.FamilyOfElementsOnObjects.IsCompatible
      (F := (internalHom O G F).presheaf ⋙ CategoryTheory.forget _) (fun i => (e i).inv) := by
    intro Z i j f g
    rw [internalHomForget_map_apply, internalHomForget_map_apply]
    exact congrArg Iso.inv (Iso.ext (key Z i j f g) :
      homRestrIso O F G f (e i) = homRestrIso O F G g (e j))
  obtain ⟨φ, hφ, -⟩ :=
    existsUnique_hom_of_isCompatible O F G hY (internalHom_isSheaf_forget O F G hG) he
  obtain ⟨ψ, hψ, -⟩ :=
    existsUnique_hom_of_isCompatible O G F hY (internalHom_isSheaf_forget O G F hF) he'
  refine ⟨⟨φ, ψ, ?_, ?_⟩, hφ⟩
  · exact comp_eq_id_of_restr_eq_id O F G hY hF φ ψ fun i => by
      rw [Functor.map_comp, hφ i, hψ i, Iso.hom_inv_id]
  · exact comp_eq_id_of_restr_eq_id O G F hY hG ψ φ fun i => by
      rw [Functor.map_comp, hψ i, hφ i, Iso.inv_hom_id]

end
