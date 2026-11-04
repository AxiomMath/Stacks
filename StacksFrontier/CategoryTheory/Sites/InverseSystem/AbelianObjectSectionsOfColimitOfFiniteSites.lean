module

public import StacksFrontier.CategoryTheory.Sites.InverseSystem.CocycleSystemsOfColimitOfFiniteSites
import all StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSites

/-! # The object-level inputs of the one-hypercover step, at abelian coefficients

`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab` — the
degree-zero step of [Stacks, Tag 09YQ] over an object which neither the levels of an inverse
system of sites nor their colimit site need contain — takes four inputs about the system itself:
the cocycle law `hψ` on sections, the compatibility `hι` of the legs on sections, and the two
object-level clauses `hsurjObj` and `hsep`, namely that every section of `𝒢` over the image of an
object of a level comes from a section at some level below, and that two sections of a level with
the same image in `𝒢` agree after a transition.

This file derives all four from an abelian colimit presentation on the levels, which is what the
geometry of Tag 09YQ supplies. For sheaves of **sets** the four are immediate — the fields `map`,
`map_comp` of `CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.SheafSystem` are
already in presheaf form, and the two object-level clauses are the lemma
`sections_colimit_pullback_of_colimit` of the same namespace. At abelian coefficients the
transition of a system is stored in the *inverse image* form, and the two object-level clauses are
not an induction but a reading of a colimit: that is what this file does.

## Main results

* `Stacks.WeakSites.ColimitSiteCohomology.transition_app_comp` — the cocycle law of the
  direct-image transition of an abelian system, on sections. This is the input `hψ`.
* `Stacks.WeakSites.ColimitSiteCohomology.leg_app_eq_of_isCompatible` — the compatibility of a
  family of legs, on sections. This is the input `hι`.
* `Stacks.WeakSites.ColimitSiteCohomology.exists_level_section_eq_of_isColimitPresentation` —
  **the input `hsurjObj`**: every section of `𝒢` over `u_i(Y)` is the image of a section of `F_j`
  over `u_a(Y)` for some arrow `a : j ⟶ i`.
* `Stacks.WeakSites.ColimitSiteCohomology.exists_transition_eq_of_isColimitPresentation` —
  **the input `hsep`**: two sections of `F_j` over `u_a(Y)` with the same image in `𝒢` are carried
  to the same section by some transition.

All four again for direct-image transition data satisfying **only the cocycle law** — the notion
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.AbelianCocycleSystem`, which is
what [Stacks, Tag 0EZL] imposes and what geometry supplies, with no identity law:

* `Stacks.WeakSites.ColimitSiteCohomology.cocycleMap_app_comp` and
  `...cocycleLeg_app_eq_of_isCompatible` — the inputs `hψ` and `hι`.
* `Stacks.WeakSites.ColimitSiteCohomology.exists_level_section_eq_of_cocycleIsColimitPresentation`
  and `...exists_cocycleMap_eq_of_cocycleIsColimitPresentation` — the inputs `hsurjObj` and
  `hsep`. These are the forms a consumer of [Stacks, Tag 0EZL] coefficients can use; the splitting
  of the identity arrows' idempotents happens inside their proofs and is invisible in their
  statements, whose sections are those of the data itself.

## Implementation notes

**The two object-level clauses are the two elementwise clauses of a filtered colimit of abelian
groups, and nothing else.**
`Stacks.WeakSites.ColimitSiteCohomology.isColimit_sectionsCocone_of_presentation` says that for
every object `X` of every level `i` the canonical cocone over the diagram of sections
`F_j(u_a(X))`, indexed by the arrows `a : j ⟶ i` and with vertex `𝒢(u_i(X))`, is a colimit
cocone. The index `(Over i)ᵒᵖ` is filtered — `InverseSystemOfFiniteSites` carries
`IsCofiltered` on its index, `CategoryTheory.IsCofiltered.over` passes it to the slice and
`CategoryTheory.isFiltered_op_of_isCofiltered` to the opposite — and the forgetful functor of
`Ab` preserves filtered colimits of that size, so
`CategoryTheory.Limits.Concrete.isColimit_exists_rep` gives joint surjectivity of the legs and
`CategoryTheory.Limits.IsColimit.eq_iff'` gives separatedness. No sheaf condition and no
geometry enters: the colimit cocone is the whole input.

**Each clause is stated with the transports the consumer writes, not with the cocone.** The legs
of the cocone and the maps of the diagram are
`Stacks.WeakSites.ColimitSiteCohomology.sectionsMapTo` of `ι` and of the transition, i.e. the
component followed by a transport of the target presheaf along an equality of objects; the
consumer writes the component and the transport separately. The two spellings differ by the
transport being pushed inside `Stacks.WeakSites.ColimitSiteCohomology.sectionsMapTo`, which is
`rfl`, and by the *proof* of the equality of objects, which is irrelevant.

**The transport in the separatedness clause has to be cancelled, and that is where the clause
stops being a restatement.** The diagram's map at an arrow `f` of `(Over i)ᵒᵖ` is the transition
followed by a transport, so the colimit hands back an equality of transported sections; the
conclusion `hsep` asks for an equality of sections before the transport. The transport is
`eqToHom` under a presheaf, hence an isomorphism, and composing with the transport along the
reversed equality cancels it.

## References

* [Stacks 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks 09YN](https://stacks.math.columbia.edu/tag/09YN)
* [Stacks 09YP](https://stacks.math.columbia.edu/tag/09YP)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sites.InverseSystem

universe v u w t

namespace Stacks.WeakSites.ColimitSiteCohomology

section AbelianObjectSections

variable (D : InverseSystemOfFiniteSites.{v, u, w})
  (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)

/-- **The cocycle law of the direct-image transition of an abelian system, on sections.** This is
`Stacks.WeakSites.ColimitSiteCohomology.transition_comp_eqToHom` read at an object and at a
section of it, which is the form
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab` asks for. -/
theorem transition_app_comp {i j k : D.I} (a : j ⟶ i) (b : k ⟶ j) (Y : D.C i)
    (x : ToType ((F.obj i).obj.obj (op Y))) :
    (transition.{v, u, w, t} D F (b ≫ a)).app (op Y) x =
      (F.obj k).obj.map (eqToHom (congrArg op (Functor.congr_obj (D.comp b a) Y).symm))
        ((transition.{v, u, w, t} D F b).app (op ((D.u a).obj Y))
          ((transition.{v, u, w, t} D F a).app (op Y) x)) := by
  have h := congrArg (fun φ => φ.app (op Y)) (transition_comp_eqToHom D F b a)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  rw [ConcreteCategory.congr_hom h x]
  simp only [ConcreteCategory.comp_apply, eqToHom_app, eqToHom_map]
  rfl

variable {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)

/-- **The compatibility of a family of legs, on sections.** The condition
`Stacks.WeakSites.ColimitSiteCohomology.IsCompatible` read at an object and at a section of it,
which is the form
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab` asks for. -/
theorem leg_app_eq_of_isCompatible (H : Cᵒᵖ ⥤ Ab.{max u v w t})
    (g : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ H)
    (hg : IsCompatible.{v, u, w, t} D uC hu F H g)
    {i j : D.I} (a : j ⟶ i) (Y : D.C i) (x : ToType ((F.obj i).obj.obj (op Y))) :
    (g i).app (op Y) x =
      H.map (eqToHom (congrArg op (Functor.congr_obj (hu a) Y)))
        ((g j).app (op ((D.u a).obj Y))
          ((transition.{v, u, w, t} D F a).app (op Y) x)) := by
  have h := congrArg (fun φ => φ.app (op Y)) (hg a)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  rw [ConcreteCategory.congr_hom h x]
  simp only [ConcreteCategory.comp_apply, eqToHom_app, eqToHom_map]
  rfl

variable
  (hobj : ∀ Y : C, ∃ (i : D.I) (Z : D.C i), (uC i).obj Z = Y)
  (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
    ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
      (uC j).map g =
        eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Z).symm)
  (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
    (uC i).map g₁ = (uC i).map g₂ →
      ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
  (K : Precoverage C)
  (hK : ∀ (Y : C) (R : Presieve Y),
    R ∈ K Y ↔
      ∃ (i : D.I) (Z : D.C i) (h : (uC i).obj Z = Y) (S : Presieve Z),
        S ∈ (D.J i).toPrecoverage Z ∧ S ∈ Precoverage.finite (D.C i) Z ∧
          R = h ▸ S.map (uC i))
  (G : Sheaf K.toGrothendieck (Ab.{max u v w t}))
  (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ G.obj)
  (hG : IsColimitPresentation.{v, u, w, t} D uC hu K F G ι)

/-- `CategoryTheory.forget` of `Ab` at the coefficient universe preserves the filtered colimits
indexed by the slices of the index of the system, which is what reads the colimit cocone of
sections elementwise. -/
private theorem preservesColimitsOfShape_forget (i : D.I) :
    PreservesColimitsOfShape (Over i)ᵒᵖ (forget (Ab.{max u v w t})) := by
  let : PreservesFilteredColimitsOfSize.{v, max u v} (forget (Ab.{max u v w t})) :=
    preservesFilteredColimitsOfSize_of_univLE.{max u v w t, max u v w t} _
  exact inferInstance

include hobj hhom hhom_inj hK hG in
/-- **The object-level surjectivity input of the one-hypercover step, at abelian coefficients.**
Let `𝒢` on the colimit site with the legs `ι` present `colim_j f_j^{-1}F_j` for a system `F` of
abelian sheaves on the levels. Then every section of `𝒢` over the image `u_i(Y)` of an object of
a level is the image, under the leg at some level `j` below `i`, of a section of `F_j` over the
transition image `u_a(Y)`.

This is the hypothesis `hsurjObj` of
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab`, and it is one
of the two elementwise clauses of the colimit cocone of
`Stacks.WeakSites.ColimitSiteCohomology.isColimit_sectionsCocone_of_presentation`: joint
surjectivity of its legs, which is
`CategoryTheory.Limits.Concrete.isColimit_exists_rep`. Separatedness is the other clause,
`exists_transition_eq_of_isColimitPresentation`. -/
theorem exists_level_section_eq_of_isColimitPresentation (i : D.I) (Y : D.C i)
    (z : ToType (G.obj.obj (op ((uC i).obj Y)))) :
    ∃ (j : D.I) (a : j ⟶ i) (s : ToType ((F.obj j).obj.obj (op ((D.u a).obj Y)))),
      G.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a) Y)))
        ((ι j).app (op ((D.u a).obj Y)) s) = z := by
  let := preservesColimitsOfShape_forget.{v, u, w, t} D i
  obtain ⟨A, y, hy⟩ := Concrete.isColimit_exists_rep (sectionsDiagram D F i Y)
    (isColimit_sectionsCocone_of_presentation D uC hu hobj hhom hhom_inj K hK F G ι hG i Y) z
  refine ⟨A.unop.left, A.unop.hom, y, ?_⟩
  refine Eq.trans ?_ hy
  exact (ConcreteCategory.comp_apply ((ι A.unop.left).app (op ((D.u A.unop.hom).obj Y)))
    (G.obj.map (eqToHom (congrArg op (uLeg_eq D uC hu A.unop Y).symm))) y).symm

include hobj hhom hhom_inj hK hG in
/-- **The object-level separatedness input of the one-hypercover step, at abelian coefficients.**
In the situation of `exists_level_section_eq_of_isColimitPresentation`, two sections of `F_j` over
the transition image `u_a(Y)` of an object of the level `i` which have the same image under the
leg `ι_j` are carried to the same section of `F_k` by the transition along some further arrow
`b : k ⟶ j`.

This is the hypothesis `hsep` of
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab`, and it is the
second elementwise clause of the colimit cocone of
`Stacks.WeakSites.ColimitSiteCohomology.isColimit_sectionsCocone_of_presentation`, namely
`CategoryTheory.Limits.IsColimit.eq_iff'` at the filtered index `(Over i)ᵒᵖ`. The transport that
the diagram's maps carry is cancelled by the transport along the reversed equality; see the
module's implementation notes. -/
theorem exists_transition_eq_of_isColimitPresentation (i : D.I) (Y : D.C i) (j : D.I) (a : j ⟶ i)
    (s s' : ToType ((F.obj j).obj.obj (op ((D.u a).obj Y))))
    (hs : (ι j).app (op ((D.u a).obj Y)) s = (ι j).app (op ((D.u a).obj Y)) s') :
    ∃ (k : D.I) (b : k ⟶ j),
      (transition.{v, u, w, t} D F b).app (op ((D.u a).obj Y)) s =
        (transition.{v, u, w, t} D F b).app (op ((D.u a).obj Y)) s' := by
  let := preservesColimitsOfShape_forget.{v, u, w, t} D i
  let : IsFiltered (Over i)ᵒᵖ := inferInstance
  have hcocone : ∀ x : ToType ((F.obj j).obj.obj (op ((D.u a).obj Y))),
      (sectionsCocone D uC hu F G.obj ι hG.1 i Y).ι.app (op (Over.mk a)) x =
        G.obj.map (eqToHom (congrArg op (uLeg_eq D uC hu (Over.mk a) Y).symm))
          ((ι j).app (op ((D.u a).obj Y)) x) :=
    fun x => ConcreteCategory.comp_apply ((ι j).app (op ((D.u a).obj Y)))
      (G.obj.map (eqToHom (congrArg op (uLeg_eq D uC hu (Over.mk a) Y).symm))) x
  have hleg : (sectionsCocone D uC hu F G.obj ι hG.1 i Y).ι.app (op (Over.mk a)) s =
      (sectionsCocone D uC hu F G.obj ι hG.1 i Y).ι.app (op (Over.mk a)) s' := by
    rw [hcocone s, hcocone s', hs]
  obtain ⟨A, f, hf⟩ := (IsColimit.eq_iff' (F := sectionsDiagram D F i Y)
    (isColimit_sectionsCocone_of_presentation D uC hu hobj hhom hhom_inj K hK F G ι hG i Y)
    (i := op (Over.mk a)) s s').mp hleg
  refine ⟨A.unop.left, f.unop.left, ?_⟩
  have hmap : ∀ x : ToType ((F.obj j).obj.obj (op ((D.u a).obj Y))),
      (sectionsDiagram D F i Y).map f x =
        (F.obj A.unop.left).obj.map
            (eqToHom (congrArg op (uObj_eq D f.unop Y).symm))
          ((transition.{v, u, w, t} D F f.unop.left).app (op ((D.u a).obj Y)) x) :=
    fun x => ConcreteCategory.comp_apply
      ((transition.{v, u, w, t} D F f.unop.left).app (op ((D.u a).obj Y)))
      ((F.obj A.unop.left).obj.map (eqToHom (congrArg op (uObj_eq D f.unop Y).symm))) x
  rw [hmap s, hmap s'] at hf
  have hcancel : ∀ x : ToType ((F.obj A.unop.left).obj.obj
      (op ((D.u f.unop.left).obj ((D.u a).obj Y)))),
      (F.obj A.unop.left).obj.map (eqToHom (congrArg op (uObj_eq D f.unop Y)))
          ((F.obj A.unop.left).obj.map
            (eqToHom (congrArg op (uObj_eq D f.unop Y).symm)) x) = x := by
    intro x
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, eqToHom_trans, eqToHom_refl,
      CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  rw [← hcancel ((transition D F f.unop.left).app (op ((D.u a).obj Y)) s),
    ← hcancel ((transition D F f.unop.left).app (op ((D.u a).obj Y)) s'), hf]

end AbelianObjectSections

/-! ### The same inputs for direct-image transition data satisfying only the cocycle law -/

section CocycleObjectSections

variable {D : InverseSystemOfFiniteSites.{v, u, w}}
  (M : InverseSystemOfFiniteSites.AbelianCocycleSystem.{v, u, w, t} D)
  {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (hobj : ∀ Y : C, ∃ (i : D.I) (Z : D.C i), (uC i).obj Z = Y)
  (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
    ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
      (uC j).map g =
        eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Z).symm)
  (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
    (uC i).map g₁ = (uC i).map g₂ →
      ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
  (K : Precoverage C)
  (hK : ∀ (Y : C) (R : Presieve Y),
    R ∈ K Y ↔
      ∃ (i : D.I) (Z : D.C i) (h : (uC i).obj Z = Y) (S : Presieve Z),
        S ∈ (D.J i).toPrecoverage Z ∧ S ∈ Precoverage.finite (D.C i) Z ∧
          R = h ▸ S.map (uC i))
  (G : Sheaf K.toGrothendieck (Ab.{max u v w t}))
  (ι : ∀ j, (M.obj j).obj ⟶ (uC j).op ⋙ G.obj)
  (hM : M.IsColimitPresentation uC hu K G ι)

/-- **The cocycle law of direct-image transition data, on sections.** The field `map_comp` of
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.AbelianCocycleSystem` read at an
object and at a section of it, which is the form
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab` asks for. -/
theorem cocycleMap_app_comp {i j k : D.I} (a : j ⟶ i) (b : k ⟶ j) (Y : D.C i)
    (x : ToType ((M.obj i).obj.obj (op Y))) :
    (M.map (b ≫ a)).app (op Y) x =
      (M.obj k).obj.map (eqToHom (congrArg op (Functor.congr_obj (D.comp b a) Y).symm))
        ((M.map b).app (op ((D.u a).obj Y)) ((M.map a).app (op Y) x)) := by
  have h := congrArg (fun φ => φ.app (op Y)) (M.map_comp b a)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  rw [ConcreteCategory.congr_hom h x]
  simp only [ConcreteCategory.comp_apply, eqToHom_app, eqToHom_map]
  rfl

/-- **The compatibility of a family of legs for direct-image transition data, on sections.** The
condition `...AbelianCocycleSystem.IsCompatible` read at an object and at a section of it, which
is the form `Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab`
asks for. -/
theorem cocycleLeg_app_eq_of_isCompatible (H : Cᵒᵖ ⥤ Ab.{max u v w t})
    (g : ∀ j, (M.obj j).obj ⟶ (uC j).op ⋙ H) (hg : M.IsCompatible uC hu H g)
    {i j : D.I} (a : j ⟶ i) (Y : D.C i) (x : ToType ((M.obj i).obj.obj (op Y))) :
    (g i).app (op Y) x =
      H.map (eqToHom (congrArg op (Functor.congr_obj (hu a) Y)))
        ((g j).app (op ((D.u a).obj Y)) ((M.map a).app (op Y) x)) := by
  have h := congrArg (fun φ => φ.app (op Y)) (hg a)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  rw [ConcreteCategory.congr_hom h x]
  simp only [ConcreteCategory.comp_apply, eqToHom_app, eqToHom_map]
  rfl


include hobj hhom hhom_inj hK hM in
/-- **The object-level surjectivity input, for direct-image transition data satisfying only the
cocycle law.** Let the abelian sheaf `𝒢` on the colimit site with the legs `ι` present
`colim_j f_j^{-1}M_j` for transition data `M` on the levels in the sense of
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.AbelianCocycleSystem` — the notion
[Stacks, Tag 0EZL] imposes, with no identity law. Then every section of `𝒢` over the image
`u_i(Y)` of an object of a level is the image, under the leg at some level `j` below `i`, of a
section of `M_j` over the transition image `u_a(Y)`.

This is `exists_level_section_eq_of_isColimitPresentation` for the split system
`...AbelianCocycleSystem.split`, read back on the data itself. The inclusion of the splitting
carries a section of the split sheaf to one of `M_j`, and the leg of the split presentation is
the inclusion followed by `ι_j`, so the section the split statement produces already has the
required image: no identity law is assumed, and none is needed. -/
theorem exists_level_section_eq_of_cocycleIsColimitPresentation (i : D.I) (Y : D.C i)
    (z : ToType (G.obj.obj (op ((uC i).obj Y)))) :
    ∃ (j : D.I) (a : j ⟶ i) (s : ToType ((M.obj j).obj.obj (op ((D.u a).obj Y)))),
      G.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a) Y)))
        ((ι j).app (op ((D.u a).obj Y)) s) = z := by
  obtain ⟨j, a, s, hs⟩ := exists_level_section_eq_of_isColimitPresentation
    D (M.split M.splitting) uC hu hobj hhom hhom_inj K hK G
    (fun j => (M.splitting j).incl.hom ≫ ι j)
    (M.isColimitPresentation_split M.splitting uC hu K G ι hM) i Y z
  refine ⟨j, a, (M.splitting j).incl.hom.app (op ((D.u a).obj Y)) s, Eq.trans ?_ hs⟩
  exact congrArg (G.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a) Y))))
    (ConcreteCategory.comp_apply ((M.splitting j).incl.hom.app (op ((D.u a).obj Y)))
      ((ι j).app (op ((D.u a).obj Y))) s).symm

include hobj hhom hhom_inj hK hM in
/-- **The object-level separatedness input, for direct-image transition data satisfying only the
cocycle law.** In the situation of
`exists_level_section_eq_of_cocycleIsColimitPresentation`, two sections of `M_j` over the
transition image `u_a(Y)` with the same image under the leg `ι_j` are carried to the same section
by the transition along some further arrow `b : k ⟶ j`.

The passage through the split system is three applications of `congrArg` and no cancellation of a
transport. The projections of the two sections have the same image under the leg of the split
presentation, because the idempotent acts as the identity on a compatible family
(`...idem_comp_of_isCompatible`); the split statement hands back an arrow `b` along which their
images agree after the projection at `k`; applying the inclusion there turns that into an equality
of the images under the idempotent at `k`, which `...AbelianCocycleSystem.map_id_eq` turns into an
equality of the images under the transition at the identity arrow, and which the cocycle law at
`𝟙 k ≫ b = b` then turns into the required equality for `b` itself. The transition at `b` of the
*source* idempotent is cancelled by `...AbelianCocycleSystem.idem_comp_map`. -/
theorem exists_cocycleMap_eq_of_cocycleIsColimitPresentation (i : D.I) (Y : D.C i) (j : D.I)
    (a : j ⟶ i) (s s' : ToType ((M.obj j).obj.obj (op ((D.u a).obj Y))))
    (hs : (ι j).app (op ((D.u a).obj Y)) s = (ι j).app (op ((D.u a).obj Y)) s') :
    ∃ (k : D.I) (b : k ⟶ j),
      (M.map b).app (op ((D.u a).obj Y)) s = (M.map b).app (op ((D.u a).obj Y)) s' := by
  have hinclproj : ∀ (n : D.I) (W : (D.C n)ᵒᵖ) (x : ToType ((M.obj n).obj.obj W)),
      (M.splitting n).incl.hom.app W ((M.splitting n).proj.hom.app W x) =
        (M.idem n).hom.app W x := by
    intro n W x
    have h := congrArg (fun φ : M.obj n ⟶ M.obj n => φ.hom.app W x) (M.splitting n).proj_incl
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ConcreteCategory.comp_apply] at h
    exact h
  have hidemι : ∀ x : ToType ((M.obj j).obj.obj (op ((D.u a).obj Y))),
      (ι j).app (op ((D.u a).obj Y)) ((M.splitting j).incl.hom.app (op ((D.u a).obj Y))
          ((M.splitting j).proj.hom.app (op ((D.u a).obj Y)) x)) =
        (ι j).app (op ((D.u a).obj Y)) x := by
    intro x
    refine Eq.trans (congrArg (fun y => (ι j).app (op ((D.u a).obj Y)) y)
      (hinclproj j (op ((D.u a).obj Y)) x)) ?_
    have h := congrArg (fun φ => φ.app (op ((D.u a).obj Y)))
      (idem_comp_of_isCompatible M uC hu G.obj ι hM.1 j)
    simp only [NatTrans.comp_app] at h
    exact (ConcreteCategory.comp_apply ((M.idem j).hom.app (op ((D.u a).obj Y)))
      ((ι j).app (op ((D.u a).obj Y))) x).symm.trans (ConcreteCategory.congr_hom h x)
  obtain ⟨k, b, hb⟩ := exists_transition_eq_of_isColimitPresentation
    D (M.split M.splitting) uC hu hobj hhom hhom_inj K hK G
    (fun j => (M.splitting j).incl.hom ≫ ι j)
    (M.isColimitPresentation_split M.splitting uC hu K G ι hM) i Y j a
    ((M.splitting j).proj.hom.app (op ((D.u a).obj Y)) s)
    ((M.splitting j).proj.hom.app (op ((D.u a).obj Y)) s')
    (by
      have hcomp : ∀ x : ToType ((M.splitting j).obj.obj.obj (op ((D.u a).obj Y))),
          ((M.splitting j).incl.hom ≫ ι j).app (op ((D.u a).obj Y)) x =
            (ι j).app (op ((D.u a).obj Y))
              ((M.splitting j).incl.hom.app (op ((D.u a).obj Y)) x) :=
        fun x => ConcreteCategory.comp_apply
          ((M.splitting j).incl.hom.app (op ((D.u a).obj Y)))
          ((ι j).app (op ((D.u a).obj Y))) x
      exact (hcomp _).trans ((hidemι s).trans
        (hs.trans ((hidemι s').symm.trans (hcomp _).symm))))
  refine ⟨k, b, ?_⟩
  -- the split transition, read on elements: inclusion, the datum's transition, projection
  have hsplit : ∀ x : ToType ((M.obj j).obj.obj (op ((D.u a).obj Y))),
      (transition.{v, u, w, t} D (M.split M.splitting) b).app (op ((D.u a).obj Y))
          ((M.splitting j).proj.hom.app (op ((D.u a).obj Y)) x) =
        (M.splitting k).proj.hom.app ((D.u b).op.obj (op ((D.u a).obj Y)))
          ((M.map b).app (op ((D.u a).obj Y)) x) := by
    intro x
    rw [M.transition_split M.splitting b]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, ConcreteCategory.comp_apply]
    refine congrArg (fun y => (M.splitting k).proj.hom.app
      ((D.u b).op.obj (op ((D.u a).obj Y))) y) ?_
    refine Eq.trans (congrArg (fun y => (M.map b).app (op ((D.u a).obj Y)) y)
      (hinclproj j (op ((D.u a).obj Y)) x)) ?_
    have h := congrArg (fun φ => φ.app (op ((D.u a).obj Y))) (M.idem_comp_map b)
    simp only [NatTrans.comp_app] at h
    exact (ConcreteCategory.comp_apply ((M.idem j).hom.app (op ((D.u a).obj Y)))
      ((M.map b).app (op ((D.u a).obj Y))) x).symm.trans (ConcreteCategory.congr_hom h x)
  rw [hsplit s, hsplit s'] at hb
  have hidem : (M.idem k).hom.app ((D.u b).op.obj (op ((D.u a).obj Y)))
        ((M.map b).app (op ((D.u a).obj Y)) s) =
      (M.idem k).hom.app ((D.u b).op.obj (op ((D.u a).obj Y)))
        ((M.map b).app (op ((D.u a).obj Y)) s') := by
    rw [← hinclproj k ((D.u b).op.obj (op ((D.u a).obj Y))) ((M.map b).app (op ((D.u a).obj Y)) s),
      ← hinclproj k ((D.u b).op.obj (op ((D.u a).obj Y)))
        ((M.map b).app (op ((D.u a).obj Y)) s'), hb]
  have hmapid : (M.map (𝟙 k)).app ((D.u b).op.obj (op ((D.u a).obj Y)))
        ((M.map b).app (op ((D.u a).obj Y)) s) =
      (M.map (𝟙 k)).app ((D.u b).op.obj (op ((D.u a).obj Y)))
        ((M.map b).app (op ((D.u a).obj Y)) s') := by
    have h := congrArg (fun φ => φ.app ((D.u b).op.obj (op ((D.u a).obj Y)))) (M.map_id_eq k)
    simp only [NatTrans.comp_app] at h
    rw [ConcreteCategory.congr_hom h, ConcreteCategory.congr_hom h]
    simp only [ConcreteCategory.comp_apply]
    exact congrArg _ hidem
  have h := congrArg (fun φ => φ.app (op ((D.u a).obj Y)))
    (M.map_comp' (𝟙 k) b (Category.id_comp b))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  refine ((ConcreteCategory.congr_hom h s).trans ?_).trans
    (ConcreteCategory.congr_hom h s').symm
  simp only [ConcreteCategory.comp_apply]
  exact congrArg _ hmapid

end CocycleObjectSections

end Stacks.WeakSites.ColimitSiteCohomology

end
