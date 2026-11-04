module

public import StacksFrontier.AlgebraicGeometry.Pushout.ColimitSections

/-!
# Sections of a pushout square of presheafed spaces, and comparison of two such squares

[Stacks Project, Tag 0E25] identifies the structure sheaf of a pushout `Y ⨿_Z X` with the fibre
product `b_* 𝒪_Y ×_{c_* 𝒪_Z} a_* 𝒪_X`.  Read on an open `U` of the pushout that says that the
square of rings of sections is cartesian.  For a colimit of a span of presheafed spaces over
`CommRingCat` this is `Stacks.Pushout.isPullback_app_colimit_span`; here it is transported to an
arbitrary pushout square, and then used to compare the sections of two pushout squares along a
morphism between them.

The comparison is the engine of the gluing construction: a morphism from the affine model of
[Stacks Project, Tag 0ET0] to the pushout is an isomorphism on sections over an open of the
pushout as soon as the three comparison maps of the span are, which for an open subspace they
are for trivial reasons.

## Main results

* `Stacks.Pushout.isPullback_app_of_isPushout`: the sections of a pushout square of presheafed
  spaces over any open of the apex form a cartesian square.  No hypothesis is needed.
* `Stacks.Pushout.isIso_app_of_isPushout_comparison`: a morphism between two pushout squares of
  presheafed spaces which is an isomorphism on the sections of the three outer objects is an
  isomorphism on the sections of the apex.
* `Stacks.Pushout.IsPullback.isIso_of_comp_eq` and
  `Stacks.Pushout.IsPushout.isIso_of_comp_eq`: a morphism between the apexes of two cartesian
  (respectively cocartesian) squares on the same cospan (span) which commutes with the two legs
  is an isomorphism.

## Implementation notes

The common target of the two bottom legs is an explicit argument of
`Stacks.Pushout.isPullback_app_of_isPushout`, together with the two equations identifying it
with the two preimages of the open in the apex of the span.  Taking the open and the equations
as separate arguments is what lets the comparison be stated with no transport on the `Z`-leg:
the consumer picks the common target to be the preimage along one square and its image along
the comparison for the other, so that the two legs are literally the components of the two
structure-sheaf maps.

Every identification in this file is an equality of opens followed by `eqToHom`.  They are
assembled from `Stacks.Pushout.app_comp_map_eqToHom` and
`Stacks.Pushout.app_comp_map_eqToHom_congr`, both of which are proved by substituting the
equality of morphisms, after which proof irrelevance makes the two transports the same term.
Writing the instantiated conclusions out instead makes the elaborator unfold
`AlgebraicGeometry.PresheafedSpace.restrict` and the colimit comparison isomorphism, which is
what the `have`-with-inferred-type style here avoids.

The universe of the carrier of `AlgebraicGeometry.PresheafedSpace CommRingCat.{u}` is pinned to
`u`, as in `AlgebraicGeometry.PresheafedSpace.instHasColimitsOfShape`: left free it is
auto-bound to a fresh universe and the colimit of a span no longer exists.

## References

* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 0ET0](https://stacks.math.columbia.edu/tag/0ET0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.Pushout

/-! ### Transports along equalities of objects -/

/-- Two successive transports of a section along equalities of opens are one transport. -/
lemma comp_map_eqToHom_eq {C : Type*} [Category C] {J : Type*} [Category J] (F : J ⥤ C)
    {A B B' : J} {R : C} (f : R ⟶ F.obj A) (p : A = B) (q : B = B') (r : A = B') :
    f ≫ F.map (eqToHom r) = (f ≫ F.map (eqToHom p)) ≫ F.map (eqToHom q) := by
  rw [Category.assoc, ← F.map_comp, eqToHom_trans]

/-- Equal morphisms of presheafed spaces have the same component on sections, after the
transport along the equality of the two preimages. -/
lemma app_comp_map_eqToHom {C : Type*} [Category C] {X Y : PresheafedSpace C} {α β : X ⟶ Y}
    (hαβ : α = β) (U : (Opens Y)ᵒᵖ)
    (e : op ((Opens.map α.base).obj (unop U)) = op ((Opens.map β.base).obj (unop U))) :
    α.c.app U ≫ X.presheaf.map (eqToHom e) = β.c.app U := by
  subst hαβ
  rw [eqToHom_refl, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- Equal morphisms of presheafed spaces have the same component on sections, after transport
to any common target. -/
lemma app_comp_map_eqToHom_congr {C : Type*} [Category C] {X Y : PresheafedSpace C}
    {α β : X ⟶ Y} (hαβ : α = β) (U : (Opens Y)ᵒᵖ) {R : (Opens X)ᵒᵖ}
    (e₁ : op ((Opens.map α.base).obj (unop U)) = R)
    (e₂ : op ((Opens.map β.base).obj (unop U)) = R) :
    α.c.app U ≫ X.presheaf.map (eqToHom e₁) = β.c.app U ≫ X.presheaf.map (eqToHom e₂) := by
  subst hαβ
  rfl

/-- Equal morphisms of presheafed spaces have equal preimages of an open. -/
private lemma op_map_obj_congr {C : Type*} [Category C] {X Y : PresheafedSpace C} {α β : X ⟶ Y}
    (hαβ : α = β) (U : Opens Y) :
    op ((Opens.map α.base).obj U) = op ((Opens.map β.base).obj U) := by
  subst hαβ
  rfl

/-! ### Two squares on the same cospan -/

/-- A morphism between the apexes of two cartesian squares on the same cospan which commutes
with both projections is an isomorphism. -/
lemma IsPullback.isIso_of_comp_eq {C : Type*} [Category C] {P P' X Y Z : C} {fst : P ⟶ X}
    {snd : P ⟶ Y} {fst' : P' ⟶ X} {snd' : P' ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : CategoryTheory.IsPullback fst snd f g)
    (h' : CategoryTheory.IsPullback fst' snd' f g) (m : P ⟶ P')
    (h₁ : m ≫ fst' = fst) (h₂ : m ≫ snd' = snd) : IsIso m := by
  refine ⟨h.lift fst' snd' h'.w, h.hom_ext ?_ ?_, h'.hom_ext ?_ ?_⟩
  · rw [Category.assoc, h.lift_fst, h₁, Category.id_comp]
  · rw [Category.assoc, h.lift_snd, h₂, Category.id_comp]
  · rw [Category.assoc, h₁, h.lift_fst, Category.id_comp]
  · rw [Category.assoc, h₂, h.lift_snd, Category.id_comp]

/-- A morphism between the apexes of two cocartesian squares on the same span which commutes
with both inclusions is an isomorphism. -/
lemma IsPushout.isIso_of_comp_eq {C : Type*} [Category C] {Z X Y P P' : C} {f : Z ⟶ X}
    {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P} {inl' : X ⟶ P'} {inr' : Y ⟶ P'}
    (h : CategoryTheory.IsPushout f g inl inr)
    (h' : CategoryTheory.IsPushout f g inl' inr') (m : P ⟶ P')
    (h₁ : inl ≫ m = inl') (h₂ : inr ≫ m = inr') : IsIso m := by
  refine ⟨h'.desc inl inr h.w, h.hom_ext ?_ ?_, h'.hom_ext ?_ ?_⟩
  · rw [← Category.assoc, h₁, h'.inl_desc, Category.comp_id]
  · rw [← Category.assoc, h₂, h'.inr_desc, Category.comp_id]
  · rw [← Category.assoc, h'.inl_desc, h₁, Category.comp_id]
  · rw [← Category.assoc, h'.inr_desc, h₂, Category.comp_id]

/-! ### Sections of a pushout square of presheafed spaces -/

/-- **The structure sheaf of a pushout of presheafed spaces is a fibre product.**  For a pushout
square `i`, `j`, `a`, `b` of presheafed spaces over `CommRingCat` and an open `O` of the apex,
the square of rings of sections is cartesian.

The common target of the two bottom legs is the argument `OZ`, with the two equations
identifying it with the two preimages of `O` in the apex of the span; taking `OZ` as an argument
is what makes the statement usable without further transport. -/
theorem isPullback_app_of_isPushout {Z X Y P : PresheafedSpace.{u, u + 1, u} CommRingCat.{u}}
    {i : Z ⟶ X} {j : Z ⟶ Y} {a : X ⟶ P} {b : Y ⟶ P} (h : IsPushout i j a b) (O : Opens P)
    (OZ : Opens Z)
    (hY : op ((Opens.map j.base).obj ((Opens.map b.base).obj O)) = op OZ)
    (hX : op ((Opens.map i.base).obj ((Opens.map a.base).obj O)) = op OZ) :
    CategoryTheory.IsPullback (b.c.app (op O)) (a.c.app (op O))
      (j.c.app (op ((Opens.map b.base).obj O)) ≫ Z.presheaf.map (eqToHom hY))
      (i.c.app (op ((Opens.map a.base).obj O)) ≫ Z.presheaf.map (eqToHom hX)) := by
  obtain ⟨e, hl, hr⟩ : ∃ e : colimit (span i j) ≅ P,
      colimit.ι (span i j) WalkingSpan.left ≫ e.hom = a ∧
      colimit.ι (span i j) WalkingSpan.right ≫ e.hom = b := by
    have hC := IsPushout.of_isColimit_cocone (colimit.isColimit (span i j))
    exact ⟨hC.isoIsPushout X Y h, IsPushout.inl_isoIsPushout_hom X Y hC h,
      IsPushout.inr_isoIsPushout_hom X Y hC h⟩
  subst hl hr
  have hzj : op ((Opens.map j.base).obj
      ((Opens.map (colimit.ι (span i j) WalkingSpan.right ≫ e.hom).base).obj O)) =
      op ((Opens.map (colimit.ι (span i j) WalkingSpan.zero).base).obj
        ((Opens.map e.hom.base).obj O)) :=
    congrArg (fun f : Z ⟶ colimit (span i j) ↦
      op ((Opens.map f.base).obj ((Opens.map e.hom.base).obj O)))
      (colimit.w (span i j) WalkingSpan.Hom.snd)
  have hzi : op ((Opens.map i.base).obj
      ((Opens.map (colimit.ι (span i j) WalkingSpan.left ≫ e.hom).base).obj O)) =
      op ((Opens.map (colimit.ι (span i j) WalkingSpan.zero).base).obj
        ((Opens.map e.hom.base).obj O)) :=
    congrArg (fun f : Z ⟶ colimit (span i j) ↦
      op ((Opens.map f.base).obj ((Opens.map e.hom.base).obj O)))
      (colimit.w (span i j) WalkingSpan.Hom.fst)
  have hz : op ((Opens.map (colimit.ι (span i j) WalkingSpan.zero).base).obj
      ((Opens.map e.hom.base).obj O)) = op OZ := hzj.symm.trans hY
  have hc : IsIso e.hom.c := PresheafedSpace.c_isIso_of_iso e.hom
  have hiso : IsIso (e.hom.c.app (op O)) := NatIso.isIso_app_of_isIso (α := e.hom.c) (op O)
  have H := (isPullback_app_colimit_span i j ((Opens.map e.hom.base).obj O)).flip
  refine H.of_iso (asIso (e.hom.c.app (op O))).symm (Iso.refl _) (Iso.refl _)
    (Z.presheaf.mapIso (eqToIso hz)) (by simp) (by simp) ?_ ?_
  · exact (comp_map_eqToHom_eq Z.presheaf _ hzj hz hY).symm.trans (Category.id_comp _).symm
  · exact (comp_map_eqToHom_eq Z.presheaf _ hzi hz hX).symm.trans (Category.id_comp _).symm

/-- Two successive structure-sheaf components, each transported to a named open. -/
lemma app_comp_app_map_eqToHom {A B C : PresheafedSpace.{u, u + 1, u} CommRingCat.{u}}
    (g : A ⟶ B) (f : B ⟶ C) (U : Opens C) {OB : Opens B} {OA : Opens A}
    (hOB : op ((Opens.map f.base).obj U) = op OB)
    (hOA : op ((Opens.map g.base).obj OB) = op OA)
    (hOA' : op ((Opens.map g.base).obj ((Opens.map f.base).obj U)) = op OA) :
    (f.c.app (op U) ≫ B.presheaf.map (eqToHom hOB)) ≫
        (g.c.app (op OB) ≫ A.presheaf.map (eqToHom hOA)) =
      (g ≫ f).c.app (op U) ≫ A.presheaf.map (eqToHom hOA') := by
  obtain rfl : OB = (Opens.map f.base).obj U := (congrArg Opposite.unop hOB).symm
  obtain rfl : OA = (Opens.map g.base).obj ((Opens.map f.base).obj U) :=
    (congrArg Opposite.unop hOA).symm
  simp

/-- Two successive structure-sheaf components, the second without a transport. -/
lemma app_comp_app' {A B C : PresheafedSpace.{u, u + 1, u} CommRingCat.{u}}
    (g : A ⟶ B) (f : B ⟶ C) (U : Opens C) {OB : Opens B}
    (hOB : op ((Opens.map f.base).obj U) = op OB)
    (hOA' : op ((Opens.map g.base).obj ((Opens.map f.base).obj U)) =
      op ((Opens.map g.base).obj OB)) :
    (f.c.app (op U) ≫ B.presheaf.map (eqToHom hOB)) ≫ g.c.app (op OB) =
      (g ≫ f).c.app (op U) ≫ A.presheaf.map (eqToHom hOA') := by
  obtain rfl : OB = (Opens.map f.base).obj U := (congrArg Opposite.unop hOB).symm
  simp

/-- **The structure sheaf of a pushout of presheafed spaces is a fibre product**, with the two
bottom legs meeting over the preimage along the right-hand leg.  This is
`Stacks.Pushout.isPullback_app_of_isPushout` with the common target chosen so that the leg from
`Y` carries no transport, which is the orientation of [Stacks Project, Tag 0E25]. -/
theorem isPullback_app_of_isPushout_right
    {Z X Y P : PresheafedSpace.{u, u + 1, u} CommRingCat.{u}}
    {i : Z ⟶ X} {j : Z ⟶ Y} {a : X ⟶ P} {b : Y ⟶ P} (h : IsPushout i j a b) (O : Opens P)
    (hX : op ((Opens.map i.base).obj ((Opens.map a.base).obj O)) =
      op ((Opens.map j.base).obj ((Opens.map b.base).obj O))) :
    CategoryTheory.IsPullback (b.c.app (op O)) (a.c.app (op O))
      (j.c.app (op ((Opens.map b.base).obj O)))
      (i.c.app (op ((Opens.map a.base).obj O)) ≫ Z.presheaf.map (eqToHom hX)) := by
  simpa using isPullback_app_of_isPushout h O ((Opens.map j.base).obj ((Opens.map b.base).obj O))
    rfl hX

/-! ### Comparison of two pushout squares -/

/-- **A morphism of pushout squares of presheafed spaces which is an isomorphism on the three
outer objects is an isomorphism on the apex.**  For a morphism `m` from the apex of one pushout
square to the apex of another, commuting with three morphisms `t`, `u`, `v` of the two spans,
and an open `O` of the target apex: if the three comparison maps are isomorphisms on the
sections over the three preimages of `O`, then so is `m` on the sections over `O`.

Both apexes have their sections over `O` cartesian over the same cospan, by
`Stacks.Pushout.isPullback_app_of_isPushout`; the common target of the two bottom legs is chosen
to be the preimage of `O` in the apex of the first span for one square and its preimage under
`t` for the other, which is what makes the `Z`-leg of the comparison the component of `t` with
no transport. -/
theorem isIso_app_of_isPushout_comparison
    {Z X Y P Z' X' Y' Q : PresheafedSpace.{u, u + 1, u} CommRingCat.{u}}
    {i : Z ⟶ X} {j : Z ⟶ Y} {a : X ⟶ P} {b : Y ⟶ P}
    {i' : Z' ⟶ X'} {j' : Z' ⟶ Y'} {α : X' ⟶ Q} {β : Y' ⟶ Q}
    (h : IsPushout i j a b) (h' : IsPushout i' j' α β)
    {t : Z' ⟶ Z} {u : X' ⟶ X} {v : Y' ⟶ Y} {m : Q ⟶ P}
    (sqa : α ≫ m = u ≫ a) (sqb : β ≫ m = v ≫ b)
    (sqi : i' ≫ u = t ≫ i) (sqj : j' ≫ v = t ≫ j)
    (O : Opens P)
    (hu : IsIso (u.c.app (op ((Opens.map a.base).obj O))))
    (hv : IsIso (v.c.app (op ((Opens.map b.base).obj O))))
    (ht : IsIso (t.c.app (op ((Opens.map i.base).obj ((Opens.map a.base).obj O))))) :
    IsIso (m.c.app (op O)) := by
  have hca : i' ≫ α ≫ m = t ≫ i ≫ a := by
    rw [sqa, ← Category.assoc, sqi, Category.assoc]
  have hcb : j' ≫ β ≫ m = t ≫ i ≫ a := by
    rw [sqb, ← Category.assoc, sqj, Category.assoc, ← h.w]
  have hYO : op ((Opens.map j.base).obj ((Opens.map b.base).obj O)) =
      op ((Opens.map i.base).obj ((Opens.map a.base).obj O)) :=
    op_map_obj_congr h.w.symm O
  have HP := isPullback_app_of_isPushout h O _ hYO rfl
  have hY' : op ((Opens.map j'.base).obj ((Opens.map β.base).obj
        ((Opens.map m.base).obj O))) =
      op ((Opens.map t.base).obj ((Opens.map i.base).obj ((Opens.map a.base).obj O))) :=
    op_map_obj_congr hcb O
  have hX' : op ((Opens.map i'.base).obj ((Opens.map α.base).obj
        ((Opens.map m.base).obj O))) =
      op ((Opens.map t.base).obj ((Opens.map i.base).obj ((Opens.map a.base).obj O))) :=
    op_map_obj_congr hca O
  have HQ := isPullback_app_of_isPushout h' ((Opens.map m.base).obj O) _ hY' hX'
  have hβY : op ((Opens.map v.base).obj ((Opens.map b.base).obj O)) =
      op ((Opens.map β.base).obj ((Opens.map m.base).obj O)) :=
    op_map_obj_congr sqb.symm O
  have hαX : op ((Opens.map u.base).obj ((Opens.map a.base).obj O)) =
      op ((Opens.map α.base).obj ((Opens.map m.base).obj O)) :=
    op_map_obj_congr sqa.symm O
  have hiY : IsIso (v.c.app (op ((Opens.map b.base).obj O)) ≫
      Y'.presheaf.map (eqToHom hβY)) := IsIso.comp_isIso' hv inferInstance
  have hiX : IsIso (u.c.app (op ((Opens.map a.base).obj O)) ≫
      X'.presheaf.map (eqToHom hαX)) := IsIso.comp_isIso' hu inferInstance
  have hLf : op ((Opens.map t.base).obj ((Opens.map j.base).obj ((Opens.map b.base).obj O))) =
      op ((Opens.map t.base).obj ((Opens.map i.base).obj ((Opens.map a.base).obj O))) :=
    congrArg (fun S : Opens Z ↦ op ((Opens.map t.base).obj S)) (congrArg Opposite.unop hYO)
  have hRf : op ((Opens.map j'.base).obj ((Opens.map v.base).obj ((Opens.map b.base).obj O))) =
      op ((Opens.map t.base).obj ((Opens.map i.base).obj ((Opens.map a.base).obj O))) :=
    (congrArg (fun f : Z' ⟶ Y ↦ op ((Opens.map f.base).obj ((Opens.map b.base).obj O)))
      sqj).trans hLf
  have hLg : op ((Opens.map t.base).obj ((Opens.map i.base).obj ((Opens.map a.base).obj O))) =
      op ((Opens.map t.base).obj ((Opens.map i.base).obj ((Opens.map a.base).obj O))) := rfl
  have hRg : op ((Opens.map i'.base).obj ((Opens.map u.base).obj ((Opens.map a.base).obj O))) =
      op ((Opens.map t.base).obj ((Opens.map i.base).obj ((Opens.map a.base).obj O))) :=
    congrArg (fun f : Z' ⟶ X ↦ op ((Opens.map f.base).obj ((Opens.map a.base).obj O))) sqi
  refine IsPullback.isIso_of_comp_eq
    (HP.of_iso (Iso.refl _) (@asIso _ _ _ _ _ hiY) (@asIso _ _ _ _ _ hiX)
      (@asIso _ _ _ _ _ ht) ?_ ?_ ?_ ?_) HQ (m.c.app (op O)) rfl rfl
  · simpa using app_comp_map_eqToHom sqb.symm (op O) hβY
  · simpa using app_comp_map_eqToHom sqa.symm (op O) hαX
  · simp only [asIso_hom]
    refine (app_comp_app' t j ((Opens.map b.base).obj O) hYO hLf).trans
      (Eq.trans ?_ (app_comp_app_map_eqToHom j' v ((Opens.map b.base).obj O) hβY hY' hRf).symm)
    exact app_comp_map_eqToHom_congr sqj.symm (op ((Opens.map b.base).obj O)) hLf hRf
  · simp only [asIso_hom]
    refine (app_comp_app' t i ((Opens.map a.base).obj O) rfl hLg).trans
      (Eq.trans ?_ (app_comp_app_map_eqToHom i' u ((Opens.map a.base).obj O) hαX hX' hRg).symm)
    exact app_comp_map_eqToHom_congr sqi.symm (op ((Opens.map a.base).obj O)) hLg hRg

end Stacks.Pushout

end
