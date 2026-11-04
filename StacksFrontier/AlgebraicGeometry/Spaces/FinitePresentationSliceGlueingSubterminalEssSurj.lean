module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueingSubterminalFull

/-!
# The glued presheaf over a subterminal base

`CategoryTheory.SubterminalGlueing.gluedPresheaf` glues two presheaves `A` over `U` and `B`
over `W` along an identification of their restrictions to `V`: its sections over `X` are the
pairs of a section of `A` over `U ⨯ X` and a section of `B` over `W ⨯ X` agreeing over `V ⨯ X`.
Over a *terminal* base `Z` that presheaf is the glued space, and
`CategoryTheory.SubterminalGlueing.gluedOver` makes it an object over `yoneda.obj Z` using the
unique morphism to a terminal object.

Over a base which is only subterminal that is wrong, and not repairably so: for `U ∪ W = Z` a
proper subobject of the terminal object, `gluedPresheaf` has sections over objects which do not
lie over `Z` at all — its value at `X` is the sections of the glued space over `Z ⨯ X`, not over
`X` — so it carries no morphism to `yoneda.obj Z` and is not the glued space. The glued space is
cut down to the objects lying over `Z`:

  `gluedPresheafOver X = gluedPresheaf X × (X ⟶ Z)`,

which is the binary product `gluedPresheaf ⨯ yoneda.obj Z` (see
`CategoryTheory.SubterminalGlueing.isLimitGluedPresheafOverBinaryFan`), written out so that its
sections
can be manipulated directly. The second factor is a subsingleton, so over an object lying over
`Z` nothing is lost, and over an object not lying over `Z` the sections are empty, as they must
be for a presheaf over `yoneda.obj Z`.

This file redoes for `gluedPresheafOver` what the `Restriction` section of
`StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing` does for `gluedOver`: its
restrictions to `U` and to `W` are the two presheaves glued, those restrictions are base changes
of its structure morphism, and they agree over `V`. None of it uses more than subterminality of
`Z`.

## Main results

* `CategoryTheory.SubterminalGlueing.gluedPresheafOver`, `gluedOverToBase` and `gluedOverSub`:
  the glued presheaf over a subterminal base, its structure morphism, and the resulting object
  of the slice.
* `CategoryTheory.SubterminalGlueing.gluedRestrictLeftIsoSub` and `gluedRestrictRightIsoSub`:
  the restrictions to `U` and to `W` are the two presheaves glued.
* `CategoryTheory.SubterminalGlueing.isPullback_gluedRestrictLeftSub` and
  `isPullback_gluedRestrictRightSub`: the structure morphisms of the two presheaves glued are
  base changes of the structure morphism of the glued presheaf.
* `CategoryTheory.SubterminalGlueing.gluedRestrictSub_comm`: the two restriction comparisons
  agree over `V`.

## References

* [Stacks Project, Tag 0E8Z](https://stacks.math.columbia.edu/tag/0E8Z)
* [Stacks Project, Tag 0E91](https://stacks.math.columbia.edu/tag/0E91)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.SubterminalGlueing

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] {U W V : C} {iU : V ⟶ U}
  {iW : V ⟶ W} (hU : IsSubterminal U) (hW : IsSubterminal W) (hV : IsSubterminal V)
  {A : Over (yoneda.obj U : Cᵒᵖ ⥤ Type v)} {Bb : Over (yoneda.obj W : Cᵒᵖ ⥤ Type v)}
  (φ : (Over.pullback (yoneda.map iU)).obj A ≅ (Over.pullback (yoneda.map iW)).obj Bb)

/-! ### The glued presheaf cut down to a subterminal base -/

section Base

/-- **The presheaf glued from `A` and `B` over a base `Z` which need not be terminal**: its
sections over `X` are the sections of `CategoryTheory.SubterminalGlueing.gluedPresheaf` over `X`
together with a morphism `X ⟶ Z`.

This is the binary product `gluedPresheaf ⨯ yoneda.obj Z`, by
`CategoryTheory.SubterminalGlueing.isLimitGluedPresheafOverBinaryFan`; it is written out because
its sections are manipulated componentwise throughout. For `Z` terminal the second factor is a
singleton and this is `gluedPresheaf` again. -/
noncomputable def gluedPresheafOver (Z : C) : Cᵒᵖ ⥤ Type v where
  obj X := (gluedPresheaf hU hW hV φ).obj X × (X.unop ⟶ Z)
  map {_ _} g := ↾fun p => ((gluedPresheaf hU hW hV φ).map g p.1, g.unop ≫ p.2)
  map_id X := by
    ext p
    · exact (gluedPresheaf hU hW hV φ).map_id_apply X p.1
    · simp
  map_comp f g := by
    ext p
    · exact (gluedPresheaf hU hW hV φ).map_comp_apply f g p.1
    · simp

/-- The first component of a restricted section of the glued presheaf. -/
@[simp]
theorem gluedPresheafOver_map_fst (Z : C) {X Y : Cᵒᵖ} (g : X ⟶ Y)
    (p : (gluedPresheafOver hU hW hV φ Z).obj X) :
    ((gluedPresheafOver hU hW hV φ Z).map g p).1 = (gluedPresheaf hU hW hV φ).map g p.1 :=
  rfl

/-- The second component of a restricted section of the glued presheaf. -/
@[simp]
theorem gluedPresheafOver_map_snd (Z : C) {X Y : Cᵒᵖ} (g : X ⟶ Y)
    (p : (gluedPresheafOver hU hW hV φ Z).obj X) :
    ((gluedPresheafOver hU hW hV φ Z).map g p).2 = g.unop ≫ p.2 :=
  rfl

/-- **The structure morphism of the glued presheaf to the representable presheaf of the base.**
Over a terminal base this is the unique such morphism,
`CategoryTheory.SubterminalGlueing.gluedToTerminal`; over a subterminal base it is part of the
construction, and is what `gluedPresheaf` alone cannot provide. -/
noncomputable def gluedOverToBase (Z : C) : gluedPresheafOver hU hW hV φ Z ⟶ yoneda.obj Z where
  app _ := ↾fun p => p.2
  naturality _ _ _ := rfl

/-- The glued presheaf, as an object over the representable presheaf of the base. -/
noncomputable def gluedOverSub (Z : C) : Over (yoneda.obj Z : Cᵒᵖ ⥤ Type v) :=
  Over.mk (gluedOverToBase hU hW hV φ Z)

/-- The structure morphism of `gluedOverSub` is `gluedOverToBase`. -/
@[simp]
theorem gluedOverSub_hom (Z : C) :
    (gluedOverSub hU hW hV φ Z).hom = gluedOverToBase hU hW hV φ Z :=
  rfl

/-- The projection of the glued presheaf over the base onto the glued presheaf, forgetting the
morphism to the base. -/
noncomputable def gluedOverSubFst (Z : C) :
    gluedPresheafOver hU hW hV φ Z ⟶ gluedPresheaf hU hW hV φ where
  app _ := ↾fun p => p.1
  naturality _ _ _ := rfl

/-- **The glued presheaf over the base, with the projection to the glued presheaf and its
structure morphism, is the binary product of the glued presheaf and the representable presheaf
of the base.** This is the sense in which the object of this file is
`gluedPresheaf ⨯ yoneda.obj Z`. -/
noncomputable def isLimitGluedPresheafOverBinaryFan (Z : C) :
    IsLimit (BinaryFan.mk (gluedOverSubFst hU hW hV φ Z) (gluedOverToBase hU hW hV φ Z)) :=
  BinaryFan.isLimitMk
    (fun s =>
      { app X := ↾fun x => (s.fst.app X x, s.snd.app X x)
        naturality _ _ g := by
          ext x
          refine Prod.ext ?_ ?_
          · exact NatTrans.naturality_apply s.fst g x
          · exact NatTrans.naturality_apply s.snd g x })
    (fun _ => rfl) (fun _ => rfl)
    (fun _ m h₁ h₂ => by
      ext X x
      refine Prod.ext ?_ ?_
      · exact ConcreteCategory.congr_hom (NatTrans.congr_app h₁ X) x
      · exact ConcreteCategory.congr_hom (NatTrans.congr_app h₂ X) x)

/-- **The glued presheaf over the base is a sheaf** as soon as the two presheaves glued and the
representable presheaf of the base are: it is their binary product. -/
theorem isSheaf_gluedPresheafOver (Z : C) (J : GrothendieckTopology C)
    (hA : Presheaf.IsSheaf J A.left) (hB : Presheaf.IsSheaf J Bb.left)
    (hZs : Presheaf.IsSheaf J (yoneda.obj Z)) :
    Presheaf.IsSheaf J (gluedPresheafOver hU hW hV φ Z) :=
  ObjectProperty.prop_of_isLimit _ (isLimitGluedPresheafOverBinaryFan hU hW hV φ Z) (by
    rintro ⟨_ | _⟩
    · exact isSheaf_gluedPresheaf hU hW hV φ J hA hB
    · exact hZs)

/-! ### Symmetry -/

/-- Swapping the two presheaves glued exchanges the glued presheaves over the base. -/
noncomputable def gluedPresheafOverSymmHom (Z : C) :
    gluedPresheafOver hU hW hV φ Z ⟶ gluedPresheafOver hW hU hV φ.symm Z where
  app X := ↾fun p => ((gluedPresheafSymmHom hU hW hV φ).app X p.1, p.2)
  naturality _ _ _ := rfl

/-- **The glueing construction over a base is symmetric in its two arguments.** -/
noncomputable def gluedPresheafOverSymmIso (Z : C) :
    gluedPresheafOver hU hW hV φ Z ≅ gluedPresheafOver hW hU hV φ.symm Z where
  hom := gluedPresheafOverSymmHom hU hW hV φ Z
  inv := gluedPresheafOverSymmHom hW hU hV φ.symm Z
  hom_inv_id := by ext X p; rfl
  inv_hom_id := by ext X p; rfl

/-- The symmetry of the glueing construction, read over the representable presheaf of the
base. -/
noncomputable def gluedOverSubSymmIso (Z : C) :
    gluedOverSub hU hW hV φ Z ≅ gluedOverSub hW hU hV φ.symm Z :=
  Over.isoMk (gluedPresheafOverSymmIso hU hW hV φ Z) (by ext X p; rfl)

end Base

/-! ### The restriction of the glued presheaf to `U` -/

section Restrict

variable {Z : C} (hZ : IsSubterminal Z)

/-- The comparison from the restriction to `U` of the glued presheaf to the first of the two
presheaves glued: a section of the glued presheaf over an object `X` lying over `U` has a first
component over `U ⨯ X`, and the graph of `X ⟶ U` carries it back to a section over `X`. This is
`CategoryTheory.SubterminalGlueing.gluedRestrictLeftHom` over a subterminal base. -/
noncomputable def gluedRestrictLeftHomSub (jU : U ⟶ Z) :
    pullback (gluedOverToBase hU hW hV φ Z) (yoneda.map jU) ⟶ A.left where
  app X := ↾fun z => A.left.map (prod.lift
      ((pullback.snd (gluedOverToBase hU hW hV φ Z) (yoneda.map jU)).app X z) (𝟙 X.unop)).op
    (((pullback.fst (gluedOverToBase hU hW hV φ Z) (yoneda.map jU)).app X z).1.1.1)
  naturality X Y h := ConcreteCategory.hom_ext _ _ fun z => by
    have hs := NatTrans.naturality_apply
      (pullback.snd (gluedOverToBase hU hW hV φ Z) (yoneda.map jU)) h z
    have hf := NatTrans.naturality_apply
      (pullback.fst (gluedOverToBase hU hW hV φ Z) (yoneda.map jU)) h z
    have hmor : prod.lift (h.unop ≫
          (pullback.snd (gluedOverToBase hU hW hV φ Z) (yoneda.map jU)).app X z)
          (𝟙 Y.unop) ≫ prod.map (𝟙 U) h.unop =
        h.unop ≫ prod.lift
          ((pullback.snd (gluedOverToBase hU hW hV φ Z) (yoneda.map jU)).app X z)
          (𝟙 X.unop) := by
      refine prod.hom_ext ?_ ?_ <;> simp
    have key : A.left.map (prod.map (𝟙 U) h.unop).op ≫
          A.left.map (prod.lift (h.unop ≫
            (pullback.snd (gluedOverToBase hU hW hV φ Z) (yoneda.map jU)).app X z)
            (𝟙 Y.unop)).op =
        A.left.map (prod.lift
            ((pullback.snd (gluedOverToBase hU hW hV φ Z) (yoneda.map jU)).app X z)
            (𝟙 X.unop)).op ≫ A.left.map h := by
      rw [← A.left.map_comp, ← A.left.map_comp, ← op_comp, hmor, op_comp, Quiver.Hom.op_unop]
    simp only [types_comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, hs, hf,
      yoneda_obj_map, gluedPresheafOver_map_fst, gluedPresheaf_map_val_fst,
      prod.functor_obj_map, Functor.comp_map, Functor.op_map]
    exact ConcreteCategory.congr_hom key _

/-- The comparison from the restriction to `U` of the glued presheaf, read on sections. -/
theorem gluedRestrictLeftHomSub_app_apply (jU : U ⟶ Z) (X : Cᵒᵖ)
    (z : (pullback (gluedOverToBase hU hW hV φ Z) (yoneda.map jU)).obj X) :
    (gluedRestrictLeftHomSub hU hW hV φ jU).app X z =
      A.left.map (prod.lift
          ((pullback.snd (gluedOverToBase hU hW hV φ Z) (yoneda.map jU)).app X z)
          (𝟙 X.unop)).op
        (((pullback.fst (gluedOverToBase hU hW hV φ Z) (yoneda.map jU)).app X z).1.1.1) :=
  rfl

/-- The comparison of `CategoryTheory.SubterminalGlueing.gluedRestrictLeftHomSub`, as a
morphism of presheaves over the representable presheaf of `U`. -/
noncomputable def gluedRestrictLeftSub (jU : U ⟶ Z) :
    (Over.pullback (yoneda.map jU)).obj (gluedOverSub hU hW hV φ Z) ⟶ A :=
  Over.homMk (gluedRestrictLeftHomSub hU hW hV φ jU) (by ext X z; exact hU _ _)

include hZ in
/-- The comparison is bijective on sections over every object: over an object not lying over
`U` both sides are empty, and over an object lying over `U` it is a composite of four
bijections — the first projection from the base change, forgetting the morphism to the base
(which is unique), the first projection from the glued presheaf, and restriction along the
graph of `X ⟶ U`.

This is `CategoryTheory.SubterminalGlueing.bijective_gluedRestrictLeftHom_app` over a
subterminal base. Terminality was used there only to know that `Z` is subterminal and that the
comparison `V ⨯ X ⟶ W ⨯ X` is invertible over an object lying over `U`, and the latter is
`CategoryTheory.isIso_prod_map_of_hom_of_isSubterminal`. -/
theorem bijective_gluedRestrictLeftHomSub_app {jU : U ⟶ Z} {jW : W ⟶ Z}
    (hVp : IsPullback iU iW jU jW) (X : Cᵒᵖ) :
    Function.Bijective ((gluedRestrictLeftHomSub hU hW hV φ jU).app X) := by
  by_cases hne : Nonempty (X.unop ⟶ U)
  · obtain ⟨p⟩ := hne
    have hb1 : Function.Bijective
        ((pullback.fst (gluedOverToBase hU hW hV φ Z) (yoneda.map jU)).app X) :=
      bijective_pullback_fst_app jU hZ hU (Over.mk (gluedOverToBase hU hW hV φ Z)) p
    have hbz : Function.Bijective ((gluedOverSubFst hU hW hV φ Z).app X) := by
      refine ⟨fun a b h => ?_, fun g => ⟨(g, p ≫ jU), rfl⟩⟩
      have ha : a.1 = b.1 := h
      exact Prod.ext ha (hZ _ _)
    have hb2 : Function.Bijective ((gluedPresheafFst hU hW hV φ).app X) :=
      bijective_gluedPresheafFst_app hU hW hV φ X
        (isIso_prod_map_of_hom_of_isSubterminal hZ hU hVp p)
    have hiso : IsIso (prod.lift p (𝟙 X.unop)) := isIso_prod_lift_id_of_hom hU p
    have hb3 : Function.Bijective (A.left.map (prod.lift p (𝟙 X.unop)).op) :=
      (isIso_iff_bijective _).1 inferInstance
    have hfun : ∀ z, (gluedRestrictLeftHomSub hU hW hV φ jU).app X z =
        A.left.map (prod.lift p (𝟙 X.unop)).op ((gluedPresheafFst hU hW hV φ).app X
          ((gluedOverSubFst hU hW hV φ Z).app X
            ((pullback.fst (gluedOverToBase hU hW hV φ Z) (yoneda.map jU)).app X z))) :=
      fun z =>
      congrArg (fun q : X.unop ⟶ U => A.left.map (prod.lift q (𝟙 X.unop)).op
        ((gluedPresheafFst hU hW hV φ).app X
          ((gluedOverSubFst hU hW hV φ Z).app X
            ((pullback.fst (gluedOverToBase hU hW hV φ Z) (yoneda.map jU)).app X z))))
        (hU _ p)
    refine ⟨fun x y hxy => hb1.injective (hbz.injective (hb2.injective (hb3.injective ?_))),
      fun a => ?_⟩
    · rw [← hfun, ← hfun]
      exact hxy
    · obtain ⟨w, hw⟩ := hb3.surjective a
      obtain ⟨s, hs⟩ := hb2.surjective w
      obtain ⟨t, ht⟩ := hbz.surjective s
      obtain ⟨z, hz⟩ := hb1.surjective t
      exact ⟨z, by rw [hfun, hz, ht, hs, hw]⟩
  · exact ⟨fun x _ _ => absurd ⟨(pullback.snd (gluedOverToBase hU hW hV φ Z)
      (yoneda.map jU)).app X x⟩ hne, fun y => absurd ⟨A.hom.app X y⟩ hne⟩

include hZ in
/-- **The restriction to `U` of the glued presheaf is the first of the two presheaves glued.**
This is `CategoryTheory.SubterminalGlueing.gluedRestrictLeftIso` over a subterminal base. -/
noncomputable def gluedRestrictLeftIsoSub {jU : U ⟶ Z} {jW : W ⟶ Z}
    (hVp : IsPullback iU iW jU jW) :
    (Over.pullback (yoneda.map jU)).obj (gluedOverSub hU hW hV φ Z) ≅ A :=
  haveI : ∀ X : Cᵒᵖ, IsIso ((gluedRestrictLeftHomSub hU hW hV φ jU).app X) := fun X =>
    (isIso_iff_bijective _).2 (bijective_gluedRestrictLeftHomSub_app hU hW hV φ hZ hVp X)
  haveI := NatIso.isIso_of_isIso_app (gluedRestrictLeftHomSub hU hW hV φ jU)
  haveI : IsIso ((Over.forget (yoneda.obj U)).map (gluedRestrictLeftSub hU hW hV φ jU)) :=
    inferInstanceAs (IsIso (gluedRestrictLeftHomSub hU hW hV φ jU))
  haveI : IsIso (gluedRestrictLeftSub hU hW hV φ jU) :=
    isIso_of_reflects_iso _ (Over.forget (yoneda.obj U))
  asIso (gluedRestrictLeftSub hU hW hV φ jU)

include hZ in
/-- The underlying morphism of presheaves of `gluedRestrictLeftIsoSub` is
`gluedRestrictLeftHomSub`. -/
@[simp]
theorem gluedRestrictLeftIsoSub_hom_left {jU : U ⟶ Z} {jW : W ⟶ Z}
    (hVp : IsPullback iU iW jU jW) :
    (gluedRestrictLeftIsoSub hU hW hV φ hZ hVp).hom.left =
      gluedRestrictLeftHomSub hU hW hV φ jU :=
  rfl

include hZ in
/-- **The restriction to `W` of the glued presheaf is the second of the two presheaves glued.**
This is `CategoryTheory.SubterminalGlueing.gluedRestrictLeftIsoSub` with the two arguments of
the glueing construction exchanged. -/
noncomputable def gluedRestrictRightIsoSub {jU : U ⟶ Z} {jW : W ⟶ Z}
    (hVp : IsPullback iU iW jU jW) :
    (Over.pullback (yoneda.map jW)).obj (gluedOverSub hU hW hV φ Z) ≅ Bb :=
  (Over.pullback (yoneda.map jW)).mapIso (gluedOverSubSymmIso hU hW hV φ Z) ≪≫
    gluedRestrictLeftIsoSub hW hU hV φ.symm hZ hVp.flip

include hZ in
/-- The comparison from the restriction to `W` of the glued presheaf, read on sections: it reads
off the second component of the compatible pair and carries it back along the graph. -/
theorem gluedRestrictRightIsoSub_hom_left_app {jU : U ⟶ Z} {jW : W ⟶ Z}
    (hVp : IsPullback iU iW jU jW) (X : Cᵒᵖ)
    (z : (pullback (gluedOverToBase hU hW hV φ Z) (yoneda.map jW)).obj X) :
    (gluedRestrictRightIsoSub hU hW hV φ hZ hVp).hom.left.app X z =
      Bb.left.map (prod.lift
          ((pullback.snd (gluedOverToBase hU hW hV φ Z) (yoneda.map jW)).app X z)
          (𝟙 X.unop)).op
        (((pullback.fst (gluedOverToBase hU hW hV φ Z) (yoneda.map jW)).app X z).1.1.2) := by
  have hfst : (pullback.fst (gluedOverToBase hW hU hV φ.symm Z) (yoneda.map jW)).app X
        (((Over.pullback (yoneda.map jW)).map
          (gluedOverSubSymmIso hU hW hV φ Z).hom).left.app X z) =
      (gluedPresheafOverSymmHom hU hW hV φ Z).app X
        ((pullback.fst (gluedOverToBase hU hW hV φ Z) (yoneda.map jW)).app X z) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app
      (Over.pullback_map_left_comp_fst (yoneda.map jW)
        (gluedOverSubSymmIso hU hW hV φ Z).hom) X) z
  have hsnd : (pullback.snd (gluedOverToBase hW hU hV φ.symm Z) (yoneda.map jW)).app X
        (((Over.pullback (yoneda.map jW)).map
          (gluedOverSubSymmIso hU hW hV φ Z).hom).left.app X z) =
      (pullback.snd (gluedOverToBase hU hW hV φ Z) (yoneda.map jW)).app X z :=
    ConcreteCategory.congr_hom (NatTrans.congr_app
      (Over.w ((Over.pullback (yoneda.map jW)).map
        (gluedOverSubSymmIso hU hW hV φ Z).hom)) X) z
  refine Eq.trans (gluedRestrictLeftHomSub_app_apply hW hU hV φ.symm jW X
    (((Over.pullback (yoneda.map jW)).map
      (gluedOverSubSymmIso hU hW hV φ Z).hom).left.app X z)) ?_
  rw [hfst, hsnd]
  rfl

/-- An isomorphism from a base change of `G` along `f` to `A` makes the structure morphism of `A`
a base change of that of `G`. -/
private theorem isPullback_inv_left_fst_of_iso {D : Type*} [Category D] [HasPullbacks D]
    {P Q : D} (f : Q ⟶ P) (G : Over P)
    (A : Over Q) (e : (Over.pullback f).obj G ≅ A) :
    IsPullback (e.inv.left ≫ pullback.fst G.hom f) A.hom G.hom f :=
  IsPullback.of_iso_pullback
    ⟨by
      rw [Category.assoc, pullback.condition, ← Category.assoc,
        show e.inv.left ≫ pullback.snd G.hom f = A.hom from Over.w _]⟩
    ((Over.forget Q).mapIso e).symm rfl (Over.w e.inv)

include hZ in
/-- **The structure morphism of the first presheaf glued is a base change of the structure
morphism of the glued presheaf** along the Yoneda image of `jU`. This is
`CategoryTheory.SubterminalGlueing.isPullback_gluedRestrictLeft` over a subterminal base. -/
theorem isPullback_gluedRestrictLeftSub {jU : U ⟶ Z} {jW : W ⟶ Z}
    (hVp : IsPullback iU iW jU jW) :
    IsPullback ((gluedRestrictLeftIsoSub hU hW hV φ hZ hVp).inv.left ≫
        pullback.fst (gluedOverSub hU hW hV φ Z).hom (yoneda.map jU))
      A.hom (gluedOverSub hU hW hV φ Z).hom (yoneda.map jU) :=
  isPullback_inv_left_fst_of_iso _ _ _ _

include hZ in
/-- **The structure morphism of the second presheaf glued is a base change of the structure
morphism of the glued presheaf** along the Yoneda image of `jW`. -/
theorem isPullback_gluedRestrictRightSub {jU : U ⟶ Z} {jW : W ⟶ Z}
    (hVp : IsPullback iU iW jU jW) :
    IsPullback ((gluedRestrictRightIsoSub hU hW hV φ hZ hVp).inv.left ≫
        pullback.fst (gluedOverSub hU hW hV φ Z).hom (yoneda.map jW))
      Bb.hom (gluedOverSub hU hW hV φ Z).hom (yoneda.map jW) :=
  isPullback_inv_left_fst_of_iso _ _ _ _

/-! ### The two restrictions agree over `V` -/

include hZ in
/-- **The two comparison isomorphisms of the restrictions of the glued presheaf are compatible
over `V`.** Base changed to `V`, the comparison over `U` followed by the given identification is
the comparison isomorphism of the square followed by the comparison over `W`. This is
`CategoryTheory.SubterminalGlueing.gluedRestrict_comm` over a subterminal base. -/
theorem gluedRestrictSub_comm {jU : U ⟶ Z} {jW : W ⟶ Z} (hVp : IsPullback iU iW jU jW) :
    (Over.pullback (yoneda.map iU)).map (gluedRestrictLeftIsoSub hU hW hV φ hZ hVp).hom ≫
        φ.hom =
      (Over.pullbackSquareObjIso (yoneda_map_comm hVp.w) (gluedOverSub hU hW hV φ Z)).hom ≫
        (Over.pullback (yoneda.map iW)).map
          (gluedRestrictRightIsoSub hU hW hV φ hZ hVp).hom := by
  refine Over.hom_ext_pullback_fst (yoneda.map iW) (NatTrans.ext (funext fun X =>
    ConcreteCategory.hom_ext _ _ fun r => ?_))
  have hfstU : (pullback.fst A.hom (yoneda.map iU)).app X
        (((Over.pullback (yoneda.map iU)).map
          (gluedRestrictLeftIsoSub hU hW hV φ hZ hVp).hom).left.app X r) =
      (gluedRestrictLeftHomSub hU hW hV φ jU).app X
        ((pullback.fst (pullback.snd (gluedOverToBase hU hW hV φ Z) (yoneda.map jU))
          (yoneda.map iU)).app X r) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app
      (Over.pullback_map_left_comp_fst (yoneda.map iU)
        (gluedRestrictLeftIsoSub hU hW hV φ hZ hVp).hom) X) r
  have hfstW : (pullback.fst Bb.hom (yoneda.map iW)).app X
        (((Over.pullback (yoneda.map iW)).map
            (gluedRestrictRightIsoSub hU hW hV φ hZ hVp).hom).left.app X
          ((Over.pullbackSquareObjIso (yoneda_map_comm hVp.w)
            (gluedOverSub hU hW hV φ Z)).hom.left.app X r)) =
      (gluedRestrictRightIsoSub hU hW hV φ hZ hVp).hom.left.app X
        ((pullback.fst (pullback.snd (gluedOverToBase hU hW hV φ Z) (yoneda.map jW))
            (yoneda.map iW)).app X
          ((Over.pullbackSquareObjIso (yoneda_map_comm hVp.w)
            (gluedOverSub hU hW hV φ Z)).hom.left.app X r)) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app
      (Over.pullback_map_left_comp_fst (yoneda.map iW)
        (gluedRestrictRightIsoSub hU hW hV φ hZ hVp).hom) X) _
  have hsqf : (pullback.fst (gluedOverToBase hU hW hV φ Z) (yoneda.map jW)).app X
        ((pullback.fst (pullback.snd (gluedOverToBase hU hW hV φ Z) (yoneda.map jW))
            (yoneda.map iW)).app X
          ((Over.pullbackSquareObjIso (yoneda_map_comm hVp.w)
            (gluedOverSub hU hW hV φ Z)).hom.left.app X r)) =
      (pullback.fst (gluedOverToBase hU hW hV φ Z) (yoneda.map jU)).app X
        ((pullback.fst (pullback.snd (gluedOverToBase hU hW hV φ Z) (yoneda.map jU))
          (yoneda.map iU)).app X r) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app
      (Over.pullbackSquareObjIso_hom_left_fst (yoneda_map_comm hVp.w)
        (gluedOverSub hU hW hV φ Z)) X) r
  have hright : (pullback.fst Bb.hom (yoneda.map iW)).app X
        (((Over.pullback (yoneda.map iW)).map
            (gluedRestrictRightIsoSub hU hW hV φ hZ hVp).hom).left.app X
          ((Over.pullbackSquareObjIso (yoneda_map_comm hVp.w)
            (gluedOverSub hU hW hV φ Z)).hom.left.app X r)) =
      Bb.left.map (prod.lift
          ((pullback.snd (pullback.snd (gluedOverToBase hU hW hV φ Z) (yoneda.map jU))
            (yoneda.map iU)).app X r ≫ iW) (𝟙 X.unop)).op
        (((pullback.fst (gluedOverToBase hU hW hV φ Z) (yoneda.map jU)).app X
          ((pullback.fst (pullback.snd (gluedOverToBase hU hW hV φ Z) (yoneda.map jU))
            (yoneda.map iU)).app X r)).1.1.2) := by
    rw [hfstW, gluedRestrictRightIsoSub_hom_left_app, hsqf]
    exact congrArg (fun q => Bb.left.map (prod.lift q (𝟙 X.unop)).op
      (((pullback.fst (gluedOverToBase hU hW hV φ Z) (yoneda.map jU)).app X
        ((pullback.fst (pullback.snd (gluedOverToBase hU hW hV φ Z) (yoneda.map jU))
          (yoneda.map iU)).app X r)).1.1.2)) (hW _ _)
  have hz : (pullback.fst A.hom (yoneda.map iU)).app X
        (((Over.pullback (yoneda.map iU)).map
          (gluedRestrictLeftIsoSub hU hW hV φ hZ hVp).hom).left.app X r) =
      A.left.map (prod.lift
          ((pullback.snd (pullback.snd (gluedOverToBase hU hW hV φ Z) (yoneda.map jU))
            (yoneda.map iU)).app X r ≫ iU) (𝟙 X.unop)).op
        (((pullback.fst (gluedOverToBase hU hW hV φ Z) (yoneda.map jU)).app X
          ((pullback.fst (pullback.snd (gluedOverToBase hU hW hV φ Z) (yoneda.map jU))
            (yoneda.map iU)).app X r)).1.1.1) := by
    rw [hfstU, gluedRestrictLeftHomSub_app_apply]
    exact congrArg (fun q => A.left.map (prod.lift q (𝟙 X.unop)).op
      (((pullback.fst (gluedOverToBase hU hW hV φ Z) (yoneda.map jU)).app X
        ((pullback.fst (pullback.snd (gluedOverToBase hU hW hV φ Z) (yoneda.map jU))
          (yoneda.map iU)).app X r)).1.1.1)) (hU _ _)
  exact (pullback_fst_app_hom_left hU hW hV φ
    ((pullback.snd (pullback.snd (gluedOverToBase hU hW hV φ Z) (yoneda.map jU))
      (yoneda.map iU)).app X r)
    (((pullback.fst (gluedOverToBase hU hW hV φ Z) (yoneda.map jU)).app X
      ((pullback.fst (pullback.snd (gluedOverToBase hU hW hV φ Z) (yoneda.map jU))
        (yoneda.map iU)).app X r)).1.1.1)
    (((pullback.fst (gluedOverToBase hU hW hV φ Z) (yoneda.map jU)).app X
      ((pullback.fst (pullback.snd (gluedOverToBase hU hW hV φ Z) (yoneda.map jU))
        (yoneda.map iU)).app X r)).1.1.2)
    (((pullback.fst (gluedOverToBase hU hW hV φ Z) (yoneda.map jU)).app X
      ((pullback.fst (pullback.snd (gluedOverToBase hU hW hV φ Z) (yoneda.map jU))
        (yoneda.map iU)).app X r)).1.2) _ hz).trans hright.symm

end Restrict

end CategoryTheory.SubterminalGlueing

namespace CategoryTheory

/-! ### Products over a subterminal object are fibre products -/

variable {C : Type u} [Category.{v} C]

/-- **Every morphism out of a subterminal object is a monomorphism**: two morphisms into a
subterminal object with a common source already agree, so nothing has to be cancelled. -/
theorem IsSubterminal.mono_from {X : C} (hX : IsSubterminal X) {T : C} (f : X ⟶ T) : Mono f :=
  ⟨fun _ _ _ => hX _ _⟩

/-- **Over a subterminal object a binary product is a fibre product.** The compatibility
condition defining the fibre product is automatic, there being at most one morphism to the
object. This generalises `CategoryTheory.IsTerminal.isPullback_prod`. -/
theorem IsSubterminal.isPullback_prod {T : C} (hT : IsSubterminal T) {X Y : C} (f : X ⟶ T)
    (g : Y ⟶ T) [HasBinaryProduct X Y] :
    IsPullback (prod.fst : X ⨯ Y ⟶ X) prod.snd f g :=
  IsPullback.of_isLimit (Limits.PullbackCone.IsLimit.mk (hT _ _)
    (fun s => prod.lift s.fst s.snd) (fun _ => by simp) (fun _ => by simp)
    (fun _ _ h₁ h₂ => prod.hom_ext (by simpa using h₁) (by simpa using h₂)))

/-- **Over a subterminal object a binary product is a fibre product**, as an isomorphism with
the chosen fibre product. This generalises
`CategoryTheory.prodIsoPullbackOfIsTerminal`. -/
noncomputable def prodIsoPullbackOfIsSubterminal {T : C} (hT : IsSubterminal T) {X Y : C}
    (f : X ⟶ T) (g : Y ⟶ T) [HasBinaryProduct X Y] [HasPullback g f] : X ⨯ Y ≅ pullback g f :=
  (hT.isPullback_prod f g).flip.isoPullback

namespace SubterminalGlueing

variable [HasBinaryProducts C] {U W V : C} {iU : V ⟶ U} {iW : V ⟶ W} (hU : IsSubterminal U)
  (hW : IsSubterminal W) (hV : IsSubterminal V)
  {A : Over (yoneda.obj U : Cᵒᵖ ⥤ Type v)} {Bb : Over (yoneda.obj W : Cᵒᵖ ⥤ Type v)}
  (φ : (Over.pullback (yoneda.map iU)).obj A ≅ (Over.pullback (yoneda.map iW)).obj Bb)
  {Z : C} (hZ : IsSubterminal Z)

include hZ in
/-- `CategoryTheory.SubterminalGlueing.gluedRestrictLeftIsoSub` read as a product: the
restriction of the glued presheaf to `U` is its product with the representable presheaf of `U`.
This is `CategoryTheory.SubterminalGlueing.prodGluedRestrictLeftIso` over a subterminal base,
the identification of the product with the fibre product being
`CategoryTheory.prodIsoPullbackOfIsSubterminal`. -/
noncomputable def prodGluedRestrictLeftIsoSub {jU : U ⟶ Z} {jW : W ⟶ Z}
    (hVp : IsPullback iU iW jU jW) :
    (yoneda.obj U : Cᵒᵖ ⥤ Type v) ⨯ gluedPresheafOver hU hW hV φ Z ≅ A.left :=
  prodIsoPullbackOfIsSubterminal hZ.yonedaObj (yoneda.map jU) (gluedOverToBase hU hW hV φ Z) ≪≫
    (Over.forget (yoneda.obj U)).mapIso (gluedRestrictLeftIsoSub hU hW hV φ hZ hVp)

include hZ in
/-- `CategoryTheory.SubterminalGlueing.gluedRestrictRightIsoSub` read as a product. -/
noncomputable def prodGluedRestrictRightIsoSub {jU : U ⟶ Z} {jW : W ⟶ Z}
    (hVp : IsPullback iU iW jU jW) :
    (yoneda.obj W : Cᵒᵖ ⥤ Type v) ⨯ gluedPresheafOver hU hW hV φ Z ≅ Bb.left :=
  prodIsoPullbackOfIsSubterminal hZ.yonedaObj (yoneda.map jW) (gluedOverToBase hU hW hV φ Z) ≪≫
    (Over.forget (yoneda.obj W)).mapIso (gluedRestrictRightIsoSub hU hW hV φ hZ hVp)

end SubterminalGlueing

end CategoryTheory

namespace AlgebraicGeometry.FinitePresentationSpacesOver

open CategoryTheory.SubterminalGlueing

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Z U W V : BigFppfOver B S hS} (hZ : IsSubterminal Z) (hU : IsSubterminal U)
  (hW : IsSubterminal W) {jU : U ⟶ Z} {jW : W ⟶ Z} {iU : V ⟶ U} {iW : V ⟶ W}
  (hV : IsPullback iU iW jU jW)
  {A : Over (yoneda.obj U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
  {Bb : Over (yoneda.obj W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
  (φ : (Over.pullback (yoneda.map iU)).obj A ≅ (Over.pullback (yoneda.map iW)).obj Bb)

/-! ### The glued space is an algebraic space of finite presentation over the base -/

omit hU hW hV in
/-- **An fppf sheaf lying over a subterminal base covered by two opens, whose restrictions to
the two opens are algebraic spaces, is an algebraic space.**

This is Stacks 02WR applied to the two projections `yoneda.obj U ⨯ F ⟶ F` and
`yoneda.obj W ⨯ F ⟶ F`. They are representable by open immersions because `U` and `W` are open
in the base scheme, and together they are locally surjective onto `F` — not because `U` and `W`
cover the base scheme, which they need not, but because a *section* of `F` over an object `X`
carries `X` to `Z` through `ζ`, and `U`, `W` cover `Z`.

This replaces `AlgebraicGeometry.isAlgebraicSpace_iff_isAlgebraicSpace_relocalizeRestrict_pair`,
which detects algebraicity on an open covering of the base *scheme* and so does not apply when
`Z` is a proper open of it. -/
theorem isAlgebraicSpace_of_prod_pair_of_hom
    (hcov : Sieve.ofTwoArrows jU jW ∈ BigFppfOver.topology B S hS Z)
    (hUopen : IsOpenImmersion (B.inclusion.map U.hom))
    (hWopen : IsOpenImmersion (B.inclusion.map W.hom))
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) (ζ : F ⟶ yoneda.obj Z)
    (hFU : IsAlgebraicSpace B S hS (yoneda.obj U ⨯ F))
    (hFW : IsAlgebraicSpace B S hS (yoneda.obj W ⨯ F)) :
    IsAlgebraicSpace B S hS F := by
  classical
  have _ : EssentiallySmall.{u} (BigFppfOver B S hS) := essentiallySmall_bigFppfOver B S hS
  let _ : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} (BigFppfOver.topology B S hS) (Type u)
  have _ : HasFiniteCoproducts (Sheaf (BigFppfOver.topology B S hS) (Type u)) := inferInstance
  have _ : HasColimitsOfShape (Discrete (ULift.{u + 1} Bool))
      (Sheaf (BigFppfOver.topology B S hS) (Type u)) :=
    CategoryTheory.Limits.hasColimitsOfShape_discrete _ (ULift.{u + 1} Bool)
  -- the two opens covering `Z`, as a two-member family of objects of the site
  let E : PreZeroHypercover.{u + 1} (Over.mk (𝟙 (B.obj hS)) : BigFppfOver B S hS) :=
    ⟨ULift.{u + 1} Bool,
      fun i => Bool.rec (motive := fun _ => BigFppfOver B S hS) W U i.down,
      fun i => Over.mkIdTerminal.from
        (Bool.rec (motive := fun _ => BigFppfOver B S hS) W U i.down)⟩
  have hEf : ∀ i, (BigFppfOver.toScheme B S hS).map (E.f i) =
      B.inclusion.map (E.X i).hom := fun i =>
    toScheme_map_mkIdTerminal_from B S hS (E.X i)
  have hEopen : ∀ i, IsOpenImmersion (B.inclusion.map (E.X i).hom) := by
    rintro ⟨b⟩; cases b; exacts [hWopen, hUopen]
  have hFi : ∀ i, IsAlgebraicSpace B S hS (yoneda.obj (E.X i) ⨯ F) := by
    rintro ⟨b⟩; cases b; exacts [hFW, hFU]
  let Fs : ULift.{u + 1} Bool → Sheaf (BigFppfOver.topology B S hS) (Type u) := fun i =>
    ⟨yoneda.obj (E.X i) ⨯ F, (hFi i).isSheaf⟩
  have hls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Space.coverCoproductProj hF E hFi (Sigma.ι Fs) (coproductIsCoproduct Fs)).hom := by
    constructor
    intro X x
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      ((BigFppfOver.topology B S hS).ofTwoArrows_prod_snd_mem_of_hom hcov
        (ζ.app (op X) x : X ⟶ Z))
    rintro Y g hg
    obtain ⟨(_ | _), q, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
    · refine ⟨yonedaEquiv (prod.lift (yoneda.map (q ≫ (prod.fst : U ⨯ X ⟶ U)))
        (yonedaEquiv.symm (F.map g.op x)) ≫ (Sigma.ι Fs ⟨true⟩).hom), ?_⟩
      rw [← yonedaEquiv_comp, Category.assoc,
        Space.coverCoproductProj_ι hF E hFi (Sigma.ι Fs) (coproductIsCoproduct Fs) ⟨true⟩,
        prod.lift_snd, Equiv.apply_symm_apply]
    · refine ⟨yonedaEquiv (prod.lift (yoneda.map (q ≫ (prod.fst : W ⨯ X ⟶ W)))
        (yonedaEquiv.symm (F.map g.op x)) ≫ (Sigma.ι Fs ⟨false⟩).hom), ?_⟩
      rw [← yonedaEquiv_comp, Category.assoc,
        Space.coverCoproductProj_ι hF E hFi (Sigma.ι Fs) (coproductIsCoproduct Fs) ⟨false⟩,
        prod.lift_snd, Equiv.apply_symm_apply]
  refine AlgebraicGeometry.isAlgebraicSpace_of_open_cover B S hS F hF (ULift.{u + 1} Bool) Fs hFi
    (∐ Fs) (Sigma.ι Fs) (coproductIsCoproduct Fs)
    (Space.coverCoproductProj hF E hFi (Sigma.ι Fs) (coproductIsCoproduct Fs)).hom
    (fun i => ?_) hls
    (Space.isAlgebraicSpace_finiteCoproduct B S hS _ hFi (∐ Fs) (Sigma.ι Fs)
      (coproductIsCoproduct Fs))
  rw [Space.coverCoproductProj_ι hF E hFi (Sigma.ι Fs) (coproductIsCoproduct Fs) i]
  exact Space.presheaf_prod_snd (P := @AlgebraicGeometry.IsOpenImmersion.{u}) inferInstance
    (E.X i) F ((hEf i) ▸ hEopen i)

include hZ hU hW hV in
/-- **The presheaf glued from two algebraic spaces over a subterminal base covered by two opens
is an algebraic space over `S`.**

This is `AlgebraicGeometry.FinitePresentationSpacesOver.isAlgebraicSpace_gluedPresheaf` over a
base which need not be terminal, and the hypothesis that `U` and `W` cover the *base scheme* is
dropped: at a stage of Stacks 0E91 they cover only `Z`. The two restrictions of the glued
presheaf are the two presheaves glued, by
`CategoryTheory.SubterminalGlueing.prodGluedRestrictLeftIsoSub` and
`prodGluedRestrictRightIsoSub`, so
`AlgebraicGeometry.FinitePresentationSpacesOver.isAlgebraicSpace_of_prod_pair_of_hom`
applies. -/
theorem isAlgebraicSpace_gluedPresheafOver
    (hcov : Sieve.ofTwoArrows jU jW ∈ BigFppfOver.topology B S hS Z)
    (hUopen : IsOpenImmersion (B.inclusion.map U.hom))
    (hWopen : IsOpenImmersion (B.inclusion.map W.hom))
    (hA : IsAlgebraicSpace B S hS A.left) (hBb : IsAlgebraicSpace B S hS Bb.left) :
    IsAlgebraicSpace B S hS
      (gluedPresheafOver hU hW (hV.isSubterminal hU hW) φ Z) :=
  isAlgebraicSpace_of_prod_pair_of_hom B S hS hcov hUopen hWopen _
    (isSheaf_gluedPresheafOver hU hW (hV.isSubterminal hU hW) φ Z
      (BigFppfOver.topology B S hS) hA.isSheaf hBb.isSheaf
      (isAlgebraicSpace_yoneda B S hS Z).isSheaf)
    (gluedOverToBase hU hW (hV.isSubterminal hU hW) φ Z)
    (hA.of_iso (prodGluedRestrictLeftIsoSub hU hW (hV.isSubterminal hU hW) φ hZ hV).symm)
    (hBb.of_iso (prodGluedRestrictRightIsoSub hU hW (hV.isSubterminal hU hW) φ hZ hV).symm)

include hZ hU hW hV in
/-- **The structure morphism of the glued presheaf over a subterminal base is of finite
presentation.** Its base changes over the two members of the Zariski covering of `yoneda.obj Z`
given by `U` and `W` are the structure morphisms of the two presheaves glued, by
`CategoryTheory.SubterminalGlueing.isPullback_gluedRestrictLeftSub` and
`isPullback_gluedRestrictRightSub`, so finite presentation descends by
`AlgebraicGeometry.Space.isFinitePresentation_iff_forall_zariskiCover`.

This is `AlgebraicGeometry.FinitePresentationSpacesOver.isFinitePresentation_gluedOver` over a
base which need not be terminal. Unlike algebraicity, this step was never about the base scheme:
the Zariski covering is of `yoneda.obj Z`, and `U`, `W` cover `Z` by hypothesis. -/
theorem isFinitePresentation_gluedOverSub
    (hjU : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map jU))
    (hjW : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map jW))
    (hsurj : ∀ x : (BigFppfOver.toScheme B S hS).obj Z,
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map jU) ∨
        x ∈ Set.range ((BigFppfOver.toScheme B S hS).map jW))
    (hUopen : IsOpenImmersion (B.inclusion.map U.hom))
    (hWopen : IsOpenImmersion (B.inclusion.map W.hom))
    (hA : IsAlgebraicSpace B S hS A.left) (hBb : IsAlgebraicSpace B S hS Bb.left)
    (hAfp : Space.IsFinitePresentation B S hS A.hom)
    (hBfp : Space.IsFinitePresentation B S hS Bb.hom) :
    Space.IsFinitePresentation B S hS
      (gluedOverSub hU hW (hV.isSubterminal hU hW) φ Z).hom := by
  have hcov := ofTwoArrows_mem_topology B S hS jU jW hjU hjW hsurj
  have : Mono (yoneda.map jU) := hU.yonedaObj.mono_from _
  have : Mono (yoneda.map jW) := hW.yonedaObj.mono_from _
  refine (Space.isFinitePresentation_iff_forall_zariskiCover B S hS
    (isAlgebraicSpace_gluedPresheafOver B S hS hZ hU hW hV φ hcov hUopen hWopen hA hBb)
    (isAlgebraicSpace_yoneda B S hS Z) _
    (Space.isZariskiCover_rangePair B S hS hjU hjW hcov)).2 ?_
  rintro ⟨_ | _⟩
  · rw [Space.rangePair_false]
    exact Space.isFinitePresentation_pullback_snd_range B S hS
      (isPullback_gluedRestrictRightSub hU hW (hV.isSubterminal hU hW) φ hZ hV) hBfp
  · rw [Space.rangePair_true]
    exact Space.isFinitePresentation_pullback_snd_range B S hS
      (isPullback_gluedRestrictLeftSub hU hW (hV.isSubterminal hU hW) φ hZ hV) hAfp

/-! ### Subterminality of an open of the base scheme -/

/-- **An object of the big fppf category over `S` whose structure morphism is a monomorphism of
schemes is subterminal in that category.** Two morphisms into it from a common source have the
same composite with its structure morphism, namely the structure morphism of the source, so
their images under the faithful functor to schemes agree.

This is what makes the subterminal hypotheses of
`AlgebraicGeometry.FinitePresentationSpacesOver.isEquivalence_glueingFunctor_of_isSubterminal`
available at a stage of Stacks 0E91: a stage is an open of `S`, and the structure morphism of an
open is an open immersion, hence a monomorphism. -/
theorem isSubterminal_of_mono_inclusion_map_hom (T : BigFppfOver B S hS)
    (h : Mono (B.inclusion.map T.hom)) : IsSubterminal T := by
  have hmap : Mono (Over.mkIdTerminal.from T) := by
    refine (BigFppfOver.toScheme B S hS).mono_of_mono_map
      (f := Over.mkIdTerminal.from T) ?_
    rw [toScheme_map_mkIdTerminal_from]
    exact h
  exact (isSubterminal_of_isTerminal Over.mkIdTerminal).of_mono (Over.mkIdTerminal.from T)

/-! ### Essential surjectivity and the equivalence -/

section EssSurj

variable (hjU : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map jU))
  (hjW : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map jW))
  (hsurj : ∀ x : (BigFppfOver.toScheme B S hS).obj Z,
    x ∈ Set.range ((BigFppfOver.toScheme B S hS).map jU) ∨
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map jW))
  (hUopen : IsOpenImmersion (B.inclusion.map U.hom))
  (hWopen : IsOpenImmersion (B.inclusion.map W.hom))

include hZ hU hW hV hjU hjW hsurj hUopen hWopen in
/-- **The algebraic space of finite presentation over a subterminal base glued from a glueing
datum.** This is the object `AlgebraicGeometry.FinitePresentationSpacesOver.glueingQuasiInverse`
produces over a terminal base; only its value at a single datum is needed for essential
surjectivity, so no functoriality is proved. -/
noncomputable def gluedFinitePresentationSpaceOver
    (T : IsoComma (baseChange B S hS iU) (baseChange B S hS iW)) :
    FinitePresentationSpacesOver B S hS Z :=
  ⟨gluedOverSub hU hW (hV.isSubterminal hU hW) (isoCommaIso B S hS T) Z,
    isAlgebraicSpace_gluedPresheafOver B S hS hZ hU hW hV (isoCommaIso B S hS T)
      (ofTwoArrows_mem_topology B S hS jU jW hjU hjW hsurj) hUopen hWopen
      T.obj.left.property.1 T.obj.right.property.1,
    isFinitePresentation_gluedOverSub B S hS hZ hU hW hV (isoCommaIso B S hS T) hjU hjW hsurj
      hUopen hWopen T.obj.left.property.1 T.obj.right.property.1 T.obj.left.property.2
      T.obj.right.property.2⟩

include hZ hU hW hV hjU hjW hsurj hUopen hWopen in
/-- The compatibility over `V` of the two restriction comparisons of the glued space, read in
the slice of presheaves on the big fppf site. This is
`AlgebraicGeometry.FinitePresentationSpacesOver.counitSquare` over a subterminal base. -/
theorem counitSquareSub (T : IsoComma (baseChange B S hS iU) (baseChange B S hS iW)) :
    (Over.pullback (yoneda.map iU)).map (gluedRestrictLeftIsoSub hU hW
          (hV.isSubterminal hU hW) (isoCommaIso B S hS T) hZ hV).hom ≫
        (isoCommaIso B S hS T).hom =
      (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS V)).map
          ((baseChangeSquareIso B S hS hV.w).hom.app
            (gluedFinitePresentationSpaceOver B S hS hZ hU hW hV hjU hjW hsurj hUopen hWopen
              T)) ≫
        (Over.pullback (yoneda.map iW)).map (gluedRestrictRightIsoSub hU hW
          (hV.isSubterminal hU hW) (isoCommaIso B S hS T) hZ hV).hom := by
  rw [baseChangeSquareIso_hom_app_left]
  exact gluedRestrictSub_comm hU hW (hV.isSubterminal hU hW) (isoCommaIso B S hS T) hZ hV

include hZ hU hW hV hjU hjW hsurj hUopen hWopen in
/-- **The two restrictions of the glued space are the two spaces glued.** This is the counit of
the equivalence of Stacks 0E8Z at a single glueing datum, over a subterminal base. -/
noncomputable def counitObjIsoSub
    (T : IsoComma (baseChange B S hS iU) (baseChange B S hS iW)) :
    (glueingFunctor B S hS hV.w).obj
        (gluedFinitePresentationSpaceOver B S hS hZ hU hW hV hjU hjW hsurj hUopen hWopen T) ≅
      T :=
  ObjectProperty.isoMk _ (Comma.isoMk
    (ObjectProperty.isoMk _ (gluedRestrictLeftIsoSub hU hW (hV.isSubterminal hU hW)
      (isoCommaIso B S hS T) hZ hV))
    (ObjectProperty.isoMk _ (gluedRestrictRightIsoSub hU hW (hV.isSubterminal hU hW)
      (isoCommaIso B S hS T) hZ hV))
    (ObjectProperty.hom_ext _
      (counitSquareSub B S hS hZ hU hW hV hjU hjW hsurj hUopen hWopen T)))

include hZ hU hW hV hjU hjW hsurj hUopen hWopen in
/-- **The comparison functor into the `2`-fibre product is essentially surjective over a
subterminal base**: every glueing datum is, up to isomorphism, the datum of restrictions of the
space glued from it. This is
`AlgebraicGeometry.FinitePresentationSpacesOver.essSurj_glueingFunctor` over a base which need
not be terminal. -/
theorem essSurj_glueingFunctor_of_isSubterminal :
    Functor.EssSurj (glueingFunctor B S hS hV.w) where
  mem_essImage T :=
    ⟨gluedFinitePresentationSpaceOver B S hS hZ hU hW hV hjU hjW hsurj hUopen hWopen T,
      ⟨counitObjIsoSub B S hS hZ hU hW hV hjU hjW hsurj hUopen hWopen T⟩⟩

include hZ hU hW hV hjU hjW hsurj hUopen hWopen in
/-- **Stacks 0E8Z over a subterminal base.** Let `Z` be a subterminal object of the big fppf
site of `S` — so that `Z ⟶ S` is a monomorphism, for instance an open subscheme of `S` — and let
`jU : U ⟶ Z`, `jW : W ⟶ Z` be open immersions whose images cover `Z`, with intersection `V`.
Then base change is an equivalence from the algebraic spaces of finite presentation over `Z` to
the `2`-fibre product `FP_U ×_{FP_V} FP_W`.

This is `AlgebraicGeometry.FinitePresentationSpacesOver.isEquivalence_glueingFunctor` with the
hypothesis that `Z` is *terminal* in the site weakened to subterminal, which is what Stacks 0E91
needs at a stage `Z i = U ∪ W i`: such a stage is a proper open of the base scheme, so terminal
in no site containing more. The hypothesis that `U` and `W` cover the base *scheme* is dropped —
it is false at a stage — and is replaced by their covering `Z`; the hypotheses `hUopen` and
`hWopen`, that `U` and `W` are open in the base scheme, remain, and are what makes the two
projections out of the glued space open immersions.

Faithfulness is
`AlgebraicGeometry.FinitePresentationSpacesOver.faithful_glueingFunctor_of_isSubterminal`,
fullness is `full_glueingFunctor_of_isSubterminal`, and essential surjectivity is
`essSurj_glueingFunctor_of_isSubterminal`. -/
theorem isEquivalence_glueingFunctor_of_isSubterminal :
    Functor.IsEquivalence (glueingFunctor B S hS hV.w) := by
  have hcov := ofTwoArrows_mem_topology B S hS jU jW hjU hjW hsurj
  have := full_glueingFunctor_of_isSubterminal B S hS hZ hU hW hV hcov
  have := faithful_glueingFunctor_of_isSubterminal B S hS hZ hU hW hV hcov
  have := essSurj_glueingFunctor_of_isSubterminal B S hS hZ hU hW hV hjU hjW hsurj hUopen
    hWopen
  exact ⟨inferInstance, inferInstance, inferInstance⟩

include hV hjU hjW hsurj hUopen hWopen in
/-- **Stacks 0E8Z over a base which is an open of the base scheme.** This is
`AlgebraicGeometry.FinitePresentationSpacesOver.isEquivalence_glueingFunctor_of_isSubterminal`
with its three subterminality hypotheses replaced by the single point-set hypothesis that the
structure morphism of the base is a monomorphism of schemes: subterminality of `U` and of `W`
already follows from `hUopen` and `hWopen`, which the theorem assumes anyway, by
`AlgebraicGeometry.FinitePresentationSpacesOver.isSubterminal_of_mono_inclusion_map_hom`.

This is the form in which the hypothesis
`hstage : ∀ i, (glueingFunctor B S hS (hsqW i).w).IsEquivalence` of
`AlgebraicGeometry.FinitePresentationSpacesOver.isGlueingColimitEquivalence_of_colimit` can be
discharged at a stage `Z i = U ∪ W i` of Stacks 0E91: every hypothesis here is a statement about
open immersions of schemes, and none mentions the ambient category. -/
theorem isEquivalence_glueingFunctor_of_mono_hom (hZmono : Mono (B.inclusion.map Z.hom)) :
    (glueingFunctor B S hS hV.w).IsEquivalence := by
  have hUs := isSubterminal_of_mono_inclusion_map_hom B S hS U inferInstance
  have hWs := isSubterminal_of_mono_inclusion_map_hom B S hS W inferInstance
  exact isEquivalence_glueingFunctor_of_isSubterminal B S hS
    (isSubterminal_of_mono_inclusion_map_hom B S hS Z hZmono) hUs hWs hV hjU hjW hsurj
    hUopen hWopen

/-- **The terminal case is a special case**: over a terminal base the hypotheses of
`AlgebraicGeometry.FinitePresentationSpacesOver.isEquivalence_glueingFunctor_of_isSubterminal`
are implied by those of
`AlgebraicGeometry.FinitePresentationSpacesOver.isEquivalence_glueingFunctor`, whose covering
hypothesis `hScov` on the base scheme is not even needed. So the generalisation weakens
nothing. -/
example (hZt : IsTerminal Z) [Mono jU] [Mono jW]
    (hjU : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map jU))
    (hjW : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map jW))
    (hsurj : ∀ x : (BigFppfOver.toScheme B S hS).obj Z,
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map jU) ∨
        x ∈ Set.range ((BigFppfOver.toScheme B S hS).map jW))
    (hUopen : IsOpenImmersion (B.inclusion.map U.hom))
    (hWopen : IsOpenImmersion (B.inclusion.map W.hom)) :
    (glueingFunctor B S hS hV.w).IsEquivalence :=
  isEquivalence_glueingFunctor_of_isSubterminal B S hS (isSubterminal_of_isTerminal hZt)
    (isSubterminal_of_mono_isTerminal hZt jU) (isSubterminal_of_mono_isTerminal hZt jW) hV
    hjU hjW hsurj hUopen hWopen

end EssSurj

end AlgebraicGeometry.FinitePresentationSpacesOver

end
