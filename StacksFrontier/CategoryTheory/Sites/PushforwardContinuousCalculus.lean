module

public import Mathlib.CategoryTheory.Sites.Continuous

/-!
# The calculus of the comparison isomorphisms of restriction along a functor of sites

Restriction of sheaves along a continuous functor of sites,
`CategoryTheory.Functor.sheafPushforwardContinuous`, is contravariantly functorial in the
functor of sites: an isomorphism `e : F ≅ F'` of continuous functors induces
`CategoryTheory.Functor.sheafPushforwardContinuousIso e`, and composition of functors of sites
becomes composition of restrictions *strictly*, by
`CategoryTheory.Functor.sheafPushforwardContinuousComp`, which is
`CategoryTheory.Iso.refl`.

The induced isomorphism is itself functorial in `e` and compatible with whiskering, and each
`CategoryTheory.Functor.sheafPushforwardContinuousComp'` is the isomorphism induced by the
isomorphism of functors of sites it is built from.

## Main results

* `CategoryTheory.Functor.sheafPushforwardContinuousIso_refl` and
  `CategoryTheory.Functor.sheafPushforwardContinuousIso_trans`: the induced isomorphism of
  restriction functors takes the identity to the identity and a composite to the composite.
* `CategoryTheory.Functor.whiskerLeft_sheafPushforwardContinuousIso_hom` and
  `CategoryTheory.Functor.whiskerRight_sheafPushforwardContinuousIso_hom`: whiskering an
  induced isomorphism with a restriction functor is the isomorphism induced by whiskering the
  functors of sites.
* `CategoryTheory.Functor.sheafPushforwardContinuousComp'_hom_eq`: a
  `CategoryTheory.Functor.sheafPushforwardContinuousComp'` is the induced isomorphism of the
  isomorphism of functors of sites it is built from.

## Implementation notes

The continuity of a composite of functors of sites is taken as an instance argument rather than
produced by `CategoryTheory.Functor.isContinuous_comp` inside the statement, so that these lemmas
apply whatever the instance's proof.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ v₃ v' u₁ u₂ u₃ u'

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] (A : Type u') [Category.{v'} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)

section

variable {F F' F'' : C ⥤ D} [instF : F.IsContinuous J K] [instF' : F'.IsContinuous J K]
  [instF'' : F''.IsContinuous J K]

/-- Restriction along a functor of sites takes the identity isomorphism of functors of sites to
the identity isomorphism of restriction functors. -/
theorem sheafPushforwardContinuousIso_refl :
    sheafPushforwardContinuousIso (Iso.refl F) A J K = Iso.refl _ := by
  ext M : 3
  ext X
  simp
  rfl

/-- The presheaf component of the isomorphism of restriction functors induced by an isomorphism
of functors of sites. -/
theorem sheafPushforwardContinuousIso_hom_app_hom_app (e : F ≅ F') (M : Sheaf K A) (Y : Cᵒᵖ) :
    ((sheafPushforwardContinuousIso e A J K).hom.app M).hom.app Y =
      M.obj.map (e.inv.app (Opposite.unop Y)).op :=
  rfl

/-- The presheaf component of the inverse of the isomorphism of restriction functors induced by
an isomorphism of functors of sites. -/
theorem sheafPushforwardContinuousIso_inv_app_hom_app (e : F ≅ F') (M : Sheaf K A) (Y : Cᵒᵖ) :
    ((sheafPushforwardContinuousIso e A J K).inv.app M).hom.app Y =
      M.obj.map (e.hom.app (Opposite.unop Y)).op :=
  rfl

/-- Restriction along a functor of sites takes the inverse of an isomorphism of functors of
sites to the inverse of the induced isomorphism. -/
theorem sheafPushforwardContinuousIso_symm (e : F ≅ F') :
    (sheafPushforwardContinuousIso e A J K).symm = sheafPushforwardContinuousIso e.symm A J K :=
  rfl

/-- Restriction along a functor of sites takes a composite of isomorphisms of functors of sites
to the composite of the induced isomorphisms. -/
theorem sheafPushforwardContinuousIso_trans (e : F ≅ F') (e' : F' ≅ F'') :
    sheafPushforwardContinuousIso (e ≪≫ e') A J K =
      sheafPushforwardContinuousIso e A J K ≪≫ sheafPushforwardContinuousIso e' A J K := by
  ext M : 3
  ext X
  simp
  rfl

end

section

variable {F F' : C ⥤ D} [instF : F.IsContinuous J K] [instF' : F'.IsContinuous J K] (G : D ⥤ E)
  [instG : G.IsContinuous K L] [instFG : (F ⋙ G).IsContinuous J L]
  [instF'G : (F' ⋙ G).IsContinuous J L]

/-- Whiskering an induced isomorphism of restriction functors on the left by a restriction
functor is the isomorphism induced by whiskering the functors of sites on the right. -/
theorem whiskerLeft_sheafPushforwardContinuousIso_hom (e : F ≅ F') :
    Functor.whiskerLeft (sheafPushforwardContinuous G A K L)
        (sheafPushforwardContinuousIso e A J K).hom =
      (sheafPushforwardContinuousIso (isoWhiskerRight e G) A J L).hom := by
  ext M : 3
  ext X
  rfl

end

section

variable (F : C ⥤ D) [instF : F.IsContinuous J K] {G G' : D ⥤ E} [instG : G.IsContinuous K L]
  [instG' : G'.IsContinuous K L] [instFG : (F ⋙ G).IsContinuous J L]
  [instFG' : (F ⋙ G').IsContinuous J L]

/-- Whiskering an induced isomorphism of restriction functors on the right by a restriction
functor is the isomorphism induced by whiskering the functors of sites on the left. -/
theorem whiskerRight_sheafPushforwardContinuousIso_hom (e : G ≅ G') :
    Functor.whiskerRight (sheafPushforwardContinuousIso e A K L).hom
        (sheafPushforwardContinuous F A J K) =
      (sheafPushforwardContinuousIso (isoWhiskerLeft F e) A J L).hom := by
  ext M : 3
  ext X
  rfl

end

section

variable {F : C ⥤ D} {G : D ⥤ E} {FG : C ⥤ E} [instF : F.IsContinuous J K]
  [instG : G.IsContinuous K L] [instFG : FG.IsContinuous J L]
  [instComp : (F ⋙ G).IsContinuous J L]

/-- A `CategoryTheory.Functor.sheafPushforwardContinuousComp'` is the isomorphism of restriction
functors induced by the isomorphism of functors of sites it is built from. -/
theorem sheafPushforwardContinuousComp'_hom_eq (e : F ⋙ G ≅ FG) :
    (sheafPushforwardContinuousComp' e A J K L).hom =
      (sheafPushforwardContinuousIso e A J L).hom :=
  Category.id_comp _

/-- The inverse half of `CategoryTheory.Functor.sheafPushforwardContinuousComp'_hom_eq`. -/
theorem sheafPushforwardContinuousComp'_inv_eq (e : F ⋙ G ≅ FG) :
    (sheafPushforwardContinuousComp' e A J K L).inv =
      (sheafPushforwardContinuousIso e A J L).inv :=
  Category.comp_id _

end

section

variable (F : C ⥤ D) (G : D ⥤ E) [instF : F.IsContinuous J K] [instG : G.IsContinuous K L]
  [instComp : (F ⋙ G).IsContinuous J L]

/-- The `CategoryTheory.Functor.sheafPushforwardContinuousComp'` of the identity isomorphism of
`F ⋙ G` is the identity. -/
theorem sheafPushforwardContinuousComp'_refl_hom :
    (sheafPushforwardContinuousComp' (Iso.refl (F ⋙ G)) A J K L).hom = 𝟙 _ := by
  rw [sheafPushforwardContinuousComp'_hom_eq, sheafPushforwardContinuousIso_refl, Iso.refl_hom]
  rfl

/-- The inverse half of `CategoryTheory.Functor.sheafPushforwardContinuousComp'_refl_hom`. -/
theorem sheafPushforwardContinuousComp'_refl_inv :
    (sheafPushforwardContinuousComp' (Iso.refl (F ⋙ G)) A J K L).inv = 𝟙 _ := by
  rw [sheafPushforwardContinuousComp'_inv_eq, sheafPushforwardContinuousIso_refl, Iso.refl_inv]

end

end CategoryTheory.Functor

end
