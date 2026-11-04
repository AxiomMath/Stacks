module

public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Higher direct images along a cocontinuous functor of sites are sheafified derived presheaves

Let `F : C ⥤ D` be a cocontinuous functor of sites. The direct image `F_*` of abelian sheaves
along `F` is right adjoint to restriction, so it is additive and has right derived functors.
Its composite with the inclusion of sheaves into presheaves is a right Kan extension, so the
direct image can also be taken at the presheaf level, where it retains its restriction maps,
and derived there. This file proves that the `n`-th higher direct image is the sheafification
of that derived presheaf:

`(F_*).rightDerived n ≅ derivedPresheafDirectImage J F n ⋙ presheafToSheaf K`.

Both sides are computed from one injective resolution of the coefficient sheaf. The comparison
is the identification of `F_*` with the presheaf direct image followed by sheafification,
together with `CategoryTheory.Functor.rightDerivedCompIso`: an exact functor may be pulled out
of a right derived functor.

## Main definitions

* `CategoryTheory.Functor.derivedPresheafDirectImage`: the right derived presheaf direct image
  along a functor of sites, a functor from abelian sheaves on the source site to abelian
  presheaves on the target category.

## Main results

* `CategoryTheory.Functor.sheafPushforwardCocontinuous_additive`: the direct image of abelian
  sheaves along a cocontinuous functor of sites is additive.
* `CategoryTheory.Functor.presheafDirectImageCompSheafifyIso`: the presheaf direct image
  followed by sheafification is the direct image of sheaves.
* `CategoryTheory.Functor.rightDerivedSheafPushforwardCocontinuousIso`: the sheafification
  formula for higher direct images.

## Implementation notes

The coefficient universe is `max v₁ v₂ w₁ w₂ a` with `a` free. That shape is load-bearing and
not a convenience: it is what makes the right Kan extension along the opposite functor exist.
Because `a` occurs only inside that `max`, it is not determined by the explicit arguments, so
applications must write the universe list out.

Enough injectives for the category of abelian sheaves on the source site is a hypothesis rather
than an instance, because in the intended applications it is obtained from essential smallness
of the site. Only the source of a right derived functor needs enough injectives, so nothing is
required of the presheaf category of the target.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

namespace CategoryTheory.Functor

universe v₁ v₂ w₁ w₂ a

variable {C : Type v₁} [Category.{w₁} C] {D : Type v₂} [Category.{w₂} D]

/-- **The right derived presheaf direct image along a functor of sites.** The direct image of a
sheaf is first taken as a presheaf, by right Kan extension along `h`, so that the restriction
maps of the result are part of the data; the right derived functors of that composite are taken
in the category of presheaves.

The coefficient universe `max v₁ v₂ w₁ w₂ a` with `a` free is load-bearing rather than
cosmetic: it is what makes the right Kan extension along `h.op` exist. Because `a` occurs only
inside that `max`, it is not determined by the explicit arguments, so applications must write
the universe list out. -/
public noncomputable def derivedPresheafDirectImage (J : GrothendieckTopology C) (h : C ⥤ D)
    [HasSheafify J AddCommGrpCat.{max v₁ v₂ w₁ w₂ a}]
    [EnoughInjectives (Sheaf J AddCommGrpCat.{max v₁ v₂ w₁ w₂ a})] (n : ℕ) :
    Sheaf J AddCommGrpCat.{max v₁ v₂ w₁ w₂ a} ⥤
      (Dᵒᵖ ⥤ AddCommGrpCat.{max v₁ v₂ w₁ w₂ a}) :=
  haveI := (sheafificationAdjunction J AddCommGrpCat.{max v₁ v₂ w₁ w₂ a}).right_adjoint_additive
  haveI := (h.op.ranAdjunction AddCommGrpCat.{max v₁ v₂ w₁ w₂ a}).right_adjoint_additive
  (sheafToPresheaf J AddCommGrpCat.{max v₁ v₂ w₁ w₂ a} ⋙ h.op.ran).rightDerived n

/-- The defining equation of `derivedPresheafDirectImage`, as a named constant: the two
`Additive` instances it supplies are propositions, so the two spellings agree. -/
public theorem derivedPresheafDirectImage_eq (J : GrothendieckTopology C) (h : C ⥤ D)
    [HasSheafify J AddCommGrpCat.{max v₁ v₂ w₁ w₂ a}]
    [EnoughInjectives (Sheaf J AddCommGrpCat.{max v₁ v₂ w₁ w₂ a})] (n : ℕ)
    [(sheafToPresheaf J AddCommGrpCat.{max v₁ v₂ w₁ w₂ a} ⋙ h.op.ran).Additive] :
    derivedPresheafDirectImage.{v₁, v₂, w₁, w₂, a} J h n =
      (sheafToPresheaf J AddCommGrpCat.{max v₁ v₂ w₁ w₂ a} ⋙ h.op.ran).rightDerived n :=
  rfl

section

variable (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsCocontinuous J K]
  [HasSheafify J AddCommGrpCat.{max v₁ v₂ w₁ w₂ a}]
  [HasSheafify K AddCommGrpCat.{max v₁ v₂ w₁ w₂ a}]
  [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{max v₁ v₂ w₁ w₂ a}, F.op.HasPointwiseRightKanExtension P]

/-- **The direct image of abelian sheaves along a cocontinuous functor of sites is additive**, so
it has right derived functors. It is a right adjoint, and its composite with the inclusion of
sheaves into presheaves is a right Kan extension after that inclusion.

The shorter argument available for the localized sites of a small category — take the
cocontinuous sheaf adjunction and apply `Functor.additive_of_preserves_binary_products` — needs
`F.IsContinuous J K` as well, which is not assumed here. -/
public theorem sheafPushforwardCocontinuous_additive :
    (F.sheafPushforwardCocontinuous AddCommGrpCat.{max v₁ v₂ w₁ w₂ a} J K).Additive := by
  have := (F.op.ranAdjunction AddCommGrpCat.{max v₁ v₂ w₁ w₂ a}).right_adjoint_additive
  have := (sheafificationAdjunction J AddCommGrpCat.{max v₁ v₂ w₁ w₂ a}).right_adjoint_additive
  have := (sheafificationAdjunction K AddCommGrpCat.{max v₁ v₂ w₁ w₂ a}).right_adjoint_additive
  have := Functor.additive_of_iso
    (F.sheafPushforwardCocontinuousCompSheafToPresheafIso
      AddCommGrpCat.{max v₁ v₂ w₁ w₂ a} J K).symm
  exact Functor.additive_of_comp_faithful _
    (sheafToPresheaf K AddCommGrpCat.{max v₁ v₂ w₁ w₂ a})

/-- The presheaf direct image followed by sheafification is the direct image of sheaves: the
comparison of `sheafPushforwardCocontinuousCompSheafToPresheafIso`, sheafified, together with
the fact that sheafifying a sheaf returns it. -/
public noncomputable def presheafDirectImageCompSheafifyIso :
    (sheafToPresheaf J AddCommGrpCat.{max v₁ v₂ w₁ w₂ a} ⋙ F.op.ran) ⋙
        presheafToSheaf K AddCommGrpCat.{max v₁ v₂ w₁ w₂ a} ≅
      F.sheafPushforwardCocontinuous AddCommGrpCat.{max v₁ v₂ w₁ w₂ a} J K :=
  Functor.isoWhiskerRight
      (F.sheafPushforwardCocontinuousCompSheafToPresheafIso
        AddCommGrpCat.{max v₁ v₂ w₁ w₂ a} J K).symm
      (presheafToSheaf K AddCommGrpCat.{max v₁ v₂ w₁ w₂ a}) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (asIso (sheafificationAdjunction K AddCommGrpCat.{max v₁ v₂ w₁ w₂ a}).counit) ≪≫
    Functor.rightUnitor _

variable [EnoughInjectives (Sheaf J AddCommGrpCat.{max v₁ v₂ w₁ w₂ a})]

/-- **The sheafification formula for higher direct images along a cocontinuous functor of
sites.** The `n`-th right derived functor of the direct image is the sheafification of the `n`-th
right derived presheaf direct image. -/
public noncomputable def rightDerivedSheafPushforwardCocontinuousIso (n : ℕ) :
    letI := sheafPushforwardCocontinuous_additive.{v₁, v₂, w₁, w₂, a} F J K
    (F.sheafPushforwardCocontinuous AddCommGrpCat.{max v₁ v₂ w₁ w₂ a} J K).rightDerived n ≅
      derivedPresheafDirectImage.{v₁, v₂, w₁, w₂, a} J F n ⋙
        presheafToSheaf K AddCommGrpCat.{max v₁ v₂ w₁ w₂ a} := by
  haveI hadd := sheafPushforwardCocontinuous_additive.{v₁, v₂, w₁, w₂, a} F J K
  haveI := (sheafificationAdjunction J AddCommGrpCat.{max v₁ v₂ w₁ w₂ a}).right_adjoint_additive
  haveI := (F.op.ranAdjunction AddCommGrpCat.{max v₁ v₂ w₁ w₂ a}).right_adjoint_additive
  rw [derivedPresheafDirectImage_eq]
  exact Functor.rightDerivedIsoOfNatIso
      (presheafDirectImageCompSheafifyIso.{v₁, v₂, w₁, w₂, a} F J K).symm n ≪≫
    Functor.rightDerivedCompIso
      (sheafToPresheaf J AddCommGrpCat.{max v₁ v₂ w₁ w₂ a} ⋙ F.op.ran)
      (presheafToSheaf K AddCommGrpCat.{max v₁ v₂ w₁ w₂ a}) n

end

end CategoryTheory.Functor

end
