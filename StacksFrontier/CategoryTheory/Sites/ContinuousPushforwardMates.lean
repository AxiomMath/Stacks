module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Bicategory.LeftAdjointPseudofunctor

/-!
# Adjoint mates and restriction of sheaves along a continuous functor

Let `p ⊣ q` and `p' ⊣ q'` be adjunctions between two sites, all four functors continuous.
Restriction of sheaves turns each adjunction into an adjunction
`CategoryTheory.Adjunction.sheafPushforwardContinuous` between the two restriction functors,
contravariantly in the functor of sites. This file records that the resulting operation on
sheaves commutes with the formation of adjoint mates: the mate of the restriction of a
natural transformation is the restriction of its mate.

It also records that the identification of two left adjoints of one and the same right
adjoint is the mate of the identity, which is what makes an isomorphism built with
`CategoryTheory.Adjunction.leftAdjointUniq` accessible to the mate calculus.

## Main results

* `CategoryTheory.leftAdjointUniq_eq_conjugateEquiv_symm_id`: the comparison of two left
  adjoints of a fixed right adjoint is the adjoint mate of the identity of that right adjoint.
* `CategoryTheory.conjugateEquiv_sheafPushforwardContinuousNatTrans` and
  `CategoryTheory.conjugateIsoEquiv_sheafPushforwardContinuousIso`: restriction of sheaves
  along a continuous functor commutes with taking adjoint mates, for a natural transformation
  and for a natural isomorphism of functors of sites.
* `CategoryTheory.Adjunction.sheafPushforwardContinuous_comp`: restriction of sheaves turns a
  composite of adjunctions of sites into the composite of the restricted adjunctions;
* `CategoryTheory.Adjunction.sheafPushforwardContinuous_id`: it turns the identity adjunction
  of a site into the identity adjunction of its category of sheaves.

## Implementation notes

The first of the two restriction statements is proved by evaluating both sides at a sheaf and
at an object and unfolding: the unit and the counit of
`CategoryTheory.Adjunction.sheafPushforwardContinuous` are by construction those of the
whiskering of the opposite adjunction, so both sides become the same composite of
`adj.unit`, the given transformation and `adj.counit`, read through the sheaf. The expansion
of `CategoryTheory.conjugateEquiv` has to happen before the restriction functors are unfolded,
which is why it is a separate `simp only` step.

Nothing here carries a Stacks attribute: these are general facts about adjunctions and
restriction of sheaves, and the source states neither.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ t w u₁ u₂

section LeftAdjointUniq

variable {A : Type u₁} [Category.{v₁} A] {D : Type u₂} [Category.{v₂} D]

/-- Two left adjoints of one and the same right adjoint are identified by the adjoint mate of
the identity of that right adjoint. -/
theorem leftAdjointUniq_eq_conjugateEquiv_symm_id {L₁ L₂ : A ⥤ D} {R : D ⥤ A}
    (adj₁ : L₁ ⊣ R) (adj₂ : L₂ ⊣ R) :
    (adj₂.leftAdjointUniq adj₁).hom = (conjugateEquiv adj₁ adj₂).symm (𝟙 R) := by
  have h : adj₁.ofNatIsoRight (Iso.refl R) = adj₁ := by
    apply Adjunction.ext
    simp [Adjunction.ofNatIsoRight]
  simpa only [h, Iso.refl_hom] using leftAdjointUniq_ofNatIsoRight_eq adj₁ adj₂ (Iso.refl R)

end LeftAdjointUniq

section Sites

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {p p' : C ⥤ D} {q q' : D ⥤ C} (a : p ⊣ q) (a' : p' ⊣ q')
  (A : Type w) [Category.{t} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [p.IsContinuous J K] [q.IsContinuous K J]
  [p'.IsContinuous J K] [q'.IsContinuous K J]

/-- **Restriction of sheaves commutes with adjoint mates.** For two adjunctions of functors of
sites, the mate of the restriction of a natural transformation of the left adjoints is the
restriction of the mate of that transformation. -/
theorem conjugateEquiv_sheafPushforwardContinuousNatTrans (α : p ⟶ p') :
    conjugateEquiv (a.sheafPushforwardContinuous (E := A) J K)
        (a'.sheafPushforwardContinuous (E := A) J K)
        (Functor.sheafPushforwardContinuousNatTrans α A J K) =
      Functor.sheafPushforwardContinuousNatTrans (conjugateEquiv a' a α) A K J := by
  ext M X
  simp only [conjugateEquiv_apply_app]
  simp [Adjunction.sheafPushforwardContinuous, Functor.sheafPushforwardContinuous,
    ObjectProperty.lift, Functor.sheafPushforwardContinuousNatTrans,
    conjugateEquiv_apply_app, ObjectProperty.FullSubcategory.comp_hom,
    Adjunction.whiskerLeft_unit_app_app, Adjunction.whiskerLeft_counit_app_app]

/-- **Restriction of sheaves commutes with adjoint mates**, for an isomorphism of functors of
sites. -/
theorem conjugateIsoEquiv_sheafPushforwardContinuousIso (e : p ≅ p') :
    conjugateIsoEquiv (a.sheafPushforwardContinuous (E := A) J K)
        (a'.sheafPushforwardContinuous (E := A) J K)
        (Functor.sheafPushforwardContinuousIso e.symm A J K) =
      Functor.sheafPushforwardContinuousIso (conjugateIsoEquiv a' a e).symm A K J :=
  Iso.ext (conjugateEquiv_sheafPushforwardContinuousNatTrans a a' A J K e.hom)

end Sites

section SitesComp

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type w} [Category.{t} E]
  {p : C ⥤ D} {q : D ⥤ C} {p' : D ⥤ E} {q' : E ⥤ D}
  (a : p ⊣ q) (b : p' ⊣ q') (A : Type*) [Category A]
  (J₁ : GrothendieckTopology C) (J₂ : GrothendieckTopology D)
  (J₃ : GrothendieckTopology E)
  [p.IsContinuous J₁ J₂] [q.IsContinuous J₂ J₁]
  [p'.IsContinuous J₂ J₃] [q'.IsContinuous J₃ J₂]

/-- **Restriction of sheaves turns a composite of adjunctions of sites into the composite of
the restricted adjunctions.** -/
theorem Adjunction.sheafPushforwardContinuous_comp :
    letI := Functor.isContinuous_comp p p' J₁ J₂ J₃
    letI := Functor.isContinuous_comp q' q J₃ J₂ J₁
    (a.comp b).sheafPushforwardContinuous (E := A) J₁ J₃ =
      (b.sheafPushforwardContinuous (E := A) J₂ J₃).comp
        (a.sheafPushforwardContinuous (E := A) J₁ J₂) := by
  refine Adjunction.ext ?_
  ext M X
  simp [Adjunction.sheafPushforwardContinuous, Functor.sheafPushforwardContinuous,
    ObjectProperty.lift, Adjunction.comp_unit_app, Adjunction.whiskerLeft_unit_app_app,
    ObjectProperty.FullSubcategory.comp_hom]

end SitesComp

section SitesId

variable {C : Type u₁} [Category.{v₁} C] (A : Type w) [Category.{t} A]
  (J : GrothendieckTopology C)

/-- **Restriction of sheaves turns the identity adjunction of a site into the identity
adjunction of its category of sheaves.** -/
theorem Adjunction.sheafPushforwardContinuous_id :
    (Adjunction.id (C := C)).sheafPushforwardContinuous (E := A) J J =
      Adjunction.id (C := Sheaf J A) := by
  refine Adjunction.ext ?_
  ext M X
  simp [Adjunction.sheafPushforwardContinuous, Functor.sheafPushforwardContinuous,
    ObjectProperty.lift, Adjunction.whiskerLeft_unit_app_app]

end SitesId

end CategoryTheory

end
