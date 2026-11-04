module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SectionsComponents

/-!
# Morphisms of sheaves of modules induced by an arrow of the site

Every factor of `AlgebraicGeometry.BigFppfOver.objRestrictSectionsIso_eq_explicit` is given on
sections by restriction along an arrow of the site; so is every composite of such factors, and two
such restrictions agree as soon as the two arrows do.  This file makes that an induction.

`Stacks.SectionsComponents.Induced M f U A A'` says that the component of `f` at the object `U`
of its own site *is* restriction along some arrow `A' ⟶ A` of the site of `M`.  The predicate is
closed under composition (`Stacks.SectionsComponents.Induced.comp`), under reindexing of the base
module along a pushforward (`Stacks.SectionsComponents.Induced.descend`), and under the
structural operations on natural transformations; and two induced morphisms with the same source
and target arrows agree when the relevant hom-set of the site is a subsingleton
(`Stacks.SectionsComponents.Induced.eq`).

## Implementation notes

Nothing here carries a `stacks` attribute.

The source and target *types* of the component are carried as `cast`s rather than being asked to
be literally `M.val.obj (Opposite.op A)`.  That is forced: the composite functors of the
comparison of Stacks 03DV are type-correct only at default transparency — the structure sheaf of
the big fppf site over `S` and the restriction of the structure sheaf of the whole site to the
object of `S` are the same sheaf of rings only after unfolding a semireducible definition — so no
`simp` lemma fires on those goals and no statement may assume the two spellings agree reducibly.
With the identifications carried as `cast`s, each step of the induction is a single `exact`, which
elaborates at default transparency.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅ w m

namespace Stacks.SectionsComponents

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  (M : SheafOfModules.{m} R)

section Def

variable {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'}
  {S' : Sheaf J' RingCat.{w}}

/-- **The component of `f` at `U` is restriction along an arrow of the site of `M`.**  The two
identifications of types are part of the data because the composite functors this is applied to
are type-correct only at default transparency. -/
public def Induced {N₁ N₂ : SheafOfModules.{m} S'} (f : N₁ ⟶ N₂) (U : C'ᵒᵖ) (A A' : C) : Prop :=
  ∃ (u : A' ⟶ A) (e₁ : ↥(N₁.val.obj U) = ↥(M.val.obj (op A)))
    (e₂ : ↥(N₂.val.obj U) = ↥(M.val.obj (op A'))),
    ∀ y, cast e₂ (f.val.app U y) = M.val.map u.op (cast e₁ y)

variable {M}

/-- **The identity is induced by the identity arrow.** -/
public theorem Induced.id (N : SheafOfModules.{m} S') (U : C'ᵒᵖ) {A : C}
    (e : ↥(N.val.obj U) = ↥(M.val.obj (op A))) : Induced M (𝟙 N) U A A :=
  ⟨𝟙 A, e, e, fun y => (val_map_id M (cast e y)).symm⟩

/-- **A composite of induced morphisms is induced**, by the composite arrow. -/
public theorem Induced.comp {N₁ N₂ N₃ : SheafOfModules.{m} S'} {f : N₁ ⟶ N₂} {g : N₂ ⟶ N₃}
    {U : C'ᵒᵖ} {A₁ A₂ A₃ : C} (hf : Induced M f U A₁ A₂) (hg : Induced M g U A₂ A₃) :
    Induced M (f ≫ g) U A₁ A₃ := by
  obtain ⟨u, e₁, e₂, hu⟩ := hf
  obtain ⟨v, e₂', e₃, hv⟩ := hg
  refine ⟨v ≫ u, e₁, e₃, fun y => ?_⟩
  have h : e₂' = e₂ := rfl
  subst h
  exact Eq.trans (hv _) (Eq.trans (congrArg (fun z => M.val.map v.op z) (hu y))
    (val_map_map M v u (cast e₁ y)))
/-- A morphism whose sections are the identity is induced by the identity arrow. -/
private theorem induced_of_cast {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'}
    {S' : Sheaf J' RingCat.{w}} {M : SheafOfModules.{m} R} {N₁ N₂ : SheafOfModules.{m} S'}
    (f : N₁ ⟶ N₂) (U : C'ᵒᵖ) {A : C} (e : ↥(N₁.val.obj U) = ↥(N₂.val.obj U))
    (hf : ∀ y, f.val.app U y = cast e y) (e₁ : ↥(N₁.val.obj U) = ↥(M.val.obj (op A))) :
    Induced M f U A A := by
  refine ⟨𝟙 A, e₁, e.symm.trans e₁, fun y => ?_⟩
  refine Eq.trans (congrArg (cast (e.symm.trans e₁)) (hf y)) ?_
  exact Eq.trans (cast_cast e (e.symm.trans e₁) y) (val_map_id M (cast e₁ y)).symm

/-- **An identity factor on the left may be dropped.**  Every structural factor of the comparison
of sections — associator, unitor, contraction of an iterated pushforward, transport along an
equality of structure maps — is the identity on sections, and this is how such a factor is
absorbed. -/
public theorem Induced.compIdLeft {N₁ N₂ N₃ : SheafOfModules.{m} S'} {f : N₁ ⟶ N₂} {g : N₂ ⟶ N₃}
    {U : C'ᵒᵖ} {A₁ A₂ : C} (e : ↥(N₁.val.obj U) = ↥(N₂.val.obj U))
    (hf : ∀ y, f.val.app U y = cast e y) (hg : Induced M g U A₁ A₂) :
    Induced M (f ≫ g) U A₁ A₂ := by
  have ⟨_, e₁, _⟩ := hg
  exact (induced_of_cast f U e hf (e.trans e₁)).comp hg

/-- **An identity factor on the right may be dropped.** -/
public theorem Induced.compIdRight {N₁ N₂ N₃ : SheafOfModules.{m} S'} {f : N₁ ⟶ N₂} {g : N₂ ⟶ N₃}
    {U : C'ᵒᵖ} {A₁ A₂ : C} (e : ↥(N₂.val.obj U) = ↥(N₃.val.obj U))
    (hg : ∀ y, g.val.app U y = cast e y) (hf : Induced M f U A₁ A₂) :
    Induced M (f ≫ g) U A₁ A₂ := by
  have ⟨_, _, e₂, _⟩ := hf
  exact hf.comp (induced_of_cast g U e hg e₂)

end Def

/-! ### Two induced morphisms with a subsingleton hom-set of arrows agree -/

section Eq

variable {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'}
  {S' : Sheaf J' RingCat.{w}} {M}

/-- **Two morphisms induced by arrows between the same two objects agree**, when there is at most
one such arrow. -/
public theorem Induced.eq {N₁ N₂ : SheafOfModules.{m} S'} {f g : N₁ ⟶ N₂} {U : C'ᵒᵖ} {A A' : C}
    [Subsingleton (A' ⟶ A)] (hf : Induced M f U A A') (hg : Induced M g U A A') :
    ∀ y, f.val.app U y = g.val.app U y := by
  intro y
  obtain ⟨u, e₁, e₂, hu⟩ := hf
  obtain ⟨u', e₁', e₂', hu'⟩ := hg
  have key : cast e₂ (f.val.app U y) = cast e₂ (g.val.app U y) :=
    Eq.trans (hu y) (Eq.trans (congrArg (fun w : A' ⟶ A => M.val.map w.op (cast e₁ y))
      (Subsingleton.elim u u')) (hu' y).symm)
  simpa only [cast_cast, cast_eq] using congrArg (cast e₂.symm) key

end Eq

/-! ### Reindexing the base module -/

section Descend

variable {D : Type u₃} [Category.{v₃} D] {J₂ : GrothendieckTopology D}
  {S₂ : Sheaf J₂ RingCat.{w}} {F : D ⥤ C} [F.IsContinuous J₂ J]
  (φ : S₂ ⟶ (F.sheafPushforwardContinuous RingCat.{w} J₂ J).obj R)

/-- **An arrow of the site of a pushed-forward base module becomes its image arrow.**  This is
what lets a factor whiskered on the left by a pushforward be read on the original base module. -/
public theorem Induced.descend {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'}
    {S' : Sheaf J' RingCat.{w}} {N₁ N₂ : SheafOfModules.{m} S'} {f : N₁ ⟶ N₂} {U : C'ᵒᵖ}
    {A A' : D} (h : Induced ((SheafOfModules.pushforward.{m} φ).obj M) f U A A') :
    Induced M f U (F.obj A) (F.obj A') := by
  obtain ⟨u, e₁, e₂, hu⟩ := h
  exact ⟨F.map u, e₁, e₂, fun y => Eq.trans (hu y) (pushforward_obj_val_map φ M u.op _)⟩

end Descend

/-! ### The structural operations, at the level of isomorphisms -/

section Iso

variable {𝒞 : Type u₄} [Category.{v₄} 𝒞] {C' : Type u₂} [Category.{v₂} C']
  {J' : GrothendieckTopology C'} {S' : Sheaf J' RingCat.{w}} {M}
  {F G H : 𝒞 ⥤ SheafOfModules.{m} S'}

/-- **A composite of two isomorphisms is induced**, by the composite arrow. -/
public theorem Induced.isoTransHom (N : 𝒞) (α : F ≅ G) (β : G ≅ H) {U : C'ᵒᵖ} {A₁ A₂ A₃ : C}
    (h₁ : Induced M (α.hom.app N) U A₁ A₂) (h₂ : Induced M (β.hom.app N) U A₂ A₃) :
    Induced M ((α ≪≫ β).hom.app N) U A₁ A₃ := h₁.comp h₂

/-- **The inverse of a composite of two isomorphisms is induced.** -/
public theorem Induced.isoTransInv (N : 𝒞) (α : F ≅ G) (β : G ≅ H) {U : C'ᵒᵖ} {A₁ A₂ A₃ : C}
    (h₁ : Induced M (β.inv.app N) U A₁ A₂) (h₂ : Induced M (α.inv.app N) U A₂ A₃) :
    Induced M ((α ≪≫ β).inv.app N) U A₁ A₃ := h₁.comp h₂

/-- **The forward direction of an inverted isomorphism is its inverse.** -/
public theorem Induced.isoSymmHom (N : 𝒞) (α : F ≅ G) {U : C'ᵒᵖ} {A₁ A₂ : C}
    (h : Induced M (α.inv.app N) U A₁ A₂) : Induced M (α.symm.hom.app N) U A₁ A₂ := h

/-- **The inverse of an inverted isomorphism is its forward direction.** -/
public theorem Induced.isoSymmInv (N : 𝒞) (α : F ≅ G) {U : C'ᵒᵖ} {A₁ A₂ : C}
    (h : Induced M (α.hom.app N) U A₁ A₂) : Induced M (α.symm.inv.app N) U A₁ A₂ := h

/-- **Whiskering on the right by a pushforward reindexes the object at which the component is
taken.** -/
public theorem Induced.isoWhiskerRightHom (N : 𝒞) {C'' : Type u₃} [Category.{v₃} C'']
    {J'' : GrothendieckTopology C''} {S'' : Sheaf J'' RingCat.{w}} {K : C' ⥤ C''}
    [K.IsContinuous J' J''] (ψ : S' ⟶ (K.sheafPushforwardContinuous RingCat.{w} J' J'').obj S'')
    {F' G' : 𝒞 ⥤ SheafOfModules.{m} S''} (α : F' ≅ G') {U : C'ᵒᵖ} {A₁ A₂ : C}
    (h : Induced M (α.hom.app N) (op (K.obj U.unop)) A₁ A₂) :
    Induced M ((Functor.isoWhiskerRight α (SheafOfModules.pushforward.{m} ψ)).hom.app N) U
      A₁ A₂ := h

/-- **The inverse of a whiskering on the right by a pushforward.** -/
public theorem Induced.isoWhiskerRightInv (N : 𝒞) {C'' : Type u₃} [Category.{v₃} C'']
    {J'' : GrothendieckTopology C''} {S'' : Sheaf J'' RingCat.{w}} {K : C' ⥤ C''}
    [K.IsContinuous J' J''] (ψ : S' ⟶ (K.sheafPushforwardContinuous RingCat.{w} J' J'').obj S'')
    {F' G' : 𝒞 ⥤ SheafOfModules.{m} S''} (α : F' ≅ G') {U : C'ᵒᵖ} {A₁ A₂ : C}
    (h : Induced M (α.inv.app N) (op (K.obj U.unop)) A₁ A₂) :
    Induced M ((Functor.isoWhiskerRight α (SheafOfModules.pushforward.{m} ψ)).inv.app N) U
      A₁ A₂ := h

end Iso

/-! ### Absorbing a structural factor without naming an object of the site -/

section Structural

variable {𝒞 : Type u₄} [Category.{v₄} 𝒞] {C' : Type u₂} [Category.{v₂} C']
  {J' : GrothendieckTopology C'} {S' : Sheaf J' RingCat.{w}} {M}
  {F G H : 𝒞 ⥤ SheafOfModules.{m} S'} {U : C'ᵒᵖ} {A₁ A₂ : C}

/-- **A composite of two isomorphisms whose first factor is the identity on sections is induced by
the arrow of the second.**  Unlike `Stacks.SectionsComponents.Induced.isoTransHom` this asks for no
object of the site for the absorbed factor, so a structural factor whose functors are *not*
pushforwards — an associator or a unitor of a composite one of whose legs is the identity functor
or a reindexing — needs no leaf of its own: its continuity hypotheses, and the object of the site
at which it would be read, never arise. -/
public theorem Induced.isoTransHomIdLeft (N : 𝒞) (α : F ≅ G) (β : G ≅ H)
    (e : ↥((F.obj N).val.obj U) = ↥((G.obj N).val.obj U))
    (hα : ∀ y, (α.hom.app N).val.app U y = cast e y)
    (h : Induced M (β.hom.app N) U A₁ A₂) : Induced M ((α ≪≫ β).hom.app N) U A₁ A₂ :=
  Induced.compIdLeft e hα h

/-- **A composite of two isomorphisms whose second factor is the identity on sections is induced by
the arrow of the first.** -/
public theorem Induced.isoTransHomIdRight (N : 𝒞) (α : F ≅ G) (β : G ≅ H)
    (e : ↥((G.obj N).val.obj U) = ↥((H.obj N).val.obj U))
    (hβ : ∀ y, (β.hom.app N).val.app U y = cast e y)
    (h : Induced M (α.hom.app N) U A₁ A₂) : Induced M ((α ≪≫ β).hom.app N) U A₁ A₂ :=
  Induced.compIdRight e hβ h

/-- **The inverse of a composite whose second factor is the identity on sections.**  The inverse of
that factor comes first in the inverse composite, and is absorbed on the left. -/
public theorem Induced.isoTransInvIdLeft (N : 𝒞) (α : F ≅ G) (β : G ≅ H)
    (e : ↥((H.obj N).val.obj U) = ↥((G.obj N).val.obj U))
    (hβ : ∀ y, (β.inv.app N).val.app U y = cast e y)
    (h : Induced M (α.inv.app N) U A₁ A₂) : Induced M ((α ≪≫ β).inv.app N) U A₁ A₂ :=
  Induced.compIdLeft e hβ h

/-- **The inverse of a composite whose first factor is the identity on sections.** -/
public theorem Induced.isoTransInvIdRight (N : 𝒞) (α : F ≅ G) (β : G ≅ H)
    (e : ↥((G.obj N).val.obj U) = ↥((F.obj N).val.obj U))
    (hα : ∀ y, (α.inv.app N).val.app U y = cast e y)
    (h : Induced M (β.inv.app N) U A₁ A₂) : Induced M ((α ≪≫ β).inv.app N) U A₁ A₂ :=
  Induced.compIdRight e hα h

end Structural

/-! ### A direct image of an induced morphism -/

section PushforwardMap

variable {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'}
  {S' : Sheaf J' RingCat.{w}} {M} {C'' : Type u₃} [Category.{v₃} C'']
  {J'' : GrothendieckTopology C''} {S'' : Sheaf J'' RingCat.{w}} {K : C' ⥤ C''}
  [K.IsContinuous J' J'']

/-- **A direct image of an induced morphism is induced by the same arrow**: taking the direct image
only reindexes the object at which the component is read.  This is
`Stacks.SectionsComponents.Induced.isoWhiskerRightHom` with the whiskered isomorphism replaced by
an arbitrary morphism, which is the form a factor split off a composite by
`CategoryTheory.Functor.map_comp` comes in: the counit of an equivalence of module categories
enters the square of direct images as a direct image of a *component*, not as a whiskering of an
isomorphism. -/
public theorem Induced.pushforwardMap
    (ψ : S' ⟶ (K.sheafPushforwardContinuous RingCat.{w} J' J'').obj S'')
    {N₁ N₂ : SheafOfModules.{m} S''} (f : N₁ ⟶ N₂) {U : C'ᵒᵖ} {A₁ A₂ : C}
    (h : Induced M f (op (K.obj U.unop)) A₁ A₂) :
    Induced M ((SheafOfModules.pushforward.{m} ψ).map f) U A₁ A₂ := h

section ReindexMap

variable {C₀ : Type u₂} [Category.{v₂} C₀] {J₀ : GrothendieckTopology C₀}
  {C₂ : Type u₃} [Category.{v₃} C₂] {J₂ : GrothendieckTopology C₂} (e : C₀ ≌ C₂)
  [e.functor.IsContinuous J₀ J₂] [e.inverse.IsContinuous J₂ J₀] (R₂ : Sheaf J₂ RingCat.{w})

/-- **The reading back of an induced morphism along the inverse reindexing equivalence of
Stacks 06WI is induced by the same arrow.**  This is
`Stacks.SectionsComponents.Induced.pushforwardMap` at the inverse of the reindexing equivalence,
stated here on variables: the two spellings of that functor — the projection out of the
equivalence and the direct image along
`Stacks.SheafOfModules.reindexBackSharp` — are identified once, where the sheaves of modules are
variables and the identification is free, instead of once per concrete equivalence, where it
exhausts the heartbeat budget at `whnf`. -/
public theorem Induced.reindexInverseMap
    {N₁ N₂ : SheafOfModules.{m} (Stacks.SheafOfModules.reindexRing J₀ e R₂)} (f : N₁ ⟶ N₂)
    {U : C₂ᵒᵖ} {A₁ A₂ : C}
    (h : Induced M f (op (e.inverse.obj U.unop)) A₁ A₂) :
    Induced M ((Stacks.SheafOfModules.reindexEquivalence.{_, m, _, _, _, _} e R₂).inverse.map f)
      U A₁ A₂ :=
  Induced.pushforwardMap (Stacks.SheafOfModules.reindexBackSharp e R₂) f h

end ReindexMap

end PushforwardMap

section IsoWhiskerLeft

variable {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'}
  {S' : Sheaf J' RingCat.{w}} {D : Type u₅} [Category.{v₅} D] {J₂ : GrothendieckTopology D}
  {S₂ : Sheaf J₂ RingCat.{w}} {Fn : D ⥤ C} [Fn.IsContinuous J₂ J]
  (φ : S₂ ⟶ (Fn.sheafPushforwardContinuous RingCat.{w} J₂ J).obj R)
  {F' G' : SheafOfModules.{m} S₂ ⥤ SheafOfModules.{m} S'}

/-- **Whiskering on the left by a pushforward**, with the arrows of the site transported to the
base module. -/
public theorem Induced.isoWhiskerLeftHom (α : F' ≅ G') {U : C'ᵒᵖ} {A A' : D}
    (h : Induced ((SheafOfModules.pushforward.{m} φ).obj M)
      (α.hom.app ((SheafOfModules.pushforward.{m} φ).obj M)) U A A') :
    Induced M ((Functor.isoWhiskerLeft (SheafOfModules.pushforward.{m} φ) α).hom.app M) U
      (Fn.obj A) (Fn.obj A') := Induced.descend _ φ h

/-- **The inverse of a whiskering on the left by a pushforward.** -/
public theorem Induced.isoWhiskerLeftInv (α : F' ≅ G') {U : C'ᵒᵖ} {A A' : D}
    (h : Induced ((SheafOfModules.pushforward.{m} φ).obj M)
      (α.inv.app ((SheafOfModules.pushforward.{m} φ).obj M)) U A A') :
    Induced M ((Functor.isoWhiskerLeft (SheafOfModules.pushforward.{m} φ) α).inv.app M) U
      (Fn.obj A) (Fn.obj A') := Induced.descend _ φ h

end IsoWhiskerLeft

/-! ### Whiskering on the left by the inverse reindexing of Stacks 06WI -/

section ReindexWhisker

variable {C₂ : Type u₁} [Category.{v₁} C₂] {J₂ : GrothendieckTopology C₂} (e : C ≌ C₂)
  [e.functor.IsContinuous J J₂] [e.inverse.IsContinuous J₂ J] (R₂ : Sheaf J₂ RingCat.{w})
  {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'} {S' : Sheaf J' RingCat.{w}}
  (N : SheafOfModules.{m} (Stacks.SheafOfModules.reindexRing J e R₂))
  {F' G' : SheafOfModules.{m} R₂ ⥤ SheafOfModules.{m} S'}

/-- **Whiskering on the left by the inverse of the reindexing equivalence of Stacks 06WI**, with
the arrows of the site carried back along the equivalence. -/
public theorem Induced.isoWhiskerLeftReindexHom (α : F' ≅ G') {U : C'ᵒᵖ} {A A' : C₂}
    (h : Induced ((Stacks.SheafOfModules.reindexEquivalence.{_, m, _, _, _, _} e R₂).inverse.obj N)
      (α.hom.app
        ((Stacks.SheafOfModules.reindexEquivalence.{_, m, _, _, _, _} e R₂).inverse.obj
            N)) U A A') :
    Induced N ((Functor.isoWhiskerLeft
        (Stacks.SheafOfModules.reindexEquivalence.{_, m, _, _, _, _} e R₂).inverse α).hom.app N) U
      (e.inverse.obj A) (e.inverse.obj A') :=
  Induced.descend _ (Stacks.SheafOfModules.reindexBackSharp e R₂) h

/-- **The inverse of a whiskering on the left by the inverse reindexing of Stacks 06WI.** -/
public theorem Induced.isoWhiskerLeftReindexInv (α : F' ≅ G') {U : C'ᵒᵖ} {A A' : C₂}
    (h : Induced ((Stacks.SheafOfModules.reindexEquivalence.{_, m, _, _, _, _} e R₂).inverse.obj N)
      (α.inv.app
        ((Stacks.SheafOfModules.reindexEquivalence.{_, m, _, _, _, _} e R₂).inverse.obj
            N)) U A A') :
    Induced N ((Functor.isoWhiskerLeft
        (Stacks.SheafOfModules.reindexEquivalence.{_, m, _, _, _, _} e R₂).inverse α).inv.app N) U
      (e.inverse.obj A) (e.inverse.obj A') :=
  Induced.descend _ (Stacks.SheafOfModules.reindexBackSharp e R₂) h

/-- **An arrow of the site of a module read back along the inverse reindexing equivalence of
Stacks 06WI becomes its image under the inverse equivalence of sites.**  This is
`Stacks.SectionsComponents.Induced.descend` at that equivalence, stated on variables: it is what a
factor read at `(reindexEquivalence e R₂).inverse.obj N` — rather than whiskered by that functor —
is rebased with, and the identification of the two spellings of the functor is paid here, where
the sheaves of modules are variables, instead of at each concrete equivalence, where it exhausts
the heartbeat budget at `whnf`. -/
public theorem Induced.descendReindex {N₁ N₂ : SheafOfModules.{m} S'} {f : N₁ ⟶ N₂} {U : C'ᵒᵖ}
    {A A' : C₂}
    (h : Induced ((Stacks.SheafOfModules.reindexEquivalence.{_, m, _, _, _, _} e R₂).inverse.obj N)
      f U A A') :
    Induced N f U (e.inverse.obj A) (e.inverse.obj A') :=
  Induced.descend _ (Stacks.SheafOfModules.reindexBackSharp e R₂) h

end ReindexWhisker

/-! ### The leaves -/

section Leaves

variable {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'}
  {S' : Sheaf J' RingCat.{w}} {M}

/-- **A morphism whose sections are the identity is induced by the identity arrow.** -/
public theorem Induced.ofCast {N₁ N₂ : SheafOfModules.{m} S'} (f : N₁ ⟶ N₂) (U : C'ᵒᵖ) {A : C}
    (e : ↥(N₁.val.obj U) = ↥(N₂.val.obj U)) (hf : ∀ y, f.val.app U y = cast e y)
    (e₁ : ↥(N₁.val.obj U) = ↥(M.val.obj (op A))) : Induced M f U A A :=
  induced_of_cast f U e hf e₁

end Leaves

/-! ### The leaves that are the identity on sections -/

section IdentityLeaves

variable {C₂ : Type u₂} [Category.{v₂} C₂] {J₂ : GrothendieckTopology C₂}
  {R₂ : Sheaf J₂ RingCat.{w}} {K₁ : C₂ ⥤ C} [K₁.IsContinuous J₂ J]
  (φ₁ : R₂ ⟶ (K₁.sheafPushforwardContinuous RingCat.{w} J₂ J).obj R)
  {C₃ : Type u₃} [Category.{v₃} C₃] {J₃ : GrothendieckTopology C₃}
  {R₃ : Sheaf J₃ RingCat.{w}} {K₂ : C₃ ⥤ C₂} [K₂.IsContinuous J₃ J₂]
  (φ₂ : R₃ ⟶ (K₂.sheafPushforwardContinuous RingCat.{w} J₃ J₂).obj R₂)

/-- **The contraction of an iterated pushforward is the identity on sections.** -/
public theorem Induced.pushforwardCompHom (U : C₃ᵒᵖ) :
    Induced M ((SheafOfModules.pushforwardComp.{m} φ₂ φ₁).hom.app M) U
      (K₁.obj (K₂.obj U.unop)) (K₁.obj (K₂.obj U.unop)) :=
  Induced.ofCast _ U rfl
    (fun y => SheafOfModules.pushforwardComp_hom_app_val_app φ₂ φ₁ M U y) rfl

/-- **The inverse contraction of an iterated pushforward is the identity on sections.** -/
public theorem Induced.pushforwardCompInv (U : C₃ᵒᵖ) :
    Induced M ((SheafOfModules.pushforwardComp.{m} φ₂ φ₁).inv.app M) U
      (K₁.obj (K₂.obj U.unop)) (K₁.obj (K₂.obj U.unop)) :=
  Induced.ofCast _ U rfl
    (fun y => SheafOfModules.pushforwardComp_inv_app_val_app φ₂ φ₁ M U y) rfl

/-- **The transport of a pushforward along an equality of structure maps is the identity on
sections.** -/
public theorem Induced.pushforwardCongrHom
    {ψ₁ : R₂ ⟶ (K₁.sheafPushforwardContinuous RingCat.{w} J₂ J).obj R} (he : φ₁ = ψ₁)
    (U : C₂ᵒᵖ) :
    Induced M ((SheafOfModules.pushforwardCongr.{m} he).hom.app M) U
      (K₁.obj U.unop) (K₁.obj U.unop) :=
  Induced.ofCast _ U rfl
    (fun y => SheafOfModules.pushforwardCongr_hom_app_val_app he M U y) rfl

/-- **The inverse transport of a pushforward along an equality of structure maps is the identity
on sections.** -/
public theorem Induced.pushforwardCongrInv
    {ψ₁ : R₂ ⟶ (K₁.sheafPushforwardContinuous RingCat.{w} J₂ J).obj R} (he : φ₁ = ψ₁)
    (U : C₂ᵒᵖ) :
    Induced M ((SheafOfModules.pushforwardCongr.{m} he).inv.app M) U
      (K₁.obj U.unop) (K₁.obj U.unop) :=
  Induced.ofCast _ U rfl
    (fun y => SheafOfModules.pushforwardCongr_inv_app_val_app he M U y) rfl

/-- **The left unitor of a pushforward is the identity on sections.** -/
public theorem Induced.leftUnitorHom (U : C₂ᵒᵖ) :
    Induced M ((SheafOfModules.pushforward.{m} φ₁).leftUnitor.hom.app M) U
      (K₁.obj U.unop) (K₁.obj U.unop) :=
  Induced.ofCast _ U rfl (fun _ => rfl) rfl

/-- **The inverse left unitor of a pushforward is the identity on sections.** -/
public theorem Induced.leftUnitorInv (U : C₂ᵒᵖ) :
    Induced M ((SheafOfModules.pushforward.{m} φ₁).leftUnitor.inv.app M) U
      (K₁.obj U.unop) (K₁.obj U.unop) :=
  Induced.ofCast _ U rfl (fun _ => rfl) rfl

variable {C₄ : Type u₅} [Category.{v₅} C₄] {J₄ : GrothendieckTopology C₄}
  {R₄ : Sheaf J₄ RingCat.{w}} {K₃ : C₄ ⥤ C₃} [K₃.IsContinuous J₄ J₃]
  (φ₃ : R₄ ⟶ (K₃.sheafPushforwardContinuous RingCat.{w} J₄ J₃).obj R₃)

/-- **The associator of three pushforwards is the identity on sections.** -/
public theorem Induced.associatorHom (U : C₄ᵒᵖ) :
    Induced M ((Functor.associator (SheafOfModules.pushforward.{m} φ₁)
        (SheafOfModules.pushforward.{m} φ₂) (SheafOfModules.pushforward.{m} φ₃)).hom.app M) U
      (K₁.obj (K₂.obj (K₃.obj U.unop))) (K₁.obj (K₂.obj (K₃.obj U.unop))) :=
  Induced.ofCast _ U rfl (fun _ => rfl) rfl

/-- **The inverse associator of three pushforwards is the identity on sections.** -/
public theorem Induced.associatorInv (U : C₄ᵒᵖ) :
    Induced M ((Functor.associator (SheafOfModules.pushforward.{m} φ₁)
        (SheafOfModules.pushforward.{m} φ₂) (SheafOfModules.pushforward.{m} φ₃)).inv.app M) U
      (K₁.obj (K₂.obj (K₃.obj U.unop))) (K₁.obj (K₂.obj (K₃.obj U.unop))) :=
  Induced.ofCast _ U rfl (fun _ => rfl) rfl

end IdentityLeaves

section NatTransLeaf

/-- **The sections of a natural transformation of pushforwards are restriction along its
component.**  This is the only factor of the comparison of sections that is not the identity on
sections. -/
public theorem Induced.pushforwardNatTrans {C₂ : Type u₃} [Category.{v₃} C₂]
    {J₂ : GrothendieckTopology C₂} {F G : C₂ ⥤ C} [F.IsContinuous J₂ J] [G.IsContinuous J₂ J]
    {T : Sheaf J₂ RingCat.{w}} (φ : T ⟶ (G.sheafPushforwardContinuous RingCat.{w} J₂ J).obj R)
    (α : F ⟶ G) (U : C₂ᵒᵖ) :
    Induced M ((SheafOfModules.pushforwardNatTrans.{m} φ α).app M) U
      (G.obj U.unop) (F.obj U.unop) :=
  ⟨α.app U.unop, rfl, rfl, fun y => SheafOfModules.pushforwardNatTrans_app_val_app φ α M U y⟩

/-- **The sections of the transport of a pushforward along an isomorphism of sites.** -/
public theorem Induced.pushforwardCongr₂Hom {C₂ : Type u₃} [Category.{v₃} C₂]
    {J₂ : GrothendieckTopology C₂} {F G : C₂ ⥤ C} [F.IsContinuous J₂ J] [G.IsContinuous J₂ J]
    {T : Sheaf J₂ RingCat.{w}} (φ : T ⟶ (G.sheafPushforwardContinuous RingCat.{w} J₂ J).obj R)
    {ψ : T ⟶ (F.sheafPushforwardContinuous RingCat.{w} J₂ J).obj R} (e : F ≅ G)
    (he : φ ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{w} J₂ J).app R = ψ)
    (U : C₂ᵒᵖ) :
    Induced M ((SheafOfModules.pushforwardCongr₂.{m} φ e he).hom.app M) U
      (G.obj U.unop) (F.obj U.unop) :=
  ⟨e.hom.app U.unop, rfl, rfl, fun y => pushforwardCongr₂_hom_app_val_app φ e he M U y⟩

/-- **The sections of the inverse transport of a pushforward along an isomorphism of sites.** -/
public theorem Induced.pushforwardCongr₂Inv {C₂ : Type u₃} [Category.{v₃} C₂]
    {J₂ : GrothendieckTopology C₂} {F G : C₂ ⥤ C} [F.IsContinuous J₂ J] [G.IsContinuous J₂ J]
    {T : Sheaf J₂ RingCat.{w}} (φ : T ⟶ (G.sheafPushforwardContinuous RingCat.{w} J₂ J).obj R)
    {ψ : T ⟶ (F.sheafPushforwardContinuous RingCat.{w} J₂ J).obj R} (e : F ≅ G)
    (he : φ ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{w} J₂ J).app R = ψ)
    (U : C₂ᵒᵖ) :
    Induced M ((SheafOfModules.pushforwardCongr₂.{m} φ e he).inv.app M) U
      (F.obj U.unop) (G.obj U.unop) :=
  ⟨e.inv.app U.unop, rfl, rfl, fun y => pushforwardCongr₂_inv_app_val_app φ e he M U y⟩

end NatTransLeaf

section ReindexLeaf

variable {C₂ : Type u₁} [Category.{v₁} C₂] {J₂ : GrothendieckTopology C₂} (e : C ≌ C₂)
  [e.functor.IsContinuous J J₂] [e.inverse.IsContinuous J₂ J] (R₂ : Sheaf J₂ RingCat.{w})

/-- **The sections of the unit of the inverse reindexing equivalence of Stacks 06WI.** -/
public theorem Induced.reindexSymmUnitHom
    (N : SheafOfModules.{m} (Stacks.SheafOfModules.reindexRing J e R₂)) (U : Cᵒᵖ) :
    Induced N
      ((Stacks.SheafOfModules.reindexEquivalence.{_, m, _, _, _, _} e R₂).symm.unitIso.hom.app N) U
      U.unop (e.inverse.obj (e.functor.obj U.unop)) :=
  ⟨e.unitIso.inv.app U.unop, rfl, rfl,
    fun y => reindexEquivalence_symm_unitIso_hom_app_val_app e R₂ N U y⟩

/-- **The sections of the inverse unit of the inverse reindexing equivalence of
Stacks 06WI.** -/
public theorem Induced.reindexSymmUnitInv
    (N : SheafOfModules.{m} (Stacks.SheafOfModules.reindexRing J e R₂)) (U : Cᵒᵖ) :
    Induced N
      ((Stacks.SheafOfModules.reindexEquivalence.{_, m, _, _, _, _} e R₂).symm.unitIso.inv.app N) U
      (e.inverse.obj (e.functor.obj U.unop)) U.unop :=
  ⟨e.unitIso.hom.app U.unop, rfl, rfl,
    fun y => reindexEquivalence_symm_unitIso_inv_app_val_app e R₂ N U y⟩

end ReindexLeaf

end Stacks.SectionsComponents

end
