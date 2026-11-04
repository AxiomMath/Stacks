module

public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.CompatibleSheafification
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Sheafification descends along a fully faithful continuous cocontinuous left adjoint

Let `I : C ⥤ D` be a functor between sites `(C, J)` and `(D, K)` which is full, faithful, a
left adjoint, and both continuous and cocontinuous for the two topologies.  Then sheafification
of `A`-valued presheaves on `(C, J)` exists as soon as it exists on `(D, K)`, and it inverts
exactly the locally bijective morphisms on `(C, J)` as soon as it does so on `(D, K)`.

The motivating instance is the localization of a small étale site at an open subspace: the
postcomposition functor from the small étale site of an open subspace `U ⊆ X` to that of `X` is
fully faithful (the inclusion is a monomorphism), a left adjoint (base change along the
inclusion is its right adjoint), and continuous and cocontinuous by Stacks 03LP.  So a space
whose small étale site carries sheafification passes that on to each of its open subspaces,
which is what an induction over elementary distinguished squares needs in order to speak of
sheaves on the smaller member.

## Main results

* `Stacks.Sites.hasSheafify_of_fullyFaithful_isLeftAdjoint`: `HasSheafify K A → HasSheafify J A`.
* `Stacks.Sites.wEqualsLocallyBijective_of_fullyFaithful_isLeftAdjoint`: the weak equivalences
  of `(C, J)` are the locally bijective morphisms as soon as those of `(D, K)` are.

## Implementation notes

Being a left adjoint makes `I.op` a right adjoint, hence every presheaf on `C` has a *pointwise*
right Kan extension along `I.op` — the structured-arrow categories have initial objects.  Write
`E = ran I.op` for that extension.  It is fully faithful because the counit of
`I.op.ranAdjunction` is an isomorphism, `I` being fully faithful, and it preserves finite limits
because it is itself a right adjoint.

Sheafification on `(C, J)` is then produced as the composite

`E ⋙ presheafToSheaf K A ⋙ I.sheafPushforwardContinuous A J K`,

whose adjunction to `sheafToPresheaf J A` is the composite of the sheafification adjunction on
`(D, K)` with `I.sheafAdjunctionCocontinuous`, cut down by `Adjunction.restrictFullyFaithful`
along `E`.  Left exactness of the composite is left exactness of each factor; for the
continuous pushforward this is read after the faithful, limit-reflecting `sheafToPresheaf J A`,
where it becomes restriction of presheaves along `I.op`, a limitwise operation.

For the second statement the point is that `toSheafify J P` is locally bijective for every
presheaf `P` on `C`.  For a presheaf restricted from `D` this is
`I.toSheafify_pullbackSheafificationCompatibility`, which identifies the restricted unit with
the unit of `(D, K)` whiskered by `I`, together with the fact that whiskering along a
continuous cocontinuous functor preserves local injectivity and local surjectivity.  A general
`P` is reduced to that case by the counit `I.op.ran.obj P ⟶ P` restricted along `I.op`, which is
an isomorphism because `I` is fully faithful.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sites

universe u₁ v₁ u₂ v₂ u₃ v₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (I : C ⥤ D) [I.Full] [I.Faithful] [I.IsLeftAdjoint]
  [I.IsContinuous J K] [I.IsCocontinuous J K]
  (A : Type u₃) [Category.{v₃} A] [HasFiniteLimits A]

omit [I.Full] [I.Faithful] [HasFiniteLimits A] in
/-- A left adjoint `I` makes `I.op` a right adjoint, so every structured arrow category over
`I.op` has an initial object and every presheaf on `C` has a pointwise right Kan extension
along `I.op`. -/
private theorem hasPointwiseRightKanExtension_op (F : Cᵒᵖ ⥤ A) :
    I.op.HasPointwiseRightKanExtension F := by
  intro X
  let : HasInitial (StructuredArrow X I.op) :=
    (isRightAdjoint_iff_hasInitial_structuredArrow.mp inferInstance) X
  infer_instance

include I in
/-- Sheafification of `A`-valued presheaves descends along a full, faithful, continuous and
cocontinuous left adjoint `I : C ⥤ D`: if it exists on `(D, K)` then it exists on `(C, J)`.

The left adjoint produced is right Kan extension along `I.op`, followed by sheafification on
`(D, K)`, followed by restriction of sheaves along `I`. -/
theorem hasSheafify_of_fullyFaithful_isLeftAdjoint [HasSheafify K A] : HasSheafify J A := by
  let := hasPointwiseRightKanExtension_op I A
  let E := I.op.ran (H := A)
  let R := I.sheafPushforwardContinuous A J K
  let L := E ⋙ presheafToSheaf K A ⋙ R
  let adjL : L ⊣ sheafToPresheaf J A :=
    ((sheafificationAdjunction K A).comp
        (I.sheafAdjunctionCocontinuous A J K)).restrictFullyFaithful
      (I.op.ranAdjunction A).fullyFaithfulROfIsIsoCounit
      (Functor.FullyFaithful.ofFullyFaithful (𝟭 _)) (Iso.refl _) (Iso.refl _)
  let : E.IsRightAdjoint := (I.op.ranAdjunction A).isRightAdjoint
  let : PreservesFiniteLimits R := ⟨fun T _ _ => by
    let : PreservesLimitsOfShape T (R ⋙ sheafToPresheaf J A) := by
      change PreservesLimitsOfShape T
        (sheafToPresheaf K A ⋙ (Functor.whiskeringLeft _ _ A).obj I.op)
      infer_instance
    exact preservesLimitsOfShape_of_reflects_of_preserves R (sheafToPresheaf J A)⟩
  let : PreservesFiniteLimits E := inferInstance
  let : PreservesFiniteLimits L := ⟨fun T _ _ =>
    comp_preservesLimitsOfShape E (presheafToSheaf K A ⋙ R)⟩
  exact HasSheafify.mk' J A adjL

variable {FA : A → A → Type*} {CA : A → Type*} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
  [ConcreteCategory A FA] [(forget A).ReflectsIsomorphisms] [J.HasSheafCompose (forget A)]

include I in
/-- The weak equivalences of `(C, J)` are the locally bijective morphisms as soon as those of
`(D, K)` are, for a full, faithful, continuous and cocontinuous left adjoint `I : C ⥤ D`.

By `CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.mk'` it suffices that the unit
`P ⟶ sheafify J P` be locally injective and locally surjective for every presheaf `P` on `C`. -/
theorem wEqualsLocallyBijective_of_fullyFaithful_isLeftAdjoint [HasSheafify K A]
    [K.WEqualsLocallyBijective A] : J.WEqualsLocallyBijective A := by
  let := hasPointwiseRightKanExtension_op I A
  let := hasSheafify_of_fullyFaithful_isLeftAdjoint J K I A
  -- For a presheaf restricted along `I`, the unit is the unit on `(D, K)` whiskered by `I`.
  have hrestrict (F : Dᵒᵖ ⥤ A) :
      Presheaf.IsLocallyInjective J (toSheafify J (I.op ⋙ F)) ∧
      Presheaf.IsLocallySurjective J (toSheafify J (I.op ⋙ F)) := by
    let t := ((I.pushforwardContinuousSheafificationCompatibility A J K).hom.app F).hom
    have h := I.toSheafify_pullbackSheafificationCompatibility A J K F
    exact ⟨(Presheaf.isLocallyInjective_comp_iff J _ t).mp
        (h ▸ Presheaf.isLocallyInjective_whisker J K I _),
      (Presheaf.isLocallySurjective_comp_iff J _ t).mp
        (h ▸ Presheaf.isLocallySurjective_whisker J K I _)⟩
  -- A general presheaf is reduced to that case by the counit of the Kan extension, which is an
  -- isomorphism because `I` is fully faithful.
  have hgeneral (P : Cᵒᵖ ⥤ A) :
      Presheaf.IsLocallyInjective J (toSheafify J P) ∧
      Presheaf.IsLocallySurjective J (toSheafify J P) := by
    let e := I.op.ranCounit.app P
    obtain ⟨hi, hs⟩ := hrestrict (I.op.ran.obj P)
    have he : e ≫ toSheafify J P =
        toSheafify J (I.op ⋙ I.op.ran.obj P) ≫ sheafifyMap J e :=
      toSheafify_naturality J e
    exact ⟨(Presheaf.comp_isLocallyInjective_iff J e _).mp (by rw [he]; infer_instance),
      (Presheaf.comp_isLocallySurjective_iff J e _).mp (by rw [he]; infer_instance)⟩
  let (P : Cᵒᵖ ⥤ A) : Presheaf.IsLocallyInjective J (toSheafify J P) := (hgeneral P).1
  let (P : Cᵒᵖ ⥤ A) : Presheaf.IsLocallySurjective J (toSheafify J P) := (hgeneral P).2
  exact GrothendieckTopology.WEqualsLocallyBijective.mk' J A

end Stacks.Sites

end
