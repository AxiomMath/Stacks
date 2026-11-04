module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Gerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategory
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElementsEquivalence
public import StacksFrontier.CategoryTheory.Sites.Gerbe.IsoClasses
public import StacksFrontier.CategoryTheory.Sites.Sheafification.InjectiveSurjective

/-!
# The algebraic space of isomorphism classes of a gerbe (Stacks 06QD)

Let `𝒳` be an algebraic stack over `S` which is a gerbe. Then the fppf sheafification of the
presheaf

`U ↦ Ob(𝒳_U)/≅`

on the big fppf site of `S` is an algebraic space, and `𝒳` is a gerbe over it. This is
**Stacks 06QD**.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.isoClassPresheaf`: the presheaf of isomorphism classes
  of objects of the fibres of an algebraic stack.
* `AlgebraicGeometry.Stack.AlgebraicStacks.sheafifiedIsoClasses`: its fppf sheafification.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_algebraicSpace_isGerbeOver_isoClasses`:
  **Stacks 06QD**.

## Implementation notes

Being a gerbe gives an algebraic stack `𝒴` representable by an algebraic space `F` and a
1-morphism `g : 𝒳 ⟶ 𝒴` making `𝒳` a gerbe over `𝒴` (**Stacks 06QC**). The statement produced
here keeps that `𝒴` and `g`, and adds the two things which say that `𝒴` *is* the sheafification
of the isomorphism classes of `𝒳`: an isomorphism `eY` identifying the presheaf of isomorphism
classes of `𝒴` with `F` — which is already a sheaf, being an algebraic space — and the equation
saying that the map on isomorphism classes induced by `g`, read through `eY`, is the unit of the
sheafification. Without the last clause the statement would only say that `𝒳` is a gerbe over
*some* algebraic space, which is the hypothesis rather than the conclusion.

The isomorphism `eY` is `CategoryTheory.PresheafOfCategories.elementsIsoClassEquiv`, the
identification of the isomorphism classes of the fibres of a category fibred in setoids with the
values of a presheaf representing it, assembled into a natural isomorphism with its naturality
lemma and composed with the universe lift, which is needed because isomorphism classes of the
fibres of an algebraic stack live one universe above the values of an algebraic space.

That the sheafification unit factors through `eY` is the only real step, and it is local
bijectivity: the map on isomorphism classes induced by a gerbe is locally injective and locally
surjective
(`CategoryTheory.IsGerbeOver.isLocallyInjective_isoClassMap` and
`...isLocallySurjective_isoClassMap`), so the induced map out of the sheafification is locally
bijective between two sheaves, hence an isomorphism
(`CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`).

## References

* [Stacks Project, Tag 06QC](https://stacks.math.columbia.edu/tag/06QC)
* [Stacks Project, Tag 06QD](https://stacks.math.columbia.edu/tag/06QD)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The presheaf `U ↦ Ob(𝒳_U)/≅` of isomorphism classes of objects of the fibres of an algebraic
stack over `S`. -/
noncomputable abbrev isoClassPresheaf (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) :=
  letI : 𝒳.val.val.p.IsFibered := (CatFiberedInGroupoids.isFiberedInGroupoids 𝒳.val).isFibered
  𝒳.val.val.p.isoClassPresheaf

/-- The fppf sheafification of the presheaf of isomorphism classes of an algebraic stack. -/
noncomputable abbrev sheafifiedIsoClasses (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) :=
  (BigFppfOver.topology B S hS).sheafify (isoClassPresheaf B S hS 𝒳)

/-- A locally injective and locally surjective map of presheaves on the big fppf site into a sheaf
induces an isomorphism out of the sheafification. -/
lemma isIso_sheafifyLift_of_isLocallyInjective_of_isLocallySurjective
    {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (a : P ⟶ Q)
    (hQ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Q)
    [Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS) a]
    [Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) a] :
    IsIso ((BigFppfOver.topology B S hS).sheafifyLift a hQ) := by
  let J := BigFppfOver.topology B S hS
  have hfac := J.toSheafify_sheafifyLift a hQ
  let liftSh : (⟨J.sheafify P, J.sheafify_isSheaf P⟩ : Sheaf J (Type (u + 1))) ⟶ ⟨Q, hQ⟩ :=
    ObjectProperty.homMk (J.sheafifyLift a hQ)
  have : IsIso liftSh := (Sheaf.isLocallyBijective_iff_isIso liftSh).mp
    ⟨Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J a hfac,
      Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac⟩
  exact inferInstanceAs (IsIso ((sheafToPresheaf J (Type (u + 1))).map liftSh))

/-- **Stacks 06QD.** If an algebraic stack `𝒳` over `S` is a gerbe, then the fppf sheafification
of the presheaf `U ↦ Ob(𝒳_U)/≅` is (the universe lift of) an algebraic space `F`, and `𝒳` is a
gerbe over the algebraic stack `𝒴` representable by `F` by a 1-morphism inducing the unit of the
sheafification on isomorphism classes. -/
@[stacks 06QD]
theorem exists_algebraicSpace_isGerbeOver_isoClasses (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsGerbe B S hS 𝒳) :
    letI : 𝒳.val.val.p.IsFibered := (CatFiberedInGroupoids.isFiberedInGroupoids 𝒳.val).isFibered
    ∃ F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS F ∧
      ∃ (e : F ⋙ uliftFunctor.{u + 1} ≅ sheafifiedIsoClasses B S hS 𝒳)
        (𝒴 : Stack.AlgebraicStacks.{u, w} B S hS) (g : 𝒳 ⟶ 𝒴), IsGerbeOver B S hS g ∧
          letI : 𝒴.val.val.p.IsFibered :=
            (CatFiberedInGroupoids.isFiberedInGroupoids 𝒴.val).isFibered
          ∃ eY : 𝒴.val.val.p.isoClassPresheaf ≅ F ⋙ uliftFunctor.{u + 1},
            Functor.isoClassMap (Functor.isFibredOneMorphism_of_isFiberedInGroupoids
              (CatFiberedInGroupoids.isFiberedInGroupoids 𝒴.val)
              (CatFiberedInGroupoids.homFunctor_comp_p g.hom)) ≫ eY.hom ≫ e.hom =
              (BigFppfOver.topology B S hS).toSheafify (isoClassPresheaf B S hS 𝒳) := by
  classical
  obtain ⟨𝒴, ⟨F, hF, ⟨E⟩⟩, g, hG⟩ := h𝒳
  let : 𝒳.val.val.p.IsFibered := (CatFiberedInGroupoids.isFiberedInGroupoids 𝒳.val).isFibered
  have h𝒴 : 𝒴.val.val.p.IsFiberedInGroupoids := CatFiberedInGroupoids.isFiberedInGroupoids 𝒴.val
  let : 𝒴.val.val.p.IsFibered := h𝒴.isFibered
  let J := BigFppfOver.topology B S hS
  -- the identification of the isomorphism classes of `𝒴` with `F`
  let eY : 𝒴.val.val.p.isoClassPresheaf ≅ F ⋙ uliftFunctor.{u + 1} :=
    NatIso.ofComponents
      (fun U => ((PresheafOfCategories.elementsIsoClassEquiv F E U.unop).trans
        Equiv.ulift.symm).toIso)
      (fun k => by
        ext c
        exact congrArg ULift.up
          (PresheafOfCategories.elementsIsoClassEquiv_naturality h𝒴 F E k.unop c))
  -- the map on isomorphism classes induced by the gerbe, landing in `F`
  let hmG := Functor.isFibredOneMorphism_of_isFiberedInGroupoids h𝒴
    (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
  let a : isoClassPresheaf B S hS 𝒳 ⟶ F ⋙ uliftFunctor.{u + 1} := Functor.isoClassMap hmG ≫ eY.hom
  have : Presheaf.IsLocallyInjective J a := by
    have := IsGerbeOver.isLocallyInjective_isoClassMap hG hmG
    infer_instance
  have : Presheaf.IsLocallySurjective J a := by
    have := IsGerbeOver.isLocallySurjective_isoClassMap hG hmG
    infer_instance
  -- an algebraic space is a sheaf, and so is its universe lift
  have hFsheaf : Presheaf.IsSheaf J (F ⋙ uliftFunctor.{u + 1}) :=
    (isSheaf_iff_isSheaf_of_type J (F ⋙ uliftFunctor.{u + 1})).2
      (Presieve.isSheaf_comp_uliftFunctor J ((isSheaf_iff_isSheaf_of_type J F).1 hF.isSheaf))
  have := isIso_sheafifyLift_of_isLocallyInjective_of_isLocallySurjective B S hS a hFsheaf
  refine ⟨F, hF, (asIso (J.sheafifyLift a hFsheaf)).symm, 𝒴, g, hG, eY, ?_⟩
  rw [Iso.symm_hom, asIso_inv, ← Category.assoc, IsIso.comp_inv_eq]
  exact (J.toSheafify_sheafifyLift a hFsheaf).symm

end AlgebraicGeometry.Stack.AlgebraicStacks

end
