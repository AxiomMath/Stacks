module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeIsoClasses

/-!
# A gerbe is a gerbe over the algebraic space of its isomorphism classes (Stacks 06QD)

Let `𝒳` be an algebraic stack over `S` which is a gerbe. Then the fppf sheafification of the
presheaf

`U ↦ Ob(𝒳_U)/≅`

on the big fppf site of `S` is an algebraic space `F`, and `𝒳` is a gerbe over `F`. This is
**Stacks 06QD**.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_isGerbeOver_isoClassSpace`: **Stacks 06QD**,
  `𝒳` is a gerbe over the algebraic space sheafifying its isomorphism classes.

## Implementation notes

As in `AlgebraicGeometry.Stack.AlgebraicStacks.IsGerbe` (**Stacks 06QC**), being a gerbe *over an
algebraic space* `F` is expressed through an algebraic stack `𝒴` represented by `F` in the sense
of `AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpace` (**Stacks 04SV**): an equivalence
`E`, over the big fppf site of `S`, between `𝒴` and the category of elements of `F`, together
with a 1-morphism `g : 𝒳 ⟶ 𝒴` making `𝒳` a gerbe over `𝒴`. The statement keeps the
representing equivalence `E` itself, with the *same* `F` that is identified with the
sheafification, so `𝒴` is the algebraic space `F` and not merely some algebraic stack with the
right isomorphism classes.

The identification of the sheafification with `F` is pinned down by the last clause: the
sheafification unit, read in `F` through `e`, sends the class of an object `x` of `𝒳_U` to the
section of `F` over `U` named, through `E`, by the class of `g(x)`
(`CategoryTheory.PresheafOfCategories.elementsIsoClassEquiv`). The universe lift is needed
because isomorphism classes of the fibres of an algebraic stack live one universe above the
values of an algebraic space.

The proof is that of
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_algebraicSpace_isGerbeOver_isoClasses`, which
already builds its comparison from the representing equivalence: the map on isomorphism classes
induced by a gerbe is locally injective and locally surjective, so the induced map out of the
sheafification is a locally bijective map of sheaves, hence an isomorphism.

## References

* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
* [Stacks Project, Tag 06QC](https://stacks.math.columbia.edu/tag/06QC)
* [Stacks Project, Tag 06QD](https://stacks.math.columbia.edu/tag/06QD)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06QD.** If an algebraic stack `𝒳` over `S` is a gerbe, then the fppf sheafification
of the presheaf `U ↦ Ob(𝒳_U)/≅` is (the universe lift of) an algebraic space `F`, and `𝒳` is a
gerbe over `F`: there are an algebraic stack `𝒴` represented by `F` through an equivalence `E`
over the site (Stacks 04SV) and a 1-morphism `g : 𝒳 ⟶ 𝒴` making `𝒳` a gerbe over `𝒴`, such that
the sheafification unit sends the class of `x` to the section of `F` named by the class of
`g(x)`. -/
@[stacks 06QD]
theorem exists_isGerbeOver_isoClassSpace
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsGerbe B S hS 𝒳) :
    letI : 𝒳.val.val.p.IsFibered := (CatFiberedInGroupoids.isFiberedInGroupoids 𝒳.val).isFibered
    ∃ F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS F ∧
      ∃ (e : F ⋙ uliftFunctor.{u + 1} ≅ sheafifiedIsoClasses B S hS 𝒳)
        (𝒴 : Stack.AlgebraicStacks.{u, w} B S hS)
        (E : StacksRepresentableCFG.EquivalenceOver
          𝒴.val.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
        (g : 𝒳 ⟶ 𝒴), IsGerbeOver B S hS g ∧
          letI : 𝒴.val.val.p.IsFibered :=
            (CatFiberedInGroupoids.isFiberedInGroupoids 𝒴.val).isFibered
          ∀ (U : (BigFppfOver B S hS)ᵒᵖ) (c : (isoClassPresheaf B S hS 𝒳).obj U),
            e.inv.app U (((BigFppfOver.topology B S hS).toSheafify
              (isoClassPresheaf B S hS 𝒳)).app U c) =
              ULift.up (PresheafOfCategories.elementsIsoClassEquiv F E U.unop
                ((Functor.isoClassMap (Functor.isFibredOneMorphism_of_isFiberedInGroupoids
                  (CatFiberedInGroupoids.isFiberedInGroupoids 𝒴.val)
                  (CatFiberedInGroupoids.homFunctor_comp_p g.hom))).app U c)) := by
  classical
  obtain ⟨𝒴, hrep, g, hG⟩ := h𝒳
  obtain ⟨F, hF, ⟨E⟩⟩ := hrep
  let : 𝒳.val.val.p.IsFibered := (CatFiberedInGroupoids.isFiberedInGroupoids 𝒳.val).isFibered
  have h𝒴 : 𝒴.val.val.p.IsFiberedInGroupoids := CatFiberedInGroupoids.isFiberedInGroupoids 𝒴.val
  let : 𝒴.val.val.p.IsFibered := h𝒴.isFibered
  set J := BigFppfOver.topology B S hS
  -- the identification of the isomorphism classes of `𝒴` with `F`, through `E`
  let equiv := fun U : (BigFppfOver B S hS)ᵒᵖ =>
    PresheafOfCategories.elementsIsoClassEquiv F E U.unop
  let eY : 𝒴.val.val.p.isoClassPresheaf ≅ F ⋙ uliftFunctor.{u + 1} :=
    NatIso.ofComponents
      (fun U => Equiv.toIso
        { toFun := fun c => ULift.up (equiv U c)
          invFun := fun c => (equiv U).symm c.down
          left_inv := fun c => by simp
          right_inv := fun ⟨x⟩ => congrArg ULift.up ((equiv U).apply_symm_apply x) })
      (fun k => by
        ext c
        exact congrArg ULift.up
          (PresheafOfCategories.elementsIsoClassEquiv_naturality h𝒴 F E k.unop c))
  -- the map on isomorphism classes induced by the gerbe, landing in `F`
  let hmG := Functor.isFibredOneMorphism_of_isFiberedInGroupoids h𝒴
    (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
  let a : isoClassPresheaf B S hS 𝒳 ⟶ F ⋙ uliftFunctor.{u + 1} :=
    Functor.isoClassMap hmG ≫ eY.hom
  have : Presheaf.IsLocallyInjective J a := by
    have : Presheaf.IsLocallyInjective J (Functor.isoClassMap hmG) :=
      IsGerbeOver.isLocallyInjective_isoClassMap hG hmG
    infer_instance
  have : Presheaf.IsLocallySurjective J a := by
    have : Presheaf.IsLocallySurjective J (Functor.isoClassMap hmG) :=
      IsGerbeOver.isLocallySurjective_isoClassMap hG hmG
    infer_instance
  -- an algebraic space is a sheaf, and so is its universe lift
  have hFsheaf : Presheaf.IsSheaf J (F ⋙ uliftFunctor.{u + 1}) :=
    (isSheaf_iff_isSheaf_of_type J (F ⋙ uliftFunctor.{u + 1})).2
      (Presieve.isSheaf_comp_uliftFunctor J ((isSheaf_iff_isSheaf_of_type J F).1 hF.isSheaf))
  let lift := J.sheafifyLift a hFsheaf
  have hfac : J.toSheafify (isoClassPresheaf B S hS 𝒳) ≫ lift = a :=
    J.toSheafify_sheafifyLift a hFsheaf
  have : IsIso lift :=
    isIso_sheafifyLift_of_isLocallyInjective_of_isLocallySurjective B S hS a hFsheaf
  exact ⟨F, hF, (asIso lift).symm, 𝒴, E, g, hG, fun U c =>
    ConcreteCategory.congr_hom (NatTrans.congr_app hfac U) c⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
