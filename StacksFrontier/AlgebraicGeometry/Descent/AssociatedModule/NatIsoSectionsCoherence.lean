module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.LocalComparisonPseudonaturalProofCocycle
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.PseudonaturalityClosure

/-!
# Mates on the side of the right adjoints: the counit criterion and the pentagon

`CategoryTheory.conjugateIsoEquiv` is the bijection between isomorphisms of left adjoints and
isomorphisms of the corresponding right adjoints. This file gives a criterion identifying the mate
of an isomorphism of left adjoints with a given isomorphism of right adjoints, computes the mate of
a three-step composite of comparisons factor by factor, and states the pentagon of
`Stacks.Mates.trans_assoc_of_conjugate` with its four mates replaced by given isomorphisms of
right adjoints.

## Main results

* `Stacks.Mates.conjugateIsoEquiv_eq_of_whiskerRight_counit`: **an isomorphism of right adjoints
  compatible with the counits is the mate.** For `adj₁ : L₁ ⊣ R₁`, `adj₂ : L₂ ⊣ R₂`, `α : L₂ ≅ L₁`
  and `β : R₁ ≅ R₂`, if `whiskerRight β.hom L₂ ≫ adj₂.counit = whiskerLeft R₁ α.hom ≫ adj₁.counit`
  as natural transformations `R₁ ⋙ L₂ ⟶ 𝟭`, then `β` is the mate of `α`.
* `Stacks.Mates.conjugateIsoEquiv_threeStep`: **the mate of a three-step route, distributed factor
  by factor.** The comparison that contracts `p ⋙ (A₁ ⋙ EU)` to `A₀ ⋙ ET'` through an
  associator, a whiskering of `NT`, a second associator and a whiskering of `c` has as mate the
  corresponding composite of the mates of `c` and of `NT`.
* `Stacks.Mates.trans_assoc_of_conjugate_of_mates`: **the pentagon for three composable left
  adjoints, with the four mates given explicitly.** This is
  `Stacks.Mates.trans_assoc_of_conjugate` with each of its four mates replaced by an isomorphism
  of right adjoints it is assumed to be equal to.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₀ v₁ v₂ v₃ v₄ v₅ u₀ u₁ u₂ u₃ u₄ u₅

namespace Stacks.Mates

/-! ### The counit criterion for a mate -/

section Counit

variable {C₀ : Type u₀} {C₁ : Type u₁} [Category.{v₀} C₀] [Category.{v₁} C₁]


/-- **An isomorphism of right adjoints compatible with the counits is the mate**, in the form that
mentions no object of either category: if
`whiskerRight β.hom L₂ ≫ adj₂.counit = whiskerLeft R₁ α.hom ≫ adj₁.counit`, then
`conjugateIsoEquiv adj₁ adj₂ α = β`. -/
public theorem conjugateIsoEquiv_eq_of_whiskerRight_counit {L₁ L₂ : C₀ ⥤ C₁} {R₁ R₂ : C₁ ⥤ C₀}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ≅ L₁) (β : R₁ ≅ R₂)
    (h : Functor.whiskerRight β.hom L₂ ≫ adj₂.counit =
      Functor.whiskerLeft R₁ α.hom ≫ adj₁.counit) :
    conjugateIsoEquiv adj₁ adj₂ α = β :=
  conjugateIsoEquiv_eq_of_counit adj₁ adj₂ α β fun X => by
    simpa using NatTrans.congr_app h X

end Counit

/-! ### The pentagon with its mates substituted -/

section Pentagon

variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  {D₀ : Type u₄} {D₁ : Type u₅}
  [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  [Category.{v₄} D₀] [Category.{v₅} D₁]
  {p : C₀ ⥤ C₁} {pR : C₁ ⥤ C₀} {q : C₁ ⥤ C₂} {qR : C₂ ⥤ C₁} {r : C₀ ⥤ C₂} {rR : C₂ ⥤ C₀}
  {A₂ : C₂ ⥤ C₃} {R₂ : C₃ ⥤ C₂} {A₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀} {A₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁}
  {ET : D₀ ⥤ D₁} {GT : D₁ ⥤ D₀} {EU : D₁ ⥤ C₃} {GU : C₃ ⥤ D₁}
  {ET' : D₀ ⥤ C₃} {GT' : C₃ ⥤ D₀}

/-- **The mate of a three-step route, distributed factor by factor.**  Let `p`, `A₁`, `EU` be
composable left adjoints, let `A₀ ⊣ R₀`, `ET ⊣ GT` and `ET' ⊣ GT'` be three further adjunctions,
let `NT : p ⋙ A₁ ≅ A₀ ⋙ ET` and `c : ET ⋙ EU ≅ ET'`.  The comparison

    `p ⋙ (A₁ ⋙ EU) ≅ (p ⋙ A₁) ⋙ EU ≅ (A₀ ⋙ ET) ⋙ EU ≅ A₀ ⋙ (ET ⋙ EU) ≅ A₀ ⋙ ET'`

assembled from the two associators, `NT` whiskered on the right and `c` whiskered on the left has
as mate the composite of the mate of `c` whiskered by `R₀`, an associator, the mate of `NT`
whiskered by `GU`, and the inverse of an associator. -/
public theorem conjugateIsoEquiv_threeStep
    (adjp : p ⊣ pR) (adjA₀ : A₀ ⊣ R₀) (adjA₁ : A₁ ⊣ R₁)
    (adjT : ET ⊣ GT) (adjU : EU ⊣ GU) (adjT' : ET' ⊣ GT')
    (NT : p ⋙ A₁ ≅ A₀ ⋙ ET) (c : ET ⋙ EU ≅ ET') :
    conjugateIsoEquiv (adjA₀.comp adjT') (adjp.comp (adjA₁.comp adjU))
        ((Functor.associator p A₁ EU).symm ≪≫
          Functor.isoWhiskerRight NT EU ≪≫
            Functor.associator A₀ ET EU ≪≫ Functor.isoWhiskerLeft A₀ c) =
      Functor.isoWhiskerRight (conjugateIsoEquiv adjT' (adjT.comp adjU) c) R₀ ≪≫
        Functor.associator GU GT R₀ ≪≫
          Functor.isoWhiskerLeft GU
              (conjugateIsoEquiv (adjA₀.comp adjT) (adjp.comp adjA₁) NT) ≪≫
            (Functor.associator GU R₁ pR).symm := by
  refine Eq.trans (Eq.trans (conjugateIsoEquiv_trans _ ((adjp.comp adjA₁).comp adjU) _ _ _)
    (congrArg₂ (fun a b => a ≪≫ b)
      (Eq.trans (conjugateIsoEquiv_trans _ ((adjA₀.comp adjT).comp adjU) _ _ _)
        (congrArg₂ (fun a b => a ≪≫ b)
          (Eq.trans (conjugateIsoEquiv_trans _ (adjA₀.comp (adjT.comp adjU)) _ _ _)
            (congrArg₂ (fun a b => a ≪≫ b)
              (conjugateIsoEquiv_isoWhiskerLeft adjT' (adjT.comp adjU) adjA₀ c)
              (Iso.ext (conjugateEquiv_associator_hom adjA₀ adjT adjU))))
          (conjugateIsoEquiv_isoWhiskerRight (adjA₀.comp adjT) (adjp.comp adjA₁) adjU NT)))
      (Eq.trans (conjugateIsoEquiv_iso_symm _ _ _)
        (congrArg Iso.symm
          (Iso.ext (conjugateEquiv_associator_hom adjp adjA₁ adjU)))))) ?_
  exact Eq.trans (Iso.trans_assoc _ _ _) (Iso.trans_assoc _ _ _)

/-- **The pentagon for three composable left adjoints, with the four mates given explicitly.**
This is `Stacks.Mates.trans_assoc_of_conjugate` with each of its four mates replaced by an
isomorphism of right adjoints that it has been computed to equal: `mP` for the contraction of the
iterated left adjoint `p ⋙ q`, `nT`, `nU` and `nT'` for the three comparisons of the shape
`p ⋙ A₁ ≅ A₀ ⋙ ET`, and `mc` for the contraction `ET ⋙ EU ≅ ET'`.  Granted the pentagon between
those five explicit isomorphisms, the long route round the square agrees with the short one. -/
public theorem trans_assoc_of_conjugate_of_mates
    (adjp : p ⊣ pR) (adjq : q ⊣ qR) (adjr : r ⊣ rR)
    (adjA₀ : A₀ ⊣ R₀) (adjA₁ : A₁ ⊣ R₁) (adjA₂ : A₂ ⊣ R₂)
    (adjT : ET ⊣ GT) (adjU : EU ⊣ GU) (adjT' : ET' ⊣ GT')
    (P : p ⋙ q ≅ r) (NT : p ⋙ A₁ ≅ A₀ ⋙ ET) (NU : q ⋙ A₂ ≅ A₁ ⋙ EU)
    (NT' : r ⋙ A₂ ≅ A₀ ⋙ ET') (c : ET ⋙ EU ≅ ET')
    {mP : rR ≅ qR ⋙ pR} {nT : GT ⋙ R₀ ≅ R₁ ⋙ pR} {nU : GU ⋙ R₁ ≅ R₂ ⋙ qR}
    {nT' : GT' ⋙ R₀ ≅ R₂ ⋙ rR} {mc : GT' ≅ GU ⋙ GT}
    (hP : conjugateIsoEquiv adjr (adjp.comp adjq) P = mP)
    (hNT : conjugateIsoEquiv (adjA₀.comp adjT) (adjp.comp adjA₁) NT = nT)
    (hNU : conjugateIsoEquiv (adjA₁.comp adjU) (adjq.comp adjA₂) NU = nU)
    (hNT' : conjugateIsoEquiv (adjA₀.comp adjT') (adjr.comp adjA₂) NT' = nT')
    (hc : conjugateIsoEquiv adjT' (adjT.comp adjU) c = mc)
    (hpent : Functor.isoWhiskerLeft R₂ mP.symm ≪≫ nT'.symm =
      (Functor.associator R₂ qR pR).symm ≪≫
        Functor.isoWhiskerRight nU.symm pR ≪≫
          (Functor.isoWhiskerRight mc R₀ ≪≫ Functor.associator GU GT R₀ ≪≫
            Functor.isoWhiskerLeft GU nT ≪≫ (Functor.associator GU R₁ pR).symm).symm) :
    (Functor.isoWhiskerRight P A₂).symm ≪≫
        Functor.associator p q A₂ ≪≫
          Functor.isoWhiskerLeft p NU ≪≫
            ((Functor.associator p A₁ EU).symm ≪≫
              Functor.isoWhiskerRight NT EU ≪≫
                Functor.associator A₀ ET EU ≪≫ Functor.isoWhiskerLeft A₀ c) = NT' := by
  subst hP
  subst hNT
  subst hNU
  subst hNT'
  subst hc
  refine trans_assoc_of_conjugate adjp adjq adjA₂ adjr (adjA₁.comp adjU) (adjA₀.comp adjT')
    P NU _ NT' ?_
  refine Eq.trans hpent ?_
  exact congrArg (fun x => (Functor.associator R₂ qR pR).symm ≪≫
      Functor.isoWhiskerRight _ pR ≪≫ x)
    (congrArg Iso.symm
      (conjugateIsoEquiv_threeStep adjp adjA₀ adjA₁ adjT adjU adjT' NT c).symm)

end Pentagon

end Stacks.Mates

end
