module

public import StacksFrontier.CategoryTheory.FiberedCategory.RelocalizeAsElements
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceBaseChangePresheaf
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverCompositeSnd

/-!
# The base change of a composite along a point, as a morphism of relocalized presheaves

Let `C` be a category, let `u : Uo ⟶ X` be a morphism of `C`, let `𝒳`, `𝒴`, `𝒵` be categories
over the slice `C/X` and let `f : 𝒳 ⥤ 𝒴`, `g : 𝒴 ⥤ 𝒵` be 1-morphisms over `C/X`. Fix a point
`z : C/Uo ⥤ 𝒵` of `𝒵` with values in `Uo`, and presheaves `Fp`, `Gq` on `C/Uo` representing,
over `C/Uo`, the two base changes

```text
  Uo ×_{z, 𝒵, f ⋙ g} 𝒳        and        Uo ×_{z, 𝒵, g} 𝒴 .
```

This file produces the **comparison morphism of the relocalized presheaves**

```text
  α : Λ_u Fp ⟶ Λ_u Gq      over      h_{Uo → X},
```

and shows that its fibre over *any* section `β` of `Λ_u Gq` over a representable `A → X` is
again a relocalization — of a presheaf on `C/A` which represents the base change of `f` alone
along a point of `𝒴` with values in `A`.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.splitSndProjection`: the 1-morphism
  `𝒰 ×_{z, 𝒵, f ⋙ g} 𝒳 ⥤ 𝒰 ×_{z, 𝒵, g} 𝒴` that `f` induces on two base changes along one point.
* `CategoryTheory.PresheafOfCategories.relocalizeBasedFunctor`: a 1-morphism `El H ⥤ El H'` over
  `C/A`, relocalized to a 1-morphism `El (Λ_a H) ⥤ El (Λ_a H')` over `C/X`.
* `CategoryTheory.PresheafOfCategories.relocalizeNatTrans`: the morphism of presheaves
  `Λ_a H ⟶ Λ_a H'` it underlies.
* `CategoryTheory.PresheafOfCategories.baseChangeElementsMap` and
  `CategoryTheory.PresheafOfCategories.baseChangeNatTrans`: the comparison `α`, first as a
  1-morphism of categories of elements over `C/Uo` and then as a morphism of presheaves on
  `C/X`.
* `CategoryTheory.PresheafOfCategories.PointwiseEquiv.toIso` and
  `CategoryTheory.PresheafOfCategories.isoOfEquivalenceOver`: two presheaves of sets whose
  categories of elements are both equivalent, over the base, to one and the same category are
  isomorphic.

## Main results

* `CategoryTheory.PresheafOfCategories.relocalizeNatTrans_comp_relocalizeToYoneda` and
  `CategoryTheory.PresheafOfCategories.baseChangeNatTrans_comp_relocalizeToYoneda`: those
  morphisms are morphisms **over** the representable presheaf of the smaller base.
* `CategoryTheory.PresheafOfCategories.exists_isPullback_baseChangeNatTrans`: the fibre of `α`
  over a representable section is the relocalization of a presheaf representing the base change
  of `f` alone.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits CategoryTheory.OverShriek

namespace CategoryTheory

universe v u v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

namespace Over

variable {C : Type u} [Category.{v} C]

/-- Two objects of a slice category that are equal have the same structure morphism, read
through the identification of their underlying objects. -/
theorem eqToHom_comp_hom {Z : C} {W W' : Over Z} (h : W = W') (p : W'.left = W.left) :
    eqToHom p ≫ W.hom = W'.hom := by
  subst h
  rw [eqToHom_refl, Category.id_comp]

end Over

namespace TwoFibreProductOver

variable {𝒞 : Type u} [Category.{v} 𝒞] {𝒰 : Type u₁} [Category.{v₁} 𝒰]
  {𝒳 : Type u₂} [Category.{v₂} 𝒳] {𝒴 : Type u₃} [Category.{v₃} 𝒴]
  {𝒵 : Type u₄} [Category.{v₄} 𝒵]

/-- The 1-morphism `𝒰 ×_{z, 𝒵, f ⋙ g} 𝒳 ⥤ 𝒰 ×_{z, 𝒵, g} 𝒴` over `𝒞` that `f` induces on the
two base changes along one point `z` of `𝒵`, namely `(W, w, x, φ) ↦ (W, w, f x, φ)`: it is the
decomposition `CategoryTheory.TwoFibreProductOver.splitSnd` followed by the projection onto the
intermediate factor. -/
abbrev splitSndProjection (p𝒰 : 𝒰 ⥤ 𝒞) (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒵 : 𝒵 ⥤ 𝒞) (z : 𝒰 ⥤ 𝒵)
    (f : 𝒳 ⥤ 𝒴) (g : 𝒴 ⥤ 𝒵) (hf : f ⋙ p𝒴 = p𝒳) :
    TwoFibreProductOver p𝒰 p𝒳 p𝒵 z (f ⋙ g) ⥤ TwoFibreProductOver p𝒰 p𝒴 p𝒵 z g :=
  splitSnd p𝒰 p𝒳 p𝒴 p𝒵 z f g hf ⋙
    fst (structureFunctor p𝒰 p𝒴 p𝒵 z g) p𝒳 p𝒴 (snd p𝒰 p𝒴 p𝒵 z g) f

/-- `CategoryTheory.TwoFibreProductOver.splitSndProjection` is strictly over the first
factor. -/
theorem splitSndProjection_comp_fst (p𝒰 : 𝒰 ⥤ 𝒞) (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒵 : 𝒵 ⥤ 𝒞)
    (z : 𝒰 ⥤ 𝒵) (f : 𝒳 ⥤ 𝒴) (g : 𝒴 ⥤ 𝒵) (hf : f ⋙ p𝒴 = p𝒳) :
    splitSndProjection p𝒰 p𝒳 p𝒴 p𝒵 z f g hf ⋙ fst p𝒰 p𝒴 p𝒵 z g =
      fst p𝒰 p𝒳 p𝒵 z (f ⋙ g) :=
  splitSnd_comp_fst_comp_fst p𝒰 p𝒳 p𝒴 p𝒵 z f g hf

/-- `CategoryTheory.TwoFibreProductOver.splitSndProjection` is strictly over `𝒞`. -/
theorem splitSndProjection_comp_structureFunctor (p𝒰 : 𝒰 ⥤ 𝒞) (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞)
    (p𝒵 : 𝒵 ⥤ 𝒞) (z : 𝒰 ⥤ 𝒵) (f : 𝒳 ⥤ 𝒴) (g : 𝒴 ⥤ 𝒵) (hf : f ⋙ p𝒴 = p𝒳) :
    splitSndProjection p𝒰 p𝒳 p𝒴 p𝒵 z f g hf ⋙ structureFunctor p𝒰 p𝒴 p𝒵 z g =
      structureFunctor p𝒰 p𝒳 p𝒵 z (f ⋙ g) :=
  calc splitSndProjection p𝒰 p𝒳 p𝒴 p𝒵 z f g hf ⋙ structureFunctor p𝒰 p𝒴 p𝒵 z g
      = splitSnd p𝒰 p𝒳 p𝒴 p𝒵 z f g hf ⋙
          (fst (structureFunctor p𝒰 p𝒴 p𝒵 z g) p𝒳 p𝒴 (snd p𝒰 p𝒴 p𝒵 z g) f ⋙
            structureFunctor p𝒰 p𝒴 p𝒵 z g) := rfl
    _ = splitSnd p𝒰 p𝒳 p𝒴 p𝒵 z f g hf ⋙
          structureFunctor (structureFunctor p𝒰 p𝒴 p𝒵 z g) p𝒳 p𝒴
            (snd p𝒰 p𝒴 p𝒵 z g) f := by rw [fst_comp_eq]
    _ = structureFunctor p𝒰 p𝒳 p𝒵 z (f ⋙ g) :=
          splitSnd_comp_structureFunctor p𝒰 p𝒳 p𝒴 p𝒵 z f g hf

end TwoFibreProductOver

namespace PresheafOfCategories

section Slice

variable {C : Type u} [Category.{v} C] {X A : C} (a : A ⟶ X)

/-- The factorization through `A` carried by the element of `Λ_a P` named by an object of the
category of elements lying over `V`: it is the one the object itself carries, read through the
identification of base objects. -/
theorem elementOf_relocalize_fst {P : (Over A)ᵒᵖ ⥤ Type v}
    {Y : (presheafOfCategories ((relocalizePresheafFunctor a).obj P ⋙ typeToCat)).obj}
    {V : Over X} (h : Y.base = V) :
    (elementOf ((relocalizePresheafFunctor a).obj P) h).1.1 =
      eqToHom (congrArg Over.left h).symm ≫ Y.fiber.as.1.1 := by
  subst h
  rw [eqToHom_refl, Category.id_comp]
  rfl

section Relocalize

variable {H H' : (Over A)ᵒᵖ ⥤ Type v}
  (mid : (presheafOfCategories (H ⋙ typeToCat)).obj ⥤
    (presheafOfCategories (H' ⋙ typeToCat)).obj)
  (hmid : mid ⋙ discreteProjection H' = discreteProjection H)

/-- A 1-morphism `El H ⥤ El H'` over `C/A`, relocalized along `a` to a 1-morphism
`El (Λ_a H) ⥤ El (Λ_a H')` over `C/X`: read a section of `Λ_a H` as a section of `H` over the
object of `C/A` its factorization names, apply the 1-morphism, and read the result back. -/
abbrev relocalizeBasedFunctor :
    (presheafOfCategories ((relocalizePresheafFunctor a).obj H ⋙ typeToCat)).obj ⥤
      (presheafOfCategories ((relocalizePresheafFunctor a).obj H' ⋙ typeToCat)).obj :=
  elementsToRelocalize a H ⋙ mid ⋙ relocalizeToElements a H'

/-- Relocalizing a functor out of `El H` that is strictly over `C/A` through a functor to `C/A`
gives a functor strictly over `C/X`. -/
private theorem elementsToRelocalize_comp_comp_overMap {𝒟 : Type u₁} [Category.{v₁} 𝒟]
    (K : (presheafOfCategories (H ⋙ typeToCat)).obj ⥤ 𝒟) (q : 𝒟 ⥤ Over A)
    (hK : K ⋙ q = discreteProjection H) :
    elementsToRelocalize a H ⋙ K ⋙ q ⋙ Over.map a =
      discreteProjection ((relocalizePresheafFunctor a).obj H) := by
  rw [← Functor.assoc K, hK]
  exact elementsToRelocalize_comp_eq a H

include hmid in
/-- The relocalized 1-morphism is strictly over `C/X`. -/
theorem relocalizeBasedFunctor_comp_eq :
    relocalizeBasedFunctor a mid ⋙
        discreteProjection ((relocalizePresheafFunctor a).obj H') =
      discreteProjection ((relocalizePresheafFunctor a).obj H) :=
  elementsToRelocalize_comp_comp_overMap a mid _ hmid

/-- The morphism of presheaves `Λ_a H ⟶ Λ_a H'` underlying the relocalization of a 1-morphism
`El H ⥤ El H'` over `C/A`. -/
def relocalizeNatTrans : (relocalizePresheafFunctor a).obj H ⟶
    (relocalizePresheafFunctor a).obj H' :=
  natTransOfBasedFunctor (relocalizeBasedFunctor a mid)
    (relocalizeBasedFunctor_comp_eq a mid hmid)

include hmid in
/-- The factorization carried by a section of `Λ_a H` is unchanged by a relocalized
1-morphism. -/
theorem relocalizeNatTrans_app_fst (V : Over X)
    (x : ((relocalizePresheafFunctor a).obj H).obj (op V)) :
    ((relocalizeNatTrans a mid hmid).app (op V) x).1.1 = x.1.1 :=
  (elementOf_relocalize_fst a (P := H')
      (Y := (relocalizeBasedFunctor a mid).obj (⟨V, Discrete.mk x⟩ :
        (presheafOfCategories ((relocalizePresheafFunctor a).obj H ⋙ typeToCat)).obj))
      (V := V) (Functor.congr_obj (relocalizeBasedFunctor_comp_eq a mid hmid) _)).trans
    (Over.eqToHom_comp_hom (W' := Over.mk x.1.1) (Functor.congr_obj hmid _) _)

include hmid in
/-- **A relocalized 1-morphism is a morphism over the representable presheaf of `A → X`.** The
structural morphisms `CategoryTheory.OverShriek.relocalizeToYoneda` commute with the comparison
`CategoryTheory.PresheafOfCategories.relocalizeNatTrans`. -/
theorem relocalizeNatTrans_comp_relocalizeToYoneda :
    relocalizeNatTrans a mid hmid ≫ relocalizeToYoneda a H' = relocalizeToYoneda a H := by
  ext W x
  obtain ⟨V⟩ := W
  exact Over.OverMorphism.ext (relocalizeNatTrans_app_fst a mid hmid V x)

end Relocalize

/-- The first projection of a 2-fibre product over `C/X` of categories fibred in groupoids,
whose first factor is a slice `C/A`, is fibred in groupoids over that slice. -/
theorem isFiberedInGroupoids_fst_overMap_of {𝒜 : Type u₁} [Category.{v₁} 𝒜]
    {ℬ : Type u₂} [Category.{v₂} ℬ] {p𝒜 : 𝒜 ⥤ Over X} {pℬ : ℬ ⥤ Over X}
    {G : Over A ⥤ ℬ} {F : 𝒜 ⥤ ℬ} (hp𝒜 : p𝒜.IsFiberedInGroupoids)
    (hpℬ : pℬ.IsFiberedInGroupoids) (hG : G ⋙ pℬ = Over.map a) (hF : F ⋙ pℬ = p𝒜) :
    (TwoFibreProductOver.fst (Over.map a) p𝒜 pℬ G F).IsFiberedInGroupoids := by
  refine (Functor.isFiberedInGroupoids_comp_overMap_iff a _).1 ?_
  rw [TwoFibreProductOver.fst_comp_eq]
  exact TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _
    (Functor.IsFiberedInGroupoids.over_map a) hp𝒜 hpℬ hG hF

end Slice

section Elements

variable {C : Type u} [Category.{v} C]

/-- A pointwise family of bijections between presheaves of sets valued in one universe is an
isomorphism of presheaves. -/
def PointwiseEquiv.toIso {G F : Cᵒᵖ ⥤ Type v} (pe : PointwiseEquiv G F) : G ≅ F :=
  NatIso.ofComponents (fun U => Equiv.toIso (pe.equiv U))
    (fun f => by ext s; exact pe.naturality f s)

/-- **Two presheaves of sets with equivalent categories of elements are isomorphic.** If the
categories of elements of `G` and of `F` are both equivalent, over the base, to one and the same
category over the base, then `G` and `F` are isomorphic. -/
noncomputable def isoOfEquivalenceOver {𝒟 : Type u₁} [Category.{v₁} 𝒟] {q : 𝒟 ⥤ C}
    {G F : Cᵒᵖ ⥤ Type v}
    (e : StacksRepresentableCFG.EquivalenceOver q (discreteProjection G))
    (e' : StacksRepresentableCFG.EquivalenceOver q (discreteProjection F)) : G ≅ F :=
  (pointwiseEquivOfEquivalenceOver (e.symm.trans e')).toIso

/-- **The identification of two representing presheaves carries a named section to the named
section.** An object `z` of the common category over `C` lying over `W` names a section of `G`
through `e` and a section of `F` through `e'`
(`CategoryTheory.PresheafOfCategories.sectionOfObj`), and
`CategoryTheory.PresheafOfCategories.isoOfEquivalenceOver` takes the first to the second. -/
theorem hom_app_sectionOfObj_isoOfEquivalenceOver {𝒟 : Type u₁} [Category.{v₁} 𝒟] {q : 𝒟 ⥤ C}
    {G F : Cᵒᵖ ⥤ Type v}
    (e : StacksRepresentableCFG.EquivalenceOver q (discreteProjection G))
    (e' : StacksRepresentableCFG.EquivalenceOver q (discreteProjection F))
    (z : 𝒟) {W : C} (h : q.obj z = W) :
    (isoOfEquivalenceOver e e').hom.app (op W) (sectionOfObj e z h) = sectionOfObj e' z h := by
  have h₃ : q.obj (e.inv.functor.obj (e.hom.functor.obj z)) = W :=
    ((Functor.congr_obj e.inv.w (e.hom.functor.obj z)).trans
      (Functor.congr_obj e.hom.w z)).trans h
  have hvert : q.IsHomLift (𝟙 W) (e.unitIso.inv.app z) := by
    have hu := e.isHomLift_unitIso_inv_app z
    rwa [h] at hu
  have key : (isoOfEquivalenceOver e e').hom.app (op W) (sectionOfObj e z h) =
      sectionOfObj e' (e.inv.functor.obj (e.hom.functor.obj z)) h₃ := by
    change elementsFiberEquiv F W ((fiberFunctorOfComp (e.symm.trans e').hom.w W).obj
        ((elementsFiberEquiv G W).symm (sectionOfObj e z h))) = _
    rw [show (elementsFiberEquiv G W).symm (sectionOfObj e z h) =
      (fiberFunctorOfComp e.hom.w W).obj (Functor.Fiber.mk h) from
      (elementsFiberEquiv G W).symm_apply_apply _]
    rfl
  rw [key]
  exact sectionOfObj_eq_of_hom e' h₃ h (e.unitIso.inv.app z) hvert

end Elements

section Composite

variable {C : Type u} [Category.{v} C] {X Uo : C} (uu : Uo ⟶ X)
  {𝒳 : Type u₁} [Category.{v₁} 𝒳] {𝒴 : Type u₂} [Category.{v₂} 𝒴]
  {𝒵 : Type u₃} [Category.{v₃} 𝒵]
  {p𝒳 : 𝒳 ⥤ Over X} {p𝒴 : 𝒴 ⥤ Over X} {p𝒵 : 𝒵 ⥤ Over X}
  {Ff : 𝒳 ⥤ 𝒴} {Fg : 𝒴 ⥤ 𝒵} (zz : Over Uo ⥤ 𝒵)
  {Fp Gq : (Over Uo)ᵒᵖ ⥤ Type v}
  (hFf : Ff ⋙ p𝒴 = p𝒳)
  (E : StacksRepresentableCFG.EquivalenceOver
    (TwoFibreProductOver.fst (Over.map uu) p𝒳 p𝒵 zz (Ff ⋙ Fg)) (discreteProjection Fp))
  (EG : StacksRepresentableCFG.EquivalenceOver
    (TwoFibreProductOver.fst (Over.map uu) p𝒴 p𝒵 zz Fg) (discreteProjection Gq))

/-- The 1-morphism `El Fp ⥤ El Gq` over `C/Uo` that `f` induces on two presheaves representing
the base changes of `f ⋙ g` and of `g` along one point `z` of `𝒵`: transport into the 2-fibre
product, apply `CategoryTheory.TwoFibreProductOver.splitSndProjection`, and transport back. -/
abbrev baseChangeElementsMap :
    (presheafOfCategories (Fp ⋙ typeToCat)).obj ⥤ (presheafOfCategories (Gq ⋙ typeToCat)).obj :=
  E.inv.functor ⋙
    TwoFibreProductOver.splitSndProjection (Over.map uu) p𝒳 p𝒴 p𝒵 zz Ff Fg hFf ⋙ EG.hom.functor

/-- `CategoryTheory.PresheafOfCategories.baseChangeElementsMap` is strictly over `C/Uo`. -/
theorem baseChangeElementsMap_comp_eq :
    baseChangeElementsMap uu zz hFf E EG ⋙ discreteProjection Gq = discreteProjection Fp :=
  calc baseChangeElementsMap uu zz hFf E EG ⋙ discreteProjection Gq
      = E.inv.functor ⋙
          (TwoFibreProductOver.splitSndProjection (Over.map uu) p𝒳 p𝒴 p𝒵 zz Ff Fg hFf ⋙
            (EG.hom.functor ⋙ discreteProjection Gq)) := rfl
    _ = discreteProjection Fp := by
          rw [EG.hom.w, TwoFibreProductOver.splitSndProjection_comp_fst, E.inv.w]

/-- **The comparison morphism of the relocalized representing presheaves.** Given presheaves on
`C/Uo` representing the base changes of `f ⋙ g` and of `g` along a point `z` of `𝒵` with values
in `Uo`, this is the morphism `Λ_u Fp ⟶ Λ_u Gq` of presheaves on `C/X` that `f` induces. -/
def baseChangeNatTrans : (relocalizePresheafFunctor uu).obj Fp ⟶
    (relocalizePresheafFunctor uu).obj Gq :=
  relocalizeNatTrans uu (baseChangeElementsMap uu zz hFf E EG)
    (baseChangeElementsMap_comp_eq uu zz hFf E EG)

/-- The comparison morphism is a morphism **over** the representable presheaf of `Uo → X`: the
structural morphism `CategoryTheory.OverShriek.relocalizeToYoneda` of the representing presheaf
of the base change of `f ⋙ g` factors through that of the base change of `g`. -/
theorem baseChangeNatTrans_comp_relocalizeToYoneda :
    baseChangeNatTrans uu zz hFf E EG ≫ relocalizeToYoneda uu Gq = relocalizeToYoneda uu Fp :=
  relocalizeNatTrans_comp_relocalizeToYoneda uu _ (baseChangeElementsMap_comp_eq uu zz hFf E EG)

/-- **The representing point of the base change of `g` is strictly over the structure functor of
that base change.** The equivalence `EG`, followed by the passage from `El Gq` to
`El (Λ_u Gq)`, is a 1-morphism over `C/X` from the 2-fibre product `Uo ×_{z, 𝒵, g} 𝒴` to the
category of elements of the relocalized representing presheaf. -/
theorem comp_relocalizeToElements_comp_discreteProjection :
    (EG.hom.functor ⋙ relocalizeToElements uu Gq) ⋙
        discreteProjection ((relocalizePresheafFunctor uu).obj Gq) =
      TwoFibreProductOver.structureFunctor (Over.map uu) p𝒴 p𝒵 zz Fg :=
  calc (EG.hom.functor ⋙ relocalizeToElements uu Gq) ⋙
        discreteProjection ((relocalizePresheafFunctor uu).obj Gq)
      = (EG.hom.functor ⋙ discreteProjection Gq) ⋙ Over.map uu := rfl
    _ = TwoFibreProductOver.fst (Over.map uu) p𝒴 p𝒵 zz Fg ⋙ Over.map uu := by
          rw [EG.hom.w]
    _ = TwoFibreProductOver.structureFunctor (Over.map uu) p𝒴 p𝒵 zz Fg :=
          TwoFibreProductOver.fst_comp_eq

/-- **The fibre of the comparison morphism over the section named by a point of the intermediate
2-fibre product.** Let `w` be a point of `Uo ×_{z, 𝒵, g} 𝒴` with values in `A` and let `β` be a
section of `Λ_u Gq` over `A → X` restricting to the family of sections that `w` names. Then
there is a presheaf `fib` on `C/A` such that

* the relocalization of `fib` along `A → X`, with its structural morphism
  `CategoryTheory.OverShriek.relocalizeToYoneda`, is the fibre product of
  `CategoryTheory.PresheafOfCategories.baseChangeNatTrans` and `β`; and
* `fib` represents, over `C/A`, the base change `A ×_{y, 𝒴, f} 𝒳` along the point
  `y = w ⋙ π₂` of `𝒴` underlying `w`. -/
theorem exists_isPullback_baseChangeNatTrans_of_point
    (hFg : Fg ⋙ p𝒵 = p𝒴) (hz : zz ⋙ p𝒵 = Over.map uu)
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (h𝒵 : p𝒵.IsFiberedInGroupoids) (A : C) (t : A ⟶ X)
    (w : Over A ⥤ TwoFibreProductOver (Over.map uu) p𝒴 p𝒵 zz Fg)
    (hw' : w ⋙ TwoFibreProductOver.structureFunctor (Over.map uu) p𝒴 p𝒵 zz Fg = Over.map t)
    (hσ : (w ⋙ (EG.hom.functor ⋙ relocalizeToElements uu Gq)) ⋙
      discreteProjection ((relocalizePresheafFunctor uu).obj Gq) = Over.map t)
    (β : yoneda.obj (Over.mk t) ⟶ (relocalizePresheafFunctor uu).obj Gq)
    (hβ : ∀ τ : Over A, β.app (op ((Over.map t).obj τ)) (overMapTautHom t τ) =
      sectionOfBasedFunctor (w ⋙ (EG.hom.functor ⋙ relocalizeToElements uu Gq)) hσ τ) :
    ∃ (fib : (Over A)ᵒᵖ ⥤ Type v)
      (c : (relocalizePresheafFunctor t).obj fib ⟶ (relocalizePresheafFunctor uu).obj Fp),
      IsPullback c (relocalizeToYoneda t fib) (baseChangeNatTrans uu zz hFf E EG) β ∧
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map t) p𝒳 p𝒴
            (w ⋙ TwoFibreProductOver.snd (Over.map uu) p𝒴 p𝒵 zz Fg) Ff)
          (discreteProjection fib)) := by
  classical
  have hFfg : (Ff ⋙ Fg) ⋙ p𝒵 = p𝒳 := by rw [Functor.assoc, hFg, hFf]
  have hsfX := TwoFibreProductOver.isFiberedInGroupoids (Over.map uu) p𝒳 p𝒵 zz (Ff ⋙ Fg)
    (Functor.IsFiberedInGroupoids.over_map uu) h𝒳 h𝒵 hz hFfg
  have hsfY := TwoFibreProductOver.isFiberedInGroupoids (Over.map uu) p𝒴 p𝒵 zz Fg
    (Functor.IsFiberedInGroupoids.over_map uu) h𝒴 h𝒵 hz hFg
  have hsfR := TwoFibreProductOver.isFiberedInGroupoids
    (TwoFibreProductOver.structureFunctor (Over.map uu) p𝒴 p𝒵 zz Fg) p𝒳 p𝒴
    (TwoFibreProductOver.snd (Over.map uu) p𝒴 p𝒵 zz Fg) Ff hsfY h𝒳 h𝒴
    TwoFibreProductOver.snd_comp_eq hFf
  have hKsf := TwoFibreProductOver.splitSndProjection_comp_structureFunctor
    (Over.map uu) p𝒳 p𝒴 p𝒵 zz Ff Fg hFf
  have hbY := comp_relocalizeToElements_comp_discreteProjection uu zz EG (p𝒴 := p𝒴)
  have hKb : (TwoFibreProductOver.splitSndProjection (Over.map uu) p𝒳 p𝒴 p𝒵 zz Ff Fg hFf ⋙
      (EG.hom.functor ⋙ relocalizeToElements uu Gq)) ⋙
      discreteProjection ((relocalizePresheafFunctor uu).obj Gq) =
      TwoFibreProductOver.structureFunctor (Over.map uu) p𝒳 p𝒵 zz (Ff ⋙ Fg) := by
    rw [Functor.assoc, hbY, hKsf]
  have hcX : (elementsToRelocalize uu Fp ⋙ E.inv.functor) ⋙
      TwoFibreProductOver.structureFunctor (Over.map uu) p𝒳 p𝒵 zz (Ff ⋙ Fg) =
      discreteProjection ((relocalizePresheafFunctor uu).obj Fp) := by
    rw [← TwoFibreProductOver.fst_comp_eq]
    exact elementsToRelocalize_comp_comp_overMap uu E.inv.functor _ E.inv.w
  have : (elementsToRelocalize uu Fp ⋙ E.inv.functor).IsEquivalence :=
    ((E.compRight (Over.map uu)).trans
      (relocalizeElementsEquivalenceOver uu Fp)).isEquivalence_inv_functor
  have : (EG.hom.functor ⋙ relocalizeToElements uu Gq).IsEquivalence :=
    ((EG.compRight (Over.map uu)).trans
      (relocalizeElementsEquivalenceOver uu Gq)).isEquivalence_hom_functor
  have h1 := isFiberedInGroupoids_fst_overMap_of t (G := w)
    (F := TwoFibreProductOver.splitSndProjection (Over.map uu) p𝒳 p𝒴 p𝒵 zz Ff Fg hFf)
    hsfX hsfY hw' hKsf
  have h2 := isFiberedInGroupoids_fst_overMap_of t (G := w)
    (F := TwoFibreProductOver.fst
      (TwoFibreProductOver.structureFunctor (Over.map uu) p𝒴 p𝒵 zz Fg) p𝒳 p𝒴
      (TwoFibreProductOver.snd (Over.map uu) p𝒴 p𝒵 zz Fg) Ff)
    hsfR hsfY hw' TwoFibreProductOver.fst_comp_eq
  have hP2 := isFiberedInGroupoids_fst_overMap_of t (G := w ⋙
      (EG.hom.functor ⋙ relocalizeToElements uu Gq))
    (F := TwoFibreProductOver.splitSndProjection (Over.map uu) p𝒳 p𝒴 p𝒵 zz Ff Fg hFf ⋙
      (EG.hom.functor ⋙ relocalizeToElements uu Gq))
    hsfX (isFiberedInSetoids_discreteProjection _).isFiberedInGroupoids hσ hKb
  have hP3 := isFiberedInGroupoids_fst_overMap_of t (G := w ⋙
      (EG.hom.functor ⋙ relocalizeToElements uu Gq))
    (F := (elementsToRelocalize uu Fp ⋙ E.inv.functor) ⋙
      (TwoFibreProductOver.splitSndProjection (Over.map uu) p𝒳 p𝒴 p𝒵 zz Ff Fg hFf ⋙
        (EG.hom.functor ⋙ relocalizeToElements uu Gq)))
    (isFiberedInSetoids_discreteProjection _).isFiberedInGroupoids
    (isFiberedInSetoids_discreteProjection _).isFiberedInGroupoids hσ
    (relocalizeBasedFunctor_comp_eq uu (baseChangeElementsMap uu zz hFf E EG)
      (baseChangeElementsMap_comp_eq uu zz hFf E EG))
  obtain ⟨cap⟩ := TwoFibreProductOver.nonempty_equivalenceOver_baseChange_splitSnd
    (Over.map uu) p𝒳 p𝒴 p𝒵 zz Ff Fg hFf (Over.map t) hFg w hw'
    (Functor.IsFiberedInGroupoids.over_map t) hsfX hsfR h1 h2
  obtain ⟨mb⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence h1 hP2
    (TwoFibreProductOver.mapBase w
      (TwoFibreProductOver.splitSndProjection (Over.map uu) p𝒳 p𝒴 p𝒵 zz Ff Fg hFf)
      (EG.hom.functor ⋙ relocalizeToElements uu Gq) hbY)
    (TwoFibreProductOver.mapBase_comp_fst _ _ _ _)
    (TwoFibreProductOver.isEquivalence_mapBase hbY)
  obtain ⟨ps⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence hP3 hP2
    (TwoFibreProductOver.precomposeSnd (w ⋙ (EG.hom.functor ⋙ relocalizeToElements uu Gq))
      (TwoFibreProductOver.splitSndProjection (Over.map uu) p𝒳 p𝒴 p𝒵 zz Ff Fg hFf ⋙
        (EG.hom.functor ⋙ relocalizeToElements uu Gq))
      (elementsToRelocalize uu Fp ⋙ E.inv.functor) hcX)
    (TwoFibreProductOver.precomposeSnd_comp_fst _ _ _ _)
    (TwoFibreProductOver.isEquivalence_precomposeSnd
      (Functor.IsFiberedInGroupoids.over_map t)
      (isFiberedInSetoids_discreteProjection _).isFiberedInGroupoids hsfX hcX hKb)
  obtain ⟨tp⟩ := nonempty_equivalenceOver_twoFibreProductPresheaf t
    (relocalizeBasedFunctor uu (baseChangeElementsMap uu zz hFf E EG))
    (relocalizeBasedFunctor_comp_eq uu (baseChangeElementsMap uu zz hFf E EG)
      (baseChangeElementsMap_comp_eq uu zz hFf E EG))
    (w ⋙ (EG.hom.functor ⋙ relocalizeToElements uu Gq)) hσ
  obtain ⟨c, hc⟩ := exists_isPullback_relocalize_twoFibreProductPresheaf t
    (relocalizeBasedFunctor uu (baseChangeElementsMap uu zz hFf E EG))
    (relocalizeBasedFunctor_comp_eq uu (baseChangeElementsMap uu zz hFf E EG)
      (baseChangeElementsMap_comp_eq uu zz hFf E EG))
    (w ⋙ (EG.hom.functor ⋙ relocalizeToElements uu Gq)) hσ β hβ
  exact ⟨_, c, hc, ⟨cap.symm.trans (mb.trans (ps.symm.trans tp))⟩⟩

/-- **The fibre of the comparison morphism over a representable section is a relocalization, of
a presheaf representing the base change of `f` alone.** Let `β` be a section of `Λ_u Gq` over
`A → X`. Then there is a presheaf `fib` on `C/A` and a point `y` of `𝒴` with values in `A` such
that

* the relocalization of `fib` along `A → X`, with its structural morphism
  `CategoryTheory.OverShriek.relocalizeToYoneda`, is the fibre product of
  `CategoryTheory.PresheafOfCategories.baseChangeNatTrans` and `β`; and
* `fib` represents, over `C/A`, the base change `A ×_{y, 𝒴, f} 𝒳`.

The point `y` is the second projection of the point of `Uo ×_{z, 𝒵, g} 𝒴` that 2-Yoneda produces
from `β`. -/
theorem exists_isPullback_baseChangeNatTrans
    (hFg : Fg ⋙ p𝒵 = p𝒴) (hz : zz ⋙ p𝒵 = Over.map uu)
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (h𝒵 : p𝒵.IsFiberedInGroupoids) (A : C) (t : A ⟶ X)
    (β : yoneda.obj (Over.mk t) ⟶ (relocalizePresheafFunctor uu).obj Gq) :
    ∃ (fib : (Over A)ᵒᵖ ⥤ Type v)
      (c : (relocalizePresheafFunctor t).obj fib ⟶ (relocalizePresheafFunctor uu).obj Fp)
      (y : Over A ⥤ 𝒴),
      IsPullback c (relocalizeToYoneda t fib) (baseChangeNatTrans uu zz hFf E EG) β ∧
        y ⋙ p𝒴 = Over.map t ∧
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map t) p𝒳 p𝒴 y Ff) (discreteProjection fib)) := by
  have hsfY := TwoFibreProductOver.isFiberedInGroupoids (Over.map uu) p𝒴 p𝒵 zz Fg
    (Functor.IsFiberedInGroupoids.over_map uu) h𝒴 h𝒵 hz hFg
  have hq : (TwoFibreProductOver.fst (Over.map uu) p𝒴 p𝒵 zz Fg ⋙
      Over.map uu).IsFiberedInGroupoids := by
    rw [TwoFibreProductOver.fst_comp_eq]
    exact hsfY
  obtain ⟨w, hw, hσ0, hβ0⟩ := exists_pointOverMap_sectionOfBasedFunctor_eq t
    (TwoFibreProductOver.fst (Over.map uu) p𝒴 p𝒵 zz Fg ⋙ Over.map uu) hq
    ((EG.compRight (Over.map uu)).trans (relocalizeElementsEquivalenceOver uu Gq)) β
  have hσ : (w ⋙ (EG.hom.functor ⋙ relocalizeToElements uu Gq)) ⋙
      discreteProjection ((relocalizePresheafFunctor uu).obj Gq) = Over.map t := hσ0
  have hβ : ∀ τ : Over A, β.app (op ((Over.map t).obj τ)) (overMapTautHom t τ) =
      sectionOfBasedFunctor (w ⋙ (EG.hom.functor ⋙ relocalizeToElements uu Gq)) hσ τ := hβ0
  have hw' : w ⋙ TwoFibreProductOver.structureFunctor (Over.map uu) p𝒴 p𝒵 zz Fg =
      Over.map t := by
    rw [← TwoFibreProductOver.fst_comp_eq]
    exact hw
  obtain ⟨fib, c, hc, hE⟩ := exists_isPullback_baseChangeNatTrans_of_point uu zz hFf E EG
    hFg hz h𝒳 h𝒴 h𝒵 A t w hw' hσ β hβ
  refine ⟨fib, c, w ⋙ TwoFibreProductOver.snd (Over.map uu) p𝒴 p𝒵 zz Fg, hc, ?_, hE⟩
  rw [Functor.assoc, TwoFibreProductOver.snd_comp_eq]
  exact hw'

end Composite

end PresheafOfCategories

end CategoryTheory

end
