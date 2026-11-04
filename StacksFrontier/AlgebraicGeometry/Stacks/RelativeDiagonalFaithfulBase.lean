module

public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeProperty
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.RelativeDiagonalFibreFaithful
public import StacksFrontier.CategoryTheory.Sites.Stack.SlicePointIsomPresheaf

/-!
# The relative diagonal over a category fibred in sets

Let `S` be a scheme contained in a big fppf site `B`, let `𝒳` and `𝒴` be categories fibred in
groupoids over the big fppf site of `S` and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism. Assume that the
structure functor of `𝒴` is faithful, as it is for the category fibred in sets `𝒮_Y` of an
algebraic space `Y`. Then the base change of the relative diagonal

`Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳`

along a scheme-valued point `(x, x', α)` of `𝒳 ×_𝒴 𝒳` over `U` is the isomorphism sheaf
`Isom_𝒳(x, x')` over `U`: by Stacks 04XT it is `Isom_𝒳(x, x') ×_{Isom_𝒴(f x, f x'), α} U`, and
`Isom_𝒴(f x, f x') ⟶ U` is a monomorphism through which `α` factors.

Consequently, to show that `Δ_f` is representable by algebraic spaces with a property `P` in the
sense of Properties of Stacks, Section 04XB, it suffices to show that for every scheme `U` and
every pair of objects `x`, `x'` of the fibre over `U` whose images in `𝒴` are identified over
`𝟙 U`, the sheaf `Isom_𝒳(x, x')` is an algebraic space over `U` whose structure morphism has `P`.
This is the reduction in the proof of Stacks 0DLY, where `𝒳 = Coh_{X/B}`, `𝒴 = 𝒮_B`, and the
pairs over a common point `g : U ⟶ B` are pairs of modules on `X_U`.

## Main results

* `AlgebraicGeometry.Stack.prop_algebraicSpaceMap_of_uliftIso`: a property of morphisms of
  algebraic spaces respecting isomorphisms holds for the structure morphism of one algebraic space
  over `U` if it holds for that of an isomorphic one.
* `AlgebraicGeometry.Stack.exists_isRepresentable_and_prop_relativeDiagonal_of_faithful`: the
  reduction described above.

## References

* [Stacks Project, Tag 04XT](https://stacks.math.columbia.edu/tag/04XT)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 0DLY](https://stacks.math.columbia.edu/tag/0DLY)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

namespace AlgebraicGeometry.Stack

universe u v w v' w' t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A property of the structure morphism transfers along an isomorphism of algebraic spaces
over `U`.** If `P` respects isomorphisms, the presheaves `G` and `F` on the big fppf site of `U`
are algebraic spaces, and `G` and `F` become isomorphic after a universe lift, then `P` holds for
the structure morphism of `F` over `U`, read over `S` by Stacks 04SG, as soon as it holds for that
of `G`. -/
theorem prop_algebraicSpaceMap_of_uliftIso
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.RespectsIso] (U : BigFppfOver B S hS)
    {G F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u}
    (hG : IsAlgebraicSpace B U.left.1 U.left.2 G) (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (e : G ⋙ uliftFunctor.{t, u} ≅ F ⋙ uliftFunctor.{t, u})
    (h : P (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨G, hG⟩))) :
    P (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) := by
  let e' : G ≅ F :=
    ((Functor.FullyFaithful.ofFullyFaithful uliftFunctor.{t, u}).whiskeringRight _).preimageIso e
  let E := spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom
  let i := E.mapIso (ObjectProperty.isoMk _ e' :
    (⟨G, hG⟩ : AlgebraicSpaces B U.left.1 U.left.2) ≅ ⟨F, hF⟩)
  let j : (⟨(E.obj ⟨G, hG⟩).1.left, (E.obj ⟨G, hG⟩).property⟩ : AlgebraicSpaces B S hS) ≅
      ⟨(E.obj ⟨F, hF⟩).1.left, (E.obj ⟨F, hF⟩).property⟩ :=
    { hom := ObjectProperty.homMk i.hom.hom.left
      inv := ObjectProperty.homMk i.inv.hom.left
      hom_inv_id := ObjectProperty.hom_ext _ (congrArg (fun k => k.hom.left) i.hom_inv_id)
      inv_hom_id := ObjectProperty.hom_ext _ (congrArg (fun k => k.hom.left) i.inv_hom_id) }
  have hw : j.hom ≫ algebraicSpaceMap B S hS U (E.obj ⟨F, hF⟩) =
      algebraicSpaceMap B S hS U (E.obj ⟨G, hG⟩) := ObjectProperty.hom_ext _ (Over.w i.hom.hom)
  rw [← hw] at h
  have : IsIso j.hom := j.isIso_hom
  exact (P.cancel_left_of_respectsIso j.hom _).1 h

variable (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
  (𝒴 : CatFiberedInGroupoids.{u, v', u + 1, w'} (BigFppfOver B S hS))
  (f : 𝒳.val ⥤ᵇ 𝒴.val)

/-- **The relative diagonal over a category fibred in sets is read on isomorphism sheaves.** Let
`f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of `S`,
whose target has a faithful structure functor. Let `P` be a property of morphisms of algebraic
spaces over `S` which respects isomorphisms. Suppose that for every scheme `U` over `S` and all
objects `x`, `x'` of the fibre of `𝒳` over `U` whose images under `f` are related by a morphism
over `𝟙 U`, the isomorphism sheaf `Isom_𝒳(x, x')` is an algebraic space over `U` whose structure
morphism has `P`. Then the relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is representable by algebraic
spaces (Stacks 02ZW), and every algebraic space representing one of its base changes along a
scheme-valued point has structure morphism with `P` (Properties of Stacks, Section 04XB). -/
theorem exists_isRepresentable_and_prop_relativeDiagonal_of_faithful [𝒴.val.p.Faithful]
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.RespectsIso]
    (h : letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
      ∀ (U : BigFppfOver B S hS) (x x' : 𝒳.val.p.Fiber U),
        (∃ φ : f.obj x.1 ⟶ f.obj x'.1, 𝒴.val.p.IsHomLift (𝟙 U) φ) →
        ∃ (G : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
          (hG : IsAlgebraicSpace B U.left.1 U.left.2 G),
          Nonempty (G ⋙ uliftFunctor.{v, u} ≅
            ((Over.iteratedSliceBackward U).op ⋙ 𝒳.val.p.isomPresheaf x x') ⋙
              uliftFunctor.{u, v}) ∧
          P (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨G, hG⟩))) :
    ∃ _hrep : IsRepresentableByAlgebraicSpaces B S hS
        (relativeDiagonalBasedFunctor B S hS 𝒳 𝒴 f),
      ∀ (U : BigFppfOver B S hS)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤ (twoFibreProduct B S hS 𝒴 𝒳 𝒳 f f).val.obj)
        (_hy : y ⋙ (twoFibreProduct B S hS 𝒴 𝒳 𝒳 f f).val.p = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p
            (twoFibreProduct B S hS 𝒴 𝒳 𝒳 f f).val.p y
            (relativeDiagonalBasedFunctor B S hS 𝒳 𝒴 f).toFunctor)
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) := by
  have hp := 𝒳.isFiberedInGroupoids
  have hpf : 𝒳.val.p.IsFibered := hp.isFibered
  have hq := 𝒴.isFiberedInGroupoids
  have key : ∀ (U : BigFppfOver B S hS)
      (Y : BigFppfOver B U.left.1 U.left.2 ⥤
        TwoFibreProductOver 𝒳.val.p 𝒳.val.p 𝒴.val.p f.toFunctor f.toFunctor)
      (hY : Y ⋙ RelProdP 𝒳.val.p 𝒴.val.p f.toFunctor = Over.map U.hom),
      ∃ (G : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hG : IsAlgebraicSpace B U.left.1 U.left.2 G),
        Nonempty (relVertHomPresheaf hq hp hY f.w ⋙ uliftFunctor.{u, v} ≅
          G ⋙ uliftFunctor.{v, u}) ∧
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨G, hG⟩)) := by
    intro U Y hY
    have hv := isHomLift_vertical_iso hY (Over.mk (𝟙 U.left))
    rw [Functor.overMap_obj_mkId U] at hv
    obtain ⟨G, hG, ⟨e⟩, hP⟩ := h U
      (Functor.sliceValue 𝒳.val.p U (Y₁' Y) (h1' hY))
      (Functor.sliceValue 𝒳.val.p U (Y₂' Y) (h2' hY))
      ⟨(Y.obj (Over.mk (𝟙 U.left))).iso.hom, hv⟩
    exact ⟨G, hG, ⟨(Functor.isoWhiskerRight
      ((relVertHomPresheafIsoOfFaithful hq hp hY f.w).trans
        (Functor.vertHomPresheafIsoIsomPresheafOfFunctors 𝒳.val.p hp U (Y₁' Y) (Y₂' Y)
          (h1' hY) (h2' hY))) uliftFunctor.{u, v}).trans e.symm⟩, hP⟩
  refine ⟨fun U Y hY => ?_, fun U Y hY F hF hE => ?_⟩
  · obtain ⟨G, hG, hi, -⟩ := key U Y hY
    exact ⟨G, hG, (nonempty_equivalenceOver_fst_iff hq hp hY f.w G).2 hi⟩
  · obtain ⟨G, hG, ⟨i⟩, hP⟩ := key U Y hY
    obtain ⟨j⟩ := (nonempty_equivalenceOver_fst_iff hq hp hY f.w F).1 hE
    exact prop_algebraicSpaceMap_of_uliftIso B S hS P U hG hF (i.symm.trans j) hP

end AlgebraicGeometry.Stack

end
