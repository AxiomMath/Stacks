module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceBaseChangePoint
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverTautologicalPoint

/-!
# Cancelling the second factor of a relative property

Let `S` be a scheme contained in a big fppf site `B`, let `P` and `Q` be properties of morphisms
of algebraic spaces over `S`, and let `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` be 1-morphisms of categories
fibred in groupoids over the big fppf site of `S`. If the composite `f ≫ g` satisfies the
condition of Stacks 04XB for `P`, `g` satisfies it for `Q`, and `P` cancels against `Q` for
morphisms of algebraic spaces, then `f` satisfies the condition for `P`.

## Main results

* `AlgebraicGeometry.Stack.prop_of_comp_of_spaceCancel`: the statement above, the converse of
  `AlgebraicGeometry.Stack.prop_comp_of_atlasDescent`.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 050M](https://stacks.math.columbia.edu/tag/050M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.OverShriek
open CategoryTheory.PresheafOfCategories

namespace AlgebraicGeometry

universe u v w

namespace Stack

/-- Let `P` and `Q` be properties of morphisms of algebraic spaces over `S`, with `P` stable under
base change and `Q` respecting isomorphisms, and suppose that `P` cancels against `Q`: a composite
`a ≫ b` of morphisms of algebraic spaces with `P (a ≫ b)` and `Q b` has `P a`. If two composable
1-morphisms of categories fibred in groupoids over the big fppf site of `S` are such that `g` and
`f ≫ g` are representable by algebraic spaces, `f ≫ g` satisfies the condition of Stacks 04XB for
`P` and `g` satisfies it for `Q`, then `f` satisfies it for `P`. -/
theorem prop_of_comp_of_spaceCancel
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P Q : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange] [Q.RespectsIso]
    (hcancel : ∀ {X Y Z : AlgebraicSpaces B S hS} (a : X ⟶ Y) (b : Y ⟶ Z),
      P (a ≫ b) → Q b → P a)
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom)
    (hfg : IsRepresentableByAlgebraicSpaces B S hS (f ≫ g).hom)
    (hPfg : ∀ (U : BigFppfOver B S hS)
      (z : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒵.val.obj)
      (_hz : z ⋙ 𝒵.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒵.val.p z
            (CatFiberedInGroupoids.homFunctor (f ≫ g)))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)))
    (hQg : ∀ (U : BigFppfOver B S hS)
      (z : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒵.val.obj)
      (_hz : z ⋙ 𝒵.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒴.val.p 𝒵.val.p z
            (CatFiberedInGroupoids.homFunctor g))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        Q (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))) :
    ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
      (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
            (CatFiberedInGroupoids.homFunctor f))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  intro U y hy Fq hFq hE
  obtain ⟨E⟩ := hE
  have hz : (y ⋙ CatFiberedInGroupoids.homFunctor g) ⋙ 𝒵.val.p = Over.map U.hom := by
    rw [Functor.assoc, g.hom.w]
    exact hy
  obtain ⟨Gq, hGq, ⟨EG⟩⟩ := hg U (y ⋙ CatFiberedInGroupoids.homFunctor g) hz
  obtain ⟨Fp, hFp, ⟨E'⟩⟩ := hfg U (y ⋙ CatFiberedInGroupoids.homFunctor g) hz
  have hΛFp := Space.isAlgebraicSpace_relocalizePresheaf B S hS U Fp hFp
  have hΛGq := Space.isAlgebraicSpace_relocalizePresheaf B S hS U Gq hGq
  have hΛFq := Space.isAlgebraicSpace_relocalizePresheaf B S hS U Fq hFq
  have hfac : (ObjectProperty.homMk (baseChangeNatTrans U.hom
          (y ⋙ CatFiberedInGroupoids.homFunctor g) f.hom.w E' EG) :
        (⟨(relocalizePresheafFunctor U.hom).obj Fp, hΛFp⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨(relocalizePresheafFunctor U.hom).obj Gq, hΛGq⟩) ≫
        (ObjectProperty.homMk (relocalizeToYoneda U.hom Gq) :
          (⟨(relocalizePresheafFunctor U.hom).obj Gq, hΛGq⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨yoneda.obj (Over.mk U.hom), isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)⟩) =
      ObjectProperty.homMk (relocalizeToYoneda U.hom Fp) :=
    ObjectProperty.hom_ext _ (baseChangeNatTrans_comp_relocalizeToYoneda U.hom
      (y ⋙ CatFiberedInGroupoids.homFunctor g) f.hom.w E' EG)
  have hPm := hcancel _ _
    (hfac ▸ (Space.prop_relocalizeToYoneda_iff B S hS P U Fp hFp).2
      (hPfg U (y ⋙ CatFiberedInGroupoids.homFunctor g) hz Fp hFp ⟨E'⟩))
    ((Space.prop_relocalizeToYoneda_iff B S hS Q U Gq hGq).2
      (hQg U (y ⋙ CatFiberedInGroupoids.homFunctor g) hz Gq hGq ⟨EG⟩))
  have hw' := TwoFibreProductOver.pointOfFunctor_comp_structureFunctor (Over.map U.hom)
    𝒴.val.p 𝒵.val.p (CatFiberedInGroupoids.homFunctor g) g.hom.w y hy
  have hσ : ((TwoFibreProductOver.pointOfFunctor (Over.map U.hom) 𝒴.val.p 𝒵.val.p
        (CatFiberedInGroupoids.homFunctor g) g.hom.w y hy) ⋙
        (EG.hom.functor ⋙ relocalizeToElements U.hom Gq)) ⋙
      discreteProjection ((relocalizePresheafFunctor U.hom).obj Gq) = Over.map U.hom := by
    rw [Functor.assoc, comp_relocalizeToElements_comp_discreteProjection]
    exact hw'
  obtain ⟨β, hβ⟩ := exists_section_sectionOfBasedFunctor_eq U.hom _ hσ
  obtain ⟨fib, c, hpb, ⟨Efib⟩⟩ := exists_isPullback_baseChangeNatTrans_of_point U.hom
    (y ⋙ CatFiberedInGroupoids.homFunctor g) f.hom.w E' EG g.hom.w hz
    𝒳.property 𝒴.property 𝒵.property U.left U.hom _ hw' hσ β hβ
  have Efib' : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor f))
      (discreteProjection fib) := Efib
  have hfib : IsAlgebraicSpace B U.left.1 U.left.2 fib :=
    isAlgebraicSpace_of_iso B U.left.1 U.left.2 (isoOfEquivalenceOver Efib' E) hFq
  have hΛfib := Space.isAlgebraicSpace_relocalizePresheaf B S hS U fib hfib
  have hsq : IsPullback
      (ObjectProperty.homMk c :
        (⟨(relocalizePresheafFunctor U.hom).obj fib, hΛfib⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨(relocalizePresheafFunctor U.hom).obj Fp, hΛFp⟩)
      (ObjectProperty.homMk (relocalizeToYoneda U.hom fib) :
        (⟨(relocalizePresheafFunctor U.hom).obj fib, hΛfib⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj (Over.mk U.hom), isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)⟩)
      (ObjectProperty.homMk (baseChangeNatTrans U.hom
          (y ⋙ CatFiberedInGroupoids.homFunctor g) f.hom.w E' EG) :
        (⟨(relocalizePresheafFunctor U.hom).obj Fp, hΛFp⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨(relocalizePresheafFunctor U.hom).obj Gq, hΛGq⟩)
      (ObjectProperty.homMk β :
        (⟨yoneda.obj (Over.mk U.hom), isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)⟩ :
          AlgebraicSpaces B S hS) ⟶ ⟨(relocalizePresheafFunctor U.hom).obj Gq, hΛGq⟩) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) hpb
  have hPfib : P (ObjectProperty.homMk (relocalizeToYoneda U.hom fib) :
      (⟨(relocalizePresheafFunctor U.hom).obj fib, hΛfib⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨yoneda.obj (Over.mk U.hom), isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)⟩) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq hPm
  refine (Space.prop_relocalizeToYoneda_iff B S hS P U Fq hFq).1 ?_
  let e : (⟨(relocalizePresheafFunctor U.hom).obj fib, hΛfib⟩ : AlgebraicSpaces B S hS) ≅
      ⟨(relocalizePresheafFunctor U.hom).obj Fq, hΛFq⟩ :=
    ObjectProperty.isoMk _ ((relocalizePresheafFunctor U.hom).mapIso
      (isoOfEquivalenceOver Efib' E))
  have hcomp : e.hom ≫ (ObjectProperty.homMk (relocalizeToYoneda U.hom Fq) :
        (⟨(relocalizePresheafFunctor U.hom).obj Fq, hΛFq⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj (Over.mk U.hom), isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)⟩) =
      ObjectProperty.homMk (relocalizeToYoneda U.hom fib) :=
    ObjectProperty.hom_ext _
      (OverShriek.relocalizePresheafFunctor_map_comp_relocalizeToYoneda U.hom
        (isoOfEquivalenceOver Efib' E).hom)
  exact (P.cancel_left_of_respectsIso e.hom _).1 (hcomp ▸ hPfib)

end Stack

end AlgebraicGeometry

end
