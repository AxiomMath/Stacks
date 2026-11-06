module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType

/-!
# Representable étale morphisms of fppf sheaves are formally étale

Let `S` be a scheme contained in a big fppf site `B`. A morphism `f : X ⟶ Y` of fppf sheaves
over `S`, with values in `Type (u + 1)`, which is representable by algebraic spaces and étale
has the unique infinitesimal lifting property of Stacks 049S against square-zero closed
immersions of affine objects of the site.

## Main results

* `AlgebraicGeometry.Space.formallyEtale_of_isEtaleULift`: an étale morphism from an algebraic
  space with values in `Type (u + 1)` to a represented presheaf is formally étale.
* `AlgebraicGeometry.FormalSpace.formallyEtale_hom_of_isRepresentableEtale`: a representable
  étale morphism of fppf sheaves is formally étale.

## Implementation notes

The value universe is the obstacle. An algebraic space with values in `Type (u + 1)` is, up to
isomorphism, the universe lift of one with values in `Type u`
(`AlgebraicGeometry.FormalSpace.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift`), and
the étale morphisms correspond (`AlgebraicGeometry.Space.isEtaleULift_whiskerRight_iff`), so
Stacks 0616 in the value universe of the site,
`AlgebraicGeometry.Space.isEtale_iff_isLocallyOfFinitePresentation_and_formallyEtale`, applies.
Formal étaleness is a condition on sections, and the sections of a universe lift are universe
lifts of sections, so it transports back.

For a representable étale `f` the lifting problem against a point `y` of `Y` over `T'` is the
lifting problem for the base change of `f` along `y`, an étale morphism from an algebraic space
to the presheaf represented by `T'`; that is `AlgebraicGeometry.Space.fibreProductLiftEquiv`.

## References

* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
* [Stacks Project, Tag 0616](https://stacks.math.columbia.edu/tag/0616)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An isomorphism of presheaves on the big fppf site of `S` is formally étale: the unique lift
is the image of the given section of the target under the inverse. -/
theorem formallyEtale_of_isIso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v} (a : F ⟶ G) [IsIso a] :
    FormallyEtale a := by
  intro T T' _ _ i _ x y hxy
  have h1 : ∀ (U : (BigFppfOver B S hS)ᵒᵖ) t, (inv a).app U (a.app U t) = t := fun U t => by
    simp
  have h2 : ∀ (U : (BigFppfOver B S hS)ᵒᵖ) t, a.app U ((inv a).app U t) = t := fun U t => by
    simp
  refine ⟨(inv a).app (op T') y, ⟨?_, h2 _ y⟩, fun z hz => ?_⟩
  · rw [← NatTrans.naturality_apply, ← hxy, h1]
  · rw [← hz.2, h1]

/-- Formal étaleness passes to the universe lift of a morphism of presheaves: the sections of
a universe lift are the universe lifts of sections. -/
theorem formallyEtale_whiskerRight_uliftFunctor {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) (ha : FormallyEtale a) :
    FormallyEtale (Functor.whiskerRight a uliftFunctor.{w}) := by
  intro T T' hT hT' i hi x y hxy
  obtain ⟨z, hz, hu⟩ := ha T T' hT hT' i hi x.down y.down (congrArg ULift.down hxy)
  refine ⟨ULift.up z, ⟨ULift.ext hz.1, ULift.ext hz.2⟩, fun w hw => ?_⟩
  exact ULift.ext (hu w.down ⟨congrArg ULift.down hw.1, congrArg ULift.down hw.2⟩)

/-- **An étale morphism from an algebraic space to a represented presheaf is formally étale**,
with values in `Type (u + 1)`. The algebraic space is the universe lift of one with values in
`Type u`, the morphism is the universe lift of an étale morphism there, and that one is formally
étale by Stacks 0616. -/
theorem formallyEtale_of_isEtaleULift {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (hP : IsAlgebraicSpaceULift.{u + 1} B S hS P) {T' : BigFppfOver B S hS}
    (π : P ⟶ (uliftYoneda.{u + 1}).obj T') (hπ : IsEtaleULift.{u + 1} B S hS π) :
    FormallyEtale π := by
  obtain ⟨P₀, hP₀, ⟨e⟩⟩ := exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hP
  obtain ⟨π₀, hπ₀⟩ := exists_whiskerRight_eq B S hS (F := P₀) (G := yoneda.obj T') (e.hom ≫ π)
  have het : IsEtale B S hS π₀ := by
    refine (isEtaleULift_whiskerRight_iff B S hS π₀).mp ?_
    rw [hπ₀]
    exact FormalSpace.isEtaleULift_precomp_iso B S hS e π hπ
  have hfe : FormallyEtale π₀ :=
    ((isEtale_iff_isLocallyOfFinitePresentation_and_formallyEtale B S hS hP₀
      (isAlgebraicSpace_yoneda B S hS T') π₀).mp het).2
  have hπ' : π = e.inv ≫ Functor.whiskerRight π₀ uliftFunctor.{u + 1} := by
    rw [hπ₀]; simp
  rw [hπ']
  exact formallyEtale_comp (formallyEtale_of_isIso e.inv)
    (formallyEtale_whiskerRight_uliftFunctor π₀ hfe)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A representable étale morphism of fppf sheaves is formally étale.** Let `f : X ⟶ Y` be a
morphism of fppf sheaves over `S` which is representable by algebraic spaces and étale. Then
every commutative square from a square-zero closed immersion `T ⟶ T'` of affine objects of the
site to `f` has exactly one diagonal lift.

The lifting problem against a section `y` of `Y` over `T'` is the lifting problem for the base
change of `f` along `y`, which is an étale morphism from an algebraic space to the presheaf
represented by `T'` and so formally étale by
`AlgebraicGeometry.Space.formallyEtale_of_isEtaleULift`. -/
theorem formallyEtale_hom_of_isRepresentableEtale {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : IsRepresentableEtale B S hS f) : Space.FormallyEtale f.hom := by
  classical
  intro T T' hT hT' i hi x y hxy
  let ξ : (uliftYoneda.{u + 1}).obj T' ⟶ Y.obj := uliftYonedaEquiv.symm y
  let D : Space.FppfFunctorPullbackSituation.{u, u + 1} :=
    ⟨B, S, hS, X.obj, Y.obj, (uliftYoneda.{u + 1}).obj T', f.hom, ξ⟩
  have hπ : Space.FormallyEtale D.toH :=
    Space.formallyEtale_of_isEtaleULift (hf.1 T' ξ) (pullback.fst ξ f.hom) (hf.2 T' ξ)
  let evT := (CategoryTheory.evaluation ((BigFppfOver B S hS)ᵒᵖ) (Type (u + 1))).obj (op T)
  have hξi : ξ.app (op T) (ULift.up i) = Y.obj.map i.op y := by
    simp [ξ, uliftYonedaEquiv]
  have hξ1 : ξ.app (op T') (ULift.up (𝟙 T')) = y := by
    simp [ξ, uliftYonedaEquiv]
  let x' : D.fibreProduct.obj (op T) :=
    Types.pullbackLiftPoint (evT.map D.toH) (evT.map D.toF) (evT.map D.b) (evT.map D.a)
      (D.isPullback.map evT) (ULift.up i) x (hxy.trans hξi.symm)
  have hx'H : D.toH.app (op T) x' = ULift.up i :=
    Types.pullbackLiftPoint_fst (evT.map D.toH) (evT.map D.toF) (evT.map D.b) (evT.map D.a)
      (D.isPullback.map evT) (ULift.up i) x (hxy.trans hξi.symm)
  have hx'F : D.toF.app (op T) x' = x :=
    Types.pullbackLiftPoint_snd (evT.map D.toH) (evT.map D.toF) (evT.map D.b) (evT.map D.a)
      (D.isPullback.map evT) (ULift.up i) x (hxy.trans hξi.symm)
  have hx'y : D.toH.app (op T) x' = D.H.map i.op (ULift.up (𝟙 T')) := by
    rw [hx'H]
    simp [D]
  have key :=
    (Space.fibreProductLiftEquiv D T T' i x' (ULift.up (𝟙 T')) hx'y).existsUnique_subtype_congr.mp
      (hπ T T' hT hT' i hi x' (ULift.up (𝟙 T')) hx'y)
  simpa only [hx'F, D, hξ1] using key

end AlgebraicGeometry.FormalSpace

end
