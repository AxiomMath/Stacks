module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesDiagonal
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallOpenSubstack

/-!
# Quasi-separatedness of an open substack of the stack of curves

Let `P` be a property of families of curves cutting out an open substack `Curves^P` of the small
model of the stack of curves (condition (o) of Moduli of Curves, Section 0E0E). The morphism
`Curves^P → Spec(ℤ)` is quasi-separated (Stacks 04YW) as soon as `Isom_U(Y, X) ⟶ U` is
quasi-compact for all families `Y`, `X` with `P` over a common base `U`.

This is the argument of the proof of Stacks 0DSS restricted to `Curves^P`. Quasi-separatedness
asks that the diagonal be quasi-compact and quasi-separated in the sense of Stacks 04XB. The base
change of the diagonal of `Curves^P → Spec(ℤ)` along a scheme-valued point is the isomorphism
space of two objects of `Curves^P`
(`AlgebraicGeometry.Stack.prop_algebraicSpaceMap_relativeDiagonal_iff_isomSpace`). The isomorphism
spaces of a full subcategory are those of the ambient stack, because the inclusion is fully
faithful (Stacks 042V), and those of the stack of curves are `Isom_U(Y, X)`
(`AlgebraicGeometry.curvesSmall.nonempty_arrowIso_isomFunctorProjection`). Their separatedness
is Stacks 0DPN and 0DPP, so only quasi-compactness is an input.

Restricting to `Curves^P` matters because for the moduli stack of stable curves the
quasi-compactness of `Isom_U(Y, X)` is available from the canonical polarization, whereas for all
families of curves it needs the boundedness argument of the proof of Stacks 0DSQ.

## Main results

* `AlgebraicGeometry.Stack.isomSpaceFullSubcategoryIso`: the isomorphism spaces of an algebraic
  full subcategory are those of the ambient stack.
* `AlgebraicGeometry.Stack.prop_relocalizeToYoneda_isomSpace_fullSubcategory_iff`: hence so are
  their properties as algebraic spaces over `U`.
* `AlgebraicGeometry.isQuasiSeparated_curvesSmallOpenSubstack_of_isQuasiCompact_isomSpace` and
  `AlgebraicGeometry.isQuasiSeparated_curvesSmallOpenSubstack_of_isQuasiCompact`: the
  quasi-separatedness of `Curves^P → Spec(ℤ)`, from the quasi-compactness of the isomorphism
  spaces of the small model, respectively of the `Isom_U(Y, X)` of families with `P`.

## References

* [Stacks Project, Tag 0DSS](https://stacks.math.columbia.edu/tag/0DSS)
* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 042V](https://stacks.math.columbia.edu/tag/042V)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The isomorphism spaces of an algebraic full subcategory are those of the ambient stack.**
For objects `x`, `y` over `U` of a full subcategory of an algebraic stack `𝒳` which is itself an
algebraic stack, `Isom(x, y)` computed in the subcategory is `Isom_𝒳(x, y)`: the inclusion is
fully faithful and preserves strongly cartesian morphisms (Stacks 042V). -/
def isomSpaceFullSubcategoryIso (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (Q : ObjectProperty 𝒳.val.val.obj)
    (hQ : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 Q))
    (U : BigFppfOver B S hS) (x y : (fullSubcategoryAlgebraicStack 𝒳 Q hQ).val.val.p.Fiber U) :
    isomSpace B S hS (fullSubcategoryAlgebraicStack 𝒳 Q hQ).val U x y ≅
      isomSpace B S hS 𝒳.val U ⟨x.1.obj, x.2⟩ ⟨y.1.obj, y.2⟩ :=
  letI : (fullSubcategoryAlgebraicStack 𝒳 Q hQ).val.val.p.IsFibered :=
    (fullSubcategoryAlgebraicStack 𝒳 Q hQ).val.isFiberedInGroupoids.isFibered
  letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  let ι := (fullSubcategoryInclusion 𝒳 Q hQ).hom.hom
  have hF : Functor.IsFibredOneMorphism (fullSubcategoryAlgebraicStack 𝒳 Q hQ).val.val.p
      𝒳.val.val.p ι.toFunctor :=
    { comp_eq := ι.w
      map_isStronglyCartesian := fun f _ _ φ _ => by
        have : 𝒳.val.val.p.IsHomLift f (ι.toFunctor.map φ) :=
          Functor.isHomLift_map_of_comp_eq (p := (fullSubcategoryAlgebraicStack 𝒳 Q hQ).val.val.p)
            ι.w f φ
        exact 𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift f (ι.toFunctor.map φ) }
  let e : (fullSubcategoryAlgebraicStack 𝒳 Q hQ).val.val.p.isomPresheaf x y ⋙
      uliftFunctor.{u, u} ≅ 𝒳.val.val.p.isomPresheaf
        ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj x)
        ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj y) :=
    liftedIsomPresheafIso hF (fullSubcategoryAlgebraicStack 𝒳 Q hQ).val.isFiberedInGroupoids
      𝒳.val.isFiberedInGroupoids x y
  Functor.isoWhiskerLeft _ ((Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ uliftFunctorTrivial.{u}.symm ≪≫ e)

/-- **A property of the isomorphism spaces of an algebraic full subcategory is that of the
ambient isomorphism spaces.** For a property `P` of morphisms of presheaves respecting
isomorphisms, the structure morphism of `Isom(x, y)` over `U`, read over `S` (Stacks 04SG), has
`P` exactly when that of `Isom_𝒳(x, y)` has. -/
theorem prop_relocalizeToYoneda_isomSpace_fullSubcategory_iff
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) [P.RespectsIso]
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (Q : ObjectProperty 𝒳.val.val.obj)
    (hQ : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 Q))
    (U : BigFppfOver B S hS) (x y : (fullSubcategoryAlgebraicStack 𝒳 Q hQ).val.val.p.Fiber U) :
    P (OverShriek.relocalizeToYoneda U.hom
        (isomSpace B S hS (fullSubcategoryAlgebraicStack 𝒳 Q hQ).val U x y)) ↔
      P (OverShriek.relocalizeToYoneda U.hom
        (isomSpace B S hS 𝒳.val U ⟨x.1.obj, x.2⟩ ⟨y.1.obj, y.2⟩)) := by
  rw [← OverShriek.relocalizePresheafFunctor_map_comp_relocalizeToYoneda U.hom
    (isomSpaceFullSubcategoryIso B S hS 𝒳 Q hQ U x y).hom]
  exact P.cancel_left_of_respectsIso _ _

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- **An open substack of the stack of curves is quasi-separated over `Spec(ℤ)` when the
isomorphism spaces of its objects are quasi-compact.** Let `P` cut out the open substack
`Curves^P` of the small model of the stack of curves. If `Isom(y₁, y₂) ⟶ U` is quasi-compact for
all objects `y₁`, `y₂` of the small model over a common `U` whose families have `P` (`hqc`), then
`Curves^P → Spec(ℤ)` is quasi-separated (Stacks 04YW): its diagonal is quasi-compact, and it is
quasi-separated being separated (Stacks 0DPN, 0DPP), both in the sense of Stacks 04XB. -/
theorem isQuasiSeparated_curvesSmallOpenSubstack_of_isQuasiCompact_isomSpace
    {P : ObjectProperty (CurveFamily B hZ)} (hP : IsOpenCurvesLocus B hZ P)
    (hqc : ∀ {U : BigFppfOver B integerBase hZ} (y₁ y₂ : (curvesSmall B hZ).val.p.Fiber U),
      P (ShrinkHoms.fromShrinkHoms y₁.1 : CurveFamily B hZ) →
      P (ShrinkHoms.fromShrinkHoms y₂.1 : CurveFamily B hZ) →
      Space.IsQuasiCompact B integerBase hZ (OverShriek.relocalizeToYoneda U.hom
        (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y₁ y₂))) :
    Stack.AlgebraicStacks.IsQuasiSeparated B integerBase hZ
      ((curvesSmallOpenSubstack B hZ h hP).inclusion ≫
        Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) := by
  set W := curvesSmallOpenSubstack B hZ h hP
  have hmem : ∀ {U : BigFppfOver B integerBase hZ}
      (x : W.toAlgebraicStack.val.val.p.Fiber U),
      P (ShrinkHoms.fromShrinkHoms x.1.obj : CurveFamily B hZ) := fun x =>
    have := W.strictlyFull
    (curvesSmallOpenSubstack_property_iff B hZ h hP _).1
      (W.property.prop_of_iso ((curvesSmallEquivalence B hZ h).counitIso.symm.app x.1.obj)
        x.1.property)
  have hqcR : MorphismProperty.RespectsIso (@Space.IsQuasiCompact B integerBase hZ) :=
    MorphismProperty.RespectsIso.of_respects_arrow_iso _ (fun f g e hf =>
      Space.isQuasiCompact_of_arrowIso B integerBase hZ f.hom g.hom e.hom.left e.hom.right
        e.hom.w hf)
  have hsR := Space.isSeparated_respectsIso B integerBase hZ
  refine ⟨fun U y hy F hF hE => ?_, fun U y hy F hF hE => ?_⟩
  · refine (Stack.prop_algebraicSpaceMap_relativeDiagonal_iff_isomSpace B integerBase hZ
      (@Space.IsQuasiCompact B integerBase hZ) _
      (Stack.faithful_schemeStack_p.{u, w} B integerBase hZ) U y hy F hF hE).2 ?_
    refine (Stack.prop_relocalizeToYoneda_isomSpace_fullSubcategory_iff B integerBase hZ
      (@Space.IsQuasiCompact B integerBase hZ) (curvesAlgebraicStack B hZ h) W.property
      W.isAlgebraic U _ _).2 ?_
    exact hqc _ _ (hmem _) (hmem _)
  · exact Space.isQuasiSeparated_of_isSeparated B integerBase hZ
      ((Stack.prop_algebraicSpaceMap_relativeDiagonal_iff_isomSpace B integerBase hZ
        (@Space.IsSeparated B integerBase hZ) _
        (Stack.faithful_schemeStack_p.{u, w} B integerBase hZ) U y hy F hF hE).2
        ((Stack.prop_relocalizeToYoneda_isomSpace_fullSubcategory_iff B integerBase hZ
          (@Space.IsSeparated B integerBase hZ) (curvesAlgebraicStack B hZ h) W.property
          W.isAlgebraic U _ _).2 (curvesSmall.isSeparated_relocalizeToYoneda_isomSpace _ _)))

/-- **An open substack of the stack of curves is quasi-separated over `Spec(ℤ)` when its
isomorphism spaces are quasi-compact.** Let `P` cut out the open substack `Curves^P` of the small
model of the stack of curves. If `Isom_U(Y, X) ⟶ U` is quasi-compact for all families of curves
`Y`, `X` with `P` over a common base `U` (`hqc`), then `Curves^P → Spec(ℤ)` is quasi-separated
(Stacks 04YW). This is the argument of Stacks 0DSS on `Curves^P`. -/
theorem isQuasiSeparated_curvesSmallOpenSubstack_of_isQuasiCompact
    {P : ObjectProperty (CurveFamily B hZ)} (hP : IsOpenCurvesLocus B hZ P)
    (hqc : ∀ (F G : CurveFamily B hZ) (hb : G.base = F.base), P F → P G →
      Space.IsQuasiCompact B integerBase hZ
        (CurveFamily.isomFunctorProjection F G (G.toBase.hom ≫ yoneda.map (eqToHom hb)))) :
    Stack.AlgebraicStacks.IsQuasiSeparated B integerBase hZ
      ((curvesSmallOpenSubstack B hZ h hP).inclusion ≫
        Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) :=
  isQuasiSeparated_curvesSmallOpenSubstack_of_isQuasiCompact_isomSpace B hZ h hP
    fun _ _ h₁ h₂ =>
      curvesSmall.isQuasiCompact_relocalizeToYoneda_isomSpace_of _ _ (hqc _ _ _ h₁ h₂)

end AlgebraicGeometry

end
