module

public import StacksFrontier.AlgebraicGeometry.Quot.FlatLfpPushoutGluing
public import StacksFrontier.CategoryTheory.FiberedCategory.HomLift
public import StacksFrontier.Deformation.Artin.RimSchlessinger
public import StacksFrontier.Deformation.Artin.RimSchlessinger.RestrictionData

/-!
# Condition (RS) for the stack of curves from Stacks 0D56

Stacks 0D56 says that restriction of families of curves across an affine thickening pushout is
an equivalence onto the compatible pairs; in this library its conclusion is
`AlgebraicGeometry.CurvePushoutEquivalenceData`, stated for the fibres of
`AlgebraicGeometry.curvesProjection` over the schemes of the site, with the base-change functors
of families of curves. Artin's criterion consumes condition (RS) of Stacks 07WP,
`Deformation.Artin.SatisfiesRS`, for `AlgebraicGeometry.curvesFiberedCategory`, whose structure
functor is `AlgebraicGeometry.curvesProjectionOver` to the slice over `Spec(ℤ)` and whose
comparison is built from a choice of pullbacks. This file passes from the first to the second.

## Main results

* `AlgebraicGeometry.satisfiesRS_curves_of_curvePushoutEquivalence`: (RS) for `Curves`, given
  the conclusion of Stacks 0D56 at every affine thickening pushout.
* `AlgebraicGeometry.satisfiesRS_curves_of_hasEtaleChartLifts`: (RS) for `Curves`, given that
  étale charts lift across thickenings (the input of Stacks 0D56's proof here).

## Implementation notes

The two structure functors differ only by the forgetful functor from the slice over `Spec(ℤ)`,
which is faithful and injective on objects because `Spec(ℤ)` is terminal; so the fibres of the
two are isomorphic categories (`AlgebraicGeometry.curvesOverFiberToFiber` and its inverse), and
the base-change data of Stacks 0D56 transports along them with the same underlying morphisms.
The comparison of the transported restriction equivalence with the canonical comparison is
`Deformation.Artin.isEquivalence_fiberSquareComparison_of_restriction`. A closed immersion of
local Artinian schemes is a thickening, and a morphism of affine schemes is affine, so every
square (RS) quantifies over is one Stacks 0D56 applies to.

## References

* [Stacks Project, Tag 0D56](https://stacks.math.columbia.edu/tag/0D56)
* [Stacks Project, Tag 07WP](https://stacks.math.columbia.edu/tag/07WP)
-/

@[expose] public noncomputable section

attribute [local implicit_reducible] AlgebraicGeometry.curvesProjectionOver

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Deformation.Artin

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

/-- An object of the slice of the site over `Spec(ℤ)` is determined by its underlying scheme. -/
theorem bigFppfOver_integerBase_ext {U V : BigFppfOver B integerBase hZ}
    (h : U.left = V.left) : U = V :=
  CostructuredArrow.obj_ext _ _ h (B.inclusion.map_injective (specULiftZIsTerminal.hom_ext _ _))

/-- A morphism of families of curves lies over a morphism of the slice over `Spec(ℤ)` exactly when
it lies over the underlying morphism of schemes. -/
theorem curvesProjection_isHomLift_iff {U V : BigFppfOver B integerBase hZ} (a : U ⟶ V)
    {x y : CurveFamily B hZ} (φ : x ⟶ y) :
    (curvesProjection B hZ).IsHomLift a.left φ ↔ (curvesProjectionOver B hZ).IsHomLift a φ := by
  refine ⟨fun h => ?_, Functor.isHomLift_comp_functor (Over.forget _) a φ⟩
  obtain rfl : x.base = U := bigFppfOver_integerBase_ext B hZ
    (IsHomLift.domain_eq (curvesProjection B hZ) a.left φ)
  obtain rfl : y.base = V := bigFppfOver_integerBase_ext B hZ
    (IsHomLift.codomain_eq (curvesProjection B hZ) a.left φ)
  obtain rfl : a = (curvesProjectionOver B hZ).map φ :=
    Over.OverMorphism.ext (@IsHomLift.eq_of_isHomLift _ _ _ _ (curvesProjection B hZ) _ _ _ _ h)
  exact IsHomLift.map φ

/-- The fibre of `AlgebraicGeometry.curvesProjectionOver` over `U` as the fibre of
`AlgebraicGeometry.curvesProjection` over the underlying scheme: the identity on families. -/
@[simps]
def curvesOverFiberToFiber (U : BigFppfOver B integerBase hZ) :
    (curvesProjectionOver B hZ).Fiber U ⥤ (curvesProjection B hZ).Fiber U.left where
  obj x := ⟨x.1, congrArg Comma.left x.2⟩
  map φ := ⟨φ.1, (curvesProjection_isHomLift_iff B hZ (𝟙 U) φ.1).2 φ.2⟩

/-- The inverse of `AlgebraicGeometry.curvesOverFiberToFiber`, again the identity on families. -/
@[simps]
def curvesFiberToOverFiber (U : BigFppfOver B integerBase hZ) :
    (curvesProjection B hZ).Fiber U.left ⥤ (curvesProjectionOver B hZ).Fiber U where
  obj x := ⟨x.1, bigFppfOver_integerBase_ext B hZ x.2⟩
  map φ := ⟨φ.1, (curvesProjection_isHomLift_iff B hZ (𝟙 U) φ.1).1 φ.2⟩

/-- The two descriptions of the fibre of the stack of curves are equivalent, by functors which
are the identity on families and on their morphisms. -/
def curvesOverFiberEquivalence (U : BigFppfOver B integerBase hZ) :
    (curvesProjectionOver B hZ).Fiber U ≌ (curvesProjection B hZ).Fiber U.left where
  functor := curvesOverFiberToFiber B hZ U
  inverse := curvesFiberToOverFiber B hZ U
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- The functor `AlgebraicGeometry.curvesOverFiberToFiber` is an equivalence of categories. -/
instance (U : BigFppfOver B integerBase hZ) : (curvesOverFiberToFiber B hZ U).IsEquivalence :=
  (curvesOverFiberEquivalence B hZ U).isEquivalence_functor

/-- A base change of families of curves along the underlying morphism of a morphism `e` of the
slice over `Spec(ℤ)`, read as a base-change functor between the fibres of
`AlgebraicGeometry.curvesProjectionOver`. -/
@[simps]
def CurveBaseChange.toFiberBaseChange {A A' : BigFppfOver B integerBase hZ} {e : A ⟶ A'}
    (F : CurveBaseChange B hZ e.left) : FiberBaseChange (curvesProjectionOver B hZ) e where
  functor := curvesOverFiberToFiber B hZ A' ⋙ F.functor ⋙ curvesFiberToOverFiber B hZ A
  comparison :=
    { app := fun x => F.comparison.app ((curvesOverFiberToFiber B hZ A').obj x)
      naturality := fun _ _ φ => F.comparison.naturality ((curvesOverFiberToFiber B hZ A').map φ) }
  comparison_isHomLift _ :=
    (curvesProjection_isHomLift_iff B hZ e _).1 (F.comparison_base _)

/-- The functor between the two-fibre products of fibres induced by the fibre equivalences:
the identity on families. -/
@[simps]
def curvesCatPullbackToOver {X Y X' : BigFppfOver B integerBase hZ} {j : X ⟶ Y} {i : X ⟶ X'}
    (Fj : CurveBaseChange B hZ j.left) (Fi : CurveBaseChange B hZ i.left) :
    CategoricalPullback Fj.functor Fi.functor ⥤
      CategoricalPullback (Fj.toFiberBaseChange B hZ).functor
        (Fi.toFiberBaseChange B hZ).functor where
  obj x := ⟨(curvesFiberToOverFiber B hZ Y).obj x.fst, (curvesFiberToOverFiber B hZ X').obj x.snd,
    (curvesFiberToOverFiber B hZ X).mapIso x.iso⟩
  map φ := ⟨(curvesFiberToOverFiber B hZ Y).map φ.fst,
    (curvesFiberToOverFiber B hZ X').map φ.snd,
    Fiber.hom_ext (congrArg (fun m => m.1) φ.w)⟩

/-- The functor `AlgebraicGeometry.curvesCatPullbackToOver` between the two-fibre products of
fibres is an equivalence of categories. -/
instance {X Y X' : BigFppfOver B integerBase hZ} {j : X ⟶ Y} {i : X ⟶ X'}
    (Fj : CurveBaseChange B hZ j.left) (Fi : CurveBaseChange B hZ i.left) :
    (curvesCatPullbackToOver B hZ Fj Fi).IsEquivalence where
  faithful := ⟨fun {x y} {φ ψ} h => CategoricalPullback.hom_ext
    (Fiber.hom_ext (congrArg (fun m => m.fst.1) h))
    (Fiber.hom_ext (congrArg (fun m => m.snd.1) h))⟩
  full := ⟨fun {x y} φ => ⟨⟨(curvesOverFiberToFiber B hZ Y).map φ.fst,
    (curvesOverFiberToFiber B hZ X').map φ.snd,
    Fiber.hom_ext (congrArg (fun m => m.1) φ.w)⟩, rfl⟩⟩
  essSurj := ⟨fun y => ⟨⟨(curvesOverFiberToFiber B hZ Y).obj y.fst,
    (curvesOverFiberToFiber B hZ X').obj y.snd, (curvesOverFiberToFiber B hZ X).mapIso y.iso⟩,
    ⟨CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _) (by
      change (Fj.toFiberBaseChange B hZ).functor.map (𝟙 y.fst) ≫ y.iso.hom =
        y.iso.hom ≫ (Fi.toFiberBaseChange B hZ).functor.map (𝟙 y.snd)
      simp)⟩⟩⟩

/-- An isomorphism between functors of fibres of `AlgebraicGeometry.curvesProjection`, read
between the corresponding functors of fibres of `AlgebraicGeometry.curvesProjectionOver`. -/
private def curvesOverFiberIsoOfIso {V U : BigFppfOver B integerBase hZ}
    {F G : (curvesProjection B hZ).Fiber V.left ⥤ (curvesProjection B hZ).Fiber U.left}
    (α : F ≅ G) :
    curvesOverFiberToFiber B hZ V ⋙ F ⋙ curvesFiberToOverFiber B hZ U ≅
      curvesOverFiberToFiber B hZ V ⋙ G ⋙ curvesFiberToOverFiber B hZ U :=
  NatIso.ofComponents (fun _ => (curvesFiberToOverFiber B hZ U).mapIso (α.app _))
    (fun φ => Fiber.hom_ext
      (congrArg (fun m => m.1) (α.hom.naturality ((curvesOverFiberToFiber B hZ V).map φ))))

/-- **(RS) for the stack of curves, from the conclusion of Stacks 0D56.** If restriction of
families of curves across every affine thickening pushout of schemes of the site is an
equivalence onto the compatible pairs (the conclusion of Stacks 0D56), then the stack of curves
satisfies condition (RS) of Stacks 07WP. -/
public theorem satisfiesRS_curves_of_curvePushoutEquivalence
    (h0D56 : ∀ {T T' S S' : B.Schemes} (i : T ⟶ T') (f : T ⟶ S) (g : T' ⟶ S') (h : S ⟶ S'),
      Stacks.Thickenings.IsThickening (B.inclusion.map i) → IsAffineHom (B.inclusion.map f) →
      IsPushout (B.inclusion.map i) (B.inclusion.map f) (B.inclusion.map g)
        (B.inclusion.map h) →
      Nonempty (CurvePushoutEquivalenceData B hZ i f g h)) :
    SatisfiesRS B integerBase hZ (curvesFiberedCategory B hZ).val.p
      (curvesFiberedCategory B hZ).property := by
  intro X X' Y Y' i j i' j' w hX hX' hY hY' _ _ _ _ hci hpo
  have : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj X) := hX.1
  have : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj X') := hX'.1
  have : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj Y) := hY.1
  have : IsAffine (B.inclusion.obj X.left) := hX.1
  have : IsAffine (B.inclusion.obj Y.left) := hY.1
  have : IsLocalRing Γ((BigFppfOver.toScheme B integerBase hZ).obj X, ⊤) := hX.2.1
  have : IsLocalRing Γ((BigFppfOver.toScheme B integerBase hZ).obj X', ⊤) := hX'.2.1
  have : IsArtinianRing Γ((BigFppfOver.toScheme B integerBase hZ).obj X', ⊤) := hX'.2.2
  have hsurj : Function.Surjective (B.inclusion.map i.left) := by
    let T' := (BigFppfOver.toScheme B integerBase hZ).obj X'
    let T := (BigFppfOver.toScheme B integerBase hZ).obj X
    have : Subsingleton (PrimeSpectrum Γ(T', ⊤)) :=
      Ring.KrullDimLE.subsingleton_primeSpectrum _
    have : Subsingleton (B.inclusion.obj X'.left) := ⟨fun a b =>
      T'.isoSpec.hom.homeomorph.injective (Subsingleton.elim (α := PrimeSpectrum Γ(T', ⊤)) _ _)⟩
    have : Nonempty (B.inclusion.obj X.left) :=
      (T.isoSpec.inv.homeomorph.symm.nonempty_congr).2 inferInstance
    exact fun _ => ⟨Classical.arbitrary (B.inclusion.obj X.left), Subsingleton.elim _ _⟩
  obtain ⟨D⟩ := h0D56 i.left j.left i'.left j'.left ⟨hci, hsurj⟩ inferInstance hpo
  let Ff := D.toOverlapFromS.toFiberBaseChange B hZ
  let Fg := D.toOverlapFromT'.toFiberBaseChange B hZ
  let Fi := D.fromPushoutToS.toFiberBaseChange B hZ
  let Fj := D.fromPushoutToT'.toFiberBaseChange B hZ
  let ιZ := curvesOverFiberToFiber B hZ Y'
  let R := ιZ ⋙ D.restrictionFunctor ⋙ curvesCatPullbackToOver B hZ D.toOverlapFromS
    D.toOverlapFromT'
  have : D.restrictionFunctor.IsEquivalence := D.equivalence
  exact isEquivalence_fiberSquareComparison_of_restriction (curvesProjectionOver B hZ)
    (curvesFiberedCategory B hZ).property _ j i j' i' w.symm Ff Fg Fi Fj
    (curvesOverFiberIsoOfIso B hZ D.overlapComparison)
    (fun s => D.overlapComparison_canonical (ιZ.obj s)) R
    (curvesOverFiberIsoOfIso B hZ D.restriction_toS)
    (curvesOverFiberIsoOfIso B hZ D.restriction_toT')
    (fun s => Fiber.hom_ext (congrArg (fun m => m.1) (D.restriction_overlap (ιZ.obj s))))

/-- **(RS) for the stack of curves, given that étale charts lift across thickenings.** This is
`AlgebraicGeometry.satisfiesRS_curves_of_curvePushoutEquivalence` applied to
`AlgebraicGeometry.curvePushoutEquivalence_of_hasEtaleChartLifts`, the conclusion of
Stacks 0D56 from the chart lift. -/
public theorem satisfiesRS_curves_of_hasEtaleChartLifts
    (hlift : Space.HasEtaleChartLifts B integerBase hZ) :
    SatisfiesRS B integerBase hZ (curvesFiberedCategory B hZ).val.p
      (curvesFiberedCategory B hZ).property :=
  satisfiesRS_curves_of_curvePushoutEquivalence B hZ fun i f g h hi _ hsq =>
    ⟨curvePushoutEquivalence_of_hasEtaleChartLifts B hZ hlift i f g h hi hsq⟩

end AlgebraicGeometry

end
