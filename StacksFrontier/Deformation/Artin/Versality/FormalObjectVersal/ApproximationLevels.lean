module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.Stalk
public import StacksFrontier.Deformation.Artin.FormalObject
public import StacksFrontier.Deformation.Artin.FormalObject.Predeformation
public import StacksFrontier.Deformation.Artin.FormalObject.Versal
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Completed.Basic
public import StacksFrontier.Deformation.FormalObject.Associated
public import StacksFrontier.Deformation.FormalObject.Basic
public import StacksFrontier.Deformation.Groupoid.BaseCategory
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.Smooth.Basic
public import StacksFrontier.Deformation.Smooth.Pushforward
public import StacksFrontier.Deformation.Smooth.Versal
public import StacksFrontier.RingTheory.Ideal.RadicalMaximalQuotient

/-!
# The levels of the approximation formal object over a complete local object

Auxiliary material for `Deformation.Artin.isVersalAt_iff_isVersal`: the maps out of the levels
of the formal object attached by the approximation functor to a complete local object, their
compatibility with the transition maps, and their underlying morphisms of schemes, the `n`-th
adic thickenings of the closed point.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Deformation.Artin

universe u v w

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
attribute [local implicit_reducible] CategoryTheory.Functor.Elements
attribute [local implicit_reducible] Deformation.Artin.baseOver
attribute [local implicit_reducible] Deformation.Artin.truncationOver

/-- The map from level `n` of the formal object `ξ` to an object receiving the complete
local object, built from the chosen restrictions of the approximation functor. -/
public noncomputable def approximationLevelToOriginal
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F]
    (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (xR : Deformation.Artin.CompleteLocalObjects B S hS p)
    (ξ : Deformation.Artin.FormalObject B S hS p)
    (hξ : ξ = (Deformation.Artin.approximationFunctor B S hS p hp).obj xR)
    {x : F} (r : xR.obj.1 ⟶ x) (n : ℕ) : ξ.level n ⟶ x := by
  let restriction := Classical.choose (Deformation.Artin.approximationFunctorData B S hS p hp).2
  exact eqToHom (congrArg (fun ζ : Deformation.Artin.FormalObject B S hS p => ζ.level n) hξ) ≫
    restriction xR n ≫ r

/-- The maps out of the levels of `ξ` built from the approximation functor are Cartesian. -/
private theorem approximationLevelToOriginal_cartesian
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F]
    (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (xR : Deformation.Artin.CompleteLocalObjects B S hS p)
    (ξ : Deformation.Artin.FormalObject B S hS p)
    (hξ : ξ = (Deformation.Artin.approximationFunctor B S hS p hp).obj xR)
    {x : F} (r : xR.obj.1 ⟶ x) (n : ℕ) :
    p.IsCartesian (p.map (approximationLevelToOriginal B S hS p hp xR ξ hξ r n))
      (approximationLevelToOriginal B S hS p hp xR ξ hξ r n) := by
  let f := approximationLevelToOriginal B S hS p hp xR ξ hξ r n
  have : p.IsStronglyCartesian (p.map f) f := hp.isStronglyCartesian f
  infer_instance

/-- The maps out of the levels of `ξ` are compatible with its transition maps. -/
public theorem approximationLevelToOriginal_transition
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F]
    (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (xR : Deformation.Artin.CompleteLocalObjects B S hS p)
    (ξ : Deformation.Artin.FormalObject B S hS p)
    (hξ : ξ = (Deformation.Artin.approximationFunctor B S hS p hp).obj xR)
    {x : F} (r : xR.obj.1 ⟶ x) (n : ℕ) :
    ξ.transition n ≫ approximationLevelToOriginal B S hS p hp xR ξ hξ r (n + 1) =
      approximationLevelToOriginal B S hS p hp xR ξ hξ r n := by
  let restriction := Classical.choose (Deformation.Artin.approximationFunctorData B S hS p hp).2
  let hrest := Classical.choose_spec (Deformation.Artin.approximationFunctorData B S hS p hp).2
  let hbase := Classical.choose hrest
  have htrans := (Classical.choose_spec hrest).2.1 xR n
  cases hξ
  simpa [approximationLevelToOriginal, Deformation.Artin.approximationFunctor,
    Category.assoc] using congrArg (fun f => f ≫ r) htrans

/-- A compatible family of maps out of the levels of a formal object collapses the
closed-point arrow to the map out of level `0`. -/
public theorem closedPointArrow_restriction
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : Type v} [Category.{w} F] {p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS}
    (ξ : Deformation.Artin.FormalObject B S hS p) {x : F}
    (r : ∀ n, ξ.level n ⟶ x)
    (hr : ∀ n, ξ.transition n ≫ r (n + 1) = r n) (n : ℕ) :
    Deformation.Artin.FormalObject.closedPointArrow ξ n ≫ r n = r 0 := by
  induction n with
  | zero => simp [Deformation.Artin.FormalObject.closedPointArrow]
  | succ n ih => rw [Deformation.Artin.FormalObject.closedPointArrow, Category.assoc, hr, ih]

/-- The base of the image of a complete local object under the approximation functor is
the chosen complete local base of that object. -/
public theorem approximation_base_eq
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F]
    (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (xR : Deformation.Artin.CompleteLocalObjects B S hS p)
    (ξ : Deformation.Artin.FormalObject B S hS p)
    (hξ : ξ = (Deformation.Artin.approximationFunctor B S hS p hp).obj xR) :
    ξ.base = Deformation.Artin.chosenBase B S hS p xR.obj :=
  (congrArg Deformation.Artin.FormalObject.base hξ).trans
    (Classical.choose (Classical.choose_spec
      (Deformation.Artin.approximationFunctorData B S hS p hp).2) xR)

/-- On underlying schemes the map out of level `n` is the `n`-th adic thickening
inclusion followed by the map of the complete local object. -/
private theorem approximationLevelToOriginal_base
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F]
    (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (xR : Deformation.Artin.CompleteLocalObjects B S hS p)
    (ξ : Deformation.Artin.FormalObject B S hS p)
    (hξ : ξ = (Deformation.Artin.approximationFunctor B S hS p hp).obj xR)
    {x : F} (r : xR.obj.1 ⟶ x) (n : ℕ) :
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
      (eqToHom (ξ.level_eq n).symm ≫
        p.map (approximationLevelToOriginal B S hS p hp xR ξ hξ r n)) =
    AlgebraicGeometry.adicThickeningι ξ.base.R (maximalIdeal ξ.base.R) n ≫
      eqToHom (congrArg (fun A : Deformation.Artin.FormalBase S => Spec (.of A.R))
        (approximation_base_eq B S hS p hp xR ξ hξ)) ≫
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
        (eqToHom (Deformation.Artin.chosenBase_eq B S hS p xR.obj).symm ≫ p.map r) := by
  have hb := (Classical.choose_spec (Classical.choose_spec
    (Deformation.Artin.approximationFunctorData B S hS p hp).2)).2.2.2 xR n
  cases hξ
  simp only [approximationLevelToOriginal, eqToHom_refl, Category.id_comp,
    Functor.map_comp]
  have he := congrArg (fun f => f ≫
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
        (eqToHom (Deformation.Artin.chosenBase_eq B S hS p xR.obj).symm ≫ p.map r)) hb
  simpa only [Functor.map_comp, eqToHom_map, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] using he

/-- Read in the slice over `U`, the map out of level `n` is the `n`-th adic thickening
inclusion followed by the chosen morphism `g` out of the complete local base. -/
public theorem approximationLevelToOriginal_schemeMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F]
    (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (xR : Deformation.Artin.CompleteLocalObjects B S hS p)
    (ξ : Deformation.Artin.FormalObject B S hS p)
    (hξ : ξ = (Deformation.Artin.approximationFunctor B S hS p hp).obj xR)
    {x : F} (r : xR.obj.1 ⟶ x) (U : Over S)
    (hx : (p ⋙ Over.post B.inclusion).obj x = U)
    (g : Spec (.of ξ.base.R) ⟶ U.left)
    (hrbase : HEq
      ((eqToHom (Deformation.Artin.chosenBase_eq B S hS p xR.obj).symm ≫
        p.map r).left.hom ≫ eqToHom (congrArg Over.left hx)) g)
    (n : ℕ) :
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
      (eqToHom (ξ.level_eq n).symm ≫
        p.map (approximationLevelToOriginal B S hS p hp xR ξ hξ r n)) ≫
      eqToHom (congrArg Over.left hx) =
        AlgebraicGeometry.adicThickeningι ξ.base.R (maximalIdeal ξ.base.R) n ≫ g := by
  rw [approximationLevelToOriginal_base]
  simp only [Category.assoc]
  congr 1
  exact eq_of_heq ((eqToHom_comp_heq _ _).trans hrbase)

/-- The spectrum of a local homomorphism takes the closed point to the closed point, so
precomposing a morphism with it evaluates that morphism at the closed point of its source. -/
public theorem closedPoint_comp_eq {X : Scheme.{u}} {T A : CommRingCat.{u}}
    [IsLocalRing T] [IsLocalRing A] (φ : T ⟶ A) [IsLocalHom φ.hom] (c : Spec T ⟶ X) :
    (Spec.map φ ≫ c) (closedPoint A) = c (closedPoint T) :=
  (Scheme.Hom.comp_apply _ _ _).trans (congrArg (fun z => c z) Spec_closedPoint)

end Deformation.Artin

end
