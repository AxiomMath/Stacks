module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FlatDeformation.Deformation
public import StacksFrontier.AlgebraicGeometry.PairDeformation.LiftMorphism
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedRSStar
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStackUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtInfinitesimalLifting

/-!
# The thickening `Spec A ⊂ Spec A'` and the flat deformation underlying a polarized lift

Let `A' → A` be a deformation situation: a surjection of `S`-algebras with square-zero kernel.
The induced morphism `Spec A ⟶ Spec A'` is a closed immersion whose ideal sheaf has square zero,
i.e. a first order thickening of schemes. A polarized family `x` over `Spec A` has a structure
morphism `X ⟶ Spec A`, and a morphism `x ⟶ x'` of polarized families lying over
`Spec A ⟶ Spec A'` is in particular a flat deformation of `X ⟶ Spec A` over `Spec A'`, in the sense
of `Stacks.Thickenings.FlatDeformation`: the total space of `x'` is flat over `Spec A'` and the
square of total spaces is cartesian.

## Main definitions

* `AlgebraicGeometry.PairDeformation.specThickening`: the morphism `Spec A ⟶ Spec A'`.
* `AlgebraicGeometry.PairDeformation.fiberStructure`: the structure morphism `X ⟶ V` of a
  polarized family in the fibre over `V`.
* `AlgebraicGeometry.PairDeformation.flatDeformationOfIsHomLift`: the flat deformation of
  `X ⟶ Spec A` over `Spec A'` underlying a morphism of polarized families over the thickening.

## Main results

* `AlgebraicGeometry.PairDeformation.specThickening_ker_sq`: the ideal sheaf of the thickening has
  square zero.
* `AlgebraicGeometry.PairDeformation.isPullback_fiberStructure`: a morphism of polarized families
  lying over `g` has cartesian square of structure morphisms over `g`.

## References

* [Stacks Project, Tag 0D14](https://stacks.math.columbia.edu/tag/0D14)
* [Stacks Project, Tag 0D1M](https://stacks.math.columbia.edu/tag/0D1M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open Deformation.Artin

universe u

namespace AlgebraicGeometry.PairDeformation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The thickening `Spec A ⊂ Spec A'` -/

section Thickening

variable {a : SiteAlgebra B S hS} (t : DeformationSituation B S hS a)

/-- The morphism `Spec A ⟶ Spec A'` of a deformation situation `A' → A`. -/
public abbrev specThickening :
    B.inclusion.obj a.over.left ⟶ B.inclusion.obj t.top.over.left :=
  B.inclusion.map t.hom.specMap.left

/-- The morphism `Spec A ⟶ Spec A'` is the spectrum of the ring map `A' → A`. -/
public theorem specThickening_eq :
    specThickening t = Spec.map (CommRingCat.ofHom t.hom.ringMap) :=
  t.hom.specMap_spec

/-- The morphism `Spec A ⟶ Spec A'` is a closed immersion, `A' → A` being surjective. -/
public instance isClosedImmersion_specThickening : IsClosedImmersion (specThickening t) := by
  rw [specThickening_eq]
  exact IsClosedImmersion.spec_of_surjective _ t.surjective

/-- The ideal sheaf of `Spec A ⊂ Spec A'` has square zero. -/
public theorem specThickening_ker_sq : (specThickening t).ker ^ 2 = ⊥ := by
  have hker := Space.specMap_ker_sq_eq_bot
    (CommRingCat.ofHom t.hom.ringMap) t.sq_eq_bot
  rw [specThickening_eq]
  ext U : 2
  have : IsAffine (B.inclusion.obj t.top.over.left) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of t.top.carrier)))
  rw [Scheme.IdealSheafData.ideal_pow, Scheme.ker_of_isAffine]
  simp only [Pi.pow_apply, Scheme.IdealSheafData.ofIdealTop_ideal,
    Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  rw [← Ideal.map_pow, hker, Ideal.map_bot]

end Thickening

/-! ### Polarized families in a fibre -/

variable (hT : IsTerminal (B.obj hS))

/-- The base of a polarized family in the fibre over `V` is `V`. -/
public theorem base_eq_of_fiber {V : BigFppfOver B S hS}
    (x : (polarizedSliceProjection B hS hT).Fiber V) : x.1.base = V.left :=
  congrArg Comma.left x.2

/-- The structure morphism `X ⟶ V` of a polarized family in the fibre over `V`. -/
public abbrev fiberStructure {V : BigFppfOver B S hS}
    (x : (polarizedSliceProjection B hS hT).Fiber V) :
    x.1.total ⟶ B.inclusion.obj V.left :=
  x.1.toBase ≫ eqToHom (congrArg B.inclusion.obj (base_eq_of_fiber hT x))

/-- Transport of a cartesian square of structure morphisms along equalities of the bases. -/
private theorem isPullback_transport {X X' : Scheme.{u}} {Y Y' Z Z' : B.Schemes}
    (i : X ⟶ X') (f : X ⟶ B.inclusion.obj Y) (f' : X' ⟶ B.inclusion.obj Y') (b : Y ⟶ Y')
    (h : IsPullback i f f' (B.inclusion.map b)) (hY : Y = Z) (hY' : Y' = Z') (g : Z ⟶ Z')
    (hb : b = eqToHom hY ≫ g ≫ eqToHom hY'.symm) :
    IsPullback i (f ≫ eqToHom (congrArg B.inclusion.obj hY))
      (f' ≫ eqToHom (congrArg B.inclusion.obj hY')) (B.inclusion.map g) := by
  subst hY hY' hb
  simpa using h

/-- A morphism of polarized families lying over `g : V ⟶ W` has a cartesian square of structure
morphisms over `g`. -/
public theorem isPullback_fiberStructure {V W : BigFppfOver B S hS} (g : V ⟶ W)
    (x : (polarizedSliceProjection B hS hT).Fiber V)
    (x' : (polarizedSliceProjection B hS hT).Fiber W) (φ : x.1 ⟶ x'.1)
    (hφ : (polarizedSliceProjection B hS hT).IsHomLift g φ) :
    IsPullback φ.totalMap (fiberStructure hT x) (fiberStructure hT x')
      (B.inclusion.map g.left) := by
  have h₁ : (polarizedProjection B).IsHomLift g.left φ :=
    isHomLift_left_of_sliceAtTerminal (polarizedProjection B) hT g φ hφ
  have hfac := IsHomLift.fac' (polarizedProjection B) g.left φ
  exact isPullback_transport φ.totalMap x.1.toBase x'.1.toBase φ.baseMap φ.cartesian
    (base_eq_of_fiber hT x) (base_eq_of_fiber hT x') g.left hfac

/-- **The flat deformation underlying a polarized lift.** A morphism `x ⟶ x'` of polarized
families lying over `Spec A ⟶ Spec A'` makes the total space of `x'` a flat deformation of the
structure morphism of `x` over the thickening `Spec A ⊂ Spec A'`. -/
public def flatDeformationOfIsHomLift (P : AffineObject B S hS (polarizedSliceProjection B hS hT))
    (t : DeformationSituation B S hS P.alg)
    (x' : (polarizedSliceProjection B hS hT).Fiber t.top.over) (φ : P.obj.1 ⟶ x'.1)
    (hφ : (polarizedSliceProjection B hS hT).IsHomLift t.hom.specMap φ) :
    Stacks.Thickenings.FlatDeformation (specThickening t) (fiberStructure hT P.obj) where
  X' := x'.1.total
  f' := fiberStructure hT x'
  flat := by
    have := x'.1.flat
    infer_instance
  i := φ.totalMap
  isPullback := isPullback_fiberStructure hT t.hom.specMap P.obj x' φ hφ

end AlgebraicGeometry.PairDeformation

end
