module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberDimension
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.LocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.FlatLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PointwiseBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.AlgebraicGeometry.Variety.FibreDimension
public import StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom

/-!
# Dimension of the fibres of a composition

Let `f : X ⟶ Y` and `g : Y ⟶ S` be locally of finite type, let `x` be a point of `X` and write
`y = f x` and `s = g y`. The three scheme-theoretic fibres `X_s`, `X_y` and `Y_s` through `x`
and `y` satisfy

```
dim_x X_s ≤ dim_x X_y + dim_y Y_s,
```

and the inequality is an equality as soon as the morphism of fibres `X_s ⟶ Y_s` induced by `f`
is flat at `x`; in particular as soon as `f` itself is flat at `x`.

## Main definitions

* `AlgebraicGeometry.fiberMapOfComp` is the morphism `X_s ⟶ Y_s` induced by `f`, that is, the
  base change of `f` along `Y_s ⟶ Y`.

## Main results

* `AlgebraicGeometry.topologicalKrullDimAt_fiber_comp_le_add` is the dimension inequality of
  **Stacks Tag 02JS**.
* `AlgebraicGeometry.topologicalKrullDimAt_fiber_comp_eq_add_of_isFlatAt_fiberMapOfComp` and
  `AlgebraicGeometry.topologicalKrullDimAt_fiber_comp_eq_add_of_isFlatAt` are the two equality
  statements of **Stacks Tag 02JS**.

## Implementation notes

Points of the three fibres are named canonically by `AlgebraicGeometry.Scheme.Hom.asFiber`, so
no choice of a point of a fibre product is made; the morphism of fibres carries the canonical
point of `X_s` to the canonical point of `Y_s`
(`AlgebraicGeometry.fiberMapOfComp_asFiber`), and `X_s` is the fibre product of `X` and `Y_s`
over `Y` (`AlgebraicGeometry.isPullback_fiberMapOfComp`), which is what makes `X_y` the fibre of
`X_s ⟶ Y_s`.

The inequality is part (3) of Stacks Tag 0B2L,
`AlgebraicGeometry.topologicalKrullDimAt_le_fiber_add_topologicalKrullDimAt_target`, applied to
`X_s ⟶ Y_s`, which are both locally of finite type over the residue field `κ(s)`; the fibre of
that morphism has the same dimension at `x` as `X_y` by part (1) of Stacks Tag 02FY, since it is
a base change of `f`.

The equality statements are proved by comparing both sides with the dimension formula for a
fibre at a point (Stacks Tag 02FX), which splits each of the three dimensions into the dimension
of a local ring plus a residue-field transcendence degree. The transcendence degrees add up
because the three residue fields form a tower (Stacks Tag 030H), and the local dimensions add up
because the stalk map of `X_s ⟶ Y_s` is a flat local homomorphism of Noetherian local rings
(Stacks Tag 00ON) whose closed fibre is the local ring of the fibre
(`AlgebraicGeometry.quotientStalkEquivFiberStalk`); the dimension of that closed fibre is at
least the dimension of the local ring of `X_y` at `x` by part (2) of Stacks Tag 02FY. Flatness
of the stalk map follows from flatness of `f` at `x` because `X_s ⟶ Y_s` is a base change of
`f`.

## References

* [Stacks Project, Tag 02JS](https://stacks.math.columbia.edu/tag/02JS)
* [Stacks Project, Tag 02FX](https://stacks.math.columbia.edu/tag/02FX)
* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
* [Stacks Project, Tag 0B2L](https://stacks.math.columbia.edu/tag/0B2L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}}

/-! ### The morphism of fibres induced by the first factor of a composition -/

/-- The morphism from the fibre of a composition `f ≫ g` over a point `s` to the fibre of `g`
over `s`, induced by `f` and the identity of `Spec κ(s)`. -/
noncomputable def fiberMapOfComp (f : X ⟶ Y) (g : Y ⟶ S) (s : S) :
    (f ≫ g).fiber s ⟶ g.fiber s :=
  pullback.lift ((f ≫ g).fiberι s ≫ f) ((f ≫ g).fiberToSpecResidueField s)
    (by simpa only [Category.assoc] using (f ≫ g).fiber_fac s)

/-- The morphism of fibres of a composition is compatible with the inclusions of the fibres. -/
@[simp]
lemma fiberMapOfComp_fiberι (f : X ⟶ Y) (g : Y ⟶ S) (s : S) :
    fiberMapOfComp f g s ≫ g.fiberι s = (f ≫ g).fiberι s ≫ f :=
  pullback.lift_fst _ _ _

/-- The morphism of fibres of a composition is a morphism of `Spec κ(s)`-schemes. -/
@[simp]
lemma fiberMapOfComp_fiberToSpecResidueField (f : X ⟶ Y) (g : Y ⟶ S) (s : S) :
    fiberMapOfComp f g s ≫ g.fiberToSpecResidueField s =
      (f ≫ g).fiberToSpecResidueField s :=
  pullback.lift_snd _ _ _

/-- The fibre of a composition over `s` is the fibre product of the source and the fibre of the
second factor over `s`: the morphism of fibres is the base change of the first factor. -/
lemma isPullback_fiberMapOfComp (f : X ⟶ Y) (g : Y ⟶ S) (s : S) :
    IsPullback (fiberMapOfComp f g s) ((f ≫ g).fiberι s) (g.fiberι s) f := by
  have hout : IsPullback (fiberMapOfComp f g s ≫ g.fiberToSpecResidueField s)
      ((f ≫ g).fiberι s) (S.fromSpecResidueField s) (f ≫ g) := by
    rw [fiberMapOfComp_fiberToSpecResidueField]
    exact (IsPullback.of_hasPullback (f ≫ g) (S.fromSpecResidueField s)).flip
  exact hout.of_right (fiberMapOfComp_fiberι f g s)
    (IsPullback.of_hasPullback g (S.fromSpecResidueField s)).flip

/-- The morphism of fibres of a composition carries the canonical point of the fibre of `f ≫ g`
through `x` to the canonical point of the fibre of `g` through `f x`. -/
@[simp]
lemma fiberMapOfComp_asFiber (f : X ⟶ Y) (g : Y ⟶ S) (x : X) :
    fiberMapOfComp f g ((f ≫ g) x) ((f ≫ g).asFiber x) = g.asFiber (f x) := by
  apply (g.fiberι _).isEmbedding.injective
  rw [← Scheme.Hom.comp_apply, fiberMapOfComp_fiberι]
  show f ((f ≫ g).fiberι _ ((f ≫ g).asFiber x)) = g.fiberι _ (g.asFiber (f x))
  rw [Scheme.Hom.fiberι_asFiber, Scheme.Hom.fiberι_asFiber]

/-- If the first factor of a composition is locally of finite type, then so is the induced
morphism of fibres. -/
instance locallyOfFiniteType_fiberMapOfComp (f : X ⟶ Y) (g : Y ⟶ S) [LocallyOfFiniteType f]
    (s : S) : LocallyOfFiniteType (fiberMapOfComp f g s) :=
  MorphismProperty.of_isPullback (isPullback_fiberMapOfComp f g s).flip inferInstance

/-- If the first factor of a composition is a preimmersion, then so is the induced morphism of
fibres: it is topologically the restriction of the first factor. -/
lemma isInducing_fiberMapOfComp {C : Scheme.{u}} (i : C ⟶ X) [IsPreimmersion i] (f : X ⟶ Y)
    (y : Y) : Topology.IsInducing (fiberMapOfComp i f y) := by
  apply (f.fiberι y).isEmbedding.isInducing.of_comp_iff.mp
  have hcomp : Topology.IsInducing (fun z : (i ≫ f).fiber y => ((i ≫ f).fiberι y ≫ i) z) :=
    i.isEmbedding.isInducing.comp ((i ≫ f).fiberι y).isEmbedding.isInducing
  show Topology.IsInducing fun z => (f.fiberι y) (fiberMapOfComp i f y z)
  convert hcomp using 1
  ext z
  exact congrArg (fun m : ((i ≫ f).fiber y ⟶ X) => m z) (fiberMapOfComp_fiberι i f y)

/-! ### The dimension of the fibre of a composition -/

/-- For two morphisms locally of finite type, the dimension at a point of a fibre of their
composition is at most the sum of the dimensions, at the corresponding points, of the two
successive fibres. -/
@[stacks 02JS "the inequality"]
theorem topologicalKrullDimAt_fiber_comp_le_add (f : X ⟶ Y) (g : Y ⟶ S)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] (x : X) :
    topologicalKrullDimAt ((f ≫ g).fiber ((f ≫ g) x)) ((f ≫ g).asFiber x) ≤
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) +
        topologicalKrullDimAt (g.fiber (g (f x))) (g.asFiber (f x)) := by
  have hdim := topologicalKrullDimAt_le_fiber_add_topologicalKrullDimAt_target
    (S.residueField ((f ≫ g) x))
    ((f ≫ g).fiberToSpecResidueField ((f ≫ g) x)) (g.fiberToSpecResidueField ((f ≫ g) x))
    (fiberMapOfComp f g ((f ≫ g) x)) (fiberMapOfComp_fiberToSpecResidueField f g _)
    ((f ≫ g).asFiber x)
  have hfib :=
    topologicalKrullDimAt_fiber_eq_of_isPullback
      (isPullback_fiberMapOfComp f g ((f ≫ g) x)).flip ((f ≫ g).asFiber x)
  rw [Scheme.Hom.fiberι_asFiber (f ≫ g) x] at hfib
  rwa [hfib, fiberMapOfComp_asFiber f g x] at hdim

/-! ### Additivity of the residue-field transcendence degrees -/

/-- The residue field extension of a composition is the composition of the two residue field
extensions, so their transcendence degrees add up. -/
private lemma trdeg_residueField_comp (f : X ⟶ Y) (g : Y ⟶ S) (x : X) :
    letI := (g.residueFieldMap (f x)).hom.toAlgebra
    letI := (f.residueFieldMap x).hom.toAlgebra
    letI := ((f.residueFieldMap x).hom.comp (g.residueFieldMap (f x)).hom).toAlgebra
    Algebra.trdeg (S.residueField (g (f x))) (Y.residueField (f x)) +
        Algebra.trdeg (Y.residueField (f x)) (X.residueField x) =
      Algebra.trdeg (S.residueField (g (f x))) (X.residueField x) := by
  let := (g.residueFieldMap (f x)).hom.toAlgebra
  let := (f.residueFieldMap x).hom.toAlgebra
  let := ((f.residueFieldMap x).hom.comp (g.residueFieldMap (f x)).hom).toAlgebra
  have : IsScalarTower (S.residueField (g (f x))) (Y.residueField (f x)) (X.residueField x) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact _root_.trdeg_add_eq _ _

/-- The transcendence degree of the residue field extension of a composition does not depend on
whether the extension is taken as the one induced by the composition or as the composition of
the two induced extensions. -/
private lemma trdeg_residueField_comp_congr (f : X ⟶ Y) (g : Y ⟶ S) (x : X) :
    letI := ((f ≫ g).residueFieldMap x).hom.toAlgebra
    letI := ((f.residueFieldMap x).hom.comp (g.residueFieldMap (f x)).hom).toAlgebra
    Algebra.trdeg (S.residueField ((f ≫ g) x)) (X.residueField x) =
      Algebra.trdeg (S.residueField (g (f x))) (X.residueField x) := by
  have hmap : ((f ≫ g).residueFieldMap x).hom =
      ((f.residueFieldMap x).hom).comp ((g.residueFieldMap (f x)).hom) :=
    congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp f g x)
  rw [hmap]
  rfl

/-- Additivity of the residue-field transcendence degrees along a composition, in `WithBot ℕ∞`
and with the extension of the composition taken as the one it induces. -/
private lemma trdeg_residueField_comp_toENat (f : X ⟶ Y) (g : Y ⟶ S) (x : X) :
    letI := (g.residueFieldMap (f x)).hom.toAlgebra
    letI := (f.residueFieldMap x).hom.toAlgebra
    letI := ((f ≫ g).residueFieldMap x).hom.toAlgebra
    (Cardinal.toENat (Algebra.trdeg (S.residueField (g (f x))) (Y.residueField (f x))) :
          WithBot ℕ∞) +
        (Cardinal.toENat (Algebra.trdeg (Y.residueField (f x)) (X.residueField x)) :
          WithBot ℕ∞) =
      (Cardinal.toENat (Algebra.trdeg (S.residueField ((f ≫ g) x)) (X.residueField x)) :
        WithBot ℕ∞) := by
  let := (g.residueFieldMap (f x)).hom.toAlgebra
  let := (f.residueFieldMap x).hom.toAlgebra
  let := ((f ≫ g).residueFieldMap x).hom.toAlgebra
  let := ((f.residueFieldMap x).hom.comp (g.residueFieldMap (f x)).hom).toAlgebra
  rw [trdeg_residueField_comp_congr f g x]
  simpa only [map_add, WithBot.coe_add] using
    congrArg (fun c : Cardinal => (Cardinal.toENat c : WithBot ℕ∞))
      (trdeg_residueField_comp f g x)

/-! ### Equality under flatness -/

/-- The local ring of the fibre of `f` at `x` has dimension at most that of the closed fibre of
the stalk map of the induced morphism of fibres, because the latter is the local ring of a base
change of `f` (part (2) of Stacks Tag 02FY). -/
private lemma ringKrullDim_stalk_fiber_le_closedFibre (f : X ⟶ Y) (g : Y ⟶ S)
    [LocallyOfFiniteType f] (x : X) :
    ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) ≤
      ringKrullDim (((fiberMapOfComp f g ((f ≫ g) x)).fiber
        (fiberMapOfComp f g ((f ≫ g) x) ((f ≫ g).asFiber x))).presheaf.stalk
          ((fiberMapOfComp f g ((f ≫ g) x)).asFiber ((f ≫ g).asFiber x))) := by
  have hsq : IsPullback ((f ≫ g).fiberι ((f ≫ g) x)) (fiberMapOfComp f g ((f ≫ g) x)) f
      (g.fiberι ((f ≫ g) x)) := (isPullback_fiberMapOfComp f g ((f ≫ g) x)).flip
  have hbase : f x = (g.fiberι ((f ≫ g) x))
      (fiberMapOfComp f g ((f ≫ g) x) ((f ≫ g).asFiber x)) := by
    rw [fiberMapOfComp_asFiber f g x]
    exact (Scheme.Hom.fiberι_asFiber g (f x)).symm
  have hpoint :
      fiberMap (fiberMapOfComp f g ((f ≫ g) x)) ((f ≫ g).fiberι ((f ≫ g) x))
          (g.fiberι ((f ≫ g) x)) f hsq.w
          (fiberMapOfComp f g ((f ≫ g) x) ((f ≫ g).asFiber x))
          ((fiberMapOfComp f g ((f ≫ g) x)).asFiber ((f ≫ g).asFiber x)) =
        (f.fiberHomeo ((g.fiberι ((f ≫ g) x))
          (fiberMapOfComp f g ((f ≫ g) x) ((f ≫ g).asFiber x)))).symm ⟨x, hbase⟩ := by
    apply (f.fiberι _).isEmbedding.injective
    rw [← Scheme.Hom.comp_apply, fiberMap_fiberι]
    simp only [Scheme.Hom.comp_apply, Scheme.Hom.fiberι_fiberHomeo_symm,
      Scheme.Hom.fiberι_asFiber]
  have hle := ringKrullDim_stalk_fiber_le_of_baseChange hsq ((f ≫ g).asFiber x)
  rwa [hpoint, ringKrullDim_stalk_fiberHomeo_symm f x _ hbase] at hle

/-- The dimension inequality for a composition is an equality as soon as the induced morphism
between the fibres is flat at the point. -/
@[stacks 02JS "equality for a flat morphism of fibres"]
theorem topologicalKrullDimAt_fiber_comp_eq_add_of_isFlatAt_fiberMapOfComp (f : X ⟶ Y)
    (g : Y ⟶ S) [LocallyOfFiniteType f] [LocallyOfFiniteType g] (x : X)
    (hflat : IsFlatAt (fiberMapOfComp f g ((f ≫ g) x)).toLRSHom.toShHom
      ((f ≫ g).asFiber x)) :
    topologicalKrullDimAt ((f ≫ g).fiber ((f ≫ g) x)) ((f ≫ g).asFiber x) =
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) +
        topologicalKrullDimAt (g.fiber (g (f x))) (g.asFiber (f x)) := by
  refine le_antisymm (topologicalKrullDimAt_fiber_comp_le_add f g x) ?_
  let := (g.residueFieldMap (f x)).hom.toAlgebra
  let := (f.residueFieldMap x).hom.toAlgebra
  let := ((f ≫ g).residueFieldMap x).hom.toAlgebra
  have : IsLocallyNoetherian ((f ≫ g).fiber ((f ≫ g) x)) :=
    isLocallyNoetherian_fiber_of_locallyOfFiniteType (f ≫ g) ((f ≫ g) x)
  have : IsLocallyNoetherian (g.fiber ((f ≫ g) x)) :=
    isLocallyNoetherian_fiber_of_locallyOfFiniteType g ((f ≫ g) x)
  let : Algebra ((g.fiber ((f ≫ g) x)).presheaf.stalk
        (fiberMapOfComp f g ((f ≫ g) x) ((f ≫ g).asFiber x)))
      (((f ≫ g).fiber ((f ≫ g) x)).presheaf.stalk ((f ≫ g).asFiber x)) :=
    ((fiberMapOfComp f g ((f ≫ g) x)).stalkMap ((f ≫ g).asFiber x)).hom.toAlgebra
  have : IsLocalHom (algebraMap ((g.fiber ((f ≫ g) x)).presheaf.stalk
        (fiberMapOfComp f g ((f ≫ g) x) ((f ≫ g).asFiber x)))
      (((f ≫ g).fiber ((f ≫ g) x)).presheaf.stalk ((f ≫ g).asFiber x))) :=
    inferInstanceAs
      (IsLocalHom ((fiberMapOfComp f g ((f ≫ g) x)).stalkMap ((f ≫ g).asFiber x)).hom)
  have hsum := ringKrullDim_eq_add_ringKrullDim_closedFibre
    ((g.fiber ((f ≫ g) x)).presheaf.stalk
      (fiberMapOfComp f g ((f ≫ g) x) ((f ≫ g).asFiber x)))
    (((f ≫ g).fiber ((f ≫ g) x)).presheaf.stalk ((f ≫ g).asFiber x)) hflat
  have hQ : ringKrullDim (ClosedFibre
        ((g.fiber ((f ≫ g) x)).presheaf.stalk
          (fiberMapOfComp f g ((f ≫ g) x) ((f ≫ g).asFiber x)))
        (((f ≫ g).fiber ((f ≫ g) x)).presheaf.stalk ((f ≫ g).asFiber x))) =
      ringKrullDim (((fiberMapOfComp f g ((f ≫ g) x)).fiber
        (fiberMapOfComp f g ((f ≫ g) x) ((f ≫ g).asFiber x))).presheaf.stalk
          ((fiberMapOfComp f g ((f ≫ g) x)).asFiber ((f ≫ g).asFiber x))) :=
    ringKrullDim_eq_of_ringEquiv (quotientStalkEquivFiberStalk
      (fiberMapOfComp f g ((f ≫ g) x)) ((f ≫ g).asFiber x))
  rw [hQ] at hsum
  have hA : ringKrullDim ((g.fiber ((f ≫ g) x)).presheaf.stalk
        (fiberMapOfComp f g ((f ≫ g) x) ((f ≫ g).asFiber x))) =
      ringKrullDim ((g.fiber (g (f x))).presheaf.stalk (g.asFiber (f x))) :=
    congrArg (fun p : g.fiber (g (f x)) => ringKrullDim ((g.fiber (g (f x))).presheaf.stalk p))
      (fiberMapOfComp_asFiber f g x)
  rw [hA] at hsum
  rw [topologicalKrullDimAt_fiber_eq_krullDimOfRing_stalk_add_trdeg f x,
    topologicalKrullDimAt_fiber_eq_krullDimOfRing_stalk_add_trdeg g (f x),
    topologicalKrullDimAt_fiber_eq_krullDimOfRing_stalk_add_trdeg (f ≫ g) x, hsum,
    ← trdeg_residueField_comp_toENat f g x]
  exact (add_le_add (add_le_add (ringKrullDim_stalk_fiber_le_closedFibre f g x) le_rfl)
    le_rfl).trans_eq (by ac_rfl)

/-- The dimension inequality for a composition is an equality as soon as the first morphism is
flat at the point. -/
@[stacks 02JS "equality when the first morphism is flat"]
theorem topologicalKrullDimAt_fiber_comp_eq_add_of_isFlatAt (f : X ⟶ Y) (g : Y ⟶ S)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] (x : X)
    (hflat : IsFlatAt f.toLRSHom.toShHom x) :
    topologicalKrullDimAt ((f ≫ g).fiber ((f ≫ g) x)) ((f ≫ g).asFiber x) =
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) +
        topologicalKrullDimAt (g.fiber (g (f x))) (g.asFiber (f x)) := by
  refine topologicalKrullDimAt_fiber_comp_eq_add_of_isFlatAt_fiberMapOfComp f g x ?_
  refine isFlatAt_of_isPullback (isPullback_fiberMapOfComp f g ((f ≫ g) x))
    ((f ≫ g).asFiber x) ?_
  rw [Scheme.Hom.fiberι_asFiber (f ≫ g) x]
  exact hflat

end AlgebraicGeometry

end
