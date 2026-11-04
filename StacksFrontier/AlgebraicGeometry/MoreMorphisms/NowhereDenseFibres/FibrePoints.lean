module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.Topology
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SourcePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic

/-!
# Points and subschemes of fibres

For a composition `i ≫ f` the fibre of `i ≫ f` over a point `s` maps to the fibre of `f`
over `s`, compatibly with the two inclusions into the sources. This module builds that map,
shows that it inherits being an open or a closed immersion from `i`, and records how a point of
the source sits in the fibre over a point of the target described by an equation rather than by
`f x` itself.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.fiberMapComp` is the induced morphism
  `(i ≫ f).fiber s ⟶ f.fiber s`.
* `AlgebraicGeometry.Scheme.Hom.asFiberAt` sends a point `x` of the source with `f x = y` to
  a point of `f.fiber y`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.fiberMapComp_fiberι` is the compatibility of
  `fiberMapComp` with the inclusions of the fibres into the sources.
* `AlgebraicGeometry.genericPoints_preimage_of_isOpenImmersion` and
  `AlgebraicGeometry.genericPoints_preimage_of_isClosedImmersion` transport generic points of
  irreducible components backwards along an open, respectively closed, immersion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

/-- Over the image point itself, `asFiberAt` is `asFiber`. -/
@[simp]
theorem asFiberAt_rfl {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    asFiberAt f x (f x) rfl = f.asFiber x := rfl

/-- Equal points of the source give equal points of the fibre, whatever the proofs `h`, `h'`. -/
theorem asFiberAt_congr {X Y : Scheme.{u}} (f : X ⟶ Y) {x x' : X} (hxx : x = x') (y : Y)
    (h : f x = y) (h' : f x' = y) : asFiberAt f x y h = asFiberAt f x' y h' := by
  cases hxx
  simp [asFiberAt]

/-- The inclusion of the fibre sends `asFiberAt f x y h` back to `x`. -/
theorem fiberι_asFiberAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y) (h : f x = y) :
    f.fiberι y (asFiberAt f x y h) = x := by
  cases h
  exact f.fiberι_asFiber x

/-- If `x` is a generic point of its fibre over `f x`, then it is a generic point of the fibre
over any `y` with `f x = y`. -/
theorem asFiberAt_mem_genericPoints {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y)
    (h : f x = y) (hx : f.asFiber x ∈ genericPoints (f.fiber (f x))) :
    asFiberAt f x y h ∈ genericPoints (f.fiber y) := by
  cases h
  exact hx

/-- The local dimension of the fibre at `x` does not depend on how its base point is named. -/
theorem topologicalKrullDimAt_asFiberAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y)
    (h : f x = y) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      topologicalKrullDimAt (f.fiber y) (asFiberAt f x y h) := by
  cases h
  rfl

/-- The morphism from the fibre of a composition `i ≫ f` to the fibre of `f` over the same
point of the target. -/
noncomputable def fiberMapComp {T X S : Scheme.{u}} (i : T ⟶ X) (f : X ⟶ S) (s : S) :
    (i ≫ f).fiber s ⟶ f.fiber s :=
  (pullbackRightPullbackFstIso f (S.fromSpecResidueField s) i).inv ≫
    pullback.snd i (f.fiberι s)

/-- The morphism of fibres induced by a composition `i ≫ f` is compatible with the inclusions of
the fibres into `X` and `T`. -/
theorem fiberMapComp_fiberι {T X S : Scheme.{u}} (i : T ⟶ X) (f : X ⟶ S) (s : S) :
    fiberMapComp i f s ≫ f.fiberι s = (i ≫ f).fiberι s ≫ i := by
  change
    ((pullbackRightPullbackFstIso f (S.fromSpecResidueField s) i).inv ≫
      pullback.snd i (pullback.fst f (S.fromSpecResidueField s))) ≫
      pullback.fst f (S.fromSpecResidueField s) =
    pullback.fst (i ≫ f) (S.fromSpecResidueField s) ≫ i
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    pullbackRightPullbackFstIso_inv_fst]

/-- The morphism of fibres induced by a composition is compatible with the two maps to the
spectrum of the residue field at the base point. -/
theorem fiberMapComp_fiberToSpecResidueField {T X S : Scheme.{u}} (i : T ⟶ X) (f : X ⟶ S)
    (s : S) : fiberMapComp i f s ≫ f.fiberToSpecResidueField s =
      (i ≫ f).fiberToSpecResidueField s :=
  pullbackRightPullbackFstIso_inv_snd_snd f (S.fromSpecResidueField s) i

/-- The image of the fibre of a composition `i ≫ f` inside the fibre of `f` is the part of the
latter lying over the image of `i`. -/
theorem range_fiberMapComp {T X S : Scheme.{u}} (i : T ⟶ X) (f : X ⟶ S) (s : S) :
    Set.range (fiberMapComp i f s).base = (f.fiberι s).base ⁻¹' Set.range i.base := by
  let e := pullbackRightPullbackFstIso f (S.fromSpecResidueField s) i
  have hsurj : Function.Surjective e.inv.base := fun x => ⟨e.hom.base x, by simp⟩
  show Set.range ((pullback.snd i (pullback.fst f (S.fromSpecResidueField s))).base ∘
      e.inv.base) =
    (pullback.fst f (S.fromSpecResidueField s)).base ⁻¹' Set.range i.base
  rw [Set.range_comp, hsurj.range_eq, Set.image_univ, Scheme.Pullback.range_snd]

/-- The morphism of fibres induced by a composition `i ≫ f` sends the point of `(i ≫ f).fiber s`
given by `t` to the point of `f.fiber s` given by `i t`. -/
theorem fiberMapComp_asFiberAt {T X S : Scheme.{u}} (i : T ⟶ X) (f : X ⟶ S) (t : T) (s : S)
    (h : (i ≫ f) t = s) :
    fiberMapComp i f s (asFiberAt (i ≫ f) t s h) =
      asFiberAt f (i t) s ((Scheme.Hom.comp_apply i f t).symm.trans h) := by
  refine (f.fiberι s).isEmbedding.injective ?_
  simpa [fiberι_asFiberAt] using
    congrArg (fun q => q (asFiberAt (i ≫ f) t s h)) (fiberMapComp_fiberι i f s)

/-- The morphism of fibres induced by a composition `i ≫ f` is a closed immersion when `i` is. -/
theorem isClosedImmersion_fiberMapComp {T X S : Scheme.{u}} (i : T ⟶ X)
    [IsClosedImmersion i] (f : X ⟶ S) (s : S) : IsClosedImmersion (fiberMapComp i f s) := by
  have h : IsClosedImmersion (pullback.snd i (f.fiberι s)) := inferInstance
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    (pullbackRightPullbackFstIso f (S.fromSpecResidueField s) i).inv
    (pullback.snd i (f.fiberι s))).mpr h

/-- The morphism of fibres induced by a composition `i ≫ f` is a closed immersion when `i` is. -/
instance fiberMapComp_isClosedImmersion {T X S : Scheme.{u}} (i : T ⟶ X)
    [IsClosedImmersion i] (f : X ⟶ S) (s : S) : IsClosedImmersion (fiberMapComp i f s) :=
  isClosedImmersion_fiberMapComp i f s

/-- The morphism of fibres induced by a composition `i ≫ f` is an open immersion when `i` is. -/
theorem isOpenImmersion_fiberMapComp {T X S : Scheme.{u}} (i : T ⟶ X) [IsOpenImmersion i]
    (f : X ⟶ S) (s : S) : IsOpenImmersion (fiberMapComp i f s) := by
  have h : IsOpenImmersion (pullback.snd i (f.fiberι s)) := inferInstance
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsOpenImmersion)
    (pullbackRightPullbackFstIso f (S.fromSpecResidueField s) i).inv
    (pullback.snd i (f.fiberι s))).mpr h

/-- The morphism of fibres induced by a composition `i ≫ f` is an open immersion when `i` is. -/
instance fiberMapComp_isOpenImmersion {T X S : Scheme.{u}} (i : T ⟶ X) [IsOpenImmersion i]
    (f : X ⟶ S) (s : S) : IsOpenImmersion (fiberMapComp i f s) :=
  isOpenImmersion_fiberMapComp i f s

end Scheme.Hom

/-- A point of the source of an open immersion whose image is generic in an irreducible
component is itself generic in an irreducible component. -/
theorem genericPoints_preimage_of_isOpenImmersion {A B : Scheme.{u}} (j : A ⟶ B)
    [IsOpenImmersion j] {a : A} (ha : j a ∈ genericPoints B) : a ∈ genericPoints A := by
  have hpre : j ⁻¹' closure ({j a} : Set B) ∈ irreducibleComponents A :=
    preimage_mem_irreducibleComponents ha j.isOpenEmbedding
      ⟨j a, subset_closure (Set.mem_singleton _), ⟨a, rfl⟩⟩
  show closure ({a} : Set A) ∈ irreducibleComponents A
  rw [j.isOpenEmbedding.closure_eq_preimage_closure_image]
  simpa using hpre

/-- A point of the source of a closed immersion whose image is generic in an irreducible
component is itself generic in an irreducible component. -/
theorem genericPoints_preimage_of_isClosedImmersion {A B : Scheme.{u}} (j : A ⟶ B)
    [IsClosedImmersion j] {a : A} (hb : j a ∈ genericPoints B) : a ∈ genericPoints A := by
  have hclosure : j '' closure ({a} : Set A) = closure ({j a} : Set B) := by
    simpa only [Set.image_singleton] using
      (j.isClosedEmbedding.closure_image_eq ({a} : Set A)).symm
  have hpre : j ⁻¹' closure ({j a} : Set B) = closure ({a} : Set A) := by
    rw [← hclosure, Set.preimage_image_eq _ j.isClosedEmbedding.injective]
  have hCmax : Maximal IsIrreducible (closure ({j a} : Set B)) := hb
  refine ⟨isIrreducible_singleton.closure, fun E hE hDE x hx => ?_⟩
  have hCF : closure ({j a} : Set B) ⊆ closure (j '' E) := by
    refine closure_minimal (fun z hz => ?_) isClosed_closure
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact subset_closure ⟨a, hDE (subset_closure (Set.mem_singleton a)), rfl⟩
  have hFC := hCmax.2 ((hE.image j j.continuous.continuousOn).closure) hCF
  rw [← hpre]
  exact hFC (subset_closure (show j x ∈ j '' E from ⟨x, hx, rfl⟩))

end AlgebraicGeometry

end
