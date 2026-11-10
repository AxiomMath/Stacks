module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Order.Cover
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.KrullDimension
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ImmediateSpecialization
public import StacksFrontier.AlgebraicGeometry.Variety.Automorphisms.PointwiseTrivial
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen

/-!
# Reducing a pointwise trivial endomorphism to integral curves

Let `X` be a reduced scheme locally of finite type over a field `k` and let `f : X ⟶ X` be an
automorphism over `k` fixing every point of the underlying topological space. This file provides
the two devissage steps which cut the verification of `f = 𝟙 X` down to one-dimensional integral
affine pieces.

The first step restricts `f` to the reduced induced structure on each irreducible component:
those closed subschemes are integral, they are stable under `f`, their union is all of `X`, and
an endomorphism of a reduced scheme which is the identity on a dense set of points of a cover is
the identity. The second step, for `X` itself integral, restricts `f` to the reduced induced
structure on integral closed subsets of dimension one through each closed point: the closed
points are dense, and in positive dimension every closed point is covered by such a curve by
taking an irreducible closed subset covering it in the specialization order.

## Main results

* `AlgebraicGeometry.eq_id_of_covering_dense`: an endomorphism of a reduced scheme which is
  fixed by a family of morphisms whose images cover a dense set of points is the identity.
* `AlgebraicGeometry.exists_restriction_to_reduced_closed`: a point-fixing automorphism restricts
  to a point-fixing automorphism of the reduced induced subscheme on any closed subset.
* `AlgebraicGeometry.eq_id_of_integral_closed_restrictions`: the reduction of the positive
  dimensional case to integral schemes of positive dimension.
* `AlgebraicGeometry.exists_integral_closed_curve`: through every closed point of an integral
  Noetherian scheme of positive dimension locally of finite type over a field there is an
  integral closed subscheme of dimension one.
* `AlgebraicGeometry.eq_id_of_affine_integral_curve_restrictions` and
  `AlgebraicGeometry.eq_id_of_integral_curve_restrictions`: the reduction of the integral
  positive dimensional case to integral affine curves, in the affine and the general case.
* `AlgebraicGeometry.eq_id_of_affine_curve_restrictions`: the two reductions composed, cutting
  the positive dimensional case down to integral affine curves in one step.

## Implementation notes

The reduced induced closed subscheme structure on a closed subset `Z` is the subscheme cut out by
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal Z`; its reducedness and its underlying
set are `AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal` and
`AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι_vanishingIdeal`. A curve is recorded by
the equation `topologicalKrullDim = 1` rather than by a bundled structure, and dimension one at a
closed point is read off from the local ring through the dimension formula.

The two reductions take the case they reduce to as a universally quantified hypothesis, so they
are statements about *all* integral schemes (resp. all integral affine curves) over `k` rather
than about a fixed one; this is what lets them be applied to the subschemes produced along the
way.

## References

* [Stacks Project, Tag 0G05](https://stacks.math.columbia.edu/tag/0G05)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The restriction of a point-fixing automorphism to an open subset is an automorphism. -/
lemma isIso_resLE_of_apply_eq {X : Scheme.{u}} (f : X ⟶ X) [IsIso f]
    (hpoints : ∀ x : X, f x = x) (U : X.Opens) :
    IsIso (f.resLE U U (preimage_eq_of_apply_eq f hpoints U).ge) := by
  have hinvpoints : ∀ x : X, inv f x = x := fun x ↦ by
    calc
      inv f x = f (inv f x) := (hpoints _).symm
      _ = x := by simpa using (Scheme.Hom.comp_apply (inv f) f x).symm
  refine ⟨(inv f).resLE U U (preimage_eq_of_apply_eq (inv f) hinvpoints U).ge, ?_, ?_⟩ <;>
    exact (cancel_mono U.ι).mp (by simp)

/-- A point-fixing endomorphism of a reduced scheme is the identity as soon as it is fixed by a
family of morphisms whose images cover a dense set of points.

The restriction of the endomorphism to an affine open `U` agrees with the identity on a closed
subscheme of `U` through which every member of the family passes; that subscheme is dominant,
hence all of `U` because `U` is reduced. -/
theorem eq_id_of_covering_dense {X : Scheme.{u}} [IsReduced X] (f : X ⟶ X)
    (hpoints : ∀ x : X, f x = x) {ι : Type*} {Y : ι → Scheme.{u}} (inclusion : ∀ j, Y j ⟶ X)
    {S : Set X} (hS : Dense S) (hcover : ∀ x ∈ S, ∃ j y, inclusion j y = x)
    (hfix : ∀ j, inclusion j ≫ f = inclusion j) : f = 𝟙 X := by
  apply eq_id_of_resLE_eq_id f hpoints
  intro U
  have : IsAffine U.1.toScheme := U.2
  have : IsReduced U.1.toScheme := isReduced_of_isOpenImmersion U.1.ι
  set g := f.resLE U.1 U.1 (preimage_eq_of_apply_eq f hpoints U.1).ge with hgdef
  have hdom : IsDominant (Limits.equalizer.ι g (𝟙 U.1.toScheme)) := by
    constructor
    apply (hS.preimage U.1.ι.isOpenEmbedding.isOpenMap).mono
    intro x hx
    obtain ⟨j, y, hy⟩ := hcover (U.1.ι x) hx
    have hyV : y ∈ inclusion j ⁻¹ᵁ U.1 := by
      change inclusion j y ∈ U.1
      rw [hy]
      exact x.2
    set r : (inclusion j ⁻¹ᵁ U.1).toScheme ⟶ U.1.toScheme :=
      (inclusion j).resLE U.1 (inclusion j ⁻¹ᵁ U.1) le_rfl with hrdef
    have hr : r ≫ g = r ≫ 𝟙 U.1.toScheme := by
      apply (cancel_mono U.1.ι).mp
      simp only [Category.assoc, Category.id_comp, hrdef, hgdef]
      rw [Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc, Scheme.Hom.resLE_comp_ι, hfix]
    refine ⟨Limits.equalizer.lift r hr (⟨y, hyV⟩ : (inclusion j ⁻¹ᵁ U.1).toScheme), ?_⟩
    have hcomp := Scheme.Hom.comp_apply (Limits.equalizer.lift r hr)
      (Limits.equalizer.ι g (𝟙 U.1.toScheme)) (⟨y, hyV⟩ : (inclusion j ⁻¹ᵁ U.1).toScheme)
    rw [Limits.equalizer.lift_ι] at hcomp
    rw [← hcomp]
    apply Subtype.ext
    rwa [hrdef, Scheme.Hom.coe_resLE_apply]
  have : Surjective (Limits.equalizer.ι g (𝟙 U.1.toScheme)) :=
    surjective_of_isDominant_of_isClosed_range _
      (Limits.equalizer.ι g (𝟙 U.1.toScheme)).isClosedEmbedding.isClosed_range
  have : IsIso (Limits.equalizer.ι g (𝟙 U.1.toScheme)) :=
    isIso_of_isClosedImmersion_of_surjective _
  exact (cancel_epi (Limits.equalizer.ι g (𝟙 U.1.toScheme))).mp
    (Limits.equalizer.condition g (𝟙 _))

/-- A point-fixing automorphism restricts to a point-fixing automorphism of the reduced induced
closed subscheme on any closed subset. -/
theorem exists_restriction_to_reduced_closed {X : Scheme.{u}} (f : X ⟶ X) [IsIso f]
    (hpoints : ∀ x : X, f x = x) (Z : Closeds X) :
    ∃ g : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶
        (Scheme.IdealSheafData.vanishingIdeal Z).subscheme,
      IsIso g ∧
      g ≫ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι =
        (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ f ∧ ∀ x, g x = x := by
  set I := Scheme.IdealSheafData.vanishingIdeal Z with hI
  have hmap : I.map f = I := by
    rw [hI, Scheme.IdealSheafData.map_vanishingIdeal]
    congr 1
    ext x
    simp only [Closeds.coe_closure]
    rw [show f '' (Z : Set X) = Z by simp [funext hpoints]]
    simp only [Z.isClosed.closure_eq]
  refine ⟨I.subschemeMap I f hmap.ge, ?_, ?_, ?_⟩
  · refine IsClosedImmersion.isIso_of_ker_eq (I.subschemeι ≫ f) I.subschemeι _ (by simp) ?_
    simpa only [Scheme.IdealSheafData.map, Scheme.IdealSheafData.ker_subschemeι] using hmap
  · simp
  · intro x
    apply I.subschemeι.isClosedEmbedding.injective
    change (I.subschemeMap I f hmap.ge ≫ I.subschemeι) x = I.subschemeι x
    rw [Scheme.IdealSheafData.subschemeMap_subschemeι, Scheme.Hom.comp_apply, hpoints]

/-- If every point-fixing automorphism over the base of the reduced induced subscheme on a closed
subset `Z` is the identity, then a point-fixing automorphism `f` over the base restricts to the
identity on that subscheme. -/
private lemma subschemeι_comp_eq_of_forall_eq_id {X T : Scheme.{u}} (p : X ⟶ T) (f : X ⟶ X)
    [IsIso f] (hf : f ≫ p = p) (hpoints : ∀ x : X, f x = x) (Z : Closeds X)
    (h : ∀ g : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶
        (Scheme.IdealSheafData.vanishingIdeal Z).subscheme, IsIso g →
      g ≫ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ p =
        (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ p → (∀ y, g y = y) → g = 𝟙 _) :
    (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ f =
      (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι := by
  obtain ⟨g, hgiso, hgi, hgpoints⟩ := exists_restriction_to_reduced_closed f hpoints Z
  have hg := h g hgiso (by rw [← Category.assoc, hgi, Category.assoc, hf]) hgpoints
  rw [hg, Category.id_comp] at hgi
  exact hgi.symm

/-- The reduced induced closed subscheme on a closed subset is homeomorphic to that subset. -/
private noncomputable def vanishingIdealSubschemeHomeo {X : Scheme.{u}} (Z : Closeds X) :
    (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≃ₜ (Z : Set X) :=
  (IsPreimmersion.isEmbedding
      (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι).toHomeomorph.trans
    (Homeomorph.setCongr (Scheme.IdealSheafData.range_subschemeι_vanishingIdeal Z))

/-- The reduced induced closed subscheme on an irreducible closed subset is integral. -/
private lemma isIntegral_vanishingIdeal_subscheme {X : Scheme.{u}} {Z : Closeds X}
    (hZ : IsIrreducible (Z : Set X)) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  have : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme X _
      ((Scheme.IdealSheafData.range_subschemeι_vanishingIdeal Z).symm ▸ hZ)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- **Reduction to the integral case.** An automorphism over `k` of a reduced scheme locally of
finite type over `k` which fixes every point is the identity as soon as the corresponding
statement holds for every integral scheme of positive dimension locally of finite type over `k`.

The automorphism restricts to each irreducible component with its reduced induced structure,
those subschemes are integral of positive dimension, and their images cover `X`. -/
theorem eq_id_of_integral_closed_restrictions {k : Type u} [Field k] {X : Scheme.{u}}
    [IsReduced X] (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (f : X ⟶ X) [IsIso f]
    (hf : f ≫ p = p) (hpoints : ∀ x : X, f x = x)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    (hintegral : ∀ (Y : Scheme.{u}) [IsIntegral Y] (q : Y ⟶ Spec (.of k)) [LocallyOfFiniteType q]
      (g : Y ⟶ Y) [IsIso g], g ≫ q = q → (∀ y, g y = y) → 0 < topologicalKrullDim Y → g = 𝟙 Y) :
    f = 𝟙 X := by
  let Zc (Z : irreducibleComponents X) : Closeds X :=
    ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩
  let I (Z : irreducibleComponents X) := Scheme.IdealSheafData.vanishingIdeal (Zc Z)
  refine eq_id_of_covering_dense f hpoints (Y := fun Z ↦ (I Z).subscheme)
    (fun Z ↦ (I Z).subschemeι) dense_univ (fun x _ ↦ ?_) (fun Z ↦ ?_)
  · refine ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
    change x ∈ Set.range (I ⟨irreducibleComponent x,
      irreducibleComponent_mem_irreducibleComponents x⟩).subschemeι
    rw [Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]
    exact mem_irreducibleComponent
  · have : IsIntegral (I Z).subscheme := isIntegral_vanishingIdeal_subscheme Z.2.1
    have hgdim : 0 < topologicalKrullDim (I Z).subscheme := by
      rw [(vanishingIdealSubschemeHomeo (Zc Z)).isHomeomorph.topologicalKrullDim_eq]
      exact hdim Z.1 Z.2
    exact subschemeι_comp_eq_of_forall_eq_id p f hf hpoints (Zc Z) fun g _ hg hgp ↦
      hintegral (I Z).subscheme ((I Z).subschemeι ≫ p) g hg hgp hgdim

/-- In a Noetherian irreducible space of positive dimension, every closed point is covered, in the
order on irreducible closed subsets, by some irreducible closed subset. -/
private lemma exists_covBy_singleton {X : Type*} [TopologicalSpace X] [NoetherianSpace X]
    [IrreducibleSpace X] (x : X) (hx : IsClosed ({x} : Set X))
    (hdim : 0 < topologicalKrullDim X) :
    ∃ Z : IrreducibleCloseds X,
      (⟨{x}, isIrreducible_singleton, hx⟩ : IrreducibleCloseds X) ⋖ Z := by
  have : WellFoundedLT (IrreducibleCloseds X) :=
    InvImage.wf (fun Z : IrreducibleCloseds X ↦ (⟨Z, Z.isClosed⟩ : Closeds X)) wellFounded_lt
  apply exists_covBy_of_wellFoundedLT
  intro hmax
  have hsubset : (Set.univ : Set X) ⊆ {x} :=
    hmax (show _ ≤ (⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩ :
      IrreducibleCloseds X) from Set.subset_univ _)
  have : Subsingleton X :=
    ⟨fun y z ↦ (hsubset (Set.mem_univ y)).trans (hsubset (Set.mem_univ z)).symm⟩
  exact (not_le_of_gt hdim) (topologicalKrullDim_zero_of_discreteTopology X)

/-- If a sober irreducible space embeds as a closed subset `Z` covering the closure of a point `x`
of it, then `x` is an immediate specialization of the generic point. -/
private lemma isImmediateSpecialization_of_covBy {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T0Space Y] [QuasiSober Y] [IrreducibleSpace Y] (i : Y → X)
    (hi : Topology.IsClosedEmbedding i) (Z : IrreducibleCloseds X) (hrange : Set.range i = Z)
    (x : Y) (hx : IsClosed ({i x} : Set X))
    (hcov : (⟨{i x}, isIrreducible_singleton, hx⟩ : IrreducibleCloseds X) ⋖ Z) :
    IsImmediateSpecialization (genericPoint Y) x := by
  have hgeneric : closure ({i (genericPoint Y)} : Set X) = Z := by
    simpa only [Set.image_univ, hrange, Z.isClosed.closure_eq] using
      ((genericPoint_spec Y).image hi.continuous).def
  refine ⟨(genericPoint_spec Y).specializes trivial, ?_, ?_⟩
  · intro heq
    apply hcov.ne
    apply IrreducibleCloseds.ext
    simpa only [heq, hx.closure_eq, IrreducibleCloseds.coe_mk] using hgeneric
  · intro y _ hyx
    let W : IrreducibleCloseds X :=
      ⟨closure {i y}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hle : (⟨{i x}, isIrreducible_singleton, hx⟩ : IrreducibleCloseds X) ≤ W :=
      Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp (hyx.map hi.continuous))
    have hleZ : W ≤ Z :=
      closure_minimal (Set.singleton_subset_iff.mpr (hrange ▸ Set.mem_range_self y)) Z.isClosed
    rcases hcov.eq_or_eq hle hleZ with hW | hW
    · right
      apply hi.injective
      have hm : i y ∈ W := subset_closure (Set.mem_singleton _)
      rwa [hW] at hm
    · left
      apply IsGenericPoint.eq _ (genericPoint_spec Y)
      rw [isGenericPoint_def, hi.isEmbedding.closure_eq_preimage_closure_image,
        Set.image_singleton]
      change i ⁻¹' (W : Set X) = Set.univ
      rw [hW, ← hrange]
      simp

/-- Through every closed point of an integral Noetherian scheme of positive dimension locally of
finite type over a field there is a closed subset whose reduced induced structure is an integral
scheme of dimension one. -/
theorem exists_integral_closed_curve {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsNoetherian X] (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (x : X)
    (hx : IsClosed ({x} : Set X)) (hdim : 0 < topologicalKrullDim X) :
    ∃ Z : Closeds X,
      IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ∧
      topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = 1 ∧ x ∈ Z := by
  obtain ⟨Z, hZ⟩ := exists_covBy_singleton x hx hdim
  let Zc : Closeds X := ⟨Z, Z.isClosed⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Zc
  have : IsIntegral I.subscheme := isIntegral_vanishingIdeal_subscheme Z.isIrreducible
  have hrange : Set.range I.subschemeι = Z :=
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal Zc
  obtain ⟨y, hy⟩ : x ∈ Set.range I.subschemeι := hrange ▸ hZ.le (Set.mem_singleton _)
  have hyclosed : IsClosed ({y} : Set I.subscheme) := by
    convert hx.preimage I.subschemeι.continuous using 1
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, ← hy,
      I.subschemeι.isClosedEmbedding.injective.eq_iff]
  have himmediate : IsImmediateSpecialization (genericPoint I.subscheme) y :=
    isImmediateSpecialization_of_covBy I.subschemeι I.subschemeι.isClosedEmbedding Z hrange y
      (by simpa only [hy] using hx) (by simpa only [hy] using hZ)
  refine ⟨Zc, inferInstance, ?_, hZ.le (Set.mem_singleton _)⟩
  rw [topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k I.subscheme
      (I.subschemeι ≫ p) y,
    topologicalKrullDimAt_eq_krullDimOfRing_stalk k I.subscheme (I.subschemeι ≫ p) y hyclosed,
    krullDimOfRing_stalk_eq_add_one_of_isImmediateSpecialization k I.subscheme
      (I.subschemeι ≫ p) _ y himmediate (Or.inl inferInstance)]
  change ringKrullDim I.subscheme.functionField + 1 = 1
  rw [ringKrullDim_eq_zero_of_isField (Field.toIsField _), zero_add]

/-- **Reduction to curves, affine case.** An automorphism over `k` of an integral affine scheme of
positive dimension locally of finite type over `k` which fixes every point is the identity as soon
as the corresponding statement holds for every integral affine curve over `k`. -/
theorem eq_id_of_affine_integral_curve_restrictions {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsAffine X] (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (f : X ⟶ X)
    [IsIso f] (hf : f ≫ p = p) (hpoints : ∀ x : X, f x = x) (hdim : 0 < topologicalKrullDim X)
    (hcurve : ∀ (C : Scheme.{u}) [IsIntegral C] [IsAffine C] (q : C ⟶ Spec (.of k))
      [LocallyOfFiniteType q] (g : C ⟶ C) [IsIso g], g ≫ q = q → (∀ y, g y = y) →
      topologicalKrullDim C = 1 → g = 𝟙 C) :
    f = 𝟙 X := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsNoetherian X := ⟨⟩
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  let curves := {Z : Closeds X //
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ∧
    topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = 1}
  let I (Z : curves) := Scheme.IdealSheafData.vanishingIdeal Z.1
  refine eq_id_of_covering_dense f hpoints (Y := fun Z : curves ↦ (I Z).subscheme)
    (fun Z ↦ (I Z).subschemeι)
    (S := closedPoints X) (by rw [dense_iff_closure_eq, closure_closedPoints])
    (fun x hx ↦ ?_) (fun Z ↦ ?_)
  · obtain ⟨Z, hZ, hdimZ, hxZ⟩ := exists_integral_closed_curve p x hx hdim
    refine ⟨⟨Z, hZ, hdimZ⟩, ?_⟩
    change x ∈ Set.range (I ⟨Z, hZ, hdimZ⟩).subschemeι
    rw [Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]
    exact hxZ
  · have : IsIntegral (I Z).subscheme := Z.2.1
    have : IsAffine (I Z).subscheme := isAffine_of_isAffineHom (I Z).subschemeι
    exact subschemeι_comp_eq_of_forall_eq_id p f hf hpoints Z.1 fun g _ hg hgp ↦
      hcurve (I Z).subscheme ((I Z).subschemeι ≫ p) g hg hgp Z.2.2

/-- **Reduction to curves.** An automorphism over `k` of an integral scheme of positive dimension
locally of finite type over `k` which fixes every point is the identity as soon as the
corresponding statement holds for every integral affine curve over `k`.

The restriction of the automorphism to a nonempty affine open subset is an automorphism of an
integral affine scheme of the same positive dimension, so the affine case applies. -/
theorem eq_id_of_integral_curve_restrictions {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (f : X ⟶ X) [IsIso f] (hf : f ≫ p = p)
    (hpoints : ∀ x : X, f x = x) (hdim : 0 < topologicalKrullDim X)
    (hcurve : ∀ (C : Scheme.{u}) [IsIntegral C] [IsAffine C] (q : C ⟶ Spec (.of k))
      [LocallyOfFiniteType q] (g : C ⟶ C) [IsIso g], g ≫ q = q → (∀ y, g y = y) →
      topologicalKrullDim C = 1 → g = 𝟙 C) :
    f = 𝟙 X := by
  apply eq_id_of_resLE_eq_id f hpoints
  intro U
  by_cases hnonempty : (U.1 : Set X).Nonempty
  · have : Nonempty U.1 := hnonempty.to_subtype
    have : IsAffine U.1.toScheme := U.2
    have : IsIntegral U.1.toScheme := isIntegral_of_isOpenImmersion U.1.ι
    have : IsIso (f.resLE U.1 U.1 (preimage_eq_of_apply_eq f hpoints U.1).ge) :=
      isIso_resLE_of_apply_eq f hpoints U.1
    have hUdim : 0 < topologicalKrullDim U.1.toScheme := by
      change 0 < topologicalKrullDim (U.1 : Set X)
      rwa [← topologicalKrullDim_eq_of_isOpen k X p U.1 U.1.isOpen hnonempty]
    refine eq_id_of_affine_integral_curve_restrictions (U.1.ι ≫ p) _ ?_
      (resLE_apply_eq_of_apply_eq f hpoints U.1) hUdim hcurve
    rw [Scheme.Hom.resLE_comp_ι_assoc, hf]
  · have : IsEmpty U.1 := ⟨fun point ↦ hnonempty ⟨point.1, point.2⟩⟩
    exact isInitialOfIsEmpty.hom_ext _ _

/-- **The two reductions together.** An automorphism over `k` of a reduced scheme locally of finite
type over `k` all of whose irreducible components have positive dimension, which fixes every point,
is the identity as soon as the corresponding statement holds for every integral affine curve
over `k`. -/
theorem eq_id_of_affine_curve_restrictions {k : Type u} [Field k] {X : Scheme.{u}} [IsReduced X]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (f : X ⟶ X) [IsIso f] (hf : f ≫ p = p)
    (hpoints : ∀ x : X, f x = x)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    (hcurve : ∀ (C : Scheme.{u}) [IsIntegral C] [IsAffine C] (q : C ⟶ Spec (.of k))
      [LocallyOfFiniteType q] (g : C ⟶ C) [IsIso g], g ≫ q = q → (∀ y, g y = y) →
      topologicalKrullDim C = 1 → g = 𝟙 C) :
    f = 𝟙 X :=
  eq_id_of_integral_closed_restrictions p f hf hpoints hdim
    fun _ _ q _ g _ hg hgp hd ↦ eq_id_of_integral_curve_restrictions q g hg hgp hd hcurve

end AlgebraicGeometry

end
