module

public import StacksFrontier.AlgebraicGeometry.Blowup.RelativeProjGluing

/-!
# Isomorphisms of relative `Proj` gluing data

A relative `Proj` is glued from a `Stacks.RelativeProj.Data`: a graded ring for every affine open
of the base, with restriction maps and a degree-zero identification. Two such data can describe
the same relative `Proj` while being built from genuinely different graded rings — one from the
homogeneous sections of a graded sheaf of algebras, the other from an explicit presentation of
those sections. This file says that an isomorphism of the data is enough to identify the glued
schemes, as schemes over the base.

The comparison is entirely formal. The glued scheme is the colimit of the diagram of charts
`U ↦ Proj (𝒜 U)`, and its structure morphism to the base is the descent of the chart structure
morphisms. A family of graded ring isomorphisms `𝒜 U ≅ ℬ U`, compatible with restriction and with
the degree-zero identifications, therefore induces an isomorphism of the two diagrams over the
cover, hence of the two colimits over the base.

## Main definitions

* `Stacks.RelativeProj.Data.Iso` is an isomorphism between two relative-`Proj` gluing data over
  one base: a graded ring isomorphism over every affine open, natural in the open and compatible
  with the degree-zero identifications.
* `Stacks.RelativeProj.Data.Iso.projIso` is the induced isomorphism of charts.
* `Stacks.RelativeProj.Data.Iso.relativeProjIso` is the induced isomorphism of the glued schemes.

## Main results

* `Stacks.RelativeProj.Data.Iso.projIso_hom_chartToOpen`: the chart isomorphism is a morphism
  over the base.
* `Stacks.RelativeProj.Data.Iso.relativeProjIso_hom_toBase`: **the isomorphism of relative
  `Proj`s is an isomorphism over the base.** This is the point: a bare isomorphism of schemes
  would not identify the two constructions as blowups.
* `Stacks.RelativeProj.Data.Iso.chartι_relativeProjIso_hom`: it is compatible with the charts.

## Implementation notes

An isomorphism of graded rings is given here as a pair of `GradedRingHom`s with both composites
the identity, since Mathlib has no bundled graded ring isomorphism. Only the two homomorphisms
and the two composition laws are data; everything else is a hypothesis.

`AlgebraicGeometry.Proj.map` is contravariant, so the chart isomorphism in the *forward*
direction is `Proj.map` of the *inverse* graded homomorphism. Its hypothesis
`ℬ₊ ≤ 𝒜₊.map f` is automatic for an isomorphism
(`Stacks.RelativeProj.irrelevant_le_map_of_comp_eq_id`), and the two composition laws for
`Proj.map` then make the two morphisms mutually inverse.

The natural isomorphism of diagrams is stated for `Stacks.RelativeProj.Data.gluingData`'s functor
rather than for `Stacks.RelativeProj.Data.functor`, even though those are the same functor: the
`AlgebraicGeometry.Scheme.IsLocallyDirected` instance that provides the colimit is stated for the
functor of a relative gluing datum, and only the first spelling lets instance search find it.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry HomogeneousIdeal Graded

universe u

namespace Stacks.RelativeProj

/-- If `g` is a right inverse of the graded ring homomorphism `f`, then `f (g y) = y`. -/
private theorem apply_apply_of_comp_eq_id {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] {f : 𝒜 →+*ᵍ ℬ} {g : ℬ →+*ᵍ 𝒜}
    (hfg : f.comp g = GradedRingHom.id ℬ) (y : B) : f (g y) = y := by
  simpa only [GradedRingHom.comp_apply, GradedRingHom.id_apply] using
    GradedRingHom.congr_fun hfg y

/-- **The irrelevant-ideal hypothesis of `AlgebraicGeometry.Proj.map` is automatic for an
isomorphism.** If `g` is a right inverse of the graded ring homomorphism `f`, then every
homogeneous element of positive degree of the target is the image of one of the source, so the
irrelevant ideal of the target is covered by the image of the irrelevant ideal of the source. -/
public theorem irrelevant_le_map_of_comp_eq_id {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hfg : f.comp g = GradedRingHom.id ℬ) : ℬ₊ ≤ 𝒜₊.map f := by
  refine (HomogeneousIdeal.irrelevant_le _).mpr fun i hi ↦ ?_
  intro y hy
  have hy' := apply_apply_of_comp_eq_id hfg y
  have hmem : (g y : A) ∈ 𝒜₊.toIdeal :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ hi (map_mem g (show y ∈ ℬ i from hy))
  show y ∈ (𝒜₊.map f).toIdeal
  rw [HomogeneousIdeal.toIdeal_map]
  exact hy' ▸ Ideal.mem_map_of_mem _ hmem

variable {S : Scheme.{u}} {A B σ τ : S.affineOpens → Type u}
  [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)] [∀ U, AddSubgroupClass (σ U) (A U)]
  [∀ U, CommRing (B U)] [∀ U, SetLike (τ U) (B U)] [∀ U, AddSubgroupClass (τ U) (B U)]
  {𝒜 : ∀ U, ℕ → σ U} {ℬ : ∀ U, ℕ → τ U} [∀ U, GradedRing (𝒜 U)] [∀ U, GradedRing (ℬ U)]

/-- **An isomorphism between two relative-`Proj` gluing data over the same base.** Over every
affine open of the base it is an isomorphism of graded rings; the last two fields say that it
commutes with the restriction maps and with the degree-zero identifications. -/
public structure Data.Iso (d : Data 𝒜) (e : Data ℬ) where
  /-- The graded ring homomorphism over an affine open. -/
  hom (U : S.affineOpens) : 𝒜 U →+*ᵍ ℬ U
  /-- Its inverse over an affine open. -/
  inv (U : S.affineOpens) : ℬ U →+*ᵍ 𝒜 U
  /-- The two homomorphisms are inverse, in one direction. -/
  inv_comp_hom (U : S.affineOpens) : (inv U).comp (hom U) = GradedRingHom.id (𝒜 U)
  /-- The two homomorphisms are inverse, in the other direction. -/
  hom_comp_inv (U : S.affineOpens) : (hom U).comp (inv U) = GradedRingHom.id (ℬ U)
  /-- The isomorphism commutes with the restriction maps. -/
  hom_comp_restrict {U V : S.affineOpens} (h : U ≤ V) :
    (hom U).comp (d.restrict h) = (e.restrict h).comp (hom V)
  /-- The isomorphism commutes with the degree-zero identifications. -/
  base_comp_hom (U : S.affineOpens) :
    d.base U ≫ CommRingCat.ofHom (hom U).gradedZeroRingHom = e.base U

namespace Data.Iso

variable {d : Data 𝒜} {e : Data ℬ} (i : Data.Iso d e)

/-- The irrelevant ideal over `U` on the second side is covered by the image of the first. -/
public theorem irrelevant_le_hom (U : S.affineOpens) : (ℬ U)₊ ≤ ((𝒜 U)₊).map (i.hom U) :=
  irrelevant_le_map_of_comp_eq_id _ _ (i.hom_comp_inv U)

/-- The irrelevant ideal over `U` on the first side is covered by the image of the second. -/
public theorem irrelevant_le_inv (U : S.affineOpens) : (𝒜 U)₊ ≤ ((ℬ U)₊).map (i.inv U) :=
  irrelevant_le_map_of_comp_eq_id _ _ (i.inv_comp_hom U)

/-- The inverse of the isomorphism also commutes with the restriction maps. This is the form the
naturality of the chart isomorphism needs, `AlgebraicGeometry.Proj.map` being contravariant. -/
public theorem restrict_comp_inv {U V : S.affineOpens} (h : U ≤ V) :
    (d.restrict h).comp (i.inv V) = (i.inv U).comp (e.restrict h) := by
  refine GradedRingHom.ext fun y ↦ ?_
  have hnat : i.hom U (d.restrict h (i.inv V y)) = e.restrict h y := by
    have h1 := GradedRingHom.congr_fun (i.hom_comp_restrict h) (i.inv V y)
    rwa [GradedRingHom.comp_apply, GradedRingHom.comp_apply,
      apply_apply_of_comp_eq_id (i.hom_comp_inv V)] at h1
  rw [GradedRingHom.comp_apply, GradedRingHom.comp_apply, ← hnat,
    apply_apply_of_comp_eq_id (i.inv_comp_hom U)]

/-- The degree-zero parts of the two homomorphisms are inverse ring isomorphisms. -/
public theorem gradedZeroRingHom_comp_gradedZeroRingHom (U : S.affineOpens) :
    ((i.inv U).gradedZeroRingHom).comp ((i.hom U).gradedZeroRingHom) =
      RingHom.id (𝒜 U 0) := by
  refine RingHom.ext fun x ↦ Subtype.ext ?_
  exact apply_apply_of_comp_eq_id (i.inv_comp_hom U) (x : A U)

/-- The degree-zero identifications are also compatible with the inverse. -/
public theorem base_comp_inv (U : S.affineOpens) :
    e.base U ≫ CommRingCat.ofHom (i.inv U).gradedZeroRingHom = d.base U := by
  rw [← i.base_comp_hom U, Category.assoc, ← CommRingCat.ofHom_comp,
    i.gradedZeroRingHom_comp_gradedZeroRingHom U, CommRingCat.ofHom_id, Category.comp_id]

/-- **The induced isomorphism of charts** over an affine open `U` of the base. -/
public def projIso (U : S.affineOpens) : Proj (𝒜 U) ≅ Proj (ℬ U) where
  hom := Proj.map (i.inv U) (i.irrelevant_le_inv U)
  inv := Proj.map (i.hom U) (i.irrelevant_le_hom U)
  hom_inv_id := by
    refine Eq.trans (Proj.map_comp (i.hom U) (i.inv U) (i.irrelevant_le_hom U)
      (i.irrelevant_le_inv U)).symm ?_
    exact (Proj.map_congr (i.inv_comp_hom U) _ (by simp)).trans Proj.map_id
  inv_hom_id := by
    refine Eq.trans (Proj.map_comp (i.inv U) (i.hom U) (i.irrelevant_le_inv U)
      (i.irrelevant_le_hom U)).symm ?_
    exact (Proj.map_congr (i.hom_comp_inv U) _ (by simp)).trans Proj.map_id

/-- **The chart isomorphism is a morphism over the base.** -/
public theorem projIso_hom_chartToOpen (U : S.affineOpens) :
    (i.projIso U).hom ≫ chartToOpen ℬ U (e.base U) = chartToOpen 𝒜 U (d.base U) := by
  show Proj.map (i.inv U) (i.irrelevant_le_inv U) ≫ chartToOpen ℬ U (e.base U) = _
  rw [chartToOpen, chartToOpen, Proj.map_toSpecZero_assoc, ← Spec.map_comp_assoc,
    i.base_comp_inv U]

/-- **The chart isomorphism is natural in the affine open**: for `U ≤ V`, the
chart isomorphisms commute with the restriction maps `d.map` and `e.map`. -/
public theorem map_projIso_hom {U V : S.affineOpens} (h : U ≤ V) :
    d.map h ≫ (i.projIso V).hom = (i.projIso U).hom ≫ e.map h := by
  show Proj.map (d.restrict h) (d.irrelevant_le h) ≫
      Proj.map (i.inv V) (i.irrelevant_le_inv V) =
    Proj.map (i.inv U) (i.irrelevant_le_inv U) ≫
      Proj.map (e.restrict h) (e.irrelevant_le h)
  refine Eq.trans (Proj.map_comp (i.inv V) (d.restrict h) (i.irrelevant_le_inv V)
    (d.irrelevant_le h)).symm ?_
  refine Eq.trans ?_ (Proj.map_comp (e.restrict h) (i.inv U) (e.irrelevant_le h)
    (i.irrelevant_le_inv U))
  exact Proj.map_congr (i.restrict_comp_inv h) _ _

/-- **The induced isomorphism of the diagrams of charts.** -/
public def natIso : d.gluingData.functor ≅ e.gluingData.functor :=
  NatIso.ofComponents i.projIso fun {_ _} h ↦ i.map_projIso_hom (leOfHom h)

/-- The component of `natIso` at an affine open `U` is the chart isomorphism `projIso U`. -/
@[simp]
public theorem natIso_hom_app (U : S.affineOpens) : i.natIso.hom.app U = (i.projIso U).hom := rfl

/-- **The induced isomorphism of the glued schemes.** -/
public def relativeProjIso : d.relativeProj ≅ e.relativeProj := HasColimit.isoOfNatIso i.natIso

/-- The isomorphism of relative `Proj`s is compatible with the charts. -/
public theorem chartι_relativeProjIso_hom (U : S.affineOpens) :
    d.chartι U ≫ i.relativeProjIso.hom = (i.projIso U).hom ≫ e.chartι U :=
  HasColimit.isoOfNatIso_ι_hom i.natIso U

/-- Over an affine open of the base, the chart isomorphism identifies the two structure
morphisms. -/
public theorem projIso_hom_chartι_toBase (U : S.affineOpens) :
    (i.projIso U).hom ≫ e.chartι U ≫ e.toBase = d.chartι U ≫ d.toBase := by
  rw [Data.chartι_toBase, Data.chartι_toBase, ← Category.assoc, projIso_hom_chartToOpen]

/-- **The isomorphism of relative `Proj`s is an isomorphism over the base**: it commutes with the
two structure morphisms. -/
public theorem relativeProjIso_hom_toBase :
    i.relativeProjIso.hom ≫ e.toBase = d.toBase := by
  refine colimit.hom_ext fun U ↦ ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k ↦ k ≫ e.toBase) (i.chartι_relativeProjIso_hom U)).trans
      ((Category.assoc _ _ _).trans (i.projIso_hom_chartι_toBase U)))

end Data.Iso

end Stacks.RelativeProj

end
