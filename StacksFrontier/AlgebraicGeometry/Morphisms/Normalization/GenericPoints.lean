module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Properties
public import StacksCore.Tactic.StacksAttribute

/-!
# Generic points of a scheme and its generic-point residue spectrum

The generic points of `X` lying in an open subscheme `U` are exactly the generic points of `U`,
because an irreducible component of `U` is the part lying in `U` of a unique irreducible
component of `X` meeting `U`.

Take the coproduct of the spectra of the residue fields at the generic points of the
irreducible components of a scheme `X`. The canonical residue-field morphisms assemble to a
morphism from this coproduct to `X`. Normalizing `X` relatively in this morphism is what gives
the normalization of `X` itself, so the elementary properties of the coproduct and of the
morphism are collected here.

The coproduct is a disjoint union of spectra of fields, hence a discrete space with one point
per generic point of `X`; in particular each of its quasi-compact opens has finitely many
irreducible components. The morphism to `X` is dominant, because its image already contains
every generic point of `X` and those are dense.

## Main definitions

* `AlgebraicGeometry.Scheme.genericPointsInOpenEquiv` identifies the generic points of `X`
  lying in an open subscheme with the generic points of that open subscheme.
* `AlgebraicGeometry.Scheme.genericPointResidueSpectrum` is the coproduct of the spectra of the
  residue fields at the generic points of a scheme.
* `AlgebraicGeometry.Scheme.fromGenericPointResidueFields` is the canonical morphism from this
  coproduct to the scheme.

## Main results

* `AlgebraicGeometry.Scheme.genericPointResidueSpectrum_ι_fromGenericPointResidueFields`
  computes the restriction of the canonical morphism to each summand, and
  `AlgebraicGeometry.Scheme.eq_fromGenericPointResidueFields_iff` characterizes the canonical
  morphism by those restrictions.
* `AlgebraicGeometry.Scheme.genericPointResidueSpectrum_finite_irreducibleComponents`: every
  quasi-compact open of the coproduct has finitely many irreducible components.
* `AlgebraicGeometry.Scheme.fromGenericPointResidueFields_isDominant`: the canonical morphism
  is dominant.

## Implementation notes

The set denoted `X^(0)` in the source is `genericPoints X`. The displayed equation of the
source specifies both the coproduct and its canonical morphism to `X`; these are recorded
separately so that later constructions can name either one directly.

Neither the finiteness of the irreducible components of the coproduct nor the dominance of the
canonical morphism needs a finiteness hypothesis on `X`, so both are stated without one.

## References

* [Stacks Project, Tag 035M](https://stacks.math.columbia.edu/tag/035M)
* [Stacks Project, Tag 035N](https://stacks.math.columbia.edu/tag/035N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- **Stacks Project, Tag 035M.** The coproduct of the spectra of the residue fields at the
generic points of the irreducible components of `X`. -/
@[stacks 035M "the source scheme"]
noncomputable def genericPointResidueSpectrum (X : Scheme.{u}) : Scheme.{u} :=
  ∐ fun η : genericPoints X ↦ Spec (.of (X.residueField η.1))

/-- **Stacks Project, Tag 035M.** The canonical morphism from the spectra of the residue fields
at the generic points of `X` to `X`. -/
@[stacks 035M "the morphism"]
noncomputable def fromGenericPointResidueFields (X : Scheme.{u}) :
    genericPointResidueSpectrum X ⟶ X :=
  Sigma.desc fun η : genericPoints X ↦ X.fromSpecResidueField η.1

/-- The canonical morphism from the generic-point residue fields restricts on each summand to
the corresponding residue-field morphism. -/
@[simp, reassoc]
theorem genericPointResidueSpectrum_ι_fromGenericPointResidueFields (X : Scheme.{u})
    (η : genericPoints X) :
    Sigma.ι (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1))) η ≫
      fromGenericPointResidueFields X = X.fromSpecResidueField η.1 := Sigma.ι_comp_desc _ _

/-- A morphism out of the coproduct of the generic-point residue spectra is the canonical one
exactly when its restriction to every summand is the corresponding residue-field morphism. -/
theorem eq_fromGenericPointResidueFields_iff (X : Scheme.{u})
    (f : genericPointResidueSpectrum X ⟶ X) :
    f = fromGenericPointResidueFields X ↔
      ∀ η : genericPoints X,
        Sigma.ι (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1))) η ≫ f =
          X.fromSpecResidueField η.1 :=
  ⟨fun h η ↦ h ▸ genericPointResidueSpectrum_ι_fromGenericPointResidueFields X η,
    fun h ↦ Sigma.hom_ext _ _ fun η ↦ (h η).trans
      (genericPointResidueSpectrum_ι_fromGenericPointResidueFields X η).symm⟩

/-- The generic points of `X` that lie in an open subscheme `U` are exactly the generic points
of `U`: an irreducible component of `U` is the part lying in `U` of a unique irreducible
component of `X` meeting `U`. -/
noncomputable def genericPointsInOpenEquiv (X : Scheme.{u}) (U : X.Opens) :
    {η : genericPoints X // η.1 ∈ U} ≃ genericPoints (U : Set X) := by
  classical
  let toOpen (η : {η : genericPoints X // η.1 ∈ U}) : genericPoints (U : Set X) :=
    ⟨⟨η.1.1, η.2⟩, by
      rw [genericPoints, Set.mem_ofPred_eq,
        Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, Set.image_singleton]
      exact preimage_mem_irreducibleComponents η.1.2
        U.isOpen.isOpenEmbedding_subtypeVal
        ⟨η.1.1, subset_closure (Set.mem_singleton _), ⟨⟨η.1.1, η.2⟩, rfl⟩⟩⟩
  have hinj : Function.Injective toOpen := fun η ξ h ↦
    Subtype.ext <| Subtype.ext <| congrArg (fun z : genericPoints (U : Set X) => z.1.1) h
  have hsurj : Function.Surjective toOpen := by
    intro η
    let C := genericPoints.component η
    let j : U → X := fun x => x.1
    obtain ⟨D, hD, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      (closure (j '' C.1)) (C.2.1.image j continuous_subtype_val.continuousOn).closure
    have hCsub : C.1 ⊆ j ⁻¹' D := fun x hx ↦ hsub (subset_closure ⟨x, hx, rfl⟩)
    have hmeet : (D ∩ Set.range (fun x : U => (x : X))).Nonempty := by
      obtain ⟨x, hx⟩ := C.2.1.nonempty
      exact ⟨x.1, hCsub hx, x, rfl⟩
    have hpre := preimage_mem_irreducibleComponents hD
      U.isOpen.isOpenEmbedding_subtypeVal hmeet
    have hCeq : j ⁻¹' D = C.1 :=
      Set.Subset.antisymm (C.2.2 hpre.1 hCsub) hCsub
    let ξ : genericPoints X := genericPoints.ofComponent ⟨D, hD⟩
    have hξU : ξ.1 ∈ U := by
      change (ξ.1 : X) ∈ (U : Set X)
      rw [(genericPoints.isGenericPoint_ofComponent ⟨D, hD⟩).mem_open_set_iff U.isOpen]
      simpa using hmeet
    refine ⟨⟨ξ, hξU⟩, ?_⟩
    apply genericPoints.component_injective
    apply Subtype.ext
    change closure {⟨ξ.1, hξU⟩} = C.1
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, Set.image_singleton]
    change j ⁻¹' (genericPoints.component ξ).1 = C.1
    rw [genericPoints.component_ofComponent, hCeq]
  exact Equiv.ofBijective toOpen ⟨hinj, hsurj⟩

/-- The generic point of `U` corresponding to a generic point `η` of `X` lying in `U` is `η`
itself, viewed as a point of `U`. -/
@[simp]
theorem genericPointsInOpenEquiv_val (X : Scheme.{u}) (U : X.Opens)
    (η : {η : genericPoints X // η.1 ∈ U}) :
    ((genericPointsInOpenEquiv X U) η).1.1 = η.1.1 := rfl

/-- The generic point of `X` corresponding to a generic point `η` of `U` is the image of `η` in
`X`. -/
theorem genericPointsInOpenEquiv_symm_val (X : Scheme.{u}) (U : X.Opens)
    (η : genericPoints (U : Set X)) :
    ((genericPointsInOpenEquiv X U).symm η).1.1 = η.1.1 := by
  simpa only [genericPointsInOpenEquiv_val] using
    congrArg (fun z : genericPoints (U : Set X) => z.1.1)
      ((genericPointsInOpenEquiv X U).apply_symm_apply η)

/-- Every quasi-compact open in the coproduct of the generic-point residue spectra has finitely
many irreducible components. -/
theorem genericPointResidueSpectrum_finite_irreducibleComponents (X : Scheme.{u})
    (U : (genericPointResidueSpectrum X).Opens)
    (hU : IsCompact (U : Set (genericPointResidueSpectrum X))) :
    (irreducibleComponents U).Finite := by
  let e := sigmaMk (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1)))
  obtain ⟨s, t, hs, _, heq⟩ := (e.isCompact_preimage.mpr hU).sigma_exists_finite_sigma_eq
  have hfin : (U : Set (genericPointResidueSpectrum X)).Finite := by
    rw [← e.image_preimage (U : Set (genericPointResidueSpectrum X)), ← heq]
    exact (hs.sigma fun _ _ ↦ Set.toFinite _).image e
  have : Finite U := hfin
  exact Set.toFinite _

/-- The canonical morphism from the generic-point residue spectra to a scheme is dominant. -/
instance fromGenericPointResidueFields_isDominant (X : Scheme.{u}) :
    IsDominant (fromGenericPointResidueFields X) := by
  rw [isDominant_iff, denseRange_iff_closure_range]
  apply Set.eq_univ_iff_forall.mpr
  intro x
  have hsub : genericPoints X ⊆ Set.range (fromGenericPointResidueFields X) := by
    intro η hη
    let η' : genericPoints X := ⟨η, hη⟩
    refine ⟨sigmaMk (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1)))
      ⟨η', (default : Spec (.of (X.residueField η'.1)))⟩, ?_⟩
    rw [sigmaMk_mk]
    change (Sigma.ι (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1))) η' ≫
      fromGenericPointResidueFields X) default = η
    rw [genericPointResidueSpectrum_ι_fromGenericPointResidueFields,
      X.fromSpecResidueField_apply]
  have hcl := closure_mono hsub
  rw [genericPoints.closure] at hcl
  exact hcl (Set.mem_univ x)

end AlgebraicGeometry.Scheme
