module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs

/-!
# The quasi-finite locus

The points at which a morphism of schemes is quasi-finite form an open subset of the source, and
the morphism restricted to that subset is locally quasi-finite. Openness is proved by exhibiting,
around a point of quasi-finiteness, a pair of affine neighbourhoods on which the morphism becomes
a finite-type ring map; Mathlib's openness of the ring-theoretic quasi-finite locus then supplies
an open neighbourhood contained in the locus.

## Main definitions

* `AlgebraicGeometry.quasiFiniteLocus` is the open locus on which a morphism is quasi-finite.

## Main results

* `AlgebraicGeometry.mem_quasiFiniteLocus_iff` identifies the points of the locus.
* `AlgebraicGeometry.locallyOfFiniteType_quasiFiniteLocus` and
  `AlgebraicGeometry.locallyQuasiFinite_quasiFiniteLocus` say that its induced morphism to the
  target is locally quasi-finite.

## Implementation notes

The locus is constructed as the interior of the set of quasi-finite points, which makes it open
by fiat; the first result is the substance, namely that this interior is the whole set. As in
`AlgebraicGeometry.quasiFiniteAt`, the source's notion of a locally quasi-finite morphism is
represented by the two Mathlib properties `LocallyOfFiniteType` and `LocallyQuasiFinite`, so the
assertion about the induced morphism is split into those two conclusions.

This locus is not Mathlib's `Scheme.Hom.quasiFiniteLocus`: the latter is defined for a morphism
already assumed locally of finite type and uses only the stalkwise condition, whereas this one is
defined for an arbitrary morphism and carries the finite-type condition pointwise.

## References

* [Stacks Project, Tag 01TI](https://stacks.math.columbia.edu/tag/01TI)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Restricting a morphism to a pair of opens does not change where it is quasi-finite, in
Mathlib's stalkwise sense: both sides compare the same stalk map. -/
private lemma resLE_quasiFiniteAt_iff {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens)
    (V : X.Opens) (hVU : V ≤ f ⁻¹ᵁ U) (z : V.toScheme) :
    (f.resLE U V hVU).QuasiFiniteAt z ↔ f.QuasiFiniteAt (V.ι z) := by
  rw [← Scheme.Hom.quasiFiniteAt_comp_iff (g := U.ι),
    Scheme.Hom.resLE_comp_ι, Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion]

/-- The open locus on which a morphism of schemes is quasi-finite. -/
public def quasiFiniteLocus {X S : Scheme.{u}} (f : X ⟶ S) : X.Opens :=
  ⟨interior {x | quasiFiniteAt f x}, isOpen_interior⟩

/-- A point belongs to the locally quasi-finite locus exactly when the morphism is quasi-finite
at that point. In particular, the set of such points is open. -/
@[simp, stacks 01TI "openness of the quasi-finite locus"]
public theorem mem_quasiFiniteLocus_iff {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    x ∈ quasiFiniteLocus f ↔ quasiFiniteAt f x := by
  have hopen : IsOpen {x | quasiFiniteAt f x} := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨U, V, hxV, hVU, hft, hqf⟩ :=
      (quasiFiniteAt_iff_exists_affineOpens f x).mp hx
    have hgft : LocallyOfFiniteType (f.resLE U.1 V.1 hVU) :=
      (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).2
        ((RingHom.finiteType_respectsIso.arrow_mk_iso_iff
          (arrowResLEAppIso f U.1 V.1 hVU)).mpr hft)
    have hgopen : IsOpen {z | (f.resLE U.1 V.1 hVU).QuasiFiniteAt z} :=
      (f.resLE U.1 V.1 hVU).isOpen_quasiFiniteAt
    refine ⟨(fun z : V.1.toScheme ↦ V.1.ι z) ''
        {z | (f.resLE U.1 V.1 hVU).QuasiFiniteAt z}, ?_,
      V.1.2.isOpenEmbedding_subtypeVal.isOpenMap _ hgopen, ?_⟩
    · rintro y ⟨z, hz, rfl⟩
      exact ⟨⟨U, V, z.property, hVU, hft⟩,
        (resLE_quasiFiniteAt_iff f U.1 V.1 hVU z).mp hz⟩
    · exact ⟨⟨x, hxV⟩, (resLE_quasiFiniteAt_iff f U.1 V.1 hVU _).mpr hx.2, rfl⟩
  change x ∈ interior {x | quasiFiniteAt f x} ↔
    x ∈ {x | quasiFiniteAt f x}
  rw [hopen.interior_eq]

/-- The restriction to the quasi-finite locus is locally of finite type. -/
@[stacks 01TI "the induced morphism, local finite type"]
public instance locallyOfFiniteType_quasiFiniteLocus {X S : Scheme.{u}} (f : X ⟶ S) :
    LocallyOfFiniteType ((quasiFiniteLocus f).ι ≫ f) := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFiniteType)
    (RingHom.finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finiteType_holdsForLocalizationAway).left]
  intro x
  have hx := (mem_quasiFiniteLocus_iff f _).mp x.property
  obtain ⟨U, V, hxV, hVU, hft, -⟩ :=
    (quasiFiniteAt_iff_exists_affineOpens f _).mp hx
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    (quasiFiniteLocus f).toScheme.isBasis_affineOpens.exists_subset_of_mem_open
      (show (quasiFiniteLocus f).ι x ∈ V.1 from hxV)
      (((quasiFiniteLocus f).ι ⁻¹ᵁ V.1).2)
  have hgft : LocallyOfFiniteType (f.resLE U.1 V.1 hVU) :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).2
      ((RingHom.finiteType_respectsIso.arrow_mk_iso_iff
        (arrowResLEAppIso f U.1 V.1 hVU)).mpr hft)
  have hWU : W ≤ ((quasiFiniteLocus f).ι ≫ f) ⁻¹ᵁ U.1 := fun y hy => hVU (hWV hy)
  refine ⟨U, ⟨W, hW⟩, hxW, hWU, ?_⟩
  let _ : IsAffine (↑W) := hW
  have hjft : LocallyOfFiniteType ((quasiFiniteLocus f).ι.resLE V.1 W hWV) :=
    instLocallyOfFiniteTypeResLE (quasiFiniteLocus f).ι W V.1 hWV
  exact (RingHom.finiteType_respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso ((quasiFiniteLocus f).ι ≫ f) U.1 W hWU)).mp
      (by
        rw [← HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType),
          ← Scheme.Hom.resLE_comp_resLE (quasiFiniteLocus f).ι hWV f hVU]
        exact MorphismProperty.comp_mem _ _ _ hjft hgft)

/-- The restriction to the quasi-finite locus is locally quasi-finite in Mathlib's
fiber-isolation sense. -/
@[stacks 01TI "the induced morphism, fiber isolation"]
public instance locallyQuasiFinite_quasiFiniteLocus {X S : Scheme.{u}} (f : X ⟶ S) :
    LocallyQuasiFinite ((quasiFiniteLocus f).ι ≫ f) := by
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
  ext x
  constructor
  · intro; trivial
  · intro
    change ((quasiFiniteLocus f).ι ≫ f).QuasiFiniteAt x
    rw [Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion]
    exact ((mem_quasiFiniteLocus_iff f _).mp x.property).2

end AlgebraicGeometry
