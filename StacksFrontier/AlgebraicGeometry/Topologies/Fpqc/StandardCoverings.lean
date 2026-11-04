module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.StandardRefinement

/-!
# Standard fpqc coverings of an affine scheme

A *standard fpqc covering* of an affine scheme `T`, Stacks 022F, is a finite family of flat
morphisms `fᵢ : Uᵢ ⟶ T` with every `Uᵢ` affine whose images cover `T`.  The predicate is formed
for an arbitrary family of morphisms of schemes, with the finiteness of the index and the
affineness of the target and of the sources recorded as fields, so that a client may install them
as local instances; the sources are arbitrary affine schemes rather than literal spectra of rings.

Such a family is an fpqc covering: it is quasi-compact because it is finite with affine members
over an affine base, and jointly surjective with flat members by definition.

## Main definitions

* `AlgebraicGeometry.IsStandardFpqcCovering` — the predicate of Stacks 022F.
* `AlgebraicGeometry.IsStandardFpqcCovering.affineCover` — the affine cover for flatness attached
  to a standard fpqc covering.

## Main results

* `AlgebraicGeometry.IsStandardFpqcCovering.presieve₀_mem_fpqcPrecoverage` — a standard fpqc
  covering is an fpqc covering.
* `AlgebraicGeometry.IsStandardFpqcCovering.of_finite_affineCover` and
  `AlgebraicGeometry.IsStandardFpqcCovering.affineCover` — the two directions of the comparison
  with the `AlgebraicGeometry.Scheme.AffineCover` presentation of the same notion.

## Implementation notes

The notion was previously used only in the shape of an
`AlgebraicGeometry.Scheme.AffineCover` for `AlgebraicGeometry.Flat` with finite index type over
an affine base, as in `AlgebraicGeometry.presieve₀_mem_fpqcPrecoverage_of_finite_affineCover` and
in the refinement statements of Stacks 022E.  That shape is equivalent, but it is not literally
the definition: the finiteness is an extra hypothesis rather than part of the data, and the
sources of an `AffineCover` are spectra of rings rather than arbitrary affine schemes.  Both
directions of the comparison are recorded here, the second by transporting each source along
`AlgebraicGeometry.Scheme.isoSpec`.

The predicate is kept separate from the five-topology predicate
`AlgebraicGeometry.IsStandardCovering`, whose `AlgebraicGeometry.CoveringTopology` enumeration
deliberately excludes the fpqc case; it is the exact analogue of
`AlgebraicGeometry.IsStandardFppfCovering` with the finite presentation requirement dropped.

## References

* [Stacks Project, Tag 022E](https://stacks.math.columbia.edu/tag/022E)
* [Stacks Project, Tag 022F](https://stacks.math.columbia.edu/tag/022F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- A family `fᵢ : Uᵢ ⟶ T` is a **standard fpqc covering** if it is finite, its target and all
its sources are affine, every `fᵢ` is flat, and the images of the `fᵢ` cover `T`. -/
@[stacks 022F]
public structure IsStandardFpqcCovering {T : Scheme.{u}} {I : Type v}
    (U : I → Scheme.{u}) (f : ∀ i, U i ⟶ T) : Prop where
  /-- The family has finitely many members. -/
  finite_index : Finite I
  /-- The target of the covering is affine. -/
  affine_target : IsAffine T
  /-- Every source scheme in the covering is affine. -/
  affine_source : ∀ i, IsAffine (U i)
  /-- Every morphism in the covering is flat. -/
  flat : ∀ i, Flat (f i)
  /-- The images of the morphisms cover the target. -/
  jointly_surjective : (⋃ i, Set.range (f i)) = Set.univ

namespace IsStandardFpqcCovering

variable {T : Scheme.{u}} {I : Type v} {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}

/-- Every point of the target of a standard fpqc covering lies in the image of one of its
members. -/
public lemma exists_mem_range (h : IsStandardFpqcCovering U f) (x : T) :
    ∃ i, x ∈ Set.range (f i) :=
  Set.mem_iUnion.mp (h.jointly_surjective ▸ Set.mem_univ x)

/-- Every point of the target of a standard fpqc covering is the image of a point of one of its
members. -/
public lemma exists_eq (h : IsStandardFpqcCovering U f) (x : T) :
    ∃ (i : I) (y : U i), (f i) y = x := by
  obtain ⟨i, y, hy⟩ := h.exists_mem_range x
  exact ⟨i, y, hy⟩

/-- A standard fpqc covering is a jointly surjective family, so the criterion for membership in
a precoverage of schemes applies to it. -/
public lemma cover_mem₀ (h : IsStandardFpqcCovering U f) :
    Presieve.ofArrows U f ∈ Scheme.precoverage (@Flat.{u}) T :=
  (Scheme.ofArrows_mem_precoverage_iff (@Flat.{u})).mpr ⟨h.exists_mem_range, h.flat⟩

/-- The `AlgebraicGeometry.Scheme.Cover` for flatness underlying a standard fpqc covering.  It is
an `abbrev` so that its index type, sources and members reduce to those of the covering during
typeclass resolution. -/
public abbrev cover (h : IsStandardFpqcCovering U f) :
    T.Cover.{v} (Scheme.precoverage (@Flat.{u})) :=
  ⟨⟨I, U, f⟩, h.cover_mem₀⟩

/-- **Stacks 022F.** A standard fpqc covering is an fpqc covering: a finite jointly surjective
family of flat morphisms from affine schemes to an affine scheme is quasi-compact, hence belongs
to the fpqc precoverage. -/
@[sga "3 IV 6.3.2" "special case"]
public theorem presieve₀_mem_fpqcPrecoverage (h : IsStandardFpqcCovering U f) :
    Presieve.ofArrows U f ∈ Scheme.fpqcPrecoverage T := by
  have hT : IsAffine T := h.affine_target
  have hU : ∀ i, IsAffine (U i) := h.affine_source
  have hI : Finite I := h.finite_index
  have hflat (i : I) : Flat (f i) := h.flat i
  have hjs : Scheme.JointlySurjective (Scheme.precoverage (@Flat.{u})) :=
    @AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage.{u} (@Flat.{u})
  have hfin : Finite h.cover.I₀ := h.finite_index
  have hqcmap (i : h.cover.I₀) : AlgebraicGeometry.QuasiCompact (h.cover.f i) :=
    inferInstanceAs (AlgebraicGeometry.QuasiCompact (f i))
  have hqc : QuasiCompactCover h.cover.toPreZeroHypercover := QuasiCompactCover.of_finite
  show Presieve.ofArrows U f ∈ Scheme.qcPrecoverage T ∧
    Presieve.ofArrows U f ∈ Scheme.precoverage (@Flat.{u}) T
  exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr hqc, h.cover_mem₀⟩

/-- An affine cover for flatness with finite index type over an affine base is a standard fpqc
covering: its sources are spectra of rings, hence affine, its members are flat by `map_prop`, and
its `covers` field is the joint surjectivity. -/
public lemma of_finite_affineCover [IsAffine T] (𝒱 : T.AffineCover.{v} (@Flat.{u}))
    [Finite 𝒱.I₀] : IsStandardFpqcCovering (fun i ↦ Spec (𝒱.X i)) 𝒱.f where
  finite_index := ‹Finite 𝒱.I₀›
  affine_target := ‹IsAffine T›
  affine_source _ := inferInstance
  flat := 𝒱.map_prop
  jointly_surjective :=
    Set.eq_univ_iff_forall.mpr fun x ↦ Set.mem_iUnion.mpr ⟨𝒱.idx x, 𝒱.covers x⟩

/-- The affine cover for flatness attached to a standard fpqc covering: the index type and the
members are those of the covering, each source being transported along the identification
`AlgebraicGeometry.Scheme.isoSpec` of an affine scheme with the spectrum of its ring of global
sections. -/
public noncomputable def affineCover (h : IsStandardFpqcCovering U f) :
    T.AffineCover.{v} (@Flat.{u}) :=
  have hU : ∀ i, IsAffine (U i) := h.affine_source
  { I₀ := I
    X i := Γ(U i, ⊤)
    f i := (U i).isoSpec.inv ≫ f i
    idx x := (h.exists_eq x).choose
    covers x := by
      obtain ⟨y, hy⟩ := (h.exists_eq x).choose_spec
      obtain ⟨z, hz⟩ := (U (h.exists_eq x).choose).isoSpec.inv.surjective y
      exact ⟨z, by rw [Scheme.Hom.comp_apply, hz, hy]⟩
    map_prop i := by
      have : Flat (f i) := h.flat i
      infer_instance }

/-- `AlgebraicGeometry.IsStandardFpqcCovering.affineCover` is indexed by the index type of the
covering. -/
@[simp]
public lemma affineCover_I₀ (h : IsStandardFpqcCovering U f) : h.affineCover.I₀ = I := rfl

/-- `AlgebraicGeometry.IsStandardFpqcCovering.affineCover` has finitely many members, because a
standard fpqc covering is finite. -/
public instance finite_I₀_affineCover (h : IsStandardFpqcCovering U f) :
    Finite h.affineCover.I₀ :=
  h.finite_index

/-- The `i`-th member of `AlgebraicGeometry.IsStandardFpqcCovering.affineCover` is the spectrum of
the ring of global sections of the `i`-th source of the covering; this is that ring. -/
@[simp]
public lemma affineCover_X (h : IsStandardFpqcCovering U f) (i : I) :
    h.affineCover.X i = Γ(U i, ⊤) :=
  rfl

/-- The members of `AlgebraicGeometry.IsStandardFpqcCovering.affineCover` are those of the
covering, precomposed with the identification of the spectrum of the ring of global sections of
the source with the source. -/
@[simp]
public lemma affineCover_f (h : IsStandardFpqcCovering U f) (i : I) [IsAffine (U i)] :
    h.affineCover.f i = (U i).isoSpec.inv ≫ f i :=
  rfl

end IsStandardFpqcCovering

end AlgebraicGeometry

end
