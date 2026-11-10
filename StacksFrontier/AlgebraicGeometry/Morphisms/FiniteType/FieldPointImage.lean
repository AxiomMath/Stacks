module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.SpecField
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint

/-!
# The image of a field-valued point of finite type

A morphism `g : Spec(k) ⟶ X` from the spectrum of a field factors canonically through the
residue field of its image point `x = g(\mathfrak m_k)`, by a field embedding
`κ(x) ⟶ k`. When `g` is locally of finite type that embedding is a *finite* field
extension and `x` is a finite type point of `X`. This is the discussion of Morphisms,
Section 29.16 that the proof of Tag 07XT appeals to.

## Main definitions

* `AlgebraicGeometry.fieldPointResidueEmbedding` — the canonical embedding of the residue
  field of the image point into `k`.

## Main results

* `AlgebraicGeometry.SpecMap_fieldPointResidueEmbedding_fromSpecResidueField` — the
  canonical factorization of `g` through `Spec(κ(x))`.
* `AlgebraicGeometry.isFiniteTypePoint_of_locallyOfFiniteType` — the image of a morphism
  locally of finite type from the spectrum of a field is a finite type point.
* `AlgebraicGeometry.finite_fieldPointResidueEmbedding` — that morphism makes `k` a finite
  extension of the residue field of its image.

## Implementation notes

The embedding and the factorization are `AlgebraicGeometry.Scheme.SpecToEquivOfField` and
its inverse; the image point is read off as `g (IsLocalRing.closedPoint k)`, which is the
first component of that equivalence by definition. Finiteness of the extension is entry (4)
of `AlgebraicGeometry.finiteType_specField_tfae` (Tag 01TA), and the finite type point
property is entry (4) of the same list for the canonical morphism from the residue field,
whose affine chart and closed point are the ones that entry supplies for `g`.

Only local finite type is assumed: a morphism out of the spectrum of a field is
automatically quasi-compact, which is the equivalence of entries (1) and (2) of Tag 01TA.

## References

* [Stacks Project, Tag 01TA](https://stacks.math.columbia.edu/tag/01TA)
* [Stacks Project, Tag 02J1](https://stacks.math.columbia.edu/tag/02J1)
* [Stacks Project, Tag 02J3](https://stacks.math.columbia.edu/tag/02J3)

Both tags are already carried in full elsewhere —
`AlgebraicGeometry.finiteType_specField_tfae` for 01TA and
`AlgebraicGeometry.mapsTo_finiteTypePoints` for 02J3 — so nothing here is tagged.
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The image of a field-valued point of a scheme. -/
public noncomputable abbrev fieldPointImage (g : Spec (.of k) ⟶ X) : X :=
  ((Scheme.SpecToEquivOfField k X) g).1

/-- The image of a field-valued point is the image of the closed point. -/
public theorem fieldPointImage_eq (g : Spec (.of k) ⟶ X) :
    fieldPointImage g = g (IsLocalRing.closedPoint k) := rfl

/-- The canonical embedding of the residue field of the image of a field-valued point into
that field. -/
public noncomputable abbrev fieldPointResidueEmbedding (g : Spec (.of k) ⟶ X) :
    X.residueField (fieldPointImage g) ⟶ CommRingCat.of k :=
  ((Scheme.SpecToEquivOfField k X) g).2

/-- A field-valued point factors through the spectrum of the residue field of its image. -/
public theorem SpecMap_fieldPointResidueEmbedding_fromSpecResidueField
    (g : Spec (.of k) ⟶ X) :
    Spec.map (fieldPointResidueEmbedding g) ≫
        X.fromSpecResidueField (fieldPointImage g) = g :=
  (Scheme.SpecToEquivOfField k X).symm_apply_apply g

/-- The image of a morphism locally of finite type from the spectrum of a field is a finite
type point. -/
public theorem isFiniteTypePoint_of_locallyOfFiniteType (g : Spec (.of k) ⟶ X)
    (hg : LocallyOfFiniteType g) :
    AlgebraicGeometry.IsFiniteTypePoint (fieldPointImage g) := by
  let s := ((Scheme.SpecToEquivOfField k X) g).1
  let k' : Type u := IsLocalRing.ResidueField (X.presheaf.stalk s)
  let g' : Spec (.of k') ⟶ X := X.fromSpecResidueField s
  have hg' : (Scheme.SpecToEquivOfField k' X) g' =
      ⟨s, CommRingCat.ofHom (RingHom.id k')⟩ := by
    rw [← Equiv.eq_symm_apply]
    change g' = Spec.map (𝟙 (.of k')) ≫ X.fromSpecResidueField s
    rw [Spec.map_id]
    exact (Category.id_comp _).symm
  apply ((finiteType_specField_tfae g').out 4 1).mp
  obtain ⟨U, -, y, hy, hyc, -⟩ := ((finiteType_specField_tfae g).out 2 4).mp hg
  refine ⟨U, ?_, y, ?_, hyc, ?_⟩
  · refine (Scheme.preimage_eq_top_of_closedPoint_mem g' ?_).ge
    change ((Scheme.SpecToEquivOfField k' X) g').1 ∈ U.1
    rw [hg', ← hy]
    exact y.property
  · simpa only [hg'] using hy
  · change let q := (Scheme.SpecToEquivOfField k' X) g'
      let := q.2.hom.toAlgebra
      Module.Finite (X.residueField q.1) k'
    rw [hg']
    change Module.Finite k' k'
    infer_instance

/-- A morphism locally of finite type from the spectrum of a field makes that field a finite
extension of the residue field of its image. -/
public theorem finite_fieldPointResidueEmbedding (g : Spec (.of k) ⟶ X)
    (hg : LocallyOfFiniteType g) :
    letI := (fieldPointResidueEmbedding g).hom.toAlgebra
    Module.Finite (X.residueField (fieldPointImage g)) k := by
  obtain ⟨-, -, -, -, -, hfin⟩ := ((finiteType_specField_tfae g).out 2 4).mp hg
  exact hfin

end AlgebraicGeometry

end
