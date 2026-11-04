module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.Examples.GroupSchemes.PrincipalNotFppf.Ring

/-!
# The radical tower as an fpqc covering with no fppf-local section

Let `R` be the radical tower algebra `ℚ[x₀, x₁, …]/(xᵢ ^ (i + 2) - 2)` of
`StacksFrontier.Examples.GroupSchemes.PrincipalNotFppf.Ring` and let `P = Spec R`.  The structure
morphism `P → Spec ℚ` is faithfully flat and affine, hence an fpqc covering, but no fppf
covering of `Spec ℚ` admits a morphism to `P` on each of its members: a morphism locally of
finite type to `Spec ℚ` from a nonempty scheme has a point whose residue field is finite over
`ℚ`, and such a field admits no ring map from `R`.

## Main definitions

* `Stacks.Examples.RadicalTower.base` is `Spec ℚ`.
* `Stacks.Examples.RadicalTower.total` is `Spec R`.
* `Stacks.Examples.RadicalTower.proj` is the structure morphism `Spec R → Spec ℚ`.

## Main results

* `Stacks.Examples.RadicalTower.exists_finite_residueField_point`: a nonempty scheme with a
  morphism locally of finite type to the spectrum of a field has a point whose residue field is
  finite over that field.
* `Stacks.Examples.RadicalTower.singleton_proj_mem_fpqcPrecoverage`: the one-element family
  `{proj}` is an fpqc covering of `Spec ℚ`.
* `Stacks.Examples.RadicalTower.isEmpty_of_locallyOfFiniteType`: a scheme locally of finite
  type over `Spec ℚ` admitting a morphism to `Spec R` is empty.
* `Stacks.Examples.RadicalTower.not_forall_nonempty_hom_of_fppf`: no fppf covering of `Spec ℚ`
  has a morphism to `Spec R` on every member.

## Implementation notes

The base is the spectrum of `ℚ` itself rather than of a universe-lifted copy, so every scheme
here lives in `Scheme.{0}`; this is enough for a counterexample, which only has to exhibit one
base scheme.

Surjectivity of `proj` is immediate because the base is a one-point space and the source is
nonempty, flatness because the base is a field, and quasi-compactness because both are affine.
The negative statement is proved directly from the description of the fppf precoverage as the
jointly surjective families of flat morphisms locally of finite presentation, rather than
through the generated topology.

## References

* [Stacks Project, Tag 077B](https://stacks.math.columbia.edu/tag/077B)
* [Stacks Project, Tag 0478](https://stacks.math.columbia.edu/tag/0478)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Stacks.Examples.RadicalTower

universe u

/-- A nonempty scheme carrying a morphism locally of finite type to the spectrum of a field has
a point whose residue field is finite over that field.  It combines the two parts of
[Stacks Project, Tag 0478](https://stacks.math.columbia.edu/tag/0478) with finiteness of the
morphism at a closed point. -/
theorem exists_finite_residueField_point {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [Nonempty X] :
    ∃ x : X, (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom.Finite := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set X).Nonempty) isClosed_univ.isLocallyClosed
  refine ⟨x, ?_⟩
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have : IsFinite (X.fromSpecResidueField x ≫ f) := by
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    infer_instance
  rw [← IsFinite.SpecMap_iff, Spec.map_preimage]
  infer_instance

/-- The base of the counterexample: the spectrum of the rational numbers. -/
noncomputable abbrev base : Scheme.{0} := Spec (.of ℚ)

/-- The total space of the counterexample: the spectrum of the radical tower algebra. -/
noncomputable abbrev total : Scheme.{0} := Spec (.of Alg)

/-- The structure morphism of the radical tower algebra. -/
noncomputable def proj : total ⟶ base :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ Alg))

/-- The radical tower has points, because its coordinate ring is nonzero. -/
instance : Nonempty total := inferInstanceAs (Nonempty (PrimeSpectrum Alg))

/-- The structure morphism is surjective, the base being a one-point space. -/
instance : Surjective proj :=
  ⟨fun _ => ⟨Classical.arbitrary total, Subsingleton.elim _ _⟩⟩

/-- The structure morphism is flat, the base being a field. -/
instance : Flat proj := by
  rw [proj, HasRingHomProperty.Spec_iff (P := @Flat)]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- The radical tower is an fpqc covering of `Spec ℚ`: it is affine, faithfully flat over the
base, and its base is a one-point space. -/
theorem singleton_proj_mem_fpqcPrecoverage :
    Presieve.singleton proj ∈ Scheme.fpqcPrecoverage base :=
  Scheme.Hom.singleton_mem_fpqcPrecoverage proj

/-- A scheme locally of finite type over `Spec ℚ` which maps to the radical tower is empty: a
point of it would have a residue field finite over `ℚ`, and the radical tower algebra admits no
ring homomorphism to such a field. -/
theorem isEmpty_of_locallyOfFiniteType {X : Scheme.{0}} (f : X ⟶ base)
    [LocallyOfFiniteType f] (g : X ⟶ total) : IsEmpty X := by
  refine ⟨fun x => ?_⟩
  have : Nonempty X := ⟨x⟩
  obtain ⟨y, hy⟩ := exists_finite_residueField_point (K := ℚ) f
  let _ : Algebra ℚ (X.residueField y) :=
    (Spec.preimage (X.fromSpecResidueField y ≫ f)).hom.toAlgebra
  let _ : Module.Finite ℚ (X.residueField y) := hy
  exact no_ringHom_to_finiteDimensional
    (Spec.preimage (X.fromSpecResidueField y ≫ g)).hom

/-- No fppf covering of `Spec ℚ` carries a morphism to the radical tower on each of its
members: some member is nonempty, and a nonempty member is locally of finite presentation,
hence locally of finite type, over the base. -/
theorem not_forall_nonempty_hom_of_fppf {I : Type*} (X : I → Scheme.{0})
    (f : ∀ i, X i ⟶ base)
    (hf : Presieve.ofArrows X f ∈ Scheme.fppfPrecoverage base) :
    ¬ ∀ i, Nonempty (X i ⟶ total) := by
  intro hg
  rw [show Scheme.fppfPrecoverage = Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)
    from rfl, Scheme.ofArrows_mem_precoverage_iff] at hf
  obtain ⟨i, x, -⟩ := hf.1 (Classical.arbitrary base)
  have : LocallyOfFinitePresentation (f i) := (hf.2 i).2
  have : LocallyOfFiniteType (f i) := inferInstance
  exact (isEmpty_of_locallyOfFiniteType (f i) (Classical.choice (hg i))).false x

end Stacks.Examples.RadicalTower

end
