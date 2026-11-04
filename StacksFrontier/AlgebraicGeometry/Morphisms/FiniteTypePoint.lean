module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms of finite type, and finite type points

A morphism of schemes is of finite type at a point if, on suitable affine open
neighbourhoods of that point and its image, the induced ring homomorphism is of finite
type. It is locally of finite type if this holds at every point, and it is of finite type
if in addition it is quasi-compact. A point of a scheme is a *finite type point* when the
canonical morphism from the spectrum of its residue field to the scheme is of finite type.

A closed point is a finite type point, and on an affine scheme it is a maximal ideal whose
residue field is a finite module. These are the three consequences of closedness that the
converse direction of [Stacks, Tag 07YM] draws on: that tag asserts `(1) ⇒ (2)` only at a
closed point, and uses closedness exactly to make the residue field finite over the ring.

Mathlib's `AlgebraicGeometry.LocallyOfFiniteType` uses the equivalent affine-local
characterization requiring finite type for every compatible pair of affine opens.
Following Mathlib's convention, a morphism of finite type is represented by the two
assumptions `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`
rather than by a duplicate bundled predicate; the definition of a finite type point uses
the same representation. The canonical morphism from a residue field is
`AlgebraicGeometry.Scheme.fromSpecResidueField`.

## Main definitions

* `AlgebraicGeometry.finiteTypeAt` says that a scheme morphism is of finite type at a
  point.
* `AlgebraicGeometry.LocallyOfFiniteType` (Mathlib) expresses that a morphism is locally
  of finite type; together with `AlgebraicGeometry.QuasiCompact` it expresses finite type.
* `AlgebraicGeometry.IsFiniteTypePoint` expresses that a point is a finite type point.

## Main results

* `AlgebraicGeometry.isFiniteTypePoint_of_isClosed_singleton` — a closed point is a finite
  type point.
* `AlgebraicGeometry.isMaximal_asIdeal_of_isClosed_singleton` — a closed point of an affine
  scheme is a maximal ideal.
* `Ideal.finiteType_residueField` and
  `AlgebraicGeometry.finiteType_residueField_of_isClosed_singleton` — the residue field at a
  maximal ideal, hence at a closed point of an affine scheme, is of finite type over the ring.

## References

* [Stacks Project, Tag 01T1](https://stacks.math.columbia.edu/tag/01T1)
* [Stacks Project, Tag 02J1](https://stacks.math.columbia.edu/tag/02J1)
* [Stacks Project, Tag 01TB](https://stacks.math.columbia.edu/tag/01TB)
* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes is of finite type at `x` if it induces a finite-type ring map on
some affine open neighbourhood of `x` mapping into an affine open of the target. -/
@[stacks 01T1 "part (1)", ega "IV 1.3.2" "finite type at x"]
def finiteTypeAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : Prop :=
  ∃ (U : Y.affineOpens) (V : X.affineOpens) (_ : x ∈ V.1) (hVU : V.1 ≤ f ⁻¹ᵁ U.1),
    (f.appLE U V hVU).hom.FiniteType

/-- A morphism locally of finite type is of finite type at every point: an affine open of the
target around the image, and an affine open of the source inside its preimage around the point,
exhibit the finite-type ring map. -/
theorem finiteTypeAt_of_locallyOfFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (x : X) : finiteTypeAt f x := by
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).2
  exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hxV, hVU, f.finiteType_appLE hU hV hVU⟩

add_to_stacks 01T1 "part (2), and the local finite-type condition in part (3)"
  AlgebraicGeometry.LocallyOfFiniteType
add_to_sga "3 VIB 1.3" AlgebraicGeometry.LocallyOfFiniteType
add_to_sga "4 Vbis 5.2.0" "partial" AlgebraicGeometry.LocallyOfFiniteType
add_to_ega "I 6.3.1" "partial" AlgebraicGeometry.LocallyOfFiniteType
add_to_ega "I 6.6.2" AlgebraicGeometry.LocallyOfFiniteType
add_to_ega "IV 1.3.2" AlgebraicGeometry.LocallyOfFiniteType
add_to_stacks 06LG "locally algebraic k-scheme, and the local half of algebraic k-scheme"
  AlgebraicGeometry.LocallyOfFiniteType

add_to_stacks 01T1 "the quasi-compact condition in part (3)" AlgebraicGeometry.QuasiCompact
add_to_sga "1 XIII 1.5" AlgebraicGeometry.QuasiCompact
add_to_sga "4 Vbis 4.2.0" "partial" AlgebraicGeometry.QuasiCompact
add_to_sga "6 II 3.0" AlgebraicGeometry.QuasiCompact
add_to_sga "7 VII 1.3.8" "partial" AlgebraicGeometry.QuasiCompact
add_to_ega "0 9.1.1" "special case" AlgebraicGeometry.QuasiCompact
add_to_ega "I 6.6.1" AlgebraicGeometry.QuasiCompact
add_to_ega "IV 1.1.1" AlgebraicGeometry.QuasiCompact
add_to_stacks 06LG "the quasi-compact half of algebraic k-scheme" AlgebraicGeometry.QuasiCompact

/-- A point `s` of a scheme `S` is a finite type point if the canonical morphism
`Spec(κ(s)) ⟶ S` is of finite type. -/
@[stacks 02J1 "finite_type_point"]
public abbrev IsFiniteTypePoint {S : AlgebraicGeometry.Scheme.{u}} (s : S) : Prop :=
  AlgebraicGeometry.LocallyOfFiniteType (S.fromSpecResidueField s) ∧
    AlgebraicGeometry.QuasiCompact (S.fromSpecResidueField s)

/-! ### Closed points -/

/-- A closed point of a scheme is a finite type point: the morphism from the spectrum of its
residue field is a closed immersion
(`AlgebraicGeometry.isClosed_singleton_iff_isClosedImmersion`), hence both locally of finite
type and quasi-compact. -/
@[stacks 01TB "closed points are finite type points"]
public theorem isFiniteTypePoint_of_isClosed_singleton {X : Scheme.{u}} {x : X}
    (hx : IsClosed ({x} : Set X)) : IsFiniteTypePoint x := by
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  constructor <;> infer_instance

/-- A closed point of an affine scheme is a maximal ideal. This is
`PrimeSpectrum.isClosed_singleton_iff_isMaximal`, stated for a point of `Spec` of an object of
`CommRingCat`, which is the shape the deformation-theoretic tags use. -/
@[ega "I 1.1.7" "closed ⇒ maximal"]
public theorem isMaximal_asIdeal_of_isClosed_singleton {A : Type u} [CommRing A]
    {u₀ : Spec (CommRingCat.of A)}
    (hu₀ : IsClosed ({u₀} : Set (Spec (CommRingCat.of A)))) :
    u₀.asIdeal.IsMaximal :=
  (PrimeSpectrum.isClosed_singleton_iff_isMaximal u₀).mp hu₀

end AlgebraicGeometry

/-- The residue field at a maximal ideal is of finite type over the ring: it is the quotient by
that ideal, hence even a finite module. -/
public theorem Ideal.finiteType_residueField {A : Type u} [CommRing A] (p : Ideal A)
    [p.IsMaximal] : Algebra.FiniteType A p.ResidueField :=
  Module.Finite.finiteType p.ResidueField

namespace AlgebraicGeometry

/-- The residue field at a closed point of an affine scheme is of finite type over the ring.

This is the use that the converse direction of [Stacks, Tag 07YM] makes of closedness: it is
the finiteness hypothesis under which [Stacks, Tag 07YL] builds its square-zero extension, and
the source notes that the step "fails if `u₀` is not closed". -/
@[stacks 07YM "the use of closedness: the residue field at the point is of finite type"]
public theorem finiteType_residueField_of_isClosed_singleton {A : Type u} [CommRing A]
    {u₀ : Spec (CommRingCat.of A)}
    (hu₀ : IsClosed ({u₀} : Set (Spec (CommRingCat.of A)))) :
    letI : u₀.asIdeal.IsPrime := u₀.isPrime
    Algebra.FiniteType A u₀.asIdeal.ResidueField := by
  have : u₀.asIdeal.IsPrime := u₀.isPrime
  have : u₀.asIdeal.IsMaximal := isMaximal_asIdeal_of_isClosed_singleton hu₀
  exact u₀.asIdeal.finiteType_residueField

end AlgebraicGeometry
