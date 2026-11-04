module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.KrullDimension.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.Modification
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RationalSingularity
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.Nagata.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# The rational singularity situation

Let `A` be a two-dimensional local normal Nagata domain defining a rational singularity, and
let `f : X ⟶ Spec(A)` be a modification with normal source. This file packages this standing
context, together with an enumeration of the irreducible components of the special fibre.

## Main definitions

* `AlgebraicGeometry.RationalSingularitySituation` is the standing rational singularity
  situation.
* `AlgebraicGeometry.RationalSingularitySituation.base`, `.closedPoint` and
  `.puncturedSpectrum` are `Spec(A)`, its closed point, and its punctured spectrum.
* `AlgebraicGeometry.RationalSingularitySituation.specialFiber` is the special fibre, and
  `AlgebraicGeometry.RationalSingularitySituation.component` gives its enumerated irreducible
  components.

## Implementation notes

The maximal ideal and residue field are the canonical ones attached to a local ring. The
components are recorded by an equivalence from `Fin r` to the subtype of irreducible
components, so the enumeration has neither repetitions nor omissions. The Noetherian instance
is obtained from the Nagata hypothesis rather than included as separate data.

## References

* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
-/

@[expose] public noncomputable section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0B4W.** A local normal Nagata domain of dimension two defining a
rational singularity, a normal modification of its spectrum, and an enumeration of the
irreducible components of the special fibre. -/
@[stacks 0B4W]
structure RationalSingularitySituation where
  /-- The local normal Nagata domain. -/
  A : Type u
  /-- The commutative-ring structure on `A`. -/
  [commRing : CommRing A]
  /-- The local-ring hypothesis on `A`. -/
  [localRing : IsLocalRing A]
  /-- The hypothesis that `A` is a normal domain. -/
  [normalDomain : IsNormalDomain A]
  /-- The ring `A` is Nagata. -/
  nagata : IsNagataRing A
  /-- The ring `A` has Krull dimension two. -/
  dimension_two : ringKrullDim A = 2
  /-- The ring `A` defines a rational singularity. -/
  definesRationalSingularity : DefinesRationalSingularity A
  /-- The source of the modification. -/
  X : Scheme.{u}
  /-- The morphism from `X` to the spectrum of `A`. -/
  f : X ⟶ Spec (.of A)
  /-- The source `X` is normal. -/
  [normalSource : IsNormal X]
  /-- The morphism `f` is a modification. -/
  modification : IsModification f
  /-- The number of irreducible components of the special fibre. -/
  numberOfComponents : ℕ
  /-- An enumeration, without repetitions or omissions, of the irreducible components of the
  special fibre. -/
  components : Fin numberOfComponents ≃
    {Z : Set (f.fiber (IsLocalRing.closedPoint A)) //
      Z ∈ irreducibleComponents (f.fiber (IsLocalRing.closedPoint A))}

attribute [instance] RationalSingularitySituation.commRing
  RationalSingularitySituation.localRing RationalSingularitySituation.normalDomain
  RationalSingularitySituation.normalSource

namespace RationalSingularitySituation

/-- A Nagata ring is Noetherian. -/
instance noetherian (S : RationalSingularitySituation) : IsNoetherianRing S.A :=
  S.nagata.1

/-- The maximal ideal `𝔪` of the local ring. -/
abbrev maximalIdeal (S : RationalSingularitySituation) : Ideal S.A :=
  IsLocalRing.maximalIdeal S.A

/-- The residue field `𝜅` of the local ring. -/
abbrev residueField (S : RationalSingularitySituation) : Type u :=
  IsLocalRing.ResidueField S.A

/-- The affine base `Spec(A)`. -/
abbrev base (S : RationalSingularitySituation) : Scheme.{u} :=
  Spec (.of S.A)

/-- The closed point of the affine local scheme `Spec(A)`. -/
abbrev closedPoint (S : RationalSingularitySituation) : S.base :=
  IsLocalRing.closedPoint S.A

/-- The open complement of the closed point in `Spec(A)`. -/
def puncturedSpectrumOpen (S : RationalSingularitySituation) : S.base.Opens :=
  ⟨{S.closedPoint}ᶜ, (IsLocalRing.isClosed_singleton_closedPoint S.A).isOpen_compl⟩

/-- The punctured spectrum `Spec(A) ∖ {s}`. -/
abbrev puncturedSpectrum (S : RationalSingularitySituation) : Scheme.{u} :=
  S.puncturedSpectrumOpen.toScheme

/-- The special fibre of the modification over the closed point. -/
abbrev specialFiber (S : RationalSingularitySituation) : Scheme.{u} :=
  S.f.fiber S.closedPoint

/-- The `i`-th irreducible component of the special fibre. -/
abbrev component (S : RationalSingularitySituation)
    (i : Fin S.numberOfComponents) : Set S.specialFiber :=
  (S.components i).1

/-- Each enumerated component is an irreducible component of the special fibre. -/
theorem component_mem_irreducibleComponents (S : RationalSingularitySituation)
    (i : Fin S.numberOfComponents) :
    S.component i ∈ irreducibleComponents S.specialFiber :=
  (S.components i).2

/-- The enumeration of the components has no repetitions. -/
theorem component_injective (S : RationalSingularitySituation) :
    Function.Injective S.component := fun _ _ h => S.components.injective (Subtype.ext h)

/-- Every irreducible component of the special fibre occurs in the enumeration. -/
theorem exists_component_eq (S : RationalSingularitySituation)
    (Z : Set S.specialFiber) (hZ : Z ∈ irreducibleComponents S.specialFiber) :
    ∃ i : Fin S.numberOfComponents, S.component i = Z :=
  (S.components.surjective ⟨Z, hZ⟩).imp fun _ h => congrArg Subtype.val h

/-- The source of the modification is integral. -/
instance source_isIntegral (S : RationalSingularitySituation) : IsIntegral S.X :=
  S.modification.source_isIntegral

/-- The modification is proper. -/
instance isProper (S : RationalSingularitySituation) : IsProper S.f :=
  S.modification.isProper

end RationalSingularitySituation

end AlgebraicGeometry
