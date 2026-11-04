module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.KrullDimension.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.Modification
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# The vanishing situation

A two-dimensional Noetherian normal local domain, a modification of its spectrum, and an
enumeration of the irreducible components of the special fibre. This is the standing context
for the vanishing results in the resolution of surfaces.

## Main definitions

* `AlgebraicGeometry.VanishingSituation` is the standing context of the vanishing results.
* `AlgebraicGeometry.VanishingSituation.base`, `.closedPoint` and `.puncturedSpectrum` are the
  affine base, its closed point, and its punctured spectrum.
* `AlgebraicGeometry.VanishingSituation.specialFiber` is the fibre over the closed point, and
  `AlgebraicGeometry.VanishingSituation.component` gives its enumerated irreducible components.

## Implementation notes

The maximal ideal and residue field are the canonical ones attached to the local ring. The
components are recorded by an equivalence from `Fin r` to the subtype of
`irreducibleComponents`; thus the enumeration has neither repetitions nor omissions.

## References

* [Stacks Project, Tag 0AX8](https://stacks.math.columbia.edu/tag/0AX8)
-/

@[expose] public section

noncomputable section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0AX8.** The standing data for the vanishing results: a
two-dimensional Noetherian normal local domain, a modification of its spectrum, and an
enumeration of the irreducible components of the special fibre. -/
@[stacks 0AX8]
structure VanishingSituation where
  /-- The local ring. -/
  A : Type u
  /-- The commutative-ring structure on `A`. -/
  [commRing : CommRing A]
  /-- The local-ring hypothesis on `A`. -/
  [localRing : IsLocalRing A]
  /-- The Noetherian hypothesis on `A`. -/
  [noetherian : IsNoetherianRing A]
  /-- The hypothesis that `A` is a normal domain. -/
  [normalDomain : IsNormalDomain A]
  /-- The ring `A` has Krull dimension two. -/
  dimension_two : ringKrullDim A = 2
  /-- The source of the modification. -/
  X : Scheme.{u}
  /-- The morphism from `X` to the spectrum of `A`. -/
  f : X ⟶ Spec (.of A)
  /-- The morphism `f` is a modification. -/
  modification : IsModification f
  /-- The number of irreducible components of the special fibre. -/
  numberOfComponents : ℕ
  /-- An enumeration, without repetitions or omissions, of the irreducible components of the
  special fibre. -/
  components : Fin numberOfComponents ≃
    {Z : Set (f.fiber (IsLocalRing.closedPoint A)) //
      Z ∈ irreducibleComponents (f.fiber (IsLocalRing.closedPoint A))}

attribute [instance] VanishingSituation.commRing VanishingSituation.localRing
  VanishingSituation.noetherian VanishingSituation.normalDomain

namespace VanishingSituation

/-- The maximal ideal `𝔪` of the local ring. -/
abbrev maximalIdeal (V : VanishingSituation) : Ideal V.A :=
  IsLocalRing.maximalIdeal V.A

/-- The affine base `S = Spec(A)`. -/
abbrev base (V : VanishingSituation) : Scheme.{u} :=
  Spec (.of V.A)

/-- The closed point `s` of the affine local scheme `S`. -/
abbrev closedPoint (V : VanishingSituation) : V.base :=
  IsLocalRing.closedPoint V.A

/-- The open complement of the closed point in `S`. -/
def puncturedSpectrumOpen (V : VanishingSituation) : V.base.Opens :=
  ⟨{V.closedPoint}ᶜ, (IsLocalRing.isClosed_singleton_closedPoint V.A).isOpen_compl⟩

/-- The punctured spectrum `U = S ∖ {s}`. -/
abbrev puncturedSpectrum (V : VanishingSituation) : Scheme.{u} :=
  V.puncturedSpectrumOpen.toScheme

/-- The special fibre `X_s` of the modification. -/
abbrev specialFiber (V : VanishingSituation) : Scheme.{u} :=
  V.f.fiber V.closedPoint

/-- The `i`-th irreducible component of the special fibre. -/
abbrev component (V : VanishingSituation) (i : Fin V.numberOfComponents) :
    Set V.specialFiber :=
  (V.components i).1

/-- Each enumerated component is an irreducible component of the special fibre. -/
theorem component_mem_irreducibleComponents (V : VanishingSituation)
    (i : Fin V.numberOfComponents) :
    V.component i ∈ irreducibleComponents V.specialFiber :=
  (V.components i).2

/-- The enumeration of the components has no repetitions. -/
theorem component_injective (V : VanishingSituation) : Function.Injective V.component :=
  fun _ _ h => V.components.injective (Subtype.ext h)

/-- Every irreducible component of the special fibre occurs in the enumeration. -/
theorem exists_component_eq (V : VanishingSituation)
    (Z : Set V.specialFiber) (hZ : Z ∈ irreducibleComponents V.specialFiber) :
    ∃ i : Fin V.numberOfComponents, V.component i = Z :=
  ⟨V.components.symm ⟨Z, hZ⟩, congrArg Subtype.val (V.components.apply_symm_apply ⟨Z, hZ⟩)⟩

/-- The source of the modification is integral. -/
instance source_isIntegral (V : VanishingSituation) : IsIntegral V.X :=
  V.modification.source_isIntegral

/-- The modification is proper. -/
instance isProper (V : VanishingSituation) : IsProper V.f :=
  V.modification.isProper

end VanishingSituation

end AlgebraicGeometry

end
