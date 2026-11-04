module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Algebra.SpecOverFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.StructureAlgebra

/-!
# The spectrum of a free algebra structure

Let `m` be a free `d`-dimensional algebra structure over a commutative ring `R`, with `d`
positive. Its spectrum, viewed as a scheme over `Spec R`, is finite locally free of degree `d`,
flat, locally of finite presentation and surjective, and the isomorphisms of free
`d`-dimensional structures over `R` are exactly the isomorphisms of the resulting schemes over
`Spec R`.

## Main definitions

* `AlgebraicGeometry.FiniteFreeAlgebra.specCover`: the spectrum of the algebra of `m`, as a
  scheme over `Spec R`.
* `AlgebraicGeometry.FiniteFreeAlgebra.structureIsoEquivSpecIso`: isomorphisms of free
  `d`-dimensional structures are exactly isomorphisms of their spectra over `Spec R`.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.isFiniteLocallyFreeOfRank_specCover`: the structural
  morphism is finite locally free of degree `d`.
* `AlgebraicGeometry.FiniteFreeAlgebra.isFinite_specCover`,
  `AlgebraicGeometry.FiniteFreeAlgebra.flat_specCover` and
  `AlgebraicGeometry.FiniteFreeAlgebra.locallyOfFinitePresentation_specCover`: the structural
  morphism is finite, flat and locally of finite presentation.
* `AlgebraicGeometry.FiniteFreeAlgebra.surjective_specCover`: the structural morphism is
  surjective.

## References

* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory CommRingCat

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

variable {R : Type u} [CommRing R] {d : ℕ} [NeZero d]

/-- The algebra of a free `d`-dimensional structure over a nontrivial ring is nontrivial. -/
theorem Carrier.nontrivial [Nontrivial R] (m : FiniteFreeAlgebra R d) :
    Nontrivial (Carrier m) := by
  refine ⟨1, 0, fun h => one_ne_zero (α := R) ?_⟩
  simpa [Carrier.one_apply, Carrier.zero_apply] using congrFun h (0 : Fin d)

/-- The spectrum of the algebra of a free `d`-dimensional structure `m`, as a scheme over the
spectrum of the base ring. -/
noncomputable abbrev specCover (m : FiniteFreeAlgebra R d) : Over (Spec (.of R)) :=
  specOver R (Carrier m)

/-- The spectrum of the algebra of a free `d`-dimensional structure is finite locally free of
degree `d` over the base. -/
@[stacks 05YQ "the degree-`d` clause for the spectrum of a free `d`-dimensional structure over \
a ring, in the affine case"]
theorem isFiniteLocallyFreeOfRank_specCover (m : FiniteFreeAlgebra R d) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (specCover m).hom d :=
  (Stacks.Morphisms.isFiniteLocallyFreeOfRank_specMap_iff d).mpr
    (Module.IsFiniteLocallyFreeOfRank.of_basis (Carrier.basis m))

/-- The spectrum of the algebra of a free `d`-dimensional structure is finite locally free. -/
private theorem isFiniteLocallyFree_specCover (m : FiniteFreeAlgebra R d) :
    Stacks.Morphisms.IsFiniteLocallyFree (specCover m).hom :=
  have := isFiniteLocallyFreeOfRank_specCover m
  Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (specCover m).hom d

/-- The spectrum of the algebra of a free `d`-dimensional structure is finite over the base. -/
theorem isFinite_specCover (m : FiniteFreeAlgebra R d) : IsFinite (specCover m).hom :=
  have := isFiniteLocallyFree_specCover m
  Stacks.Morphisms.IsFiniteLocallyFree.isFinite _

/-- The spectrum of the algebra of a free `d`-dimensional structure is flat over the base. -/
theorem flat_specCover (m : FiniteFreeAlgebra R d) : Flat (specCover m).hom :=
  have := isFiniteLocallyFree_specCover m
  Stacks.Morphisms.IsFiniteLocallyFree.flat _

/-- The spectrum of the algebra of a free `d`-dimensional structure is locally of finite
presentation over the base. -/
theorem locallyOfFinitePresentation_specCover (m : FiniteFreeAlgebra R d) :
    LocallyOfFinitePresentation (specCover m).hom :=
  have := isFiniteLocallyFree_specCover m
  Stacks.Morphisms.IsFiniteLocallyFree.locallyOfFinitePresentation _

/-- The spectrum of the algebra of a free `d`-dimensional structure is surjective over the
base. -/
theorem surjective_specCover (m : FiniteFreeAlgebra R d) : Surjective (specCover m).hom := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have hempty : IsEmpty (Spec (CommRingCat.of R)) :=
      ⟨fun p => p.asIdeal.ne_top_iff_one.mp p.isPrime.ne_top (by
        rw [Subsingleton.elim (1 : R) 0]; exact Submodule.zero_mem _)⟩
    exact ⟨fun y => (hempty.false y).elim⟩
  · have := Carrier.nontrivial m
    refine ⟨fun y => ?_⟩
    obtain ⟨x, hx⟩ :=
      PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := Carrier m) y
    exact ⟨x, hx⟩

/-- The isomorphisms of two free `d`-dimensional structures over `R` are exactly the
isomorphisms of their spectra as schemes over `Spec R`. -/
@[stacks 05YQ "clause (a) of the proof over an affine base: `Isom (m, n)` is `Isom (Spec m, \
Spec n)` as schemes over the base"]
noncomputable def structureIsoEquivSpecIso (m n : FiniteFreeAlgebra R d) :
    StructureIso m n ≃ (specCover m ≅ specCover n) where
  toFun e := specOverMapIso ((structureIsoEquivAlgEquiv m n e).symm)
  invFun e := (structureIsoEquivAlgEquiv m n).symm (algEquivOfSpecOverIso e).symm
  left_inv e := by
    dsimp only
    rw [algEquivOfSpecOverIso_specOverMapIso, AlgEquiv.symm_symm, Equiv.symm_apply_apply]
  right_inv e := by
    dsimp only
    rw [Equiv.apply_symm_apply, AlgEquiv.symm_symm, specOverMapIso_algEquivOfSpecOverIso]

end AlgebraicGeometry.FiniteFreeAlgebra

end
