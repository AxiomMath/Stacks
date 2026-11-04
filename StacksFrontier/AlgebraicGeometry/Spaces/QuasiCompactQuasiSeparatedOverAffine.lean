module

public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# The source of a quasi-compact quasi-separated morphism to an affine algebraic space

A quasi-compact morphism of algebraic spaces with quasi-compact target has quasi-compact
source, and a quasi-separated morphism with quasi-separated target has quasi-separated
source.  An affine algebraic space satisfies both finiteness conditions, so the source of a
quasi-compact quasi-separated morphism whose target is affine is a quasi-compact,
absolutely quasi-separated algebraic space.

These are exactly the two hypotheses that the filtered-colimit statement for cohomology,
`AlgebraicGeometry.Space.isIso_colimit_post_rightDerived_globalSections` (Stacks 073E), asks
of the space it is applied to, and a morphism to an affine target is how Stacks 073K part (2)
produces them for the source of a quasi-compact quasi-separated morphism.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.IsAffineSpace.isAbsolutelyQuasiSeparated`: an affine algebraic
  space is quasi-separated over the terminal scheme.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace`: the source
  of a quasi-compact morphism to an affine algebraic space is a quasi-compact algebraic space.
* `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_isAffineSpace`:
  the source of a quasi-separated morphism to an affine algebraic space is quasi-separated.

## Implementation notes

Both statements are instances of a general permanence property at a target which happens to be
affine, and neither needs an argument of its own beyond identifying the finiteness property of
the affine target.

For quasi-compactness, the definition of Stacks 03HE is instantiated at the *target*: an affine
algebraic space is quasi-compact by
`AlgebraicGeometry.Space.IsAffineSpace.isQuasiCompactSpace`, so it is an admissible test space,
and testing along its identity makes the base change `Y ×_Y X` quasi-compact.  That base change
is isomorphic to `X` because `pullback.snd (𝟙 Y) f` is an isomorphism, and quasi-compactness of
an algebraic space transfers along an isomorphism of presheaves.  Algebraicity of the source is
not used, so it is not assumed.

For quasi-separatedness the permanence property is Stacks 04ZH part (2),
`AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated`, which needs the target
to be quasi-separated over the terminal scheme.  That is supplied by the helper
`AlgebraicGeometry.Space.IsAffineSpace.isAbsolutelyQuasiSeparated`: an affine scheme is a
quasi-separated topological space, so the representing object of an affine algebraic space
exhibits it as a quasi-separated scheme in the sense of Stacks 03JX condition (ι), and that
implies quasi-separatedness by
`AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme`.  Here
algebraicity of the source *is* needed, because Stacks 04ZH part (2) uses it to know that the
relative diagonal of the morphism is representable.

The route through condition (4) of the local criterion
`AlgebraicGeometry.Space.isQuasiSeparated_tfae` would reach the same conclusion, at the cost of
transporting the fibre product `X ×_Y h_T` back to `X` along the isomorphism `Y ≅ h_T`; going
through the permanence property avoids that transport entirely.

## References

* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
* [Stacks Project, Tag 03E3](https://stacks.math.columbia.edu/tag/03E3)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 04ZH](https://stacks.math.columbia.edu/tag/04ZH)
* [Stacks Project, Tag 073E](https://stacks.math.columbia.edu/tag/073E)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Quasi-separatedness of an affine algebraic space -/

/-- An affine algebraic space is quasi-separated over the terminal scheme.

The representing object has affine underlying scheme, hence quasi-separated underlying
topological space, so the isomorphism with the presheaf it represents exhibits the space as a
quasi-separated scheme in the sense of Stacks 03JX condition (ι); the implication `(ι) ⇒ (η)`
is `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme`. -/
theorem IsAffineSpace.isAbsolutelyQuasiSeparated (hZ : B.Contains (⊤_ Scheme.{u}))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (h : IsAffineSpace B S hS F) :
    IsAbsolutelyQuasiSeparated B S hS hZ F := by
  obtain ⟨T, hT, ⟨e⟩⟩ := h
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hT
  exact isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS F hZ
    ⟨T, inferInstance, ⟨Functor.representableByEquiv.symm e.symm⟩⟩

/-! ### The source of a morphism to an affine algebraic space -/

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The source of a quasi-compact morphism to an affine algebraic space is quasi-compact.**
This is the quasi-compactness half of the hypotheses that Stacks 073E asks of the source of a
quasi-compact quasi-separated morphism to an affine algebraic space, as used in Stacks 073K
part (2).

An affine algebraic space is a quasi-compact algebraic space, so it is itself an admissible
test space for quasi-compactness of `f` in the sense of Stacks 03HE.  Testing along its
identity says that `Y ×_Y X` is quasi-compact, and `pullback.snd (𝟙 Y) f : Y ×_Y X ⟶ X` is an
isomorphism.

Algebraicity of the source is not used and is not assumed. -/
theorem isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace (f : X ⟶ Y)
    (hY : IsAffineSpace B S hS Y) (hf : IsQuasiCompact B S hS f) :
    IsQuasiCompactSpace B S hS X := by
  have _ : IsIso (pullback.snd (𝟙 Y) f) := inferInstance
  exact (hf Y hY.isAlgebraicSpace hY.isQuasiCompactSpace (𝟙 Y)).of_iso B S hS
    (asIso (pullback.snd (𝟙 Y) f))

/-- **The source of a quasi-separated morphism to an affine algebraic space is
quasi-separated.** This is the quasi-separatedness half of the hypotheses that Stacks 073E asks
of the source of a quasi-compact quasi-separated morphism to an affine algebraic space, as used
in Stacks 073K part (2).

An affine algebraic space is quasi-separated over the terminal scheme, so Stacks 04ZH part (2)
applies to `f`.  Algebraicity of the source enters there, through representability of the
relative diagonal of `f`. -/
theorem isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_isAffineSpace
    (hZ : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAffineSpace B S hS Y) (hf : IsQuasiSeparated B S hS f) :
    IsAbsolutelyQuasiSeparated B S hS hZ X :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hX
    (IsAffineSpace.isAbsolutelyQuasiSeparated B S hS hZ hY) hf

end AlgebraicGeometry.Space

end
