module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDifferentialsTriangle
import StacksCore.Tactic.StacksAttribute

/-!
# Exactness at the right term of the conormal sequence of an immersion

Let `i : Z ⟶ X` be a morphism of algebraic spaces over a scheme `S` and let `b : X ⟶ B` be a
morphism to an algebraic space `B`.  The second arrow of the conormal sequence of Stacks 05ZA,
```
  𝒞_{Z/X} ⟶ i^*Ω_{X/B} ⟶ Ω_{Z/B} ⟶ 0,
```
is the comparison map `c_i` of Stacks 04CX for the square with top edge `i`, right edge `b`, left
edge `i ≫ b` and bottom edge the identity of `B`, which is
`AlgebraicGeometry.Space.pullbackDifferentialsMap`.  This file proves that it is an epimorphism,
which is the assertion *exactness at the right term*.  The first arrow is built in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDifferentials.lean`.

## Route

Epimorphy is left-cancellation, and it is checked against the universal property of `Ω_{Z/B}`,
not by exhibiting local preimages.  This is the route the scheme-level statement of Stacks 01UZ
takes in `StacksFrontier/AlgebraicGeometry/ConormalSequenceRight/Basic.lean`, transposed into the
setting of the small étale ringed topoi.

1. Let `g, g' : Ω_{Z/B} ⟶ F` satisfy `c_i ≫ g = c_i ≫ g'`.
2. `AlgebraicGeometry.Space.sheafOfDifferentialsMap_comp_eq_iff` reads that equation as the
   statement that `g` and `g'` agree on `d_{Z/B}(i♯ s)` for every local section `s` of
   `i⁻¹𝒪_X`.  **No formula for the effect of the comparison map on a section of `𝒪_X` is
   needed**, and none is available in this development: the equivalence is proved from the
   characterizing property of Stacks 04CX and the adjunction between the two forms of the
   structure map, both of which are statements about morphisms rather than about sections.
3. Local surjectivity of `i♯` makes every local section of `𝒪_Z` locally of the form `i♯ s`, so
   the two values agree on a covering sieve and are therefore equal, `F` being a sheaf; and
   `AlgebraicGeometry.Space.sheafOfDifferentials_hom_ext` turns that into `g = g'`.

## Main results

* `AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_of_isLocallySurjective`: **Stacks 05ZA**,
  exactness at the right term.

## Implementation notes

**Why this is a separate module from the construction of the first arrow.**  The two need
different parts of the development — this one needs the comparison map, that one needs the
conormal module and the annihilation clause of Stacks 04CJ — and the union of the two import
surfaces, together with the elaboration of either, does not fit comfortably in the memory a
single Lean process gets on the machine this was developed on.  Keeping each file's imports to
what it uses is what makes both compile.

**No immersion hypothesis appears below.**  Epimorphy holds as soon as `i♯` is locally
surjective, and that is the only property of an immersion the source's proof uses at this step,
so the statement is made at that hypothesis.  It is the same hypothesis, carried the same way,
as the `hsharp` of `AlgebraicGeometry.Space.isZero_sheafOfDifferentials_of_isImmersion` for
Stacks 05Z9.

**For a closed immersion the hypothesis is discharged**, so the clause is unconditional there.
`AlgebraicGeometry.Space.isLocallySurjective_structureSharpInverseImage` of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionStructureSharpInverseImage.lean:145` is the
inverse-image form of the surjectivity clause of Stacks 03MB, for a closed immersion, and its
own docstring names this file's `hsharp` as what it discharges.  The inverse-image form is the
one needed: `AlgebraicGeometry.Space.isLocallySurjective_structureSharp` states local
surjectivity of the direct-image form `𝒪_X ⟶ i_*𝒪_Z` instead, which is not the hypothesis
below.  For the inclusion of a closed subspace the closed immersion is
`Z.2.2`, and the unconditional statement is
`AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_subspaceInclusion` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceMiddleExactness.lean`.

**For a general immersion the hypothesis is discharged as well.**  Local surjectivity of `i♯`
for an arbitrary immersion is
`AlgebraicGeometry.Space.isLocallySurjective_structureSharpInverseImage_of_isImmersion` of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsImmersion.lean`, proved there for
Stacks 05Z9.  The composite, which is this clause of Stacks 05ZA with nothing beyond the
immersion assumed, is `AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_of_isImmersion` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceEpiImmersion.lean`; that file exists
because this one does not import `SheafOfDifferentialsImmersion.lean` and the
hypothesis-carrying form is wanted in its own right.

## References

* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA)
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map.
* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ), the scheme case.
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), whose surjectivity
  clause is the carried hypothesis.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Bb : AlgebraicSpaces B S hS}

/-- **Stacks 05ZA, exactness at the right term**, under local surjectivity of the structure map
`i♯ : i⁻¹𝒪_X ⟶ 𝒪_Z`.  The comparison map `c_i : i^*Ω_{X/B} ⟶ Ω_{Z/B}` of Stacks 04CX is an
epimorphism, so the conormal sequence of `i` ends in zero.

Left-cancellation is checked directly: given `g, g'` with equal composites,
`AlgebraicGeometry.Space.sheafOfDifferentialsMap_comp_eq_iff` makes them agree on the universal
differentials of the sections in the image of `i♯`; local surjectivity makes every local section
of `𝒪_Z` locally of that form, so the two values agree on a covering sieve and hence are equal,
the target being a sheaf; and `AlgebraicGeometry.Space.sheafOfDifferentials_hom_ext` turns that
into `g = g'`. -/
@[stacks 05ZA "exactness at the right term: the second arrow `i^*Ω_{X/B} ⟶ Ω_{Z/B}` is an \
epimorphism, carrying local surjectivity of `i♯ : i⁻¹𝒪_X ⟶ 𝒪_Z` (the inverse-image form of the \
surjectivity clause of 03MB) as `hsharp`"]
theorem epi_pullbackDifferentialsMap_of_isLocallySurjective (i : X ⟶ Y) (b : Y ⟶ Bb)
    (hsharp : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
      (structureSharpInverseImage B S hS i).hom) :
    Epi (pullbackDifferentialsMap B S hS i b) where
  left_cancellation {F} g g' hgg := by
    refine sheafOfDifferentials_hom_ext B S hS (i ≫ b) fun V t ↦ ?_
    have hsep : Presheaf.IsSeparated (SmallEtale.topology B S hS X.1) F.val.presheaf :=
      F.isSheaf.isSeparated
    refine hsep V.unop (Presheaf.imageSieve (structureSharpInverseImage B S hS i).hom t)
      (hsharp.imageSieve_mem _) _ _ ?_
    rintro W k hk
    obtain ⟨s, hs⟩ := hk
    -- `hs` says the restriction of `t` is `i♯ s`; both spellings of the structure ring sheaf
    -- occur, so the substitution is made in term mode rather than by rewriting.
    have hnat : ∀ ψ : sheafOfDifferentials B S hS (i ≫ b) ⟶ F,
        (F.val.map k.op).hom
            ((ψ.val.app V).hom ((universalDerivation B S hS (i ≫ b)).d t)) =
          (ψ.val.app (op W)).hom ((universalDerivation B S hS (i ≫ b)).d
            ((structureSharpInverseImage B S hS i).hom.app (op W) s)) := fun ψ ↦
      (PresheafOfModules.naturality_apply ψ.val k.op _).symm.trans
        (congrArg (fun y ↦ (ψ.val.app (op W)).hom y)
          (((universalDerivation B S hS (i ≫ b)).d_map k.op t).symm.trans
            (congrArg _ hs.symm)))
    exact (hnat g).trans
      (((sheafOfDifferentialsMap_comp_eq_iff B S hS i b (i ≫ b) (𝟙 Bb) (by simp) g g').mp
          hgg (op W) s).trans (hnat g').symm)

end AlgebraicGeometry.Space

end
