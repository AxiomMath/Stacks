module

public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpenUniversal
public import
  StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The single-degree rank locus is characterised by its two descriptions

Let `X` be a scheme, `E` a perfect object of the derived category of sheaves of modules on `X`,
`i` an integer and `r` a natural number, and let `U = singleDegreeRankOpen E i r` be the largest
open subscheme of `X` on which `E` is a finite locally free module of rank `r` placed in degree
`i`. This file records that `U` satisfies both descriptions of [stacks 0BDK] at once, and that
an open subscheme satisfying them is unique: description (2), applied to the inclusion of either
of two candidates, puts each inside the other.

## Main results

* `AlgebraicGeometry.Scheme.Modules.singleDegreeRankOpen_spec`: the two descriptions together, at
  a natural rank, for the explicitly constructed open subscheme.
* `AlgebraicGeometry.Scheme.Modules.existsUnique_opens_singleDegreeRank`: the same, in the
  source's existential form, with the uniqueness which makes the two descriptions a
  characterisation.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_of_isPerfect`: a perfect object of `D(𝒪_X)`
  is pseudo-coherent, in the spelling `AlgebraicGeometry.RingedSpace.IsPseudoCoherent`.

The tag at the source's integer rank is
`AlgebraicGeometry.Scheme.Modules.existsUnique_opens_singleDegreeRank_int`.

## References

* [The Stacks Project, Lemma 36.31.3 (0BDK)](https://stacks.math.columbia.edu/tag/0BDK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-! ### Pseudo-coherence from perfectness, at the scheme-level spelling -/

/-- **A perfect object of `D(𝒪_X)` is pseudo-coherent**, in the spelling
`AlgebraicGeometry.RingedSpace.IsPseudoCoherent` that the derived-fibre Betti functions are stated
at. This is `Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect` read across
`Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent'`. -/
theorem isPseudoCoherent_of_isPerfect (E : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) :
    RingedSpace.IsPseudoCoherent.{u, u + 1} (X := X.toRingedSpace) E :=
  (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent' E).1
    (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect E hE)

/-! ### The tag -/

/-- An open subscheme through which the inclusion of another one factors contains it. -/
@[ega "I 4.1.10" "partial"]
theorem le_of_factorsThrough {U V : X.Opens}
    (h : ∃ g : U.toScheme ⟶ V.toScheme, g ≫ V.ι = U.ι) : U ≤ V := by
  obtain ⟨g, hg⟩ := h
  intro x hx
  have hmem : (g ≫ V.ι).base ⟨x, hx⟩ ∈ Set.range V.ι.base := ⟨g.base ⟨x, hx⟩, rfl⟩
  rw [hg, Scheme.Opens.range_ι] at hmem
  exact hmem

/-- **[Stacks, Tag 0BDK] at the explicitly constructed open subscheme.** Let `X` be a scheme, `E`
a perfect object of `D(𝒪_X)`, `i` an integer and `r` a natural number. The open subscheme
`U = singleDegreeRankOpen E i r` satisfies both descriptions of the tag:

1. `E|_U ≅ H^i(E|_U)[-i]` and `H^i(E|_U)` is a finite locally free `𝒪_U`-module of rank `r`;
2. a morphism `f : Y ⟶ X` factors through `U` if and only if `Lf^* E` is isomorphic to a finite
   locally free module of rank `r` placed in degree `i`.

This exhibits the open subscheme the tag asserts to exist, so it is stronger than the tag's
existential form; `existsUnique_opens_singleDegreeRank` is that form, together with the uniqueness
that makes the two descriptions a characterisation. -/
theorem singleDegreeRankOpen_spec (E : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (i : ℤ) (r : ℕ) :
    (Nonempty ((restrictFunctor (singleDegreeRankOpen E i r).ι).mapDerivedCategory.obj E ≅
          (DerivedCategory.singleFunctor (singleDegreeRankOpen E i r).toScheme.Modules i).obj
            ((DerivedCategory.homologyFunctor
                (singleDegreeRankOpen E i r).toScheme.Modules i).obj
              ((restrictFunctor (singleDegreeRankOpen E i r).ι).mapDerivedCategory.obj E))) ∧
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((DerivedCategory.homologyFunctor
              (singleDegreeRankOpen E i r).toScheme.Modules i).obj
            ((restrictFunctor (singleDegreeRankOpen E i r).ι).mapDerivedCategory.obj E)) r) ∧
      ∀ (Y : Scheme.{u}) (f : Y ⟶ X),
        (∃ g : Y ⟶ (singleDegreeRankOpen E i r).toScheme,
            g ≫ (singleDegreeRankOpen E i r).ι = f) ↔
          ∃ M : Y.Modules,
            AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r ∧
              Nonempty ((derivedPullback f.toLRSHom.toShHom).obj E ≅
                (DerivedCategory.singleFunctor Y.Modules i).obj M) :=
  ⟨⟨nonempty_iso_singleFunctor_restrict_singleDegreeRankOpen E i r,
      isFiniteLocallyFreeOfRank_homology_singleDegreeRankOpen E i r⟩,
    fun _ f => factorsThrough_singleDegreeRankOpen_iff_derivedPullback E i r hE f⟩

/-- **[Stacks, Tag 0BDK], in the source's form, at a natural rank.** Let `X` be a scheme, `E` a
perfect object of `D(𝒪_X)`, `i` an integer and `r` a natural number. There is a **unique** open
subscheme `U ⊆ X` such that

1. `E|_U ≅ H^i(E|_U)[-i]` and `H^i(E|_U)` is a finite locally free `𝒪_U`-module of rank `r`, and
2. a morphism `f : Y ⟶ X` factors through `U` if and only if `Lf^* E` is isomorphic to a finite
   locally free module of rank `r` placed in degree `i`.

The uniqueness is what makes the two descriptions a *characterisation* of `U`, and it follows from
description (2) alone: applied to the inclusion of either candidate it puts each inside the other.
The witness is `singleDegreeRankOpen E i r`. -/
theorem existsUnique_opens_singleDegreeRank (E : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (i : ℤ) (r : ℕ) :
    ∃! U : X.Opens,
      (Nonempty ((restrictFunctor U.ι).mapDerivedCategory.obj E ≅
            (DerivedCategory.singleFunctor U.toScheme.Modules i).obj
              ((DerivedCategory.homologyFunctor U.toScheme.Modules i).obj
                ((restrictFunctor U.ι).mapDerivedCategory.obj E))) ∧
          AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
            ((DerivedCategory.homologyFunctor U.toScheme.Modules i).obj
              ((restrictFunctor U.ι).mapDerivedCategory.obj E)) r) ∧
        ∀ (Y : Scheme.{u}) (f : Y ⟶ X),
          (∃ g : Y ⟶ U.toScheme, g ≫ U.ι = f) ↔
            ∃ M : Y.Modules,
              AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r ∧
                Nonempty ((derivedPullback f.toLRSHom.toShHom).obj E ≅
                  (DerivedCategory.singleFunctor Y.Modules i).obj M) := by
  refine ⟨singleDegreeRankOpen E i r, singleDegreeRankOpen_spec E hE i r, fun V hV => ?_⟩
  have hU := singleDegreeRankOpen_spec E hE i r
  refine le_antisymm ?_ ?_
  · exact le_of_factorsThrough ((hU.2 V.toScheme V.ι).2 ((hV.2 V.toScheme V.ι).1 ⟨𝟙 _, by simp⟩))
  · exact le_of_factorsThrough ((hV.2 _ (singleDegreeRankOpen E i r).ι).2
      ((hU.2 _ (singleDegreeRankOpen E i r).ι).1 ⟨𝟙 _, by simp⟩))

end AlgebraicGeometry.Scheme.Modules

end
