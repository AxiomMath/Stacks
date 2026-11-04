module

public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosureSubscheme
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.PointClosureSquare
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic

/-!
# Reflecting coherence along a closed immersion, and the point-closure square

Let `i : Z ⟶ X` be a closed immersion of locally Noetherian schemes. Because `i_*` is fully
faithful, the counit of the adjunction `i^* ⊣ i_*` is an isomorphism, so a module on `Z` is
recovered from its direct image by pulling back. Pulling back preserves coherence on a locally
Noetherian source, so coherence of `i_* G` forces coherence of `G`.

Applied to the square of point closures of [Stacks, Tag 0BK2], this says that coherence of the
iterated direct image `j_* i_{W,*} 𝒪_W` of the structure sheaf of the reduced closure of a point
`x` of an open subscheme `U ⊆ X` forces coherence of `j'_* 𝒪_W` on the reduced closure of `j x`
in `X`.

## Main results

* `Stacks.LocalCohomology.isCoherent_of_isCoherent_pushforward`: coherence of a direct image
  along a closed immersion reflects to the module itself.
* `Stacks.LocalCohomology.isCoherent_pushforward_pointClosure_of_isCoherent`: the forward
  implication of the coherence equivalence of [Stacks, Tag 0BK2].

## Implementation notes

Coherence is transferred along isomorphisms by
`Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso`, which holds over an arbitrary sheaf
of rings on a space; it takes the isomorphism in the direction `source ≅ coherent target`, so
the isomorphisms below are supplied reversed.

Every coherence hypothesis is an explicit argument rather than an instance, and every coherence
conclusion is produced by applying a named lemma rather than by instance search: the modules
involved are direct images of direct images, and instance search normalises the composite
functor applied to an object differently from the iterated application, so a hypothesis stated
in one shape is not found for a goal stated in the other.

The square of point closures itself, and the comparison of the two iterated direct images
around it, are `AlgebraicGeometry.Scheme.IdealSheafData.exists_isOpenImmersion_pointClosure` and
`AlgebraicGeometry.Scheme.Modules.pushforwardPointClosureIso`; this file only adds the coherence
statement.

## References

* [Stacks Project, Tag 0BK2](https://stacks.math.columbia.edu/tag/0BK2)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.LocalCohomology

/-- **Coherence descends along a closed immersion.** If the direct image of `G` along a closed
immersion of locally Noetherian schemes is coherent, then so is `G`: the counit of
`i^* ⊣ i_*` is an isomorphism because `i_*` is fully faithful ([Stacks, Tag 08KS]), and `i^*`
preserves coherence because the source is locally Noetherian ([Stacks, Tag 0EBF]). -/
theorem isCoherent_of_isCoherent_pushforward {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsLocallyNoetherian Z] [IsLocallyNoetherian X] (G : Z.Modules)
    (h : ((Scheme.Modules.pushforward i).obj G).IsCoherent) : G.IsCoherent := by
  have : (Scheme.Modules.pushforward i).Full := Stacks.ClosedImmersion.full_pushforward i
  have : (Scheme.Modules.pushforward i).Faithful :=
    Stacks.ClosedImmersion.faithful_pushforward i
  have hiso : IsIso (Scheme.Modules.pullbackPushforwardAdjunction i).counit :=
    Adjunction.counit_isIso_of_R_fully_faithful _
  -- stated at the composite functor, which is the shape the counit's source has
  have hpull : ((Scheme.Modules.pushforward i ⋙ Scheme.Modules.pullback i).obj G).IsCoherent :=
    have := h
    isCoherent_pullback i ((Scheme.Modules.pushforward i).obj G)
  have := hpull
  exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
    (asIso ((Scheme.Modules.pullbackPushforwardAdjunction i).counit.app G)).symm

/-- **Stacks Project, Tag 0BK2**, forward implication of the coherence equivalence. Let
`j : U ⟶ X` be an open immersion of locally Noetherian schemes, `x` a point of `U`, and `j'` the
induced morphism from the reduced closure of `{x}` in `U` to the reduced closure of `{j x}` in
`X`. If the iterated direct image to `X` of the structure sheaf of the reduced closure of `{x}`
is coherent, then its direct image along `j'` is coherent. -/
theorem isCoherent_pushforward_pointClosure_of_isCoherent {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [IsLocallyNoetherian U] [IsLocallyNoetherian X] (x : U)
    (j' : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set U))).subscheme ⟶
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({j x} : Set X))).subscheme)
    (comm : j' ≫ (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({j x} : Set X))).subschemeι =
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set U))).subschemeι ≫ j)
    (h : ((Scheme.Modules.pushforward j).obj
      ((Scheme.Modules.pushforward
        (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set U))).subschemeι).obj
        (SheafOfModules.unit
          (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({x} : Set U))).subscheme.ringCatSheaf))).IsCoherent) :
    ((Scheme.Modules.pushforward j').obj
      (SheafOfModules.unit
        (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set U))).subscheme.ringCatSheaf)).IsCoherent :=
  have : IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({j x} : Set X))).subscheme :=
    Scheme.IdealSheafData.isLocallyNoetherian_subscheme _
  have := h
  isCoherent_of_isCoherent_pushforward
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({j x} : Set X))).subschemeι _
    (Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
      (Scheme.Modules.pushforwardPointClosureIso j x j' comm).symm)

end Stacks.LocalCohomology

end
