module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafPushforwardNormal

/-!
# Integral objects cover the small étale site of an integral normal scheme

Let `X` be an integral normal scheme. A scheme étale over `X` is again normal, and a normal
scheme with finitely many irreducible components on every quasi-compact open is a disjoint union
of integral schemes, so every point of an étale `X`-scheme has an integral open neighbourhood:
this is `Stacks.EtaleCohomology.exists_isIntegral_open_of_etale`. Those neighbourhoods are
themselves objects of the small étale site of `X`, and they cover.

This file packages that decomposition in the two forms a construction on the small étale site
needs. The first says that any sieve containing every morphism out of an integral object is a
covering sieve, which is what a local statement about sections has to be reduced to. The second
says that the full subcategory of the integral objects is a cover-dense subsite, which is what
lets a morphism *into* a sheaf be defined on integral objects alone, through
`CategoryTheory.Functor.IsCoverDense.sheafHom`.

The decomposition is the one the Stacks Project appeals to in the proof of Tag 03RI, where the
fundamental exact sequence is written down on sections over an étale `X`-scheme and the order of
vanishing — which needs a function field, hence an irreducible scheme — is taken there.

## Main definitions

* `Stacks.EtaleCohomology.isIntegralEtale`: the property of an object of the small étale site of
  having integral underlying scheme.

## Main results

* `Stacks.EtaleCohomology.mem_smallEtaleTopology_of_forall_isIntegral`: **a sieve containing
  every morphism from an integral object of the small étale site of an integral normal scheme is
  a covering sieve.**
* `Stacks.EtaleCohomology.isCoverDense_isIntegralEtale_ι`: **the integral objects form a
  cover-dense subsite**.

## Implementation notes

The underlying scheme of an integral open neighbourhood is turned into an object of the small
étale site by `AlgebraicGeometry.Scheme.Etale.mk` applied to the composite with the structure
morphism, which is étale because an open immersion is and étale morphisms compose; the covering
criterion used is `AlgebraicGeometry.Scheme.ofArrows_mem_smallEtaleTopology_iff`, joint
surjectivity on points.

No Noetherian hypothesis appears: the finiteness of the irreducible components on quasi-compact
opens that the decomposition needs is supplied by irreducibility of `X` itself, through
`Stacks.EtaleCohomology.finiteIrreducibleComponents_of_isIntegral`.

## References

* [Stacks Project, Tag 0357](https://stacks.math.columbia.edu/tag/0357): a normal scheme is a
  disjoint union of integral normal schemes.
* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI): the fundamental exact
  sequence, whose second map is defined on integral objects.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {X : Scheme.{u}} [AlgebraicGeometry.IsIntegral X] [IsNormal X]

/-- **A sieve on an object of the small étale site of an integral normal scheme containing every
morphism from an integral object is a covering sieve.** -/
theorem mem_smallEtaleTopology_of_forall_isIntegral {U : X.Etale} (S : Sieve U)
    (hS : ∀ (V : X.Etale) (g : V ⟶ U), AlgebraicGeometry.IsIntegral V.left → S.arrows g) :
    S ∈ X.smallEtaleTopology U := by
  choose Z g hg hZ hw using exists_isIntegral_open_of_etale (X := X) (Y := U.left) U.hom
  have hgi : ∀ w, IsOpenImmersion (g w) := hg
  let V : ↥U.left → X.Etale := fun w => Scheme.Etale.mk (g w ≫ U.hom)
  let k : ∀ w, V w ⟶ U := fun w => MorphismProperty.Over.homMk (g w)
  refine X.smallEtaleTopology.superset_covering ?_
    ((Scheme.ofArrows_mem_smallEtaleTopology_iff k).mpr ?_)
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro W - ⟨w⟩
    exact hS (V w) (k w) (hZ w)
  · ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨x, hw x⟩

/-- **The property of an object of the small étale site of having integral underlying scheme.** -/
def isIntegralEtale (X : Scheme.{u}) : ObjectProperty X.Etale :=
  fun U => AlgebraicGeometry.IsIntegral U.left

omit [AlgebraicGeometry.IsIntegral X] [IsNormal X] in
/-- An object of the small étale site satisfies `Stacks.EtaleCohomology.isIntegralEtale` if and
only if its underlying scheme is integral. -/
theorem isIntegralEtale_iff {U : X.Etale} :
    isIntegralEtale X U ↔ AlgebraicGeometry.IsIntegral U.left :=
  Iff.rfl

/-- **The integral objects of the small étale site of an integral normal scheme form a cover-dense
subsite.** -/
instance isCoverDense_isIntegralEtale_ι :
    (isIntegralEtale X).ι.IsCoverDense X.smallEtaleTopology where
  is_cover _U := mem_smallEtaleTopology_of_forall_isIntegral _ fun V g hV =>
    ⟨{ obj := ⟨V, hV⟩, lift := 𝟙 V, map := g, fac := Category.id_comp g }⟩

end Stacks.EtaleCohomology

end
