module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralEtaleCovering

/-!
# Integral quasi-compact objects cover the small étale site of an integral normal scheme

Let `X` be an integral normal scheme. Every point of an étale `X`-scheme has an integral open
neighbourhood, by `Stacks.EtaleCohomology.exists_isIntegral_open_of_etale`, and inside that
neighbourhood an affine open neighbourhood, which is integral again and is quasi-compact. So the
objects of the small étale site of `X` whose underlying scheme is integral **and** has a compact
space already cover, and they form a cover-dense subsite.

The quasi-compactness is not a convenience. The second map of the fundamental exact sequence of
Stacks 03RI sends a section over `U` to its family of orders of vanishing, and that family is
finitely supported only when `U` is quasi-compact: on the line with infinitely many origins —
an irreducible scheme étale over the affine line, not quasi-compact — the coordinate function has
a zero of order one at every origin. The target of the sequence is the *sheafification* of the
coproduct of the skyscrapers, whose sections are only locally finite sums, so nothing is lost;
but the finitely supported family, which is what a section of the coproduct of the underlying
presheaves is, exists only over a quasi-compact object.

## Main definitions

* `Stacks.EtaleCohomology.isIntegralCompactEtale`: the property of an object of the small étale
  site of having integral underlying scheme with a compact space.

## Main results

* `Stacks.EtaleCohomology.exists_isIntegral_compactSpace_open_of_etale`: every point of a scheme
  étale over an integral normal scheme has an integral quasi-compact open neighbourhood.
* `Stacks.EtaleCohomology.mem_smallEtaleTopology_of_forall_isIntegralCompact`: a sieve containing
  every morphism from an integral quasi-compact object is a covering sieve.
* `Stacks.EtaleCohomology.isCoverDense_isIntegralCompactEtale_ι`: **the integral quasi-compact
  objects form a cover-dense subsite**, so a morphism of presheaves on them into a sheaf extends
  uniquely to the whole site.

## References

* [Stacks Project, Tag 0357](https://stacks.math.columbia.edu/tag/0357): a normal scheme is a
  disjoint union of integral normal schemes.
* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI): the fundamental exact
  sequence, whose second map is defined on integral quasi-compact objects.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {X : Scheme.{u}} [AlgebraicGeometry.IsIntegral X] [IsNormal X]

/-- **Every point of a scheme étale over an integral normal scheme has an integral quasi-compact
open neighbourhood.** -/
theorem exists_isIntegral_compactSpace_open_of_etale {Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
    (y : Y) :
    ∃ (Z : Scheme.{u}) (g : Z ⟶ Y), IsOpenImmersion g ∧ AlgebraicGeometry.IsIntegral Z ∧
      CompactSpace Z ∧ y ∈ Set.range g.base := by
  obtain ⟨Z, g, hg, hZ, z, hz⟩ := exists_isIntegral_open_of_etale f y
  obtain ⟨W, hW, hzW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Z) (x := z) (U := ⊤) trivial
  have : IsOpenImmersion g := hg
  have : AlgebraicGeometry.IsIntegral Z := hZ
  have : Nonempty ↥W.toScheme := ⟨⟨z, hzW⟩⟩
  have : IsAffine W.toScheme := hW
  have : AlgebraicGeometry.IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  refine ⟨W.toScheme, W.ι ≫ g, inferInstance, inferInstance, inferInstance, ⟨z, hzW⟩, ?_⟩
  show g.base (W.ι.base ⟨z, hzW⟩) = y
  rw [show W.ι.base ⟨z, hzW⟩ = z from rfl]
  exact hz

/-- **A sieve on an object of the small étale site of an integral normal scheme containing every
morphism from an integral quasi-compact object is a covering sieve.** -/
theorem mem_smallEtaleTopology_of_forall_isIntegralCompact {U : X.Etale} (S : Sieve U)
    (hS : ∀ (V : X.Etale) (g : V ⟶ U), AlgebraicGeometry.IsIntegral V.left →
      CompactSpace V.left → S.arrows g) :
    S ∈ X.smallEtaleTopology U := by
  choose Z g hg hZ hZc hw using
    exists_isIntegral_compactSpace_open_of_etale (X := X) (Y := U.left) U.hom
  have hgi : ∀ w, IsOpenImmersion (g w) := hg
  let V : ↥U.left → X.Etale := fun w => Scheme.Etale.mk (g w ≫ U.hom)
  let k : ∀ w, V w ⟶ U := fun w => MorphismProperty.Over.homMk (g w)
  refine X.smallEtaleTopology.superset_covering ?_
    ((Scheme.ofArrows_mem_smallEtaleTopology_iff k).mpr ?_)
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro W - ⟨w⟩
    exact hS (V w) (k w) (hZ w) (hZc w)
  · ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨x, hw x⟩

/-- **The property of an object of the small étale site of having integral underlying scheme with
a compact space.** -/
def isIntegralCompactEtale (X : Scheme.{u}) : ObjectProperty X.Etale :=
  fun U => AlgebraicGeometry.IsIntegral U.left ∧ CompactSpace U.left

omit [AlgebraicGeometry.IsIntegral X] [IsNormal X] in
/-- An object `U` of the small étale site satisfies `isIntegralCompactEtale X` if and only if
its underlying scheme `U.left` is integral and has a compact space. -/
theorem isIntegralCompactEtale_iff {U : X.Etale} :
    isIntegralCompactEtale X U ↔
      AlgebraicGeometry.IsIntegral U.left ∧ CompactSpace U.left :=
  Iff.rfl

/-- **The integral quasi-compact objects of the small étale site of an integral normal scheme
form a cover-dense subsite.** -/
instance isCoverDense_isIntegralCompactEtale_ι :
    (isIntegralCompactEtale X).ι.IsCoverDense X.smallEtaleTopology where
  is_cover _ := mem_smallEtaleTopology_of_forall_isIntegralCompact _ fun V g hV hVc =>
    ⟨{ obj := ⟨V, hV, hVc⟩, lift := 𝟙 V, map := g, fac := Category.id_comp g }⟩

end Stacks.EtaleCohomology

end
