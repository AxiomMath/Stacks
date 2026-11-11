module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksFrontier.RingTheory.NoetherNormalization.MaximalSpectrumCardinal
public import StacksFrontier.Topology.Dimension.OpenCover

/-!
# A positive-dimensional scheme of finite type over `k = k̄` has at least `#k` rational points

Let `k` be an algebraically closed field and `X` a scheme locally of finite type over `k` with
`0 < dim X`. Then `X` has at least `#k` rational points, i.e. sections of `X → Spec k`.

Some affine open `U ⊆ X` has positive dimension, since otherwise `X`, covered by its affine opens,
would have dimension `≤ 0` (Tag 0B7I, `topologicalKrullDim_le_of_isOpen_cover`). The ring
`Γ(X, U)` is a finite type `k`-algebra of the same positive dimension, so it has at least `#k`
maximal ideals (`Algebra.FiniteType.cardinalMk_le_maximalSpectrum`). Maximal ideals are the closed
points of `U ≅ Spec Γ(X, U)`, and over an algebraically closed field the closed points of `U` are
its rational points (`AlgebraicGeometry.pointEquivClosedPoint`); composing with the open immersion
`U → X` is injective.

## Main results

* `AlgebraicGeometry.exists_isAffineOpen_zero_lt_topologicalKrullDim`: a scheme of positive
  dimension has an affine open of positive dimension.
* `AlgebraicGeometry.cardinalMk_le_sections`: `#k ≤ #X(k)`.

## References

* [Stacks Project, Tag 0B7I](https://stacks.math.columbia.edu/tag/0B7I)
* [Stacks Project, Tag 00OY](https://stacks.math.columbia.edu/tag/00OY)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **A scheme of positive dimension has an affine open of positive dimension**: the affine opens
cover it, and a space covered by opens of dimension `≤ 0` has dimension `≤ 0`. -/
theorem exists_isAffineOpen_zero_lt_topologicalKrullDim {X : Scheme.{u}}
    (hX : 0 < topologicalKrullDim X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ 0 < topologicalKrullDim U := by
  by_contra h
  simp only [not_exists, not_and, not_lt] at h
  have := topologicalKrullDim_le_of_isOpen_cover (X := X) (fun U : X.affineOpens => (U : Set X))
    (fun U => U.1.2) (fun x => by
      obtain ⟨W, hW, hx, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
      exact ⟨⟨W, hW⟩, hx⟩) (n := 0) (fun U => h U.1 U.2)
  exact absurd hX (not_lt.mpr this)

/-- **A scheme locally of finite type and of positive dimension over an algebraically closed field
`k` has at least `#k` rational points.** -/
theorem cardinalMk_le_sections {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (hX : 0 < topologicalKrullDim X) :
    Cardinal.mk k ≤ Cardinal.mk {p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 _} := by
  obtain ⟨U, hU, hUdim⟩ := exists_isAffineOpen_zero_lt_topologicalKrullDim hX
  let φ : CommRingCat.of k ⟶ Γ(X, U) :=
    (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)
  let : Algebra k Γ(X, U) := φ.hom.toAlgebra
  have hft : Algebra.FiniteType k Γ(X, U) := by
    have h := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f ‹_›
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
    have h' : φ.hom.FiniteType := by
      change ((f.appLE ⊤ U _).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).FiniteType
      exact RingHom.FiniteType.comp h
        (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)
    exact h'
  let e : U.toScheme ≃ₜ PrimeSpectrum Γ(X, U) := Scheme.homeoOfIso hU.isoSpec
  have hdim : 0 < ringKrullDim Γ(X, U) := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      ← IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph]
    exact hUdim
  refine (Algebra.FiniteType.cardinalMk_le_maximalSpectrum hdim).trans (Cardinal.mk_le_of_injective
    (f := fun m : MaximalSpectrum Γ(X, U) =>
      let y : PrimeSpectrum Γ(X, U) := ⟨m.asIdeal, m.isMaximal.isPrime⟩
      have hy : IsClosed ({y} : Set (PrimeSpectrum Γ(X, U))) :=
        (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mpr m.isMaximal
      have hx : IsClosed ({e.symm y} : Set U.toScheme) := by
        have h := e.symm.isClosedMap _ hy
        rwa [Set.image_singleton] at h
      let s := (pointEquivClosedPoint (U.ι ≫ f)).symm ⟨e.symm y, hx⟩
      (⟨s.1 ≫ U.ι, by simpa using s.2⟩ : {p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 _})) ?_)
  intro m m' hmm'
  have h1 := congrArg Subtype.val hmm'
  simp only at h1
  have h2 := Subtype.ext ((cancel_mono U.ι).mp h1)
  have h3 := congrArg Subtype.val ((pointEquivClosedPoint (U.ι ≫ f)).symm.injective h2)
  have h4 := e.symm.injective h3
  have h5 := congrArg PrimeSpectrum.asIdeal h4
  exact MaximalSpectrum.ext h5

end AlgebraicGeometry

end
