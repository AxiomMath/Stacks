module

public import StacksFrontier.AlgebraicGeometry.AmpleNoetherianDimensionOne.Proper

/-!
# Lifting an invertible module along a tower of thickenings of dimension at most one

Let `X₀ ⟶ X₁ ⟶ X₂ ⟶ ⋯` be a tower of surjective closed immersions of schemes whose underlying
spaces are Noetherian, with `dim X₀ ≤ 1`. Every invertible `𝒪_{X₀}`-module `ℒ₀` extends to a
compatible system: invertible `𝒪_{Xₙ}`-modules `ℒₙ` with `ℒ₀ ≅` the given one and isomorphisms
`iₙ^* ℒₙ₊₁ ≅ ℒₙ`. If moreover `X₀` is proper over a Noetherian ring, the system can be chosen with
`ℒ₀` ample.

This is the second paragraph of the proof of [Stacks, Tag 0E7R]. The source lifts `ℒₙ` to
`Xₙ₊₁` by killing the obstruction in `H²(Xₙ₊₁, (1 + 𝔪ⁿ𝒪)^*)`, which vanishes on a Noetherian
space of dimension at most one; the library carries that step, for an arbitrary closed immersion
into a Noetherian scheme of dimension at most one, as [Stacks, Tag 09NY]
(`Stacks.LiftInvertible.exists_modulePullback_iso_of_isClosedImmersion_of_dimension_le_one`).
Each `iₙ` is a homeomorphism, so every `Xₙ` has the dimension of `X₀`, and the lifts are chained
by recursion on `n`. The ample `ℒ₀` is
`Stacks.AmpleNoetherianDimensionOne.exists_isAmple_of_isProper_of_topologicalKrullDim_le_one`.

## Main results

* `Stacks.AmpleNoetherianDimensionOne.exists_invertibleTower_of_topologicalKrullDim_le_one`
* `Stacks.AmpleNoetherianDimensionOne.exists_ampleInvertibleTower_of_isProper`

## References

* [Stacks Project, Tag 0E7R](https://stacks.math.columbia.edu/tag/0E7R)
* [Stacks Project, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.AmpleNoetherianDimensionOne

/-- A surjective closed immersion of schemes is a homeomorphism of underlying spaces, so it
preserves the topological Krull dimension. -/
theorem topologicalKrullDim_eq_of_isClosedImmersion_of_surjective {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [AlgebraicGeometry.Surjective i] :
    topologicalKrullDim (Z : Type u) = topologicalKrullDim (X : Type u) :=
  IsHomeomorph.topologicalKrullDim_eq _
    (isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨i.isClosedEmbedding.isEmbedding, i.surjective⟩)

/-- An invertible module on the `n`-th member of a tower of schemes, bundled with its
invertibility, so that a compatible system can be built by recursion on `n`. -/
private abbrev InvertibleOn (X : Scheme.{u}) : Type (u + 1) :=
  Σ' L : X.Modules, Stacks.Ample.IsInvertibleModule X L

variable {Xn : ℕ → Scheme.{u}} (i : ∀ n, Xn n ⟶ Xn (n + 1))
  [∀ n, IsClosedImmersion (i n)] [∀ n, AlgebraicGeometry.Surjective (i n)]
  [∀ n, NoetherianSpace (Xn n)]

omit [∀ n, NoetherianSpace (Xn n)] in
include i in
private theorem topologicalKrullDim_le (hdim : topologicalKrullDim (Xn 0 : Type u) ≤ 1) (n : ℕ) :
    topologicalKrullDim (Xn n : Type u) ≤ 1 := by
  induction n with
  | zero => exact hdim
  | succ n ih =>
    rw [← topologicalKrullDim_eq_of_isClosedImmersion_of_surjective (i n)]
    exact ih

private theorem exists_lift (hdim : topologicalKrullDim (Xn 0 : Type u) ≤ 1) (n : ℕ)
    (M : InvertibleOn (Xn n)) :
    ∃ N : InvertibleOn (Xn (n + 1)),
      Nonempty ((Scheme.Modules.pullback (i n)).obj N.1 ≅ M.1) := by
  have := M.2
  obtain ⟨N, hN, ⟨e⟩⟩ :=
    Stacks.LiftInvertible.exists_modulePullback_iso_of_isClosedImmersion_of_dimension_le_one
      (Xn (n + 1)) (Xn n) (i n) (topologicalKrullDim_le i hdim (n + 1)) M.1
  exact ⟨⟨N, hN⟩, ⟨e⟩⟩

/-- The recursively chosen system of lifts of `M`. -/
private def liftTower (hdim : topologicalKrullDim (Xn 0 : Type u) ≤ 1)
    (M : InvertibleOn (Xn 0)) : ∀ n, InvertibleOn (Xn n)
  | 0 => M
  | n + 1 => (exists_lift i hdim n (liftTower hdim M n)).choose

/-- **Lifting an invertible module along a tower of thickenings of dimension at most one.**
Let `iₙ : Xₙ ⟶ Xₙ₊₁` be surjective closed immersions of schemes with Noetherian underlying spaces,
and suppose `dim X₀ ≤ 1`. Then every invertible `𝒪_{X₀}`-module `M` is the first member of a
compatible system of invertible modules: there are invertible `𝒪_{Xₙ}`-modules `Lₙ`, isomorphisms
`φₙ : iₙ^* Lₙ₊₁ ≅ Lₙ`, and `L₀ = M`.

This is the lifting paragraph of the proof of [Stacks, Tag 0E7R], with [Stacks, Tag 09NY]
lifting one level at a time. -/
theorem exists_invertibleTower_of_topologicalKrullDim_le_one
    (hdim : topologicalKrullDim (Xn 0 : Type u) ≤ 1) (M : (Xn 0).Modules)
    [Stacks.Ample.IsInvertibleModule (Xn 0) M] :
    ∃ (L : ∀ n, (Xn n).Modules) (_hL : ∀ n, Stacks.Ample.IsInvertibleModule (Xn n) (L n))
      (_ : ∀ n, (Scheme.Modules.pullback (i n)).obj (L (n + 1)) ≅ L n), L 0 = M := by
  let T := liftTower i hdim ⟨M, inferInstance⟩
  refine ⟨fun n => (T n).1, fun n => (T n).2,
    fun n => (exists_lift i hdim n (T n)).choose_spec.some, rfl⟩

/-- **An ample compatible system of invertible modules along a tower over a proper curve.** Let
`iₙ : Xₙ ⟶ Xₙ₊₁` be surjective closed immersions of schemes with Noetherian underlying spaces,
and let `X₀` be proper over a Noetherian ring `R`, of topological Krull dimension at most one.
Then there are invertible `𝒪_{Xₙ}`-modules `Lₙ` with `L₀` ample and isomorphisms
`φₙ : iₙ^* Lₙ₊₁ ≅ Lₙ`.

These are the data, together with the ampleness of the first member, that Grothendieck's
algebraization theorem [Stacks, Tag 089A] takes as input in the proof of [Stacks, Tag 0E7R]. -/
theorem exists_ampleInvertibleTower_of_isProper {R : Type u} [CommRing R] [IsNoetherianRing R]
    (f : Xn 0 ⟶ Spec (.of R)) [IsProper f] (hdim : topologicalKrullDim (Xn 0 : Type u) ≤ 1) :
    ∃ (L : ∀ n, (Xn n).Modules) (hL : ∀ n, Stacks.Ample.IsInvertibleModule (Xn n) (L n))
      (_ : ∀ n, (Scheme.Modules.pullback (i n)).obj (L (n + 1)) ≅ L n),
      letI := hL 0; Stacks.Ample.IsAmple (Xn 0) (L 0) := by
  obtain ⟨M, hM, hMamp⟩ := exists_isAmple_of_isProper_of_topologicalKrullDim_le_one f hdim
  have hMinv : Stacks.Ample.IsInvertibleModule (Xn 0) M := hM
  obtain ⟨L, hL, φ, h0⟩ := exists_invertibleTower_of_topologicalKrullDim_le_one i hdim M
  subst h0
  exact ⟨L, hL, φ, (Stacks.AmpleBridge.isAmple_iff_isAmple (Xn 0) (L 0)).mpr hMamp⟩

end Stacks.AmpleNoetherianDimensionOne

end
