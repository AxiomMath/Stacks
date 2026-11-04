module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.BrauerRank

/-!
# A trivialising covering on which the matrix size is the one the rank prescribes

The Azumaya condition of [Stacks, Tag 0A2J] gives an étale covering `{φ_i : U_i → S}` and sizes
`d_i ≥ 1` with `φ_i^* A ≅ Mat_{d_i}(𝒪_{U_i})`, with no relation between the `d_i` and any global
invariant of `A`. [Stacks, Tag 0A2L] is stated for an Azumaya algebra whose underlying sheaf of
modules is finite locally free of rank `d ^ 2`, and its proof wants every `d_i` to be that `d`.

`Stacks.EtaleCohomology.BrauerScheme.eq_of_pullback_matrixAlgebra_iso` identifies `d_i` with `d`
as soon as `U_i` has a point. The members with no point are simply discarded: they contribute
nothing to the joint surjectivity of the family, so the subfamily of the inhabited members is
again an étale covering, and on it the matrix size is `d` everywhere.

## Main results

* `Stacks.EtaleCohomology.BrauerScheme.coverNonempty`: the subfamily of the inhabited members of
  an étale covering is an étale covering.
* `Stacks.EtaleCohomology.BrauerScheme.exists_etaleCover_matrixAlgebra_of_rank`: **an Azumaya
  `𝒪_S`-algebra whose underlying sheaf of modules is finite locally free of rank `d ^ 2` is
  trivialised, on some étale covering, by the matrix algebra of size exactly `d`.**
* `Stacks.EtaleCohomology.BrauerScheme.isFiniteLocallyFreeOfRank_natTensorPow_X`: the underlying
  sheaf of modules of the `n`-fold tensor power of such an algebra is finite locally free of rank
  `(d ^ 2) ^ n`.

## Implementation notes

The discarded members are those `U_i` with `IsEmpty (U_i)`; the subtype `{i // Nonempty (𝒰.X i)}`
stays in the index universe of the original covering, so the result is again a
`AlgebraicGeometry.Scheme.Cover.{u}`.

## References

* [Stacks Project, Tag 0A2J](https://stacks.math.columbia.edu/tag/0A2J)
* [Stacks Project, Tag 0A2L](https://stacks.math.columbia.edu/tag/0A2L)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory TopologicalSpace
open Stacks.SheafOfModules

universe u

noncomputable section

namespace Stacks.EtaleCohomology.BrauerScheme

variable {S : Scheme.{u}}

/-- **The subfamily of the inhabited members of an étale covering is an étale covering.** -/
def coverNonempty (𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage S) :
    Scheme.Cover.{u} Scheme.etalePrecoverage S :=
  haveI (i : 𝒰.I₀) : AlgebraicGeometry.Etale (𝒰.f i) := (etaleCover_spec 𝒰).2 i
  Scheme.Cover.mkOfCovers {i : 𝒰.I₀ // Nonempty (𝒰.X i)} (fun i ↦ 𝒰.X i.1)
    (fun i ↦ 𝒰.f i.1)
    (fun x ↦ by
      obtain ⟨i, y, hy⟩ := (etaleCover_spec 𝒰).1 x
      exact ⟨⟨i, ⟨y⟩⟩, y, hy⟩)
    (fun i ↦ (etaleCover_spec 𝒰).2 i.1)

/-- The member of `coverNonempty 𝒰` indexed by an inhabited index `i` of `𝒰` is the member
`𝒰.f i` of `𝒰`. -/
@[simp]
lemma coverNonempty_f (𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage S)
    (i : {i : 𝒰.I₀ // Nonempty (𝒰.X i)}) : (coverNonempty 𝒰).f i = 𝒰.f i.1 :=
  rfl

/-- **An Azumaya `𝒪_S`-algebra whose underlying sheaf of modules is finite locally free of rank
`d ^ 2` is trivialised by the matrix algebra of size exactly `d`** on some étale covering of
`S`. -/
theorem exists_etaleCover_matrixAlgebra_of_rank {A : AlgebraSheaf S} (hA : IsAzumaya A) {d : ℕ}
    (hrank : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens S)
      (J := Opens.grothendieckTopology S) A.X (d ^ 2)) :
    ∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage S,
      ∀ i, Nonempty ((algebraPullback (𝒰.f i)).obj A ≅ matrixAlgebra (𝒰.X i) d) := by
  obtain ⟨𝒰, e, _, hiso⟩ := hA
  refine ⟨coverNonempty 𝒰, fun i ↦ ?_⟩
  obtain ⟨m⟩ := hiso i.1
  obtain ⟨x⟩ := i.2
  have hed : e i.1 = d := eq_of_pullback_matrixAlgebra_iso (𝒰.f i.1) x hrank m
  exact ⟨m ≪≫ eqToIso (congrArg (matrixAlgebra (𝒰.X i.1)) hed)⟩

/-- **The underlying sheaf of modules of a tensor power of a sheaf of algebras of rank `r` is
finite locally free of rank `r ^ n`.** -/
theorem isFiniteLocallyFreeOfRank_natTensorPow_X (A : AlgebraSheaf S) {r : ℕ}
    (hrank : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens S)
      (J := Opens.grothendieckTopology S) A.X r) (n : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens S)
      (J := Opens.grothendieckTopology S) (Stacks.TensorPowers.natTensorPow A n).X (r ^ n) :=
  (natTensorPow_X A n) ▸ isFiniteLocallyFreeOfRank_natTensorPow hrank n

end Stacks.EtaleCohomology.BrauerScheme

end

end
