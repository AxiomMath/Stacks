module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerResolutionPostnikov
public import StacksFrontier.CategoryTheory.Triangulated.SequentialPostnikovSystems

/-!
# The sequential Postnikov system of the brutal truncations of a complex

Let `L` be a cochain complex in an abelian category `A`, concentrated in degrees `≤ 0`, read as
the chain complex `… → L₂ → L₁ → L₀` with `Lₙ = L⁻ⁿ`. The brutal truncations
`Yₙ = σ^{≥-n}L[-n] = (Lₙ → … → L₀)[-n]` together with the canonical maps `Yₙ ⟶ Lₙ`,
`Lₙ₊₁ ⟶ Yₙ` and `Yₙ ⟶ Yₙ₊₁[1]` form a Postnikov system, in the sense of the sequential
extension of [Stacks, Tag 0D7Z], for the complex `… ⟶ L₂ ⟶ L₁ ⟶ L₀` of objects of `D(A)`. This
is the first assertion of [Stacks, Tag 0D8Z], for the whole infinite complex at once.

The triangles and the identities they satisfy are those of `StacksDraft.BrutalPostnikov`, which
records one finite Postnikov system for each truncation length; here they are packaged as a
single `CategoryTheory.Triangulated.SequentialPostnikovSystem`.

## Main definitions

* `StacksDraft.BrutalPostnikov.sequentialPostnikovSystem`: the sequential Postnikov system of the
  brutal truncations.

## References

* [Stacks Project, Tag 0D8Z](https://stacks.math.columbia.edu/tag/0D8Z)
* [Stacks Project, Tag 0D7Z](https://stacks.math.columbia.edu/tag/0D7Z)
-/

@[expose] public section

open CategoryTheory

namespace StacksDraft.BrutalPostnikov

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
  (L : CochainComplex A ℤ) [L.IsStrictlyLE 0]

/-- **The brutal truncations of a complex concentrated in degrees `≤ 0` form a sequential
Postnikov system** for the complex `… ⟶ L₂ ⟶ L₁ ⟶ L₀` of its terms, placed in degree zero, with
objects `Yₙ = σ^{≥-n}L[-n]`. -/
noncomputable def sequentialPostnikovSystem :
    Triangulated.SequentialPostnikovSystem (term L) (termDiff L) where
  obj := tot L
  π := totProj L
  isIso_π_zero := inferInstanceAs (IsIso (totProj L 0))
  p := termToTot L
  δ := totConnecting L
  distinguished := truncTriangle_distinguished L
  p_comp_π := termToTot_comp_totProj L

/-- The `n`-th object of `sequentialPostnikovSystem L` is `tot L n`. -/
@[simp]
theorem sequentialPostnikovSystem_obj (n : ℕ) :
    (sequentialPostnikovSystem L).obj n = tot L n :=
  rfl

/-- The `n`-th map `π` of `sequentialPostnikovSystem L` is `totProj L n`. -/
@[simp]
theorem sequentialPostnikovSystem_π (n : ℕ) :
    (sequentialPostnikovSystem L).π n = totProj L n :=
  rfl

/-- The `n`-th map `p` of `sequentialPostnikovSystem L` is `termToTot L n`. -/
@[simp]
theorem sequentialPostnikovSystem_p (n : ℕ) :
    (sequentialPostnikovSystem L).p n = termToTot L n :=
  rfl

/-- The `n`-th connecting morphism `δ` of `sequentialPostnikovSystem L` is `totConnecting L n`. -/
@[simp]
theorem sequentialPostnikovSystem_δ (n : ℕ) :
    (sequentialPostnikovSystem L).δ n = totConnecting L n :=
  rfl

end StacksDraft.BrutalPostnikov
