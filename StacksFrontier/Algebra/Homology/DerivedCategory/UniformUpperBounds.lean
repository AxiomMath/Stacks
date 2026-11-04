module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import StacksCore.Tactic.StacksAttribute

/-!
# Uniform upper bounds on the cohomology of a family of objects of a derived category

An object of the derived category of an abelian category is bounded above by an integer `b` when
its cohomology vanishes in every degree above `b`. A *family* of objects is uniformly bounded
above when one `b` does this for every member of the family at once.

This file holds those predicates together with the two ways a bound propagates along a
distinguished triangle, and the resulting induction principle: a family indexed by the natural
numbers whose successive terms sit in distinguished triangles with uniformly bounded third
vertices is itself uniformly bounded above.

## Main definitions

* `Stacks.DerivedCategory.IsBoundedAboveBy`: cohomology vanishing above a given degree.
* `Stacks.DerivedCategory.IsBoundedAbove`: cohomology vanishing above some degree.
* `Stacks.DerivedCategory.IsUniformlyBoundedAbove`: one degree above which the cohomology of
  every member of a family vanishes.

## Main results

* `Stacks.DerivedCategory.IsBoundedAboveBy.obj₂` and
  `Stacks.DerivedCategory.IsBoundedAboveBy.obj₃`: in a distinguished triangle a bound on two of
  the three vertices gives the same bound on the third, for the second and third vertices.
* `Stacks.DerivedCategory.isUniformlyBoundedAbove_of_triangles`: the induction principle for a
  tower of distinguished triangles with a uniform bound on the first vertices.
* `Stacks.DerivedCategory.isBoundedAboveBy_iff_isLE`: being bounded above by `b` is lying in
  the aisle `D^{≤ b}` of the canonical t-structure.

## Implementation notes

The bound is phrased with a strict inequality `b < n`, so that `IsBoundedAboveBy E b` says the
cohomology of `E` is concentrated in degrees at most `b`, matching the way the source states an
upper bound. Uniform boundedness is one integer together with vanishing for every member of the
family, rather than a family of individually bounded-above assertions: the latter is implied by
the former and is strictly weaker, and it is the former that the applications need.

The two triangle lemmas are not symmetric in the three vertices. A bound `b` on the second and
third vertices gives only the bound `b + 1` on the first, because the cohomology of the first
vertex in degree `n` is caught between that of the third in degree `n - 1` and that of the
second in degree `n`; that case is not needed here and is omitted.

## References

* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace Stacks.DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- An object of the derived category is *bounded above by `b`* when its cohomology vanishes in
every degree strictly above `b`. -/
def IsBoundedAboveBy (E : DerivedCategory A) (b : ℤ) : Prop :=
  ∀ n : ℤ, b < n → IsZero ((DerivedCategory.homologyFunctor A n).obj E)

/-- An object of the derived category is *bounded above* when its cohomology vanishes in every
degree strictly above some integer. -/
def IsBoundedAbove (E : DerivedCategory A) : Prop :=
  ∃ b : ℤ, IsBoundedAboveBy E b

/-- A family of objects of the derived category is *uniformly bounded above* when there is one
integer above which the cohomology of every member of the family vanishes. -/
def IsUniformlyBoundedAbove {ι : Sort*} (E : ι → DerivedCategory A) : Prop :=
  ∃ b : ℤ, ∀ i, IsBoundedAboveBy (E i) b

/-- **A bound above is membership in the aisle of the canonical t-structure.** An object of the
derived category is bounded above by `b` exactly when it lies in `D^{≤ b}`. -/
theorem isBoundedAboveBy_iff_isLE (E : DerivedCategory A) (b : ℤ) :
    IsBoundedAboveBy E b ↔ E.IsLE b :=
  (DerivedCategory.isLE_iff E b).symm

/-- A bound above holds for every larger bound. -/
theorem IsBoundedAboveBy.mono {E : DerivedCategory A} {b b' : ℤ} (hb : b ≤ b')
    (h : IsBoundedAboveBy E b) : IsBoundedAboveBy E b' :=
  fun n hn => h n (lt_of_le_of_lt hb hn)

/-- A bound above transports along an isomorphism of the derived category. -/
theorem IsBoundedAboveBy.of_iso {E E' : DerivedCategory A} (e : E ≅ E') {b : ℤ}
    (h : IsBoundedAboveBy E b) : IsBoundedAboveBy E' b :=
  fun n hn => (h n hn).of_iso ((DerivedCategory.homologyFunctor A n).mapIso e).symm

/-- An object bounded above by an integer is bounded above. -/
theorem IsBoundedAboveBy.isBoundedAbove {E : DerivedCategory A} {b : ℤ}
    (h : IsBoundedAboveBy E b) : IsBoundedAbove E :=
  ⟨b, h⟩

/-- Every member of a uniformly bounded above family is bounded above by the common bound. -/
theorem IsUniformlyBoundedAbove.isBoundedAboveBy {ι : Sort*} {E : ι → DerivedCategory A}
    (h : IsUniformlyBoundedAbove E) (i : ι) : IsBoundedAboveBy (E i) h.choose :=
  h.choose_spec i

/-- Every member of a uniformly bounded above family is bounded above. -/
theorem IsUniformlyBoundedAbove.isBoundedAbove {ι : Sort*} {E : ι → DerivedCategory A}
    (h : IsUniformlyBoundedAbove E) (i : ι) : IsBoundedAbove (E i) :=
  ⟨h.choose, h.isBoundedAboveBy i⟩

/-- A reindexing of a uniformly bounded above family is uniformly bounded above. -/
theorem IsUniformlyBoundedAbove.comp {ι ι' : Sort*} {E : ι → DerivedCategory A}
    (h : IsUniformlyBoundedAbove E) (f : ι' → ι) : IsUniformlyBoundedAbove (E ∘ f) :=
  ⟨h.choose, fun i => h.isBoundedAboveBy (f i)⟩

/-- **A bound on the first and third vertices of a distinguished triangle bounds the second.**
The cohomology of the second vertex in a degree is caught between that of the first and that of
the third in the same degree. -/
theorem IsBoundedAboveBy.obj₂ (tri : Triangle (DerivedCategory A))
    (htri : tri ∈ distinguishedTriangles) {b : ℤ}
    (h₁ : IsBoundedAboveBy tri.obj₁ b) (h₃ : IsBoundedAboveBy tri.obj₃ b) :
    IsBoundedAboveBy tri.obj₂ b := by
  intro n hn
  have hex := (DerivedCategory.homologyFunctor A 0).homologySequence_exact₂ tri htri n
  exact hex.isZero_X₂ ((h₁ n hn).eq_of_src _ _) ((h₃ n hn).eq_of_tgt _ _)

/-- **A bound on the first and second vertices of a distinguished triangle bounds the third.**
The cohomology of the third vertex in a degree is caught between that of the second in the same
degree and that of the first one degree higher. -/
theorem IsBoundedAboveBy.obj₃ (tri : Triangle (DerivedCategory A))
    (htri : tri ∈ distinguishedTriangles) {b : ℤ}
    (h₁ : IsBoundedAboveBy tri.obj₁ b) (h₂ : IsBoundedAboveBy tri.obj₂ b) :
    IsBoundedAboveBy tri.obj₃ b := by
  intro n hn
  have hex := (DerivedCategory.homologyFunctor A 0).homologySequence_exact₃ tri htri n (n + 1) rfl
  refine hex.isZero_X₂ ((h₂ n hn).eq_of_src _ _) ?_
  exact (h₁ (n + 1) (by omega)).eq_of_tgt _ _

/-- **The induction principle for a tower of distinguished triangles.** If the first term of a
family of objects indexed by the natural numbers is bounded above by `b`, and each successive
term is the second vertex of a distinguished triangle whose first vertex is bounded above by `b`
and whose third vertex is the preceding term, then the whole family is uniformly bounded above
by `b`. -/
theorem isUniformlyBoundedAbove_of_triangles (E : ℕ → DerivedCategory A) (b : ℤ)
    (h0 : IsBoundedAboveBy (E 0) b)
    (tri : ℕ → Triangle (DerivedCategory A))
    (htri : ∀ n, tri n ∈ distinguishedTriangles)
    (h₁ : ∀ n, IsBoundedAboveBy (tri n).obj₁ b)
    (e₂ : ∀ n, (tri n).obj₂ ≅ E (n + 1))
    (e₃ : ∀ n, (tri n).obj₃ ≅ E n) :
    IsUniformlyBoundedAbove E := by
  refine ⟨b, fun n => ?_⟩
  induction n with
  | zero => exact h0
  | succ n ih =>
    exact ((IsBoundedAboveBy.obj₂ (tri n) (htri n) (h₁ n)
      (ih.of_iso (e₃ n).symm)).of_iso (e₂ n))

end Stacks.DerivedCategory

end
