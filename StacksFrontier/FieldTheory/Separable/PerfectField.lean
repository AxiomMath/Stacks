module

public import Mathlib.FieldTheory.SeparablyGenerated
public import StacksFrontier.FieldTheory.Separable.Defs

/-!
# Extensions of a perfect field are separable

Every field extension of a perfect field is separable in the sense of
`Algebra.IsSeparableExtension`, transcendental extensions included: a subextension of finite type
has a transcendence basis over which it is separably generated.

## Main results

* `Algebra.isSeparableExtension_of_perfectField`: every extension of a perfect field is separable.
-/

@[expose] public section

/-- Every extension of a perfect field is separable in the sense of
`Algebra.IsSeparableExtension`: each of its subextensions of finite type is separably generated. -/
lemma Algebra.isSeparableExtension_of_perfectField (k K : Type*) [Field k] [Field K]
    [Algebra k K] [PerfectField k] : Algebra.IsSeparableExtension k K where
  isSeparablyGenerated K' := by
    intro _
    obtain ⟨s, hs, H⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K'
    exact ⟨(s : Set K'), hs, H⟩

end
