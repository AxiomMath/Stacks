module

public import StacksFrontier.AlgebraicGeometry.Limits.ChowLemma
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.OneAffineOpenStep

/-!
# Absolute Noetherian approximation

A quasi-compact and quasi-separated scheme is the inverse limit, over a directed set, of an
inverse system of schemes of finite type over the integers whose transition morphisms are
affine.

## Main results

* `AlgebraicGeometry.Scheme.exists_isLimit_affine_locallyOfFiniteType`: **absolute Noetherian
  approximation.**

## Implementation notes

The statement is the case `U = ⊥` of approximation relative to a quasi-compact open,
`AlgebraicGeometry.Scheme.FiniteTypeApproximation.nonempty_of_isLimit`.  The system on `⊥`
which that result extends is the constant system with a single index at the empty subscheme:
its transition morphisms are identities, hence affine; it is of finite type over the integers
because an empty scheme is affine with the zero ring as its ring of global functions; and `⊥`
is its limit because a constant system indexed by a category with one object has its value as
limit.  The data the relative statement produces on the `⊥` side is then discarded.

Finite type over the integers is expressed, as elsewhere in this development, by
`LocallyOfFiniteType` together with `QuasiCompact` for the morphism to the terminal scheme,
which is `Spec (ULift ℤ)`.

The ingredients of that `⊥` system live in the modules the whole approximation development
shares, so that the conditional deduction of 01ZA in
`StacksFrontier.AlgebraicGeometry.Limits.AbsoluteNoetherianApproximation` uses the same ones:
`AlgebraicGeometry.Scheme.botDiagram` and `AlgebraicGeometry.Scheme.isLimitConstConePUnit` are in
`StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.Basic`, and the finite-type and
quasi-compactness of an empty scheme over the integers,
`AlgebraicGeometry.locallyOfFiniteType_terminal_from_of_isEmpty` and
`AlgebraicGeometry.quasiCompact_terminal_from_of_isEmpty`, are in
`StacksFrontier.AlgebraicGeometry.Limits.ChowLemma` beside
`AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType_terminal_from`.

## References

* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Scheme

/-- **Absolute Noetherian approximation.**  A quasi-compact and quasi-separated scheme `S` is
the inverse limit of an inverse system of schemes over a directed set whose transition
morphisms are affine and whose every stage is of finite type over the integers. -/
@[stacks 01ZA]
theorem exists_isLimit_affine_locallyOfFiniteType (S : Scheme.{u}) [CompactSpace S]
    [QuasiSeparatedSpace S] :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : Iᵒᵈ ⥤ Scheme.{u}) (c : (Functor.const Iᵒᵈ).obj S ⟶ F),
      (∀ {i j : Iᵒᵈ} (f : i ⟶ j), IsAffineHom (F.map f)) ∧
      (∀ i, LocallyOfFiniteType (terminal.from (F.obj i))) ∧
      (∀ i, QuasiCompact (terminal.from (F.obj i))) ∧
      Nonempty (IsLimit (Cone.mk S c)) := by
  have : IsEmpty ((⊥ : S.Opens) : Scheme.{u}) := inferInstanceAs (IsEmpty (∅ : Set S))
  have : ∀ {i j : PUnit.{u + 1}ᵒᵈ} (f : i ⟶ j), IsAffineHom ((botDiagram S).map f) :=
    fun _ ↦ inferInstanceAs (IsAffineHom (𝟙 _))
  have : ∀ i, LocallyOfFiniteType (terminal.from ((botDiagram S).obj i)) :=
    fun _ ↦ locallyOfFiniteType_terminal_from_of_isEmpty ((⊥ : S.Opens) : Scheme.{u})
  have : ∀ i, QuasiCompact (terminal.from ((botDiagram S).obj i)) :=
    fun _ ↦ quasiCompact_terminal_from_of_isEmpty ((⊥ : S.Opens) : Scheme.{u})
  obtain ⟨Q⟩ := FiniteTypeApproximation.nonempty_of_isLimit (botDiagram S) S ⊥ (𝟙 _)
    (isLimitConstConePUnit ((⊥ : S.Opens) : Scheme.{u}))
  exact ⟨Q.indexType, Q.indexPreorder, Q.indexNonempty, Q.indexDirected, Q.ambient,
    Q.ambientCone, Q.transition_affine, Q.locallyOfFiniteType, Q.quasiCompact,
    ⟨Q.ambientCone_isLimit⟩⟩

end Scheme

end AlgebraicGeometry

end
