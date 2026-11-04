module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition

/-!
# Composition of fpqc coverings of algebraic spaces (Stacks 03MR, composition)

Let `S` be a scheme contained in a big fppf site `B`. Refining every member of an fpqc covering
of an algebraic space over `S` by an fpqc covering of that member gives an fpqc covering of the
original space, indexed by the dependent sum of the two index types.

The flatness clause of **Stacks 03MQ** is composition of flat morphisms of algebraic spaces,
which is **Stacks 03MN**. The refinement clause is composed in two steps: an affine
scheme-valued point of the target is refined by a finite affine fpqc family factoring through
the first covering, each member of that family is an affine scheme-valued point of the member it
factors through, and so is refined again by a finite affine fpqc family factoring through the
second covering. The resulting doubly-indexed family is finite because a dependent sum of
finitely many finite types is finite, and it is an fpqc covering of the point because
`CategoryTheory.Precoverage.comp_mem_coverings` composes the two fpqc precoverage memberships
of the underlying scheme families.

## Main results

* `AlgebraicGeometry.Space.isFpqcCovering_comp`: **Stacks 03MR**, the composition clause.

## Implementation notes

The factorisation data of the two refinement clauses is extracted with `choose`, which is why
the proof opens with `classical`: the index of the member a refinement factors through, and the
factoring morphism itself, are only known to exist.

This is a **Chapter 67 tag**, stated here because the fpqc source-locality transfer of
Stacks 06ER needs it.

## References

* [Stacks Project, Tag 03MR](https://stacks.math.columbia.edu/tag/03MR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v w

/-- **Stacks 03MR**, the composition clause. Composing an fpqc covering of an algebraic space
over `S` with fpqc coverings of each of its members gives an fpqc covering. -/
@[stacks 03MR "composition"]
theorem isFpqcCovering_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {J : I → Type w}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Xi : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Xij : (Σ i, J i) → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hXi : ∀ i, IsAlgebraicSpace B S hS (Xi i))
    (hXij : ∀ (i : I) (j : J i), IsAlgebraicSpace B S hS (Xij ⟨i, j⟩))
    (f : ∀ i, Xi i ⟶ X)
    (g : ∀ (i : I) (j : J i), Xij ⟨i, j⟩ ⟶ Xi i)
    (hf : IsFpqcCovering B S hS f)
    (hg : ∀ i, IsFpqcCovering B S hS (g i)) :
    IsFpqcCovering B S hS (fun ij : Σ i, J i => g ij.1 ij.2 ≫ f ij.1) := by
  classical
  refine ⟨fun ij => isFlat_comp B S hS (hXij ij.1 ij.2) (hXi ij.1) hX
    (g ij.1 ij.2) (f ij.1) ((hg ij.1).1 ij.2) (hf.1 ij.1), fun T h => ?_⟩
  rcases hf.2 T h with ⟨U, hUfinite, hUcover, hUfactor⟩
  choose i a ha using hUfactor
  choose V hVfinite hVcover hVfactor using fun j => (hg (i j)).2 (U.X j) (a j)
  let F := BigAffineFppf.toScheme B S hS
  let W : PreZeroHypercover T :=
    { I₀ := Σ j, (V j).I₀
      X p := (V p.1).X p.2
      f p := (V p.1).f p.2 ≫ U.f p.1 }
  let : Finite U.I₀ := hUfinite
  have (j : U.I₀) : Finite (V j).I₀ := hVfinite j
  refine ⟨W, inferInstance, ?_, ?_⟩
  · show Presieve.map F W.presieve₀ ∈ Scheme.fpqcPrecoverage (F.obj T)
    simpa [W, PreZeroHypercover.presieve₀_map, Functor.map_comp] using
      (Precoverage.comp_mem_coverings (J := Scheme.fpqcPrecoverage)
        (f := fun j => F.map (U.f j))
        (by simpa [F, PreZeroHypercover.presieve₀] using hUcover)
        (g := fun j l => F.map ((V j).f l)) (fun j => by
          simpa [F, PreZeroHypercover.presieve₀] using hVcover j))
  · intro jl
    obtain ⟨k, b, hb⟩ := hVfactor jl.1 jl.2
    refine ⟨⟨i jl.1, k⟩, b, ?_⟩
    show b ≫ (g (i jl.1) k ≫ f (i jl.1)) =
      yoneda.map ((BigAffineFppf.inclusion B S hS).map (W.f jl)) ≫ h
    rw [← Category.assoc, hb, Category.assoc, ha]
    simp [W, Functor.map_comp, Category.assoc]

end AlgebraicGeometry.Space

end
