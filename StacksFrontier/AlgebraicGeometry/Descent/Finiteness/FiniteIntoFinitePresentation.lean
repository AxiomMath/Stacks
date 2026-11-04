module

public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.FiniteLimitPresentation
public import StacksFrontier.AlgebraicGeometry.EventualFiniteness.Basic

/-!
# A finite morphism is a closed subscheme of a finite morphism of finite presentation

Let `f : X ⟶ S` be a finite morphism of schemes with `S` quasi-compact and quasi-separated.
Then `f` factors as a closed immersion `X ⟶ X'` followed by a morphism `X' ⟶ S` which is both
finite and of finite presentation.

## Main results

* `AlgebraicGeometry.exists_isFinite_finitePresentation_closedImmersion`: the closed immersion
  of `X` into a scheme finite and of finite presentation over `S`.

## References

* [Stacks Project, Tag 01ZK](https://stacks.math.columbia.edu/tag/01ZK)
* [Stacks Project, Tag 09ZQ](https://stacks.math.columbia.edu/tag/09ZQ)
* [Stacks Project, Tag 09ZN](https://stacks.math.columbia.edu/tag/09ZN)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

universe u

/-- A finite morphism `f : X ⟶ S` of schemes whose target is
quasi-compact and quasi-separated factors as a closed immersion `X ⟶ X'` followed by a morphism
`X' ⟶ S` which is finite and of finite presentation. -/
@[stacks 01ZK]
theorem exists_isFinite_finitePresentation_closedImmersion {X S : Scheme.{u}} (f : X ⟶ S)
    [IsFinite f] [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (X' : Scheme.{u}) (f' : X' ⟶ S) (i : X ⟶ X'),
      IsFinite f' ∧ FinitePresentation f' ∧ IsClosedImmersion i ∧ i ≫ f' = f := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨I, _, _, _, D, t, p, hlim, hcompat, hstage, htrans, hproj⟩ :=
    exists_isLimit_finitePresentation_closedImmersion f
  have hfac : ∀ i : I, p.app (Opposite.op i) ≫ t.app (Opposite.op i) = f := fun i ↦ by
    simpa using congrArg (fun η ↦ η.app (Opposite.op i)) hcompat
  have hcs : ∀ i : I, CompactSpace (D.obj (Opposite.op i)) := fun i ↦ (hstage _).2.1
  have hqs : ∀ i : I, QuasiSeparatedSpace (D.obj (Opposite.op i)) := fun i ↦ (hstage _).2.2
  have hft : ∀ i : I, LocallyOfFiniteType (t.app (Opposite.op i)) := fun i ↦ by
    have : LocallyOfFinitePresentation (t.app (Opposite.op i)) :=
      (hstage _).1.locallyOfFinitePresentation
    infer_instance
  obtain ⟨i₀, hi₀⟩ := Filter.eventually_atTop.mp
    (eventually_isFinite_of_isLimit_of_isIntegral D t (Cone.mk X p) hlim f
      (fun i ↦ (hfac i).symm)
      (fun {_ _} h ↦ by have := htrans (homOfLE h).op; infer_instance)
      (fun {_ _} h ↦ by have := htrans (homOfLE h).op; infer_instance))
  exact ⟨D.obj (Opposite.op i₀), t.app (Opposite.op i₀), p.app (Opposite.op i₀),
    hi₀ i₀ le_rfl, (hstage _).1, hproj _, hfac i₀⟩

end AlgebraicGeometry

end
