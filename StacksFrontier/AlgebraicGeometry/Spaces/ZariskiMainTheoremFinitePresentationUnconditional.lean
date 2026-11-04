module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismLimitSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiMainTheoremFinitePresentation

/-!
# Zariski's main theorem for algebraic spaces with a finitely presented compactification

Let `f : X ⟶ Y` be a quasi-finite separated morphism of algebraic spaces over a scheme `S`
which is locally of finite presentation, with `Y` quasi-compact and quasi-separated. Stacks 0874
says that the factorization `f = π ∘ j` of Stacks 082K, with `j` a quasi-compact open immersion
and `π` finite, can be chosen with `π` moreover of finite presentation.

The argument is the one of
`AlgebraicGeometry.Space.exists_isOpenImmersion_isFinitePresentation_of_isQuasiFinite`: the
factorization of Stacks 082K
(`AlgebraicGeometry.Space.exists_isOpenImmersion_isFinite_comp_eq_of_isQuasiFinite`) is
improved by writing its finite part as a limit of spaces finite and of finite presentation over
`Y` along closed immersions, which is Stacks 07VR
(`AlgebraicGeometry.Space.exists_integralFiniteSystem_of_isFinite`), and replacing it by a
stage. That theorem takes Stacks 07VR as a hypothesis; it is discharged here.

## Main results

* `AlgebraicGeometry.Space.exists_isOpenImmersion_isFinitePresentation_comp_eq_of_isQuasiFinite`:
  **Stacks 0874**.

## References

* [Stacks Project, Tag 0874](https://stacks.math.columbia.edu/tag/0874)
* [Stacks Project, Tag 082K](https://stacks.math.columbia.edu/tag/082K)
* [Stacks Project, Tag 07VR](https://stacks.math.columbia.edu/tag/07VR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0874.** Let `f : X ⟶ Y` be a quasi-finite separated morphism of algebraic spaces
over `S` which is locally of finite presentation, with `Y` quasi-compact and quasi-separated.
Then `f = π ∘ j` with `j : X ⟶ T` a quasi-compact open immersion into an algebraic space `T`
and `π : T ⟶ Y` finite and of finite presentation. -/
@[stacks 0874]
theorem exists_isOpenImmersion_isFinitePresentation_comp_eq_of_isQuasiFinite
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hqf : IsQuasiFinite B S hS f) (hsep : IsSeparated B S hS f)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (hfp : IsLocallyOfFinitePresentation B S hS f) :
    ∃ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (j : X ⟶ T) (π : T ⟶ Y),
      IsAlgebraicSpace B S hS T ∧ IsOpenImmersion B S hS j ∧ IsQuasiCompact B S hS j ∧
        IsFinite B S hS π ∧ IsFinitePresentation B S hS π ∧ j ≫ π = f :=
  exists_isOpenImmersion_isFinitePresentation_of_isQuasiFinite
    (fun g hX' hY' hg hY'qc hY'qs ↦
      exists_integralFiniteSystem_of_isFinite B S hS g hX' hY' hg hY'qc hY'qs)
    f hX hY hqf hsep hYqc hYqs hfp

end AlgebraicGeometry.Space

end
