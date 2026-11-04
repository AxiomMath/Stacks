module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.ProjectiveBundleTransfer
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.RankZero

/-!
# The projective bundle formula for de Rham cohomology in rank zero

The projective bundle of a module finite locally free of rank zero is empty
(`Stacks.Chow.isEmpty_bundle_of_rank_zero`), and the de Rham cohomology of an empty scheme
vanishes: it is a module over the global sections of a sheaf of rings on the empty space, which
form the zero ring. So in rank zero both sides of [Stacks, Tag 0FMT] vanish and the map between
them, out of an empty direct sum, is bijective.

## Main results

* `Stacks.ProjectiveBundleDeRham.subsingleton_deRhamCohomology_of_isEmpty`.
* `Stacks.ProjectiveBundleDeRham.isEmpty_projectiveBundle_of_rank_zero`.

## References

* [Stacks Project, Tag 0FMT](https://stacks.math.columbia.edu/tag/0FMT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.RelativeProj (projectiveBundle projectiveBundleToBase)
open scoped Stacks.StandardDerivedModel

universe u

namespace Stacks.ProjectiveBundleDeRham

/-- **The de Rham cohomology of an empty scheme vanishes**: it is a module over the global
sections of a sheaf of rings on the empty space, which form the zero ring. -/
theorem subsingleton_deRhamCohomology_of_isEmpty {P S : Scheme.{u}} (f : P ⟶ S) [IsEmpty P]
    (k : ℤ) :
    Subsingleton (SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras f)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) k) := by
  have htop : (⊤ : P.Opens) = ⊥ := by
    ext x
    exact isEmptyElim x
  have : Subsingleton (Stacks.DeRhamWeil.baseSectionRing f) :=
    CommRingCat.subsingleton_of_isTerminal
      (TopCat.Sheaf.isTerminalOfEqEmpty ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)
        htop)
  exact Module.subsingleton (Stacks.DeRhamWeil.baseSectionRing f) _

/-- **The projective bundle of a module finite locally free of rank zero is empty.** -/
theorem isEmpty_projectiveBundle_of_rank_zero {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 0] :
    IsEmpty (projectiveBundle X E) := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 0
  have : IsEmpty (Stacks.RelativeProj.symGradedBundle E).scheme :=
    Stacks.Chow.isEmpty_bundle_of_rank_zero E
  exact Function.isEmpty (Stacks.RelativeProj.bundlePresentationIso E).inv.base

/-- **[Stacks, Tag 0FMT] in rank zero**: for `ℰ` finite locally free of rank zero the map
`⨁_{i < 0} H^{k-2i}_{dR}(X/S) ⟶ H^k_{dR}(P/S)` is bijective, both sides being zero. -/
theorem bijective_sum_cup_of_rank_zero {X S : Scheme.{u}} (g : X ⟶ S) (E : X.Modules)
    [E.IsQuasicoherent] [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 0]
    (k : ℤ) :
    Function.Bijective (fun a : ∀ i : Fin 0, SheafOfModules.deRhamCohomology
        (Scheme.Hom.deRhamAlgebras g)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras g))
        (k - ((2 * (i : ℕ) : ℕ) : ℤ)) =>
      ∑ i : Fin 0, (eqToHom (congrArg (SheafOfModules.deRhamCohomology
          (Scheme.Hom.deRhamAlgebras (projectiveBundleToBase X E ≫ g))
          (SheafOfModules.deRhamDifferential
            (Scheme.Hom.deRhamAlgebras (projectiveBundleToBase X E ≫ g))))
          (add_sub_cancel ((2 * (i : ℕ) : ℕ) : ℤ) k))).hom
        (SheafOfModules.deRhamCohomologyCup _ _ ((2 * (i : ℕ) : ℕ) : ℤ)
          (k - ((2 * (i : ℕ) : ℕ) : ℤ))
          (DeRhamLerayHirsch.classPow (projectiveBundleToBase X E ≫ g) 2
            (DeRhamLerayHirsch.projectiveBundleChernClass g E) i)
          (DeRhamKatzOdaCech.deRhamPullbackModule (projectiveBundleToBase X E) g
            (k - ((2 * (i : ℕ) : ℕ) : ℤ)) (a i)))) := by
  have := isEmpty_projectiveBundle_of_rank_zero E
  have := subsingleton_deRhamCohomology_of_isEmpty (projectiveBundleToBase X E ≫ g) k
  exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨isEmptyElim, Subsingleton.elim _ _⟩⟩

end Stacks.ProjectiveBundleDeRham
