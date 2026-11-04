module

public import Mathlib.Topology.Sheaves.Flasque
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksFrontier.Topology.Sheaves.Cohomology.AbelianFilteredColimits.CechAcyclicityOfInjectives
public import StacksFrontier.Topology.Sheaves.Cohomology.AbelianFilteredColimits.NativeCohomologyAndColimits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flasque abelian sheaves are acyclic

A flasque sheaf of abelian groups on a topological space is right acyclic for sections over
every open subset, so its higher cohomology vanishes.

This is the abelian-sheaf analogue of [Stacks, Tag 09SY], which is stated there for
`O_X`-modules on a ringed space and is proved in that spelling as
`Stacks.Cohomology.FlasqueAcyclic.rightAcyclic_evaluation_of_isFlasque`.  The module spelling
cannot be consumed by a statement about `Sheaf (Opens.grothendieckTopology X) AddCommGrpCat`:
crossing between the two needs the equivalence between sheaves of modules over the constant
sheaf `ℤ` and abelian sheaves, which the repository does not have.  No declaration here carries
the tag 09SY, which belongs to the module statement.

Nothing of the module argument is needed beyond what is already available for abelian sheaves:
the resolving class is the flasque abelian sheaves, it contains an embedding of every object
because an injective abelian sheaf is flasque
(`Stacks.Cohomology.AbelianVanishing.isFlasque_of_injective`), and it is stable under the
two-out-of-three property for short exact sequences while keeping sections exact, by Mathlib's
`TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂` and
`TopCat.Sheaf.IsFlasque.epi_of_shortExact`.

## Main results

* `rightAcyclic_abSections_of_isFlasque`: a flasque abelian sheaf is right acyclic for sections
  over any open subset.
* `isZero_rightDerived_abSections_of_isFlasque`: its higher right derived sections vanish.
* `subsingleton_sheafH_of_isFlasque`: its higher cohomology vanishes, in the
  `CategoryTheory.Sheaf.H` spelling.

## Implementation notes

The sheaves are spelled `Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}` with `X` a
`Type u` carrying a topology, because that is the spelling in which
`Stacks.Cohomology.AbelianColimit.abSections` and the comparison of native cohomology with
right derived sections are stated.  Flasqueness is Mathlib's `TopCat.Sheaf.IsFlasque`, stated at
`TopCat.of X`; the two categories are the same by a semireducible `def`, which `exact` crosses
but instance search does not, so each flasqueness instance is passed explicitly.

The derived categories and the existence of the right derived functor are instance arguments
rather than derived, as in the module spelling and in
`Stacks.Topology.isZero_cohomologyPresheaf_pullback_of_isFlasque`: the statement names the right
derived functor, so the instances have to be in scope to write it down.

## References

* [Stacks Project, Tag 09SY](https://stacks.math.columbia.edu/tag/09SY)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.AbelianColimit

universe u w w'

namespace Stacks.Cohomology.FlasqueAbelian

variable {X : Type u} [TopologicalSpace X]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/-- **A flasque abelian sheaf is right acyclic for sections over every open subset.**  The
resolving class is the flasque abelian sheaves: every abelian sheaf embeds in an injective one,
which is flasque; and for a short exact sequence whose first two terms are flasque the third is
flasque and sections over an open stay short exact, left exactness of sections giving the first
two conditions and flasqueness of the first term the surjectivity. -/
@[ega "0 12.1.7" "partial", sga "2 I 2.12" "special case", sga "4 V 4.6" "special case"]
theorem rightAcyclic_abSections_of_isFlasque (U : Opens X)
    [HasDerivedCategory.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    [HasDerivedCategory.{w'} AddCommGrpCat.{u}]
    [((abSections (X := X) U).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : TopCat.Sheaf.IsFlasque (X := TopCat.of X) F) :
    (abSections U).rightAcyclic F := by
  let I : ObjectProperty (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    fun G => TopCat.Sheaf.IsFlasque (X := TopCat.of X) G
  have hI₁ : ∀ G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u},
      ∃ H, ∃ (_ : I H), ∃ i : G ⟶ H, Mono i := by
    intro G
    obtain ⟨p⟩ := EnoughInjectives.presentation G
    let _ := p.injective
    exact ⟨p.J, Stacks.Cohomology.AbelianVanishing.isFlasque_of_injective p.J, p.f, p.mono⟩
  have hI₂ : ∀ S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}),
      S.ShortExact → I S.X₁ → I S.X₂ →
        I S.X₃ ∧ (S.map (abSections U)).ShortExact := by
    intro S hS h₁ h₂
    let S' : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of X)) := S
    have hS' : S'.ShortExact := hS
    let _ : S'.X₁.IsFlasque := h₁
    let _ : S'.X₂.IsFlasque := h₂
    refine ⟨(TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS' : S'.X₃.IsFlasque), ?_⟩
    have hMap := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
      (abSections (X := X) U)).mp inferInstance S hS
    refine { exact := hMap.1, mono_f := hMap.2, epi_g := ?_ }
    exact TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := U) hS'
  exact Functor.le_rightAcyclic (abSections U) I hI₁ hI₂ F hF

/-- **The higher right derived sections of a flasque abelian sheaf vanish**, over every open:
a flasque sheaf is right acyclic for sections, and for a left exact functor right acyclicity is
the vanishing of all its higher right derived functors ([Stacks, Tag 015C]). -/
@[ega "0 12.1.7" "partial", sga "2 I 2.12" "special case", sga "4 V 4.6" "special case"]
theorem isZero_rightDerived_abSections_of_isFlasque (U : Opens X)
    [HasDerivedCategory.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    [HasDerivedCategory.{w'} AddCommGrpCat.{u}]
    [((abSections (X := X) U).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : TopCat.Sheaf.IsFlasque (X := TopCat.of X) F) (p : ℕ) (hp : 0 < p) :
    IsZero (((abSections U).rightDerived p).obj F) :=
  (Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived (abSections U) F).1
    (rightAcyclic_abSections_of_isFlasque U F hF) p hp

section SheafH

variable (Y : TopCat.{u})
  [HasSheafify (Opens.grothendieckTopology (Y : Type u)) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology (Y : Type u)) AddCommGrpCat.{u})]

/-- **The higher cohomology of a flasque abelian sheaf vanishes**, in the
`CategoryTheory.Sheaf.H` spelling of the vanishing theorems of
`StacksFrontier/Topology/Sheaves/Cohomology/Vanishing`.  Native cohomology over the terminal open
is right derived global sections, and those vanish by
`isZero_rightDerived_abSections_of_isFlasque`. -/
@[sga "2 I 2.12" "special case", sga "4 V 4.6" "partial"]
theorem subsingleton_sheafH_of_isFlasque
    [HasDerivedCategory.{u} (Sheaf (Opens.grothendieckTopology (Y : Type u)) AddCommGrpCat.{u})]
    [HasDerivedCategory.{u} AddCommGrpCat.{u}]
    [((abSections (X := (Y : Type u)) ⊤).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (Opens.grothendieckTopology (Y : Type u)) AddCommGrpCat.{u}))]
    (F : TopCat.Sheaf AddCommGrpCat.{u} Y) [TopCat.Sheaf.IsFlasque F] (p : ℕ) (hp : 0 < p) :
    Subsingleton (Sheaf.H.{u, u, u, u} F p) := by
  refine (Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top
    (X := (Y : Type u)) F p).2 ?_
  have e := (nonempty_H'functor_iso_rightDerived (X := (Y : Type u)) ⊤ p).some.app F
  exact AddCommGrpCat.isZero_iff_subsingleton.1
    (IsZero.of_iso (isZero_rightDerived_abSections_of_isFlasque ⊤ F inferInstance p hp) e)

end SheafH

end Stacks.Cohomology.FlasqueAbelian

end
