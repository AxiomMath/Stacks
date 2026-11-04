module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.TermFunctorExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.DerivedSectionsAndInverseLimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphism
import StacksCore.Tactic.StacksAttribute

/-!
# The Milnor sequence for hypercohomology over an object of a ringed site

Let `(C, O)` be a ringed site, `U` an object of `C` and `(K_n)` an inverse system in the
unbounded derived category of `O`-modules with derived limit `L`. Then there is a short exact
sequence

`0 ⟶ R¹lim H^{m-1}(U, K_n) ⟶ H^m(U, L) ⟶ lim H^m(U, K_n) ⟶ 0`

of modules over the ring of sections of `O` on `U`. This is Stacks 0BKX, the display used in the
proof of Tag 0BKZ, and it is Tag 0D6K read with coefficients in modules rather than abelian
groups.

Tag 0D6K is also stated as
`Stacks.Cohomology.DerivedSectionsMilnor.exists_shortExact_limOne_cohomology_derivedSections`,
for a ringed site whose site, ring and module universes coincide. The statement here has
independent universes and coefficients in modules over `O(U)`: it is the general
`Stacks.Cohomology.DerivedSectionsMilnor.exists_milnor_shortExact_of_rightDerived` at
`Stacks.Cohomology.HypercohomologyEdge.derivedSections`.

## Main results

* `Stacks.Cohomology.HypercohomologyEdge.exists_milnor_shortExact_derivedSections`: the Milnor
  short exact sequence, with the quotient map characterized by its composites with the limit
  projections.

## Implementation notes

The hypotheses the general lemma needs of the target category are that countable products exist,
that they are exact, and that countable inverse limits exist; for modules over a ring the second
is `moduleCat_hasExactLimitsOfShape_discrete`, which is not found by instance search from the
`AB4Star` API and is therefore imported explicitly. Evaluation of sheaves of modules at an object
preserves countable products, which is what makes the right derived functor carry a derived limit
triangle to one.

The derived limit is presented by its defining distinguished triangle rather than by
`CategoryTheory.Pretriangulated.IsDerivedLimit`, so that the structural map can be named; this
is the form `Stacks.Cohomology.AcyclicCover.isIso_to_isDerivedLimit_truncGETower_of_acyclic`
produces and the form Tag 0D6K uses.

## References

* [Stacks Project, Tag 0BKX](https://stacks.math.columbia.edu/tag/0BKX)
* [Stacks Project, Tag 0D6K](https://stacks.math.columbia.edu/tag/0D6K)
* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.Cohomology.HypercohomologyEdge

universe u v wRing wModule g

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{wRing})
  [HasSheafify J AddCommGrpCat.{wModule}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{wModule} O)]

attribute [local instance] evaluation_additive

/-- **Stacks Project, Tag 0BKX.** The Milnor short exact sequence for hypercohomology over an
object of a ringed site: the first derived inverse limit of the degree-`m - 1` hypercohomologies
of an inverse system includes into the degree-`m` hypercohomology of its derived limit, with
quotient the inverse limit of the degree-`m` hypercohomologies.

This is Tag 0D6K with coefficients in modules over the ring of sections on `U`, at independent
site, ring and module universes. -/
theorem exists_milnor_shortExact_derivedSections (U : C)
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{wModule} O))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (L : DerivedCategory (SheafOfModules.{wModule} O))
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hL : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (SheafOfModules.{wModule} O)))
    (m : ℤ) :
    let RG := derivedSections O U
    let Hprev := DerivedCategory.homologyFunctor
      (ModuleCat.{wModule} (O.obj.obj (.op U))) (m - 1)
    let Hcur := DerivedCategory.homologyFunctor
      (ModuleCat.{wModule} (O.obj.obj (.op U))) m
    let E := K ⋙ RG
    let Fprev := E ⋙ Hprev
    let Fcur := E ⋙ Hcur
    let dprev : (∏ᶜ fun n : ℕ ↦ Fprev.obj ⟨n⟩) ⟶ (∏ᶜ fun n : ℕ ↦ Fprev.obj ⟨n⟩) :=
      Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ Fprev.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ Fprev.obj ⟨n⟩) (n + 1) ≫
            Fprev.map (homOfLE (Nat.le_succ n)).op
    ∃ h : HasProduct fun n : ℕ ↦ E.obj ⟨n⟩,
      letI := h
      ∃ (a : RG.obj L ⟶ ∏ᶜ fun n : ℕ ↦ E.obj ⟨n⟩)
        (b : (∏ᶜ fun n : ℕ ↦ E.obj ⟨n⟩) ⟶ (RG.obj L)⟦(1 : ℤ)⟧),
        let T := Triangle.mk a (Pi.lift fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n -
            Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) (n + 1) ≫
              E.map (homOfLE (Nat.le_succ n)).op) b
        T ∈ distTriang (DerivedCategory (ModuleCat.{wModule} (O.obj.obj (.op U)))) ∧
        (∀ n : ℕ, a ≫ Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n =
          RG.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) ∧
        ∃ (ePrev : Hprev.obj (∏ᶜ fun n : ℕ ↦ E.obj ⟨n⟩) ≅ ∏ᶜ fun n : ℕ ↦ Fprev.obj ⟨n⟩)
          (i : cokernel dprev ⟶ Hcur.obj (RG.obj L))
          (q : Hcur.obj (RG.obj L) ⟶ limit Fcur)
          (zero : i ≫ q = 0),
          ePrev.hom = piComparison Hprev (fun n : ℕ ↦ E.obj ⟨n⟩) ∧
            cokernel.π dprev ≫ i =
              ePrev.inv ≫ DerivedCategory.HomologySequence.δ T (m - 1) m ∧
            (ShortComplex.mk i q zero).ShortExact ∧
            ∀ n : ℕ, q ≫ limit.π Fcur ⟨n⟩ =
              Hcur.map (RG.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) :=
  Stacks.Cohomology.DerivedSectionsMilnor.exists_milnor_shortExact_of_rightDerived
    (SheafOfModules.evaluation O (.op U)) (derivedSections O U)
    ((homotopySections O U).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)))
    K L p hL m

end Stacks.Cohomology.HypercohomologyEdge

end
