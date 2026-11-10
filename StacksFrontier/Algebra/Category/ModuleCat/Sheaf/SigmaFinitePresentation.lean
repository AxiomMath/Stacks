module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleFinitePresentation
public import StacksFrontier.CategoryTheory.Limits.SigmaSupport

/-!
# A graded sheaf of modules with finitely many nonzero pieces is of finite presentation

A coproduct `∐ G` of sheaves of modules whose summands vanish outside a predicate with finitely
many witnesses, each surviving summand being a direct summand of a finite free sheaf of modules,
has a finite presentation.

This is the shape in which the determinant of a sheaf of modules asks the question. The
determinant is the `ℕ`-indexed coproduct of the degreewise exterior annihilators
(`SheafOfModules.TensorExteriorSymmetricAlgebras.determinant`), only finitely many degrees
survive on a trivialising open, and each surviving degree sits inside an exterior power of a
finite free sheaf of modules. The index of the coproduct is `ℕ`, which is not in the universe of
the module, so the enumeration of the surviving summands is taken as a datum `T ≃ {i // p i}`
with `T` in the module universe; that is what makes the free sheaf of modules on the disjoint
union of the index sets well-typed.

## Main results

* `Stacks.SheafOfModules.exists_isFinite_presentation_sigma_of_isZero_of_retract_free`: the
  finite presentation.

## Implementation notes

Nothing here is about presentations as such. The three comparisons —
`CategoryTheory.Limits.sigmaSubtypeIsoOfIsZero` discarding the vanishing summands,
`CategoryTheory.Limits.Sigma.whiskerEquiv` reindexing the survivors by `T`, and
`SheafOfModules.freeSigmaIso` folding the coproduct of free sheaves of modules into the free
sheaf of modules on the disjoint union — compose with `CategoryTheory.Retract.sigma` into a
single retract of a finite free sheaf of modules, and
`Stacks.SheafOfModules.exists_isFinite_presentation_of_retract` reads the presentation off that.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits SheafOfModules

universe u₁ v₁ w

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **A coproduct of sheaves of modules with finitely many nonzero summands, each a direct
summand of a finite free sheaf of modules, has a finite presentation.**

The vanishing summands are discarded, the survivors are reindexed by `T`, and the coproduct of
the ambient finite free sheaves of modules is the finite free sheaf of modules on the disjoint
union of their index sets; a coproduct of retracts being a retract, the whole coproduct is a
retract of that one finite free sheaf of modules. -/
theorem exists_isFinite_presentation_sigma_of_isZero_of_retract_free
    {ι : Type*} {G : ι → SheafOfModules.{w} R} (p : ι → Prop)
    (hz : ∀ i, ¬ p i → IsZero (G i))
    {T : Type w} [Finite T] (e : T ≃ Subtype p)
    (K : T → Type w) [∀ t, Finite (K t)]
    (ρ : ∀ t : T, Retract (G (e t).1) (free (R := R) (K t)))
    [HasCoproduct G] [HasCoproduct fun j : Subtype p => G j.1]
    [HasCoproduct fun t : T => G (e t).1]
    [HasCoproduct fun t : T => free (R := R) (K t)] :
    ∃ q : (∐ G).Presentation, q.IsFinite := by
  classical
  let i₁ : (∐ fun j : Subtype p => G j.1) ≅ ∐ G := sigmaSubtypeIsoOfIsZero G p hz
  let i₂ : (∐ fun t : T => G (e t).1) ≅ ∐ fun j : Subtype p => G j.1 :=
    Sigma.whiskerEquiv (f := fun t : T => G (e t).1) (g := fun j : Subtype p => G j.1) e
      fun _ => Iso.refl _
  let τ : Retract (∐ G) (free (R := R) (Σ t : T, K t)) :=
    ((Retract.ofIso (i₂.trans i₁).symm).trans (Retract.sigma ρ)).trans
      (Retract.ofIso (freeSigmaIso (O := R) K))
  exact exists_isFinite_presentation_of_retract τ.i τ.r τ.retract

end Stacks.SheafOfModules

end
