module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

/-!
# A module of finite type is locally a quotient of a finite free module

Let `(C, J)` be a site, `R` a sheaf of rings on it and `M` a sheaf of `R`-modules of finite type
in the sense of `SheafOfModules.IsFiniteType`.  Then there is a family of objects covering the
terminal object over each member of which `M` receives an epimorphism from a free module on a
finite index type.

This is the **local surjection `𝒪^{⊕t} ⟶ Hⁿ(E)`** of Stacks 08HE (2) ⇒ (1), at `M = Hⁿ(E)`: the
finite-type conclusion produced by Stacks 08FX on the étale side and carried to the Zariski side
by `AlgebraicGeometry.SmallEtale.isFiniteType_homology_of_isFiniteType_homology_associatedModule`
is exactly `SheafOfModules.IsFiniteType`, and what the induction step needs out of it is the
epimorphism.

## Main results

* `SheafOfModules.exists_coversTop_epi_free_of_isFiniteType`: the local surjection.

## Implementation notes

Nothing is proved here that `SheafOfModules.IsFiniteType` does not already say; the content is
that the data it carries — `SheafOfModules.LocalGeneratorsData`, a covering of the terminal object
together with generating sections of each restriction — is unpacked into the epimorphism
`SheafOfModules.GeneratingSections.π` and the finiteness of its index, which is the shape a
consumer of the surjection uses.  The index type of the covering lives in the universe of the
objects of the site, which is where `SheafOfModules.IsFiniteType` puts it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace SheafOfModules

/-- **A sheaf of modules of finite type is locally a quotient of a finite free module.**  There is
a family of objects of the site covering the terminal object over each member of which the
restricted module receives an epimorphism from `𝒪^{⊕t}` for some finite index type.

This is the local surjection the induction of Stacks 08HE (2) ⇒ (1) applies to `Hⁿ(E)`. -/
public theorem exists_coversTop_epi_free_of_isFiniteType {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (M : SheafOfModules.{w} R) (hM : M.IsFiniteType) :
    ∃ (I : Type u) (V : I → C), J.CoversTop V ∧
      ∀ i : I, ∃ (ι : Type w) (_ : Finite ι)
        (π : SheafOfModules.free (R := R.over (V i)) ι ⟶ M.over (V i)), Epi π := by
  obtain ⟨σ, hσ⟩ := hM.exists_localGeneratorsData
  refine ⟨σ.I, σ.X, σ.coversTop, fun i => ?_⟩
  have := (hσ.isFiniteType i).finite
  exact ⟨(σ.generators i).I, inferInstance, (σ.generators i).π, inferInstance⟩

end SheafOfModules

end
