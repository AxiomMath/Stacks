module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PseudoCoherenceAndTorAmplitude
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherentObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatnessOfFiniteFreeSummands
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocallyFiniteTorDimension
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PseudoCoherenceGeneral

/-!
# Supplement to `PseudoCoherenceAndTorAmplitude`

The results of this module extend those of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PseudoCoherenceAndTorAmplitude`.
They use imports, universe variables or `open` declarations that the base module does not
have, and are kept in a module of their own so that its header is unchanged.

## Main results

* `isPseudoCoherentComplex_of_isPerfectComplex_anyModuleUniverse`
* `isPseudoCoherent_of_isPerfect_univ`
-/

/-! ### The generalizations made by this development

The declarations below restate, under weaker hypotheses or at more general universes, declarations
of this file whose statements are kept as they are above. Each carries the name of the declaration
it generalizes with the suffix `_univ` (or `Univ` for a definition). -/

universe u v w m d

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w})
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{m}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}]
variable [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]

variable [HasSheafify X.J AddCommGrpCat.{m}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{m}]
variable [HasDerivedCategory.{d} (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

omit [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})] in
/-- A perfect object of `D(O)` is pseudo-coherent. This is the first clause of the implication
(1) ⟹ (2) of Stacks 08G8. -/
theorem isPseudoCoherent_of_isPerfect_univ
    {E : DerivedCategory (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hE : X.IsPerfect E) :
    X.IsPseudoCoherent E := by
  obtain ⟨K, hK, e⟩ := hE
  exact ⟨K, isPseudoCoherentComplex_of_isPerfectComplex_anyModuleUniverse X hK, e⟩

end AlgebraicGeometry.RingedSite

/-! ### Locally finite Tor dimension -/

end
