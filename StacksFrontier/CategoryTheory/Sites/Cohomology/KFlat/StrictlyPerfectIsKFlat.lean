module

public import
  StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatnessOfFiniteFreeSummands
import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# A strictly perfect complex on a ringed site is K-flat

Let `(C, O)` be a ringed site. A strictly perfect complex of `O`-modules (Stacks 08FL) has
only finitely many nonzero terms, and each of its terms is a direct summand of a finite free
`O`-module. Both clauses of Stacks 06YQ are therefore available — the complex is bounded above,
and its terms are flat — so it is K-flat.

## Main results

* `AlgebraicGeometry.RingedSite.isStrictlyLE_of_isStrictlyPerfect`: a strictly perfect complex
  is bounded above.
* `AlgebraicGeometry.RingedSite.kFlat_of_isStrictlyPerfect`: a strictly perfect complex of
  `O`-modules is K-flat.

## Implementation notes

Both inputs are available at full site generality, so this file is only the assembly. Flatness
of the terms is `Stacks.SheafOfModules.isFlat_X_of_isStrictlyPerfect`, which rests on the
flatness of a finite free `O`-module and on the closure of flatness under retracts,
`Stacks.SheafOfModules.FlatRetract.isFlat_of_retract`; no objectwise argument on the presheaf
level is needed, unlike in the ringed-space analogue
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_of_isStrictlyPerfect`. Stacks 06YQ is
`Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat`.

Boundedness is recorded in `IsStrictlyPerfect` as finiteness of the set of degrees carrying a
nonzero term; `Set.Finite.bddAbove` turns that into the `CochainComplex.IsStrictlyLE` bound that
Stacks 06YQ asks for.

The universes are the diagonal `RingedSite.{u, u, u}`. That is where
`Stacks.SheafOfModules.isFlat_X_of_isStrictlyPerfect` lives: flatness of the structure sheaf is
read off the monoidal structure on `Mod(O)`, which pins the sections of the structure sheaf to
`Type (max u v)`, and the module sections of a strictly perfect complex share that universe.

Two spellings of the sheaf of rings meet here. `AlgebraicGeometry.RingedSite.ringSheaf X`, which
the statement is written in, and `Stacks.SheafOfModules.Tensor.ringSheaf X.O`, which
`Stacks.SheafOfModules.IsKFlat` and Stacks 06YQ are stated through, are both
`sheafCompose J (forget₂ CommRingCat RingCat)` applied to `X.O` and differ only in which proof
of `GrothendieckTopology.HasSheafCompose` they supply. They are therefore interchangeable at
default transparency, and the two results are applied as terms rather than rewritten.

## References

* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YN](https://stacks.math.columbia.edu/tag/06YN)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **A strictly perfect complex of `O`-modules is bounded above.** Only finitely many of its
terms are nonzero, and a finite set of integers is bounded above. -/
theorem isStrictlyLE_of_isStrictlyPerfect
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hK : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) K) :
    ∃ n : ℤ, K.IsStrictlyLE n := by
  obtain ⟨n, hn⟩ := hK.bounded.bddAbove
  refine ⟨n, (CochainComplex.isStrictlyLE_iff K n).2 fun i hi => ?_⟩
  by_contra h
  exact absurd (hn (by simpa only [Set.mem_ofPred_eq] using h)) (by omega)

/-- **A strictly perfect complex of `O`-modules on a ringed site is K-flat.** Its terms are
direct summands of finite free `O`-modules, hence flat, and only finitely many of them are
nonzero, so the complex is bounded above; Stacks 06YQ concludes. -/
theorem kFlat_of_isStrictlyPerfect
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hK : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) K) :
    Stacks.SheafOfModules.IsKFlat X.O K :=
  Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat X.O K
    (isStrictlyLE_of_isStrictlyPerfect X K hK)
    fun i => Stacks.SheafOfModules.isFlat_X_of_isStrictlyPerfect (Y := X) hK i

end AlgebraicGeometry.RingedSite

end
