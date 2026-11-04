module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleDualEvaluation
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulDerivedTensorDual
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedDualOfAStrictlyPerfectComplex
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomFiniteFree

/-!
# The derived dual of the Koszul complex is its naive dual

Let `(C, O)` be a ringed site and let `f_1, …, f_r` be global sections of `O`. The Koszul
complex `AlgebraicGeometry.RingedSite.koszulPowerComplex` on the `(n+1)`-st powers is bounded,
and its term in degree `p` is the product of copies of `O` indexed by the subsets of `Fin r` of
cardinality `p`. It is therefore strictly perfect, so the general statement
`AlgebraicGeometry.RingedSite.derivedDualIsoSheafHomComplexUnit` applies to it: **its derived
dual is its naive termwise dual.**

This is the identification that the module doc of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulCechHomotopyColimit`
describes as holding "because `K^n` is a bounded complex of finite products of copies of `𝒪`"
and records as not proved. It is the first half of the comparison of the tower of
[Stacks, Tag 0A0E] with the Koszul power tower.

## Main results

* `AlgebraicGeometry.RingedSite.isFiniteFreeSummand_pi_unit`: a finite product of copies of `O`
  is a direct summand of a finite free module.
* `AlgebraicGeometry.RingedSite.isFiniteFreeSummand_koszulPowerComplex_X`: every term of the
  Koszul complex is a direct summand of a finite free module.
* `AlgebraicGeometry.RingedSite.derivedDualIsoSheafHomComplexUnit_koszulPowerComplex`: **the
  derived dual of the Koszul complex is the class of its naive termwise dual.**

## Implementation notes

The termwise hypothesis of [Stacks, Tag 08JH] is
`AlgebraicGeometry.RingedSite.IsFiniteFreeSummand`, a retract of an iterated *binary* biproduct
of copies of `O`, while the Koszul term is a *product over a finite index type*. The bridge is
`AlgebraicGeometry.RingedSite.isFiniteFreeSummand_of_retract_free`, whose hypothesis is a
retract of `SheafOfModules.free`, together with
`Stacks.SheafOfModules.piUnitIsoFree`, which identifies a product of `n` copies of `O` with the
finite free module on `ULift (Fin n)`. The index type of the Koszul term is reindexed to
`Fin (Fintype.card ι)` by `CategoryTheory.Limits.Pi.whiskerEquiv` along
`Fintype.equivFin`, which is where the choice of a bijection enters; the conclusion does not
depend on it, `IsFiniteFreeSummand` asserting only existence.

No separate description of the Koszul term as a product is needed: it is
`CategoryTheory.AlternatingCech.term` of the constant functor at `O`, which is that product
definitionally, so `isFiniteFreeSummand_pi_unit` applies at the index type
`CategoryTheory.AlternatingCech.Idx r p` with no transport.

## References

* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **A finite product of copies of the structure sheaf is a direct summand of a finite free
module.** Reindexing the product along a bijection of its index type with `Fin n` and then
identifying it with the finite free module on `ULift (Fin n)` by
`Stacks.SheafOfModules.piUnitIsoFree` exhibits it as a retract of a finite free module. -/
theorem isFiniteFreeSummand_pi_unit {ι : Type} [Finite ι] :
    IsFiniteFreeSummand X
      (∏ᶜ fun _ : ι ↦ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) := by
  let := Fintype.ofFinite ι
  exact isFiniteFreeSummand_of_retract_free X (ULift.{u} (Fin (Fintype.card ι)))
    (Retract.ofIso
      (Pi.whiskerEquiv
          (f := fun _ : ι ↦ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (g := fun _ : Fin (Fintype.card ι) ↦
            SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (Fintype.equivFin ι) (fun _ ↦ Iso.refl _) ≪≫
        Stacks.SheafOfModules.piUnitIsoFree (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (Fintype.card ι)))

variable {r : ℕ} (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **Every term of the Koszul complex is a direct summand of a finite free module.** The term
in degree `p` is the product of copies of `O` indexed by the subsets of `Fin r` of cardinality
`p`, a finite type, so this is `isFiniteFreeSummand_pi_unit` at that index type. -/
theorem isFiniteFreeSummand_koszulPowerComplex_X (n : ℕ) (p : ℤ) :
    IsFiniteFreeSummand X ((koszulPowerComplex X f n).X p) :=
  isFiniteFreeSummand_pi_unit X

/-- **The derived dual of the Koszul complex is its naive termwise dual.** The Koszul complex is
bounded by `AlgebraicGeometry.RingedSite.finite_support_koszulPowerComplex` and its terms are
direct summands of finite free modules by `isFiniteFreeSummand_koszulPowerComplex_X`, so it is
strictly perfect, and [Stacks, Tag 08JH] at the target `O` identifies its derived dual with the
internal Hom complex `SheafHom(K(𝒪, f^{n+1}), 𝒪)`.

This is the identification the module doc of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulCechHomotopyColimit`
asserts and leaves unproved, and the first half of the comparison of the tower of
[Stacks, Tag 0A0E] with the Koszul power tower. -/
def derivedDualIsoSheafHomComplexUnit_koszulPowerComplex (n : ℕ) :
    DerivedCategory.Q.obj (sheafHomComplex X (koszulPowerComplex X f n)
        (structureSheafComplex X)).obj ≅
      derivedDual X (DerivedCategory.Q.obj (koszulPowerComplex X f n)) :=
  derivedDualIsoSheafHomComplexUnit X (koszulPowerComplex X f n)
    (finite_support_koszulPowerComplex X f n)
    (isFiniteFreeSummand_koszulPowerComplex_X X f n)

end AlgebraicGeometry.RingedSite

end
