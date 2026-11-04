module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjects
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedObjects
import StacksCore.Tactic.StacksAttribute

/-!
# Clause (2) of Stacks 0FPY is inhabited at a ringed site

`AlgebraicGeometry.RingedSite.InvertibleDerived.isPerfect_of_hasInvertibleModuleDecomposition`
is the one assertion of Stacks 0FPY that is proved, and it consumes
`AlgebraicGeometry.RingedSite.InvertibleDerived.HasInvertibleModuleDecomposition` as a
hypothesis. That hypothesis is an existential over
`AlgebraicGeometry.RingedSite.InvertibleDerived.ProductDecomposition`, and before this file no
declaration in the library inhabited either of them at a ringed site: the only product
decompositions built were the ringed-*space* ones of
`StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedObjects` and
`…InvertibleDerivedTwoFactorWitness`, which are a different structure. So the site-level theorem
had content only to the extent that its hypothesis had an inhabitant, and it had none.

This file supplies one, over an arbitrary ringed site and assuming nothing: the decomposition
with `O_0 = O` and the zero ring in every other degree, carrying the unit module in each degree.
For it `⨁ ℋ^n[-n]` is `O` placed in degree zero, so the conclusion of Stacks 0FPY reads as the
perfectness of the structure sheaf.

## No second copy of the one-factor construction

The construction of the family `O_0 = O`, `O_n = 0` for `n ≠ 0`, of the projections onto it and
of the proof that they form a limit fan is **not** repeated here. That development —
`Stacks.Cohomology.InvertibleDerived.zeroRingSheaf`, `…oneFactorFamily`, `…oneFactorProj`,
`…isLimitOneFactorFan` and `…subsingleton_oneFactorFamily_of_ne` — is already stated for an
arbitrary site and an arbitrary sheaf of commutative rings on it, even though it is hosted in a
ringed-space file and was written for the ringed-space decomposition. It is used here verbatim;
what this file adds is the one step the two decompositions genuinely differ by. The ringed-space
structure stores an isomorphism `O ≅ ∏ᶜ factor` with the categorical product, which needs that
product to exist; the ringed-site structure stores a
`Stacks.SheafOfModules.RingSheafProductFactor.ProductPresentation`, which asks only for
projections whose joint evaluation on sections is bijective. The passage from a limit fan to a
product presentation is
`Stacks.SheafOfModules.RingSheafProductFactor.ProductPresentation.ofIsLimit`, so the one-factor
decomposition is available at a ringed site **without** assuming `HasProduct`, which the
ringed-space one does assume.

Local finiteness also differs: the ringed-space field asks for a neighbourhood of each point on
which all but finitely many factors vanish, the ringed-site field for a covering sieve of each
object with the same property over its members. For the one-factor family the condition holds
over *every* object, so the maximal sieve serves and no covering has to be produced.

## Main definitions

* `AlgebraicGeometry.RingedSite.InvertibleDerived.oneFactorDecomposition`: the one-factor
  locally finite direct product decomposition of the structure sheaf of a ringed site.

## Main results

* `AlgebraicGeometry.RingedSite.InvertibleDerived.exists_hasInvertibleModuleDecomposition`:
  clause (2) of Stacks 0FPY has an inhabitant over every ringed site.
* `AlgebraicGeometry.RingedSite.InvertibleDerived.isPerfect_oneFactorComplex`: the conclusion of
  Stacks 0FPY is reached at that inhabitant, at a named object of `D(O)`.

Neither is a clause of the tag, so neither carries a `@[stacks]` attribute.

## References

* [Stacks Project, Tag 0FPY](https://stacks.math.columbia.edu/tag/0FPY)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.InvertibleDerived (oneFactorFamily oneFactorFamily_zero oneFactorProj
  isLimitOneFactorFan subsingleton_oneFactorFamily_of_ne)

universe u d

namespace AlgebraicGeometry.RingedSite.InvertibleDerived

section Decomposition

variable (X : RingedSite.{u, u, u})

/-- **The one-factor product decomposition of the structure sheaf of a ringed site**: `O_0 = O`
and `O_n = 0` for `n ≠ 0`.

The product presentation is read off the limit fan of the one-factor family, so no product of
sheaves of commutative rings is required to exist; local finiteness holds over every object of
the site, only the degree-zero factor having any sections, so the maximal sieve witnesses it. -/
def oneFactorDecomposition : ProductDecomposition X where
  factor := oneFactorFamily X.O
  presentation :=
    Stacks.SheafOfModules.RingSheafProductFactor.ProductPresentation.ofIsLimit
      (oneFactorProj X.O) (isLimitOneFactorFan X.O)
  locallyFinite U := by
    refine ⟨(⊤ : Sieve U).arrows, ?_, fun {V} _ _ => ?_⟩
    · rw [Sieve.generate_sieve]
      exact X.J.top_mem U
    · refine Set.Finite.subset (Set.finite_singleton (0 : ℤ)) fun n hn => ?_
      simp only [Set.mem_singleton_iff]
      by_contra hne
      exact hn (subsingleton_oneFactorFamily_of_ne X.O hne _)

/-- The factors of `oneFactorDecomposition X` form the one-factor family of `O`. -/
@[simp]
theorem oneFactorDecomposition_factor :
    (oneFactorDecomposition X).factor = oneFactorFamily X.O := rfl

/-- **The degree-zero factor of the one-factor decomposition is the structure sheaf itself.** So
the decomposition is not the one all of whose factors are the zero ring: the datum inhabited by
`oneFactorDecomposition` is not degenerate in the only way a product decomposition can be, and
the degree-zero factor is nonzero exactly when `O` is. -/
theorem oneFactorDecomposition_factor_zero : (oneFactorDecomposition X).factor 0 = X.O :=
  oneFactorFamily_zero X.O

end Decomposition

section Clause

variable {X : RingedSite.{u, u, u}}
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

variable (X) in
/-- The complex with the unit module of the `n`-th one-factor factor in degree `n` and zero
differentials: the representing complex of clause (2) of Stacks 0FPY at
`AlgebraicGeometry.RingedSite.InvertibleDerived.oneFactorDecomposition` and the unit modules. It
is `O` in degree zero and zero elsewhere, every factor but the degree-zero one being the zero
ring. -/
abbrev oneFactorComplex : CochainComplex (Stacks.SheafOfModules.DerivedMonoidal.Mod X.O) ℤ :=
  CochainComplex.zeroDifferentialComplex fun n : ℤ =>
    ((oneFactorDecomposition X).toOMod n).obj (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf ((oneFactorDecomposition X).factor n)))

variable (X) in
/-- **The representing complex of clause (2) at the one-factor decomposition is a perfect
complex.** This is `isPerfectComplex_zeroDifferentialComplex` at the one-factor decomposition and
the unit modules, the unit module over any sheaf of commutative rings being invertible. -/
theorem isPerfectComplex_oneFactorComplex : X.IsPerfectComplex (oneFactorComplex X) :=
  isPerfectComplex_zeroDifferentialComplex (oneFactorDecomposition X) _
    fun _ => Stacks.SheafOfModules.isInvertible_unit _ _

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (Stacks.SheafOfModules.DerivedMonoidal.Mod X.O)]

omit [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
variable (X) in
/-- **Clause (2) of Stacks 0FPY has an inhabitant over every ringed site**, so
`isPerfect_of_hasInvertibleModuleDecomposition` is not vacuous. Take the one-factor
decomposition and the unit module in each degree: the unit of a sheaf of rings is invertible,
and the representing complex is then `O` in degree zero. -/
theorem exists_hasInvertibleModuleDecomposition :
    ∃ M : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.O,
      HasInvertibleModuleDecomposition X M :=
  ⟨DerivedCategory.Q.obj (oneFactorComplex X), oneFactorDecomposition X, _,
    fun _ => Stacks.SheafOfModules.isInvertible_unit _ _, ⟨Iso.refl _⟩⟩

variable (X) in
/-- **The conclusion of Stacks 0FPY is reached at a named object of `D(O)`**: the class of the
representing complex of clause (2) at the one-factor decomposition is a perfect object. -/
theorem isPerfect_oneFactorComplex :
    X.IsPerfect (DerivedCategory.Q.obj (oneFactorComplex X)) :=
  isPerfect_of_hasInvertibleModuleDecomposition _
    ⟨oneFactorDecomposition X, _, fun _ => Stacks.SheafOfModules.isInvertible_unit _ _,
      ⟨Iso.refl _⟩⟩

end Clause

end AlgebraicGeometry.RingedSite.InvertibleDerived

end
