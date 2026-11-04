module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactorTensorMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorCoherence
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObjectDual
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsUniqueFactor
import StacksCore.Tactic.StacksAttribute

/-!
# Clauses (1) and (3) of Stacks 0FPY, and clause (2) implies clause (3)

Let `(C, O)` be a ringed site and `M` an object of `D(O)`. Stacks 0FPY states the equivalence of

1. `M` is invertible in `D(O)` for the derived tensor product,
2. there is a locally finite direct product decomposition `O = ∏_{n ∈ ℤ} O_n` of the structure
   sheaf and for each `n` an invertible `O_n`-module `ℋ^n` with `M = ⨁ ℋ^n[-n]` in `D(O)`,

together with the assertion that these imply `M` perfect, and — when `(C, O)` is a locally
ringed site — the further equivalence with

3. every object `U` of `C` has a covering `{U_i → U}` and for each `i` an integer `n_i` such
   that `M|_{U_i}` is given by an invertible `O_{U_i}`-module placed in degree `n_i`.

Clause (2) is `AlgebraicGeometry.RingedSite.InvertibleDerived.HasInvertibleModuleDecomposition`
and the perfectness assertion is
`AlgebraicGeometry.RingedSite.InvertibleDerived.isPerfect_of_hasInvertibleModuleDecomposition`.
This file states clauses (1) and (3) and proves the implication `(2) ⟹ (3)` on a locally ringed
site. The whole tag is `AlgebraicGeometry.RingedSite.InvertibleDerived.isInvertibleObject_tfae`
of `StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsTFAE`.

## Main definitions

* `AlgebraicGeometry.RingedSite.InvertibleDerived.IsInvertibleObject`: clause (1).
* `AlgebraicGeometry.RingedSite.InvertibleDerived.HasLocalInvertibleDegree`: clause (3).

## Main results

* `AlgebraicGeometry.RingedSite.InvertibleDerived.exists_exactPairing_of_isInvertibleObject`:
  clause (1) exhibits a left dual of `M` in `D(O)`, which is the input of Stacks 0FPV.
* `...InvertibleDerived.ProductDecomposition.isInvertibleModuleOver_toOMod`:
  the invertibility half of clause (3) — on an object where only the `n₀`-th factor survives, an
  invertible `O_{n₀}`-module, read as an `O`-module, becomes an invertible module on the slice
  site.
* `...InvertibleDerived.ProductDecomposition.nonempty_restrictComplex_iso_single`:
  the single-degree half — there the complex `⨁ ℋ^n[-n]` becomes one module in one degree.
* `...InvertibleDerived.hasLocalInvertibleDegree_of_hasInvertibleModuleDecomposition`:
  the implication `(2) ⟹ (3)` on a locally ringed site.

The three dots abbreviate the namespace `AlgebraicGeometry.RingedSite`.

## Implementation notes

Clause (1) names the symmetric monoidal structure of Stacks 0FPT through
`Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal`, which is a `def` carrying
`@[instance_reducible]` rather than an instance, so it is introduced with `letI`; invertibility
is then the notion of Stacks 0FFN, `CategoryTheory.MonoidalCategory.IsInvertible`.

Clause (3) is read in the derived categories of the slice sites: `M|_{U_i}` is the image of `M`
under `CategoryTheory.Functor.mapDerivedCategory` of the exact restriction functor
`SheafOfModules.overFunctor`, and it is asked to be isomorphic to `L[-n_i]` there. A
representative `E` of `M` computes `M|_{U_i}` as the class of the degreewise restriction
`AlgebraicGeometry.RingedSite.restrictComplex`, which is `restrictComplexDerivedIso`.

The covering of the implication `(2) ⟹ (3)` is
`ProductDecomposition.uniqueFactorSieve_mem`: on a locally ringed site every object has a
covering on each member of which at most one factor of the decomposition is nonzero. Over such a
member every term of the complex with `ℋ^n` in degree `n` other than the surviving one is a zero
module, by `ProductDecomposition.isZero_over_toOMod`, so the complex is strictly bounded on both
sides by that degree and `CochainComplex.exists_iso_single` collapses it. The invertibility of
the surviving module is read off Tag 0B8K: it supplies a partner whose tensor product with `ℋ^n`
over `O_n` is `O_n`, the tensor product of sheaves of modules commutes with passage to a slice
site (`Stacks.TensorCoherence.tensorSheafOverIso`), and on the slice the factor module is the
structure sheaf, by `ProductDecomposition.isIso_over_factorProjection`. Restriction of scalars
along the projection `O ⟶ O_n` commutes with passage to the slice site on the nose, so no
comparison appears for it.

## References

* [Stacks Project, Tag 0FPY](https://stacks.math.columbia.edu/tag/0FPY)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 04EU](https://stacks.math.columbia.edu/tag/04EU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.DerivedMonoidal

universe u d e

namespace AlgebraicGeometry.RingedSite.InvertibleDerived

/-! ### Clause (1): invertibility in `D(O)` -/

section ClauseOne

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (Mod X.O)]

/-- **Clause (1) of Stacks 0FPY.** `M` is an invertible object of `D(O)`: there is an object `N`
of `D(O)` with `M ⊗^L N ≅ O` and `N ⊗^L M ≅ O`, the tensor product being the derived tensor
product of Stacks 0FPT and `O` the structure sheaf in degree zero. -/
@[stacks 0FPY "clause (1) as a condition on M: that M is invertible in D(O) in the sense of \
Stacks 0FFN, for the symmetric monoidal structure of Stacks 0FPT. This is the clause, not an \
implication between clauses"]
def IsInvertibleObject (M : DerivedModules X.O) : Prop :=
  letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
  MonoidalCategory.IsInvertible M

/-- **Clause (1) of Stacks 0FPY supplies the input of Stacks 0FPV.** An object of `D(O)` which
is invertible for the derived tensor product admits a left dual there: its tensor inverse is
one, with a coevaluation and an evaluation satisfying the two triangle identities.

This is the first step of the source's proof of `(1) ⟹ (2)` — "then `N` is a left dual for `M`
in the monoidal category `D(O)` and we conclude that `M` is perfect by Lemma 0FPV" — and a step
of a proof rather than a clause of the tag, so it bears no `@[stacks]` attribute. It is
`CategoryTheory.MonoidalCategory.IsInvertible.exists_exactPairing` read at the derived tensor
product. -/
theorem exists_exactPairing_of_isInvertibleObject (M : DerivedModules X.O)
    (hM : IsInvertibleObject X M) :
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
    ∃ N : DerivedModules X.O, Nonempty (CategoryTheory.ExactPairing M N) :=
  let := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
  MonoidalCategory.IsInvertible.exists_exactPairing hM

end ClauseOne

/-! ### Clause (3): one invertible module in one degree, locally -/

section ClauseThree

variable (X : RingedSite.{u, u, u})

/-- Invertibility of an `O|_V`-module in the sense of Stacks 01CS, for an object `V` of the site:
`Stacks.SheafOfModules.IsInvertible` read at the structure sheaf of the slice site over `V`. -/
abbrev IsInvertibleModuleOver (V : X.C)
    (L : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) : Prop :=
  Stacks.SheafOfModules.IsInvertible (X.O.over V).obj
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V).property L

variable [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits

variable [HasDerivedCategory.{d} (Mod X.O)]

/-- **Clause (3) of Stacks 0FPY.** Every object `U` of the site has a covering `{U_i → U}` and
for each `i` an integer `n_i` such that `M|_{U_i}` is represented by an invertible
`O_{U_i}`-module placed in degree `n_i`: there are an invertible `O_{U_i}`-module `L` and an
isomorphism `M|_{U_i} ≅ L[-n_i]` in `D(O_{U_i})`.

`M|_{U_i}` is the image of `M` under the functor `D(O) ⥤ D(O_{U_i})` induced by the exact
restriction functor `Mod(O) ⥤ Mod(O_{U_i})`, and `L[-n_i]` is `L` placed in degree `n_i`. The
derived category `D(O_{U_i})` is read in its standard model `HasDerivedCategory.standard`; any
two models are equivalent compatibly with their localization functors, so the condition does not
depend on that reading. -/
@[stacks 0FPY "clause (3) as a condition on M: that every object U of the site has a covering \
{U_i → U} and for each i an integer n_i with M|_{U_i} isomorphic in D(O_{U_i}) to an invertible \
O_{U_i}-module placed in degree n_i. This is the clause, not an implication between clauses"]
def HasLocalInvertibleDegree (M : DerivedModules X.O) : Prop :=
  ∀ U : X.C, ∃ S : Presieve U, Sieve.generate S ∈ X.J U ∧
    ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
      ∃ (n : ℤ) (L : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)),
        IsInvertibleModuleOver X V L ∧
          letI := HasDerivedCategory.standard
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V))
          Nonempty ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
              V).mapDerivedCategory.obj M ≅ (DerivedCategory.singleFunctor _ n).obj L)

/-- **A representative computes the restriction of clause (3).** If `E` represents `M`, then
for any model of `D(O_V)` the restriction `M|_V` is the class of the degreewise restriction
`E|_V`. -/
def restrictComplexDerivedIso {V : X.C}
    [HasDerivedCategory.{e}
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V))]
    {M : DerivedModules X.O} {E : Complexes X.O} (eM : DerivedCategory.Q.obj E ≅ M) :
    DerivedCategory.Q.obj (X.restrictComplex E V) ≅
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategory.obj M :=
  ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      V).mapDerivedCategoryFactors.app E).symm ≪≫
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      V).mapDerivedCategory.mapIso eM

end ClauseThree

/-! ### The two halves of clause (3) where only one factor survives -/

namespace ProductDecomposition

variable {X : RingedSite.{u, u, u}} (D : ProductDecomposition X)
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

open Stacks.SheafOfModules.RingSheafProductFactor

/-- **The invertibility half of clause (3) of Stacks 0FPY.** Let `O = ∏_n O_n` be a direct
product decomposition of the structure sheaf of a ringed site, let `V` be an object on which
every factor other than the `n₀`-th has no sections, and let `H` be an invertible
`O_{n₀}`-module. Then `H`, read as an `O`-module and taken over the slice site over `V`, is an
invertible `O|_V`-module.

Tag 0B8K gives a partner `H'` with `H ⊗_O H' ≅ O_{n₀}` as `O`-modules; the tensor product
commutes with passage to the slice site, and over `V` the factor module `O_{n₀}` is the
structure sheaf, so the module has a tensor inverse there. -/
theorem isInvertibleModuleOver_toOMod {n₀ : ℤ} {V : X.C}
    (hsub : ∀ n : ℤ, n ≠ n₀ → Subsingleton ((D.factor n).obj.obj (op V)))
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n₀)))
    (hH : Stacks.SheafOfModules.Tensor.IsInvertibleModule (D.factor n₀) H) :
    IsInvertibleModuleOver X V
      ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).obj
        ((D.toOMod n₀).obj H)) := by
  obtain ⟨H', ⟨e⟩⟩ :=
    exists_tensorObj_iso_factorModule_of_isInvertibleModule D.presentation n₀ H hH
  have := D.isIso_over_factorProjection (n₀ := n₀) hsub
  refine (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit _).mpr
    ⟨(SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).obj
      ((D.toOMod n₀).obj H'), ⟨?_⟩⟩
  refine Stacks.TensorCoherence.tensorSheafOverIso ((D.toOMod n₀).obj H)
      ((D.toOMod n₀).obj H') V ≪≫ ?_
  refine (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapIso e ≪≫ ?_
  exact (asIso ((factorProjection D.presentation n₀).over V)).symm

/-- **The single-degree half of clause (3) of Stacks 0FPY.** Over an object on which every factor
other than the `n₀`-th has no sections, the complex carrying `ℋ^n` in degree `n` with zero
differentials — the complex representing `⨁ ℋ^n[-n]` — becomes the single complex with the
`n₀`-th module in degree `n₀`: every other term is a zero module, so the complex is strictly
bounded on both sides by `n₀`. -/
theorem nonempty_restrictComplex_iso_single {n₀ : ℤ} {V : X.C}
    (H : ∀ n : ℤ, SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (hsub : ∀ n : ℤ, n ≠ n₀ → Subsingleton ((D.factor n).obj.obj (op V))) :
    Nonempty (X.restrictComplex (CochainComplex.zeroDifferentialComplex
        fun m => (D.toOMod m).obj (H m)) V ≅
      (CochainComplex.singleFunctor
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) n₀).obj
        ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).obj
          ((D.toOMod n₀).obj (H n₀)))) := by
  set K := X.restrictComplex (CochainComplex.zeroDifferentialComplex
    fun m => (D.toOMod m).obj (H m)) V with hK
  have hzero : ∀ i : ℤ, i ≠ n₀ → IsZero (K.X i) := fun i hi =>
    D.isZero_over_toOMod i (H i) (hsub i hi)
  have : CochainComplex.IsStrictlyGE K n₀ :=
    (CochainComplex.isStrictlyGE_iff K n₀).mpr fun i hi => hzero i (by omega)
  have : CochainComplex.IsStrictlyLE K n₀ :=
    (CochainComplex.isStrictlyLE_iff K n₀).mpr fun i hi => hzero i (by omega)
  obtain ⟨L, ⟨e⟩⟩ := CochainComplex.exists_iso_single K n₀
  refine ⟨e ≪≫ (CochainComplex.singleFunctor _ n₀).mapIso ?_⟩
  exact (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n₀ L).symm ≪≫
    (HomologicalComplex.eval _ _ n₀).mapIso e.symm

end ProductDecomposition

/-! ### Clause (2) implies clause (3) -/

section Implication

variable {X : RingedSite.{u, u, u}}
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (Mod X.O)]

attribute [local instance] Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits

/-- **The implication `(2) ⟹ (3)` of Stacks 0FPY.** Let `(C, O)` be a locally ringed site and let
`M` be an object of `D(O)` admitting a locally finite invertible module decomposition — clause
(2): a locally finite direct product decomposition `O = ∏_{n ∈ ℤ} O_n`, invertible `O_n`-modules
`ℋ^n`, and `M = ⨁ ℋ^n[-n]`. Then `M` satisfies clause (3): over each member of a covering of
every object of the site it is given by an invertible module placed in a single degree.

The complex is the one with `ℋ^n` in degree `n` and zero differentials, which represents
`⨁ ℋ^n[-n]`; the covering is `ProductDecomposition.uniqueFactorSieve_mem`, on whose members only
one factor survives, so that the complex there is a single module
(`ProductDecomposition.nonempty_restrictComplex_iso_single`) and that module is invertible
(`ProductDecomposition.isInvertibleModuleOver_toOMod`). -/
theorem hasLocalInvertibleDegree_of_hasInvertibleModuleDecomposition
    (M : DerivedModules X.O) (hM : HasInvertibleModuleDecomposition X M)
    (hX : AlgebraicGeometry.RingedSite.IsLocallyRinged X) :
    HasLocalInvertibleDegree X M := by
  obtain ⟨D, H, hinv, ⟨eM⟩⟩ := hM
  refine fun U => ⟨(D.uniqueFactorSieve U).arrows, ?_, fun {V} f hf => ?_⟩
  · rw [Sieve.generate_sieve]
    exact D.uniqueFactorSieve_mem hX U
  · obtain ⟨n₀, hsub⟩ := hf
    refine ⟨n₀,
      (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).obj
        ((D.toOMod n₀).obj (H n₀)),
      D.isInvertibleModuleOver_toOMod hsub (H n₀) (hinv n₀), ?_⟩
    let := HasDerivedCategory.standard
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V))
    obtain ⟨e⟩ := D.nonempty_restrictComplex_iso_single H hsub
    exact ⟨(restrictComplexDerivedIso X eM.symm).symm ≪≫ DerivedCategory.Q.mapIso e ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) n₀).app
          ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).obj
            ((D.toOMod n₀).obj (H n₀)))).symm⟩

end Implication

end AlgebraicGeometry.RingedSite.InvertibleDerived

end
