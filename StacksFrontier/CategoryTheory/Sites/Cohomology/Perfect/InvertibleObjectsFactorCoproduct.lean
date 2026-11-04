module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactorLimit
public import StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.Coproduct
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjects
public import StacksFrontier.Homology.DerivedCategory.ZeroDifferentialCoproduct
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The coproduct of the factors of a product decomposition is the structure sheaf

Let `(C, O)` be a ringed site with a locally finite direct product decomposition
`O = ∏_{n ∈ ℤ} O_n` of its structure sheaf
(`AlgebraicGeometry.RingedSite.InvertibleDerived.ProductDecomposition`).  Then the canonical
morphism `∐_n O_n ⟶ ∏_n O_n` of `O`-modules is an isomorphism, and the product is the structure
sheaf itself, so that `∐_n O_n ≅ O`.

That identification is one of the three obligations of the implication `(2) ⟹ (1)` of Stacks
0FPY: the assembly ends at `⨁_n O_n`, and the monoidal unit of `D(O)` is `O` in degree zero.

## Main results

* `...ProductDecomposition.coversTop_finiteSupport`: the objects of the site over which only
  finitely many factors are nonzero cover the site.
* `...ProductDecomposition.isIso_sigmaPiComparison_toOMod_unit`: `∐_n O_n ⟶ ∏_n O_n` is an
  isomorphism.

## Main definitions

* `...ProductDecomposition.sigmaIsoPiToOModUnit`: the isomorphism `∐_n O_n ≅ ∏_n O_n` it gives.
* `...ProductDecomposition.piIsoUnit`: `∏_n O_n ≅ O`, with `piIsoUnit_inv_comp_π` identifying it
  by its composites with the product projections.
* `...ProductDecomposition.sigmaIsoUnit`: the composite `∐_n O_n ≅ O`.

The three dots abbreviate the namespace `AlgebraicGeometry.RingedSite.InvertibleDerived`.

## Implementation notes

Being an isomorphism is local on the site
(`Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over`), so the comparison may be
checked over the members of a family of objects covering the site, and local finiteness supplies
one: the objects over which all but finitely many factors have no sections.  That family covers
the site because the sieve it generates at an object contains
`ProductDecomposition.finiteSupportSieve`, each of whose members is itself such an object, so no
refinement step is needed; `CategoryTheory.GrothendieckTopology.CoversTop` asks exactly for the
`Sieve.ofObjects` of the family to be a covering sieve of every object.  Over such an object all
but finitely many of the restricted modules are zero objects, and for a family finite modulo zero
objects the comparison from the coproduct to the product is invertible
(`CategoryTheory.Limits.isIso_sigmaPiComparison_of_isZero`), restriction to a slice carrying the
comparison to the comparison (`CategoryTheory.Limits.isIso_map_sigmaPiComparison`).

The second half, `piIsoUnit`, uses none of that: a product presentation presents every section of
`O` uniquely by its components, which is the universal property of the product, so `O` is
exhibited as a limit fan of the factors and no comparison with the categorical product has to be
computed.  That argument is already generic over a site and lives in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactorLimit`; the ringed-space
statement `Stacks.Cohomology.InvertibleDerived.ProductDecomposition.piIsoUnit` is the same
generic theorem read at the site of opens.

Passing the product presentation to the generic results **by name** rather than leaving it to
unification is not optional: with `_` in its place the ringed-space analogue of
`piIsoUnit_inv_comp_π` exhausts the heartbeat budget in a single `isDefEq`.

Nothing here is a clause of Stacks 0FPY; everything is a step of the proof of its implication
`(2) ⟹ (1)`, so no declaration carries the project tag.

## References

* [Stacks Project, Tag 0FPY](https://stacks.math.columbia.edu/tag/0FPY) — the implication
  `(2) ⟹ (1)`, whose assembly consumes this identification.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.RingedSite.InvertibleDerived.ProductDecomposition

variable {X : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Restriction of `O`-modules to a slice site preserves colimits**, pinned as an instance for
every object of the site.  This is `Stacks.SheafOfModules.overFunctor_preservesColimits`, the
left adjointness of the pushforward along `CategoryTheory.Over.forget`; the instance
`Stacks.SheafOfModules.FiniteTypeKernel.preservesColimitsOverFunctor` is not usable here, since
it assumes the site has binary products, which a general site has not.  With it in force the
small-shape limit preservation `Stacks.SheafOfModules.FiniteTypeKernel.preservesLimitOverFunctor`
is available too, and those two are what carry the comparison morphism to a slice. -/
@[sga "4 IV 11.2.2" "partial"]
local instance preservesColimitsOfSize_overFunctor (V : X.C) :
    PreservesColimitsOfSize.{u, u}
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V) :=
  Stacks.SheafOfModules.overFunctor_preservesColimits.{u, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V

/-- The same at the index type `ℤ`, which does not lie in the site's universe: the shape has to
be shrunk along `Discrete.equivalence Equiv.ulift`, exactly as it does for the derived tensor
product in
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSigmaDistribution`. -/
local instance preservesColimitsOfShapeInt_overFunctor (V : X.C) :
    PreservesColimitsOfShape (Discrete ℤ)
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V) :=
  preservesColimitsOfShape_discrete_shrink.{u} _ _

/-- The objects of the site over which only finitely many factors of the decomposition have
nonzero sections, as a family indexed by itself. -/
def finiteSupportObject (D : ProductDecomposition X) : Type u :=
  {V : X.C // {n : ℤ | ¬ Subsingleton ((D.factor n).obj.obj (op V))}.Finite}

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The objects over which only finitely many factors survive cover the site.**  The sieve
`Sieve.ofObjects` of the family contains `ProductDecomposition.finiteSupportSieve` at every
object, because an arrow of that sieve has such an object as its source and so factors through a
member of the family by the identity; and that sieve is a covering sieve by local finiteness. -/
theorem coversTop_finiteSupport (D : ProductDecomposition X) :
    X.J.CoversTop (fun V : D.finiteSupportObject => V.1) := by
  intro U
  refine X.J.superset_covering ?_ (D.finiteSupportSieve_mem U)
  exact fun W g hg => ⟨⟨W, hg⟩, ⟨𝟙 W⟩⟩

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The coproduct of the factors of a locally finite product decomposition is their product.**

Being an isomorphism is local on the site, and over an object on which all but finitely many of
the factors have no sections all but finitely many of the restricted modules are zero objects,
for which the comparison from the coproduct to the product is invertible.

A step of the proof of the implication `(2) ⟹ (1)` of Stacks 0FPY, not a clause of the tag, so it
carries no `@[stacks]` attribute. -/
theorem isIso_sigmaPiComparison_toOMod_unit (D : ProductDecomposition X)
    [HasCoproduct fun n : ℤ => (D.toOMod n).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))] :
    IsIso (sigmaPiComparison fun n : ℤ => (D.toOMod n).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))) := by
  classical
  have := Stacks.SheafOfModules.RingSheafProductFactor.hasProduct_factorModule D.presentation
  refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over
    D.coversTop_finiteSupport _ fun V => ?_
  have hz : ∀ n : ℤ, ¬ (¬ Subsingleton ((D.factor n).obj.obj (op V.1))) →
      IsZero ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V.1).obj
        ((D.toOMod n).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))))) :=
    fun n hn => D.isZero_over_toOMod n _ (not_not.mp hn)
  let : Finite {n : ℤ // ¬ Subsingleton ((D.factor n).obj.obj (op V.1))} := V.2.to_subtype
  exact isIso_map_sigmaPiComparison _ _
    (isIso_sigmaPiComparison_of_isZero _
      (fun n : ℤ => ¬ Subsingleton ((D.factor n).obj.obj (op V.1))) hz)

/-- The identification `∐_n O_n ≅ ∏_n O_n` of `isIso_sigmaPiComparison_toOMod_unit`. -/
def sigmaIsoPiToOModUnit (D : ProductDecomposition X)
    [HasCoproduct fun n : ℤ => (D.toOMod n).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))] :
    letI := Stacks.SheafOfModules.RingSheafProductFactor.hasProduct_factorModule D.presentation
    (∐ fun n : ℤ => (D.toOMod n).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))) ≅
      ∏ᶜ fun n : ℤ => (D.toOMod n).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))) :=
  letI := Stacks.SheafOfModules.RingSheafProductFactor.hasProduct_factorModule D.presentation
  have := D.isIso_sigmaPiComparison_toOMod_unit
  asIso (sigmaPiComparison _)

/-- **The product of the factors of a product decomposition is the structure sheaf**:
`∏_n O_n ≅ O` as `O`-modules.

This is `Stacks.SheafOfModules.RingSheafProductFactor.piIsoUnit` at the decomposition's own
presentation: the presentation exhibits `O`, with the projections onto the factors, as a limit
fan of the family of factors, so it *is* their product. -/
def piIsoUnit (D : ProductDecomposition X) :
    letI := Stacks.SheafOfModules.RingSheafProductFactor.hasProduct_factorModule D.presentation
    (∏ᶜ fun n : ℤ => (D.toOMod n).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  Stacks.SheafOfModules.RingSheafProductFactor.piIsoUnit D.presentation

/-- **The coproduct of the factors of a product decomposition is the structure sheaf**:
`∐_n O_n ≅ O` as `O`-modules, the composite of `sigmaIsoPiToOModUnit` with `piIsoUnit`.

A step of the proof of an implication of Stacks 0FPY, not a clause of it, so it carries no
`@[stacks]` attribute. -/
def sigmaIsoUnit (D : ProductDecomposition X)
    [HasCoproduct fun n : ℤ => (D.toOMod n).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))] :
    (∐ fun n : ℤ => (D.toOMod n).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  letI := Stacks.SheafOfModules.RingSheafProductFactor.hasProduct_factorModule D.presentation
  D.sigmaIsoPiToOModUnit ≪≫ D.piIsoUnit

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The identification `∏_n O_n ≅ O` is the one carrying the `n`-th product projection to the
projection `O ⟶ O_n` of the decomposition.  This pins it down: it is not merely an abstract
isomorphism between the two objects. -/
theorem piIsoUnit_inv_comp_π (D : ProductDecomposition X) (n : ℤ) :
    letI := Stacks.SheafOfModules.RingSheafProductFactor.hasProduct_factorModule D.presentation
    D.piIsoUnit.inv ≫ Pi.π (fun n : ℤ => (D.toOMod n).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))) n =
      Stacks.SheafOfModules.RingSheafProductFactor.factorProjection D.presentation n :=
  Stacks.SheafOfModules.RingSheafProductFactor.piIsoUnit_inv_comp_π D.presentation n

end AlgebraicGeometry.RingedSite.InvertibleDerived.ProductDecomposition

end
