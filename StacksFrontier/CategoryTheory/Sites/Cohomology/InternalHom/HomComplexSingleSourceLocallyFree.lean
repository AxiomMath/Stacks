module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDual
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexSingleSource
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# The derived internal Hom out of a finite locally free sheaf of modules

Let `(C, O)` be a ringed site and let `A` be a finite locally free sheaf of `O`-modules. Then `A`
is locally a direct summand of a finite free module — locally it *is* a finite free module — so
by [Stacks, Tag 08JH] in the local form
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_isIso_of_isLocallyFiniteFreeSummand`
the derived internal Hom out of `A` placed in degree zero is computed by the internal Hom complex,
which for a target `B` placed in degree zero collapses to `SheafHom(A, B)` placed in degree zero:

`RSheafHom(A[0], B[0]) ≅ SheafHom(A, B)[0]`.

At `B = O` this says **the derived dual of a finite locally free sheaf of modules is its
underived dual** `A^∨ = SheafHom(A, O)`, in degree zero.

## Main results

* `AlgebraicGeometry.RingedSite.isLocallyFiniteFreeSummand_of_isFiniteLocallyFree`: a finite
  locally free sheaf of modules is locally a direct summand of a finite free one.
* `AlgebraicGeometry.RingedSite.derivedSheafHomSingleIsoOfIsFiniteLocallyFree`:
  `RSheafHom(A[0], B[0]) ≅ SheafHom(A, B)[0]` for `A` finite locally free.
* `AlgebraicGeometry.RingedSite.derivedDualSingleIsoOfIsFiniteLocallyFree`: the derived dual of
  `A[0]` is `A^∨[0]`.

## References

* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u d

namespace AlgebraicGeometry.RingedSite

-- The two slice spellings of sheaves of modules over the site over `V`, indexed by
-- `(X.over V).ringSheaf` and by `X.ringSheaf.over V`, agree; these attributes let the
-- elaborator see it.
attribute [local implicit_reducible]
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  SheafOfModules.pushforward
  SheafOfModules.overFunctor

variable (X : RingedSite.{u, u, u})
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasWeakSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasWeakSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- A finite locally free sheaf of modules is locally a direct summand of a finite free
module. -/
theorem isLocallyFiniteFreeSummand_of_isFiniteLocallyFree
    (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [hA : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} A] :
    IsLocallyFiniteFreeSummand X A := by
  obtain ⟨q, hfree, hfin⟩ := hA.exists_isFiniteLocallyFreeData
  refine ⟨q.I, q.X, q.coversTop, fun i => ?_⟩
  have : IsIso (q.generators i).π := hfree.isIso i
  have : Finite (q.generators i).I := (hfin.isFiniteType i).finite
  let e := asIso (q.generators i).π
  exact isFiniteFreeSummand_of_retract_free (X.over (q.X i)) (q.generators i).I
    ⟨e.inv, e.hom, e.inv_hom_id⟩

variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  (D : DerivedInternalHom.{u, d} X)

/-- The derived internal Hom out of a finite locally free sheaf of modules is the underived
one: for `A` finite locally free and any `B`, `RSheafHom(A[0], B[0]) ≅ SheafHom(A, B)[0]` in
`D(Mod(O))`. -/
def derivedSheafHomSingleIsoOfIsFiniteLocallyFree
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} A] :
    (D.hom.obj (op (DerivedCategory.Q.obj (sgl X A)))).obj (DerivedCategory.Q.obj (sgl X B)) ≅
      DerivedCategory.Q.obj (sgl X (internalHomSheaf X A B)) :=
  (@asIso _ _ _ _ (strictlyPerfectHomComparison X D (sgl X A) (sgl X B))
      (strictlyPerfectHomComparison_isIso_of_isLocallyFiniteFreeSummand X D 0
        (isLocallyFiniteFreeSummand_of_isFiniteLocallyFree X A) (sgl X B))).symm ≪≫
    DerivedCategory.Q.mapIso (sheafHomComplexSingleIso X A B)

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasWeakSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The derived dual of a finite locally free sheaf of modules is its underived dual, in degree
zero: `(A[0])^∨ = RSheafHom(A[0], O) ≅ SheafHom(A, O)[0]`. -/
def derivedDualSingleIsoOfIsFiniteLocallyFree
    (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} A] :
    derivedDual X (DerivedCategory.Q.obj (sgl X A)) ≅
      DerivedCategory.Q.obj (sgl X (internalHomSheaf X A
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :=
  derivedSheafHomSingleIsoOfIsFiniteLocallyFree X (derivedInternalHomOfBifunctor X) A
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

end AlgebraicGeometry.RingedSite
