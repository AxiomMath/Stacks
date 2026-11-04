module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SheafInternalHomFirstVariable
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDual
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.MonoidalClosedComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LocalModels
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.ConeOfAMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexIntoASingleComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexOfAStrictlyPerfectComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomFiniteFree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
public import StacksFrontier.CategoryTheory.Limits.CoproductSingleSupport
import StacksCore.Tactic.StacksAttribute

/-!
# Duals of perfect objects on a ringed site

Let `(C, O)` be a ringed site. The **dual** of an object `K` of `D(O)` is
`K^∨ = RSheafHom(K, O)`, the derived internal Hom into the structure sheaf placed in degree
zero (`AlgebraicGeometry.RingedSite.derivedDual`, Stacks 08JD). This file proves the first
assertion of **Stacks 08JJ**: if `K` is perfect then so is `K^∨`.

The argument is the one of the source. Perfectness is local, so it suffices to produce a
strictly perfect model of `K^∨` above a covering of each object of the site; over a member `V`
of a covering on which `K` is modelled by a strictly perfect complex `E` of `O|_V`-modules, the
dual is modelled by the internal Hom complex `SheafHom(E, O|_V)`, whose degree-`n` term is the
dual `Hom(E^{-n}, O|_V)` of a direct summand of a finite free module and hence again a direct
summand of a finite free module.

## Main results

* `AlgebraicGeometry.RingedSite.isDirectSummandOfFiniteFree_internalHomSheaf_unit`: the dual
  `Hom_O(M, O)` of a direct summand of a finite free `O`-module is again one.
* `AlgebraicGeometry.RingedSite.isStrictlyPerfect_sheafHomComplex_structureSheaf`: the internal
  Hom complex `SheafHom(E, O[0])` of a strictly perfect complex is strictly perfect.
* `AlgebraicGeometry.RingedSite.restrictStructureSheafComplexIso`: the restriction of the
  structure sheaf complex to a slice is the structure sheaf complex of the slice.
* `AlgebraicGeometry.RingedSite.isPerfect_derivedDual`: **Stacks 08JJ**, the dual of a perfect
  object of `D(O)` is perfect.

## Implementation notes

The degreewise description of the internal Hom complex is Stacks 08JH,
`AlgebraicGeometry.RingedSite.strictlyPerfectHomDegreeIso`: the `n`-th term of `SheafHom(E, F)`
is `∐_q Hom(E^{-q}, F^{n-q})`. For `F = O[0]` every target `F^{n-q}` with `q ≠ n` vanishes, so
the coproduct collapses to the single summand `Hom(E^{-n}, O)`; both boundedness and the
termwise condition are then read off from `E` at the index `-n`.

The dual of a finite free module is computed through the monoidal closed structure on sheaves
of modules rather than through the explicit internal Hom presheaf: `Hom_O(-, O)` is
`MonoidalClosed.internalHom` in its first variable at the unit, which turns the coproduct
`O^{⊕n}` into the product of the duals, and
`AlgebraicGeometry.RingedSite.ihomIsoInternalHomSheaf` identifies that with the internal Hom
sheaf of Stacks 03EM. A direct summand is a retract, so applying a contravariant functor to a
retract of `O^{⊕n}` suffices.

The identification of the dual with its local model uses Stacks 08JB for the restriction of a
derived internal Hom to a slice (`AlgebraicGeometry.RingedSite.derivedHomRestriction`) and
Stacks 08JH for the comparison of the derived internal Hom out of a strictly perfect complex
with the ordinary internal Hom complex
(`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison`), taken at the derived internal
Hom datum carried by the bifunctor `RSheafHom(-, -)` itself,
`AlgebraicGeometry.RingedSite.derivedInternalHomOfBifunctor`.

The universes are the diagonal `RingedSite.{u, u, u}`, free in `u`. The diagonal itself is
forced by the two clusters the proof joins, and is not a narrowing introduced here. The derived
internal Hom cluster — `AlgebraicGeometry.RingedSite.derivedDual` and Stacks 08JA, 08JB, 08JD,
08JH — is stated at `RingedSite.{u, u, u}` with modules in `SheafOfModules.{u}`, because
`AlgebraicGeometry.RingedSite.internalHomSheaf` lands in `SheafOfModules.{max u v m}` and so
forces `max u v m = m`; and the perfectness cluster —
`isPerfect_of_forall_coveringFamily_strictlyPerfect` and everything under it, down to
Stacks 08FR in
`StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocalRepresentationOfADerivedMap`
— is stated at `RingedSite.{u, u, w}` with modules in `SheafOfModules.{w}`, the module universe
being tied to the ring universe by strict perfectness and the morphism universe to the object
universe by Stacks 08FR. Taking `w = u` joins them.

Nothing in the argument forces the universe *value* `0`, and the neighbouring
`RingedSite.{0, 0, 0}` statements of this chapter (Stacks 08G8 in
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessCriterion`, Stacks 08GA in
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DirectSummands`) are pinned by their own
inputs, not by anything here.

## What this file does not contain

Stacks 08JJ has four assertions; only the first is proved here. Of the other three:

* `(K^∨)^∨ ≅ K` for `K` perfect **is** in the library, elsewhere. The canonical map
  `K ⟶ (K^∨)^∨` is `AlgebraicGeometry.RingedSite.derivedBidual` in
  `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedBidual`, and
  `AlgebraicGeometry.RingedSite.isIso_derivedBidual_of_isPerfect` in
  `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationPerfect` asserts that it is
  an isomorphism, with perfectness of `K` its only hypothesis.
* the isomorphism `M ⊗^L_O K^∨ ≅ RSheafHom_O(K, M)`, functorial in `M`, **is** in the library,
  as `AlgebraicGeometry.RingedSite.derivedDualTensorSheafHomIso` with
  `derivedDualTensorSheafHomIso_naturality`, in
  `StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualTensorSheafHom`. It is obtained not
  from the canonical map of Stacks 08JD but from the diagonal of Stacks 0BYS at target object
  the structure sheaf, which Stacks 0ATN makes invertible at a perfect internal-Hom source, and
  the right unit constraint of Stacks 0FPT. That the *canonical* map
  `AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom` (Stacks 08JD) is an isomorphism
  for perfect `K` is `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_isPerfect`
  of `StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCompositionPerfect`, for an
  arbitrary derived tensor product datum, for arbitrary `M`, and with perfectness of `K` as the
  only hypothesis. Its proof replaces invertibility of the derived morphism by quasi-isomorphy
  of a morphism of *complexes* at one choice of models
  (`AlgebraicGeometry.RingedSite.isIso_derivedSheafHomComposition_of_coversTop`), which is local
  on the site, so the condition may be checked over the members of the covering that
  perfectness supplies.
* the identification `H⁰(C, M ⊗^L_O K^∨) = Hom_{D(O)}(K, M)` **is** in the library too, as
  `AlgebraicGeometry.RingedSite.derivedDualTensorGlobalSectionsEquiv` in
  `StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualTensorSheafHom`: the degree-zero
  global hypercohomology of the previous item, followed by Stacks 08JA
  (`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv`). On a ringed space the
  bijectivity of the canonical map
  `AlgebraicGeometry.RingedSite.derivedTensorDualGlobalSectionsMap` (Stacks 08JD) is
  `Stacks.SheafOfModules.bijective_derivedTensorDualGlobalSectionsMap_of_isPerfect` of
  `StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualGlobalSections`.

## References

* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08G6](https://stacks.math.columbia.edu/tag/08G6)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.RingedSite

section DualModule

variable (X : RingedSite.{u, u, u})
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] _root_.SheafOfModules.monoidalCategory
  _root_.SheafOfModules.symmetricCategory SheafOfModules.monoidalClosed

/-- The dual `Hom_O(-, O)` of sheaves of `O`-modules on a ringed site, as a contravariant
functor: the internal hom of the monoidal closed structure, in its first variable, evaluated
at the structure sheaf. -/
@[sga "3 I 4.6.5.1" "more general"]
private def unitDualFunctor :
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))ᵒᵖ ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  MonoidalClosed.internalHom.flip.obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **The dual of a finite free module is finite free of the same rank.** The dual of a
coproduct is the product of the duals, the dual of `O` is `O`, and a finite product of copies
of `O` is the coproduct of those copies, i.e. `O^{⊕n}` again. -/
private def unitDualFreeIso (n : ℕ) :
    (unitDualFunctor X).obj
        (op (SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ULift.{u} (Fin n)))) ≅
      SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ULift.{u} (Fin n)) :=
  letI : HasFiniteBiproducts (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  Stacks.SheafOfModules.InternalHom.ihomFreeIsoProduct X.O _ _ ≪≫ biproductIso _

/-- The monoidal-closed dual of `M` is Stacks 03EM's internal Hom sheaf `Hom_O(M, O)`: both
are right adjoint to tensoring by `M`, evaluated at the structure sheaf. -/
private def unitDualIsoInternalHomSheaf
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (unitDualFunctor X).obj (op M) ≅
      internalHomSheaf X M (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  ihomIsoInternalHomSheaf X M _

/-- **The dual of a direct summand of a finite free module is again one.** If `M` is a retract
of `O^{⊕n}`, applying the contravariant functor `Hom_O(-, O)` makes `Hom_O(M, O)` a retract of
`Hom_O(O^{⊕n}, O) ≅ O^{⊕n}`. -/
theorem isDirectSummandOfFiniteFree_internalHomSheaf_unit
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hM : _root_.IsDirectSummandOfFiniteFree (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M) :
    _root_.IsDirectSummandOfFiniteFree (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (internalHomSheaf X M
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) := by
  refine _root_.IsDirectSummandOfFiniteFree.of_iso (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (unitDualIsoInternalHomSheaf X M).symm ?_
  rw [isDirectSummandOfFiniteFree_iff_free] at hM ⊢
  obtain ⟨n, i, r, hir⟩ := hM
  refine ⟨n, (unitDualFunctor X).map r.op ≫ (unitDualFreeIso X n).hom,
    (unitDualFreeIso X n).inv ≫ (unitDualFunctor X).map i.op, ?_⟩
  rw [Category.assoc, Iso.hom_inv_id_assoc, ← CategoryTheory.Functor.map_comp, ← op_comp, hir,
    op_id, CategoryTheory.Functor.map_id]

end DualModule

section DualComplex

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The dual of a strictly perfect complex is strictly perfect.** The internal Hom complex
`SheafHom(E, O[0])` of a strictly perfect complex `E` of `O`-modules into the structure sheaf
placed in degree zero is again strictly perfect. -/
theorem isStrictlyPerfect_sheafHomComplex_structureSheaf
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hE : _root_.IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) E) :
    _root_.IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (sheafHomComplex X E (structureSheafComplex X)).obj where
  bounded := sheafHomComplex_structureSheaf_bounded X E hE.bounded
  termDirectSummand n :=
    _root_.IsDirectSummandOfFiniteFree.of_iso (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (homStructureSheafDegreeIso X E hE.bounded n)
      (isDirectSummandOfFiniteFree_internalHomSheaf_unit X (E.X (-n))
        (hE.termDirectSummand (-n)))

end DualComplex

section Perfect

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restriction to a slice of the site preserves finite limits, at a free universe of the
sections. -/
local instance dualsPreservesFiniteLimitsOverFunctor (V : X.C) :
    PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits V

/-- Restriction to a slice of the site preserves finite colimits, at a free universe of the
sections. -/
local instance dualsPreservesFiniteColimitsOverFunctor (V : X.C) :
    PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits V

/-- The restriction of the structure sheaf complex to the slice over `V` is the structure sheaf
complex of the slice: restriction is additive and carries the structure sheaf to the structure
sheaf, so it commutes with placing a module in degree zero. -/
def restrictStructureSheafComplexIso (V : X.C) :
    X.restrictComplex (structureSheafComplex X) V ≅ structureSheafComplex (X.over V) :=
  (HomologicalComplex.singleMapHomologicalComplex
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V)
    (ComplexShape.up ℤ) 0).app _

/-- **Stacks 08JJ, first assertion.** Let `(C, O)` be a ringed site and let `K` be a perfect
object of `D(O)`. Then the dual `K^∨ = RSheafHom(K, O)` is perfect as well.

Perfectness is local, so it is enough to model `K^∨` above a covering of each object of the
site. Over a member `V` on which `K` is modelled by a strictly perfect complex `E`, the
restriction of `K^∨` is `RSheafHom(K|_V, O|_V)` by Stacks 08JB, which is the class of the
internal Hom complex `SheafHom(E, O|_V)` by Stacks 08JH; and that complex is strictly perfect
because the dual of a direct summand of a finite free module is again one. -/
@[stacks 08JJ "the dual of a perfect object is perfect",
  sga "6 I 7.3" "perfect ⇒ dual perfect",
  sga "6 III 4.9" "Case S = X = Y"]
theorem isPerfect_derivedDual
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K) : X.IsPerfect (derivedDual X K) := by
  obtain ⟨E, hE, ⟨eE⟩⟩ := hK
  apply isPerfect_of_forall_coveringFamily_strictlyPerfect
  intro U
  obtain ⟨S, hS, hmod⟩ := hE U
  refine ⟨S, hS, ?_⟩
  intro V f hf
  obtain ⟨P, hP, q, hq⟩ := hmod f hf
  refine ⟨(sheafHomComplex (X.over V) P (structureSheafComplex (X.over V))).obj,
    isStrictlyPerfect_sheafHomComplex_structureSheaf (X.over V) P hP, ⟨?_⟩⟩
  have : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 hq
  -- the restriction of `K` to the slice over `V` is the class of the local model `P`
  let a : (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategory.obj K ≅
      DerivedCategory.Q.obj P :=
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategory.mapIso eE.symm ≪≫
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategoryFactors.app E ≪≫
      (asIso (DerivedCategory.Q.map q)).symm
  -- the restriction of the structure sheaf is the structure sheaf of the slice
  let b : (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategory.obj (derivedStructureSheaf X) ≅ derivedStructureSheaf (X.over V) :=
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategoryFactors.app (structureSheafComplex X) ≪≫
      DerivedCategory.Q.mapIso (restrictStructureSheafComplexIso X V)
  let cmp := strictlyPerfectHomComparison (X.over V)
    (derivedInternalHomOfBifunctor (X.over V)) P (structureSheafComplex (X.over V))
  have hcmp : IsIso cmp :=
    strictlyPerfectHomComparison_isIso_of_isStrictlyPerfect (X.over V)
      (derivedInternalHomOfBifunctor (X.over V)) P (structureSheafComplex (X.over V)) hP
  exact @asIso _ _ _ _ cmp hcmp ≪≫
    ((derivedSheafHomBifunctor (X.over V)).mapIso a.op).app _ ≪≫
    ((derivedSheafHomBifunctor (X.over V)).obj
        (op ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          V).mapDerivedCategory.obj K))).mapIso b.symm ≪≫
    ((derivedHomRestriction X V).iso K (derivedStructureSheaf X)).symm

end Perfect

end AlgebraicGeometry.RingedSite

end
