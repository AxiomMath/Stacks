module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CountableSectionsDerivedTensorPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.QcohDualTensorPerfectQcoh
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Braiding

/-!
# The `Ext` clause of Stacks 0CRU

Let `X` be a quasi-compact absolutely quasi-separated algebraic space over a scheme `S`, let `K`
be an object of `D_QCoh(𝒪_X)` whose cohomology sheaves have countable sets of sections over the
affine schemes étale over `X`, and let `E` be a perfect object of `D(𝒪_X)`.  Then
`Ext^i_{𝒪_U}(E|_U, K|_U)` is countable for every quasi-compact absolutely quasi-separated `U`
étale over `X`.

That is the `Ext` half of [Stacks, Tag 0CRU]; the cohomology half is
`AlgebraicGeometry.Space.hasCountableCohomology_derivedTensor_restrict_of_isPerfect`.  The
statement here carries **no hypothesis beyond the tag's own**.

## What this file adds

`AlgebraicGeometry.Space.countable_ext_etaleRestrict_of_countable_sections_derivedDualTensor` is
the same conclusion stated with two *inputs* about the object `E^∨ ⊗^𝐋_{𝒪_X} K`: that its
cohomology sheaves are quasi-coherent, and that they have countable sets of sections over the
affine étale charts of `X`.  Both are theorems, and both are now available.

* Quasi-coherence is
  `AlgebraicGeometry.Space.qcohDerived_smallEtaleDerivedTensor_derivedDual_of_isPerfect`, already
  used by
  `countable_ext_etaleRestrict_of_countable_sections_derivedDualTensor_of_qcohDerived` in this
  namespace, which is the statement this file builds on.  It needs only that `K` lies in
  `D_QCoh(𝒪_X)`, which is the tag's own hypothesis on `K`.
* Countability of the sections is
  `AlgebraicGeometry.Space.countable_sections_homology_derivedTensor_of_isPerfect` — the second
  input of the cohomology half — read at the perfect factor `E^∨`, which is perfect by
  Stacks 08JJ (`AlgebraicGeometry.Space.isPerfect_smallEtaleDerivedDual`).  That statement writes
  the tensor product with the perfect factor on the **right**, as `K ⊗^𝐋 E^∨`, while Stacks 08JJ
  produces `E^∨ ⊗^𝐋 K`; the two are identified by the commutativity constraint of [Stacks,
  Tag 0FPT], `Stacks.SheafOfModules.DerivedTensorProduct.braiding`.

## Main results

Both are in the namespace `AlgebraicGeometry.Space`.

* `countable_sections_homology_derivedDualTensor_of_isPerfect`: the cohomology sheaves of
  `E^∨ ⊗^𝐋 K` have countable sets of sections over the affine étale charts of `X`.
* `countable_ext_etaleRestrict_of_countable_sections_of_isPerfect`: the `Ext` clause of
  Stacks 0CRU, with the tag's own hypotheses and nothing else.

## Implementation notes

Transporting countability of the sections across the braiding is done with
`CategoryTheory.Functor.mapIso` of the cohomology functor followed by
`SheafOfModules.evaluation` at the chart, read as a linear equivalence.  The `Countable` instance
on the source is supplied by hand rather than left to instance search: the search does not unfold
`SheafOfModules.evaluation` to the sections of the underlying presheaf, so the hypothesis in
context is not found.

## References

* [Stacks Project, Tag 0CRU](https://stacks.math.columbia.edu/tag/0CRU)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 08F5](https://stacks.math.columbia.edu/tag/08F5)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel
attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback
attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The cohomology sheaves of `E^∨ ⊗^𝐋_{𝒪_X} K` have countable sets of sections over the affine
étale charts of `X`**, for `E` perfect and `K` an object of `D_QCoh(𝒪_X)` whose own cohomology
sheaves have countable sets of sections over those charts.

`E^∨` is perfect by Stacks 08JJ
(`AlgebraicGeometry.Space.isPerfect_smallEtaleDerivedDual`), so this is the second input of the
cohomology clause of Stacks 0CRU,
`AlgebraicGeometry.Space.countable_sections_homology_derivedTensor_of_isPerfect`, read at that
perfect factor.  That statement puts the perfect factor on the right, so the two tensor factors
are exchanged by the commutativity constraint of [Stacks, Tag 0FPT],
`Stacks.SheafOfModules.DerivedTensorProduct.braiding`; its quasi-coherence input is Stacks 08F5
and 08JL (`AlgebraicGeometry.Space.qcohDerived_derivedTensor_of_isPerfect`). -/
theorem countable_sections_homology_derivedDualTensor_of_isPerfect
    (X : AlgebraicSpaces B S hS)
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hqcK : ∀ q : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) q).obj
      K).IsQuasicoherentOnSite)
    (hcountK : ∀ v : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 v → ∀ q : ℤ,
      Countable (((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) q).obj
        K).val.obj (op v)))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (v : SmallEtale B S hS X.1) (hv : IsAffineChart B S hS X.1 v) (q : ℤ) :
    Countable (((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) q).obj
      (((smallEtaleDerivedTensor B S hS X).obj
        (smallEtaleDerivedDual B S hS X E)).obj K)).val.obj (op v)) := by
  have hdual := isPerfect_smallEtaleDerivedDual B S hS X E hE
  have hqcL : ∀ q : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) q).obj
      (((smallEtaleDerivedTensorProduct B S hS X).tensor.obj K).obj
        (smallEtaleDerivedDual B S hS X E))).IsQuasicoherentOnSite :=
    qcohDerived_derivedTensor_of_isPerfect B S hS X (smallEtaleDerivedTensorProduct B S hS X)
      ⟨K, hqcK⟩ (smallEtaleDerivedDual B S hS X E) hdual
  have hc := countable_sections_homology_derivedTensor_of_isPerfect B S hS
    (smallEtaleDerivedTensorProduct B S hS X) K hqcK hcountK
    (smallEtaleDerivedDual B S hS X E) hdual hqcL v hv q
  have : Countable ((SheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
      (op v)).obj ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) q).obj
        (((smallEtaleDerivedTensorProduct B S hS X).tensor.obj K).obj
          (smallEtaleDerivedDual B S hS X E)))) := hc
  exact Countable.of_equiv _
    (((SheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
      (op v)).mapIso
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) q).mapIso
          ((smallEtaleDerivedTensorProduct B S hS X).braiding
            (smallEtaleDerivedDual B S hS X E) K))).symm.toLinearEquiv.toEquiv)

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
/-- **The `Ext` clause of [Stacks, Tag 0CRU].**  Let `X` be a quasi-compact absolutely
quasi-separated algebraic space over `S`, let `K` be an object of `D_QCoh(𝒪_X)` whose cohomology
sheaves have countable sets of sections over the affine schemes étale over `X`, and let `E` be a
perfect object of `D(𝒪_X)`.  Then `Ext^i_{𝒪_U}(E|_U, K|_U)` is countable for every quasi-compact
absolutely quasi-separated object `U` of the spaces-étale site of `X`.

Every hypothesis is the tag's own.  This is
`countable_ext_etaleRestrict_of_countable_sections_derivedDualTensor_of_qcohDerived`, in this
namespace, with its remaining input — countability of the sections of the cohomology sheaves of
`E^∨ ⊗^𝐋 K` — supplied by
`AlgebraicGeometry.Space.countable_sections_homology_derivedDualTensor_of_isPerfect`.

This is one half of the tag's covering set; the other is the `H^i(U, K ⊗^𝐋 E)` clause,
`AlgebraicGeometry.Space.hasCountableCohomology_derivedTensor_restrict_of_isPerfect`. -/
@[stacks 0CRU "the sets Ext^i(E|_U, K|_U), at the tag's own hypotheses; the H^i(U, K ⊗^𝐋 E) \
clause is `AlgebraicGeometry.Space.hasCountableCohomology_derivedTensor_restrict_of_isPerfect`"]
theorem countable_ext_etaleRestrict_of_countable_sections_of_isPerfect
    (X : AlgebraicSpaces B S hS) (hZ : B.Contains (⊤_ Scheme.{u}))
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hqcK : ∀ q : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) q).obj
      K).IsQuasicoherentOnSite)
    (hcountK : ∀ v : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 v → ∀ q : ℤ,
      Countable (((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) q).obj
        K).val.obj (op v)))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (U : SpacesEtale B S hS X) (hUqc : IsQuasiCompactSpace B S hS U.1.left.1)
    (hUqs : IsAbsolutelyQuasiSeparated B S hS hZ U.1.left.1) (i : ℤ) :
    Countable (DerivedCategory.Ext
      ((etaleModulePullback.{u, u} B S hS U.1.hom U.2).mapDerivedCategory.obj E)
      ((etaleModulePullback.{u, u} B S hS U.1.hom U.2).mapDerivedCategory.obj K) i) :=
  countable_ext_etaleRestrict_of_countable_sections_derivedDualTensor_of_qcohDerived B S hS X hZ
    K E hE hqcK
    (fun v hv q => countable_sections_homology_derivedDualTensor_of_isPerfect B S hS X K hqcK
      hcountK E hE v hv q)
    U hUqc hUqs i

end AlgebraicGeometry.Space

end
