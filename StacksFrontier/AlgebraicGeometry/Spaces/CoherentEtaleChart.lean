module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Coherence
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart

/-!
# Coherence on an algebraic space from its étale charts

Stacks 07UB characterizes the coherent `𝒪_X`-modules on a locally Noetherian algebraic space
`X` by five equivalent conditions, two of which test coherence on étale scheme charts: its
condition (4) asks that the pullback to *every* étale chart be coherent, and its condition (5)
that the pullback to *one* surjective étale chart be coherent.  This file proves the
**local-to-global half** of both, that is the implications (4) ⇒ (1) and (5) ⇒ (1), with the
restriction to a chart read as restriction to the slice of the small étale site at that chart.

The mathematical content is entirely in the covering facts already in the tree — a surjective
étale chart covers the final object of the small étale site, and so do the affine étale charts
— applied to the clause of Stacks 03DN for coherence,
`Stacks.SheafOfModules.isCoherentOnSite_iff_exists_cover_isCoherentOnSite`.  This is the exact
analogue for coherence of what
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart` proves for quasi-coherence, and
the quasi-coherence clause of each statement below is supplied by that file.

## Main results

* `AlgebraicGeometry.Space.isCoherentOnSite_of_over_of_isSurjective`: coherence on the small
  étale ringed site follows from coherence of the restriction to one surjective étale chart.
* `AlgebraicGeometry.Space.isCoherentOnSite_of_forall_over` and
  `AlgebraicGeometry.Space.isCoherentOnSite_of_forall_affine_over`: the same from coherence of
  the restriction to every étale chart, respectively to every affine étale chart.
* `AlgebraicGeometry.Space.isCoherent_of_over_of_isSurjective`,
  `AlgebraicGeometry.Space.isCoherent_of_forall_over` and
  `AlgebraicGeometry.Space.isCoherent_of_forall_affine_over`: the corresponding conclusions for
  `AlgebraicGeometry.Space.IsCoherent`, obtained by pairing each of the above with the
  quasi-coherence equivalence of Stacks 03M0 at the same charts.

## Implementation notes

**No statement here carries `@[stacks 07UB]`, for two independent reasons, and neither is a
weakening.**

First, only one direction is proved.  The converse implications (1) ⇒ (4) and (1) ⇒ (5) say
that the restriction of a coherent module to *any* object of the site is coherent on the slice.
The forward branch of
`Stacks.SheafOfModules.isCoherentOnSite_iff_exists_cover_isCoherentOnSite` already proves
exactly that for an arbitrary object — nothing in that branch uses that the object came from
the covering family, so the generalization is a re-parametrization and not new mathematics —
but every helper it runs through is `private` to
`StacksDraft.Ch18.Sec23.CoherenceLocalOnCover`: `overObjIso`, `isFiniteType_over`,
`isFiniteType_pushforward_of_equiv`, `isFiniteType_of_presheafIso` and
`relationsIteratedSliceSymmIso`.  So what is owed is a public form of that branch.  Its
quasi-coherence counterpart `Stacks.SheafOfModules.isQuasicoherent_over` *is* public, so the
asymmetry is an oversight rather than a limitation.

Second, the restriction used here is restriction to the slice of the small étale site,
`SheafOfModules.over`, and not the pullback `φ^*` that Stacks 07UB(4) names.  Identifying the
two is the abuse of notation of Stacks Equation 03LW.  At the level of *sites* that
identification is formalized and tagged, as
`AlgebraicGeometry.Space.smallEtaleEquivalenceOverChart` (Stacks 04M0), but transporting a
module across it additionally requires matching the two structure sheaves, which this library does
not do; the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart` record the same gap for
quasi-coherence.  Note also that `AlgebraicGeometry.Space.modulePullback` is *not* a substitute:
it is the tensor inverse image of Stacks 03D6, part (2), and no comparison of it with the étale
restriction `AlgebraicGeometry.Space.etaleModulePullback` is proved anywhere in this
development.

The three site-level results are stated at a **free module universe**.  Nothing in them
synthesizes a sheafification, a cokernel or an abelian structure, and neither
`SheafOfModules.IsCoherentOnSite` nor `PresheafOfModules.IsFiniteType` pins the module
universe; `Stacks.SheafOfModules.isCoherentOnSite_iff_exists_cover_isCoherentOnSite` is itself
stated at a free module universe.  The three `AlgebraicGeometry.Space.IsCoherent` results are
confined to module universe `u` instead, and the binding constraint is exactly one declaration:
`Stacks.SheafOfModules.isQuasicoherent_over` takes the module sections in the universe of the
coefficient rings, so the quasi-coherence equivalences of
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart` are available only there.

The index type of a covering family in
`Stacks.SheafOfModules.isCoherentOnSite_iff_exists_cover_isCoherentOnSite` lies in
`Type (max u v)`, which for the small étale ringed site `RingedSite.{u + 1, u, u}` is
`Type (u + 1)`; this is why the one-chart family is indexed by `PUnit.{u + 2}` and why the
family of all charts may be indexed by the category of charts itself.

## References

* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- A module on the small étale site is coherent if its restriction to each member of a family of
étale charts covering the final object is coherent. -/
private theorem isCoherentOnSite_of_coversTop_over (M : Modules.{u, m} B S hS F hF)
    {I : Type (u + 1)} (U : I → (smallEtaleRingedSite B S hS F hF).C)
    (hU : (smallEtaleRingedSite B S hS F hF).J.CoversTop U)
    (h : ∀ i, SheafOfModules.IsCoherentOnSite
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf
        ((smallEtaleRingedSite B S hS F hF).over (U i)).O)) (M.over (U i))) :
    SheafOfModules.IsCoherentOnSite M :=
  (Stacks.SheafOfModules.isCoherentOnSite_iff_exists_cover_isCoherentOnSite
    (smallEtaleRingedSite B S hS F hF) M).2 ⟨I, U, hU, h⟩

/-- **The local-to-global half of Stacks 07UB(5), on the site.**  A module on the small étale
site of an algebraic space is coherent on that site as soon as its restriction to the slice at
*one* étale chart whose structure morphism is surjective on points is coherent.

The chart covers the final object of the small étale site by
`AlgebraicGeometry.Space.SmallEtale.coversTop_of_isSurjective`, so the one-element family it
spans is a covering family to which the clause of Stacks 03DN for coherence applies.  The
module universe is free. -/
theorem isCoherentOnSite_of_over_of_isSurjective (M : Modules.{u, m} B S hS F hF)
    (U : (smallEtaleRingedSite B S hS F hF).C) (hsurj : IsSurjective B S hS U.1.hom)
    (h : SheafOfModules.IsCoherentOnSite
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf
        ((smallEtaleRingedSite B S hS F hF).over U).O)) (M.over U)) :
    SheafOfModules.IsCoherentOnSite M :=
  isCoherentOnSite_of_coversTop_over B S hS F hF M (fun _ : PUnit.{u + 2} => U)
    (SmallEtale.coversTop_of_isSurjective B S hS F hF U hsurj) fun _ => h

/-- **The local-to-global half of Stacks 07UB(4), on the site.**  A module on the small étale
site of an algebraic space is coherent on that site as soon as its restriction to the slice at
*every* étale chart is coherent.

Unlike `AlgebraicGeometry.Space.isCoherentOnSite_of_over_of_isSurjective` this needs no
geometry: the family of all objects of a site covers the final object, since the maximal sieve
on any object is generated by the identity of that object.  The module universe is free. -/
theorem isCoherentOnSite_of_forall_over (M : Modules.{u, m} B S hS F hF)
    (h : ∀ U : (smallEtaleRingedSite B S hS F hF).C,
      SheafOfModules.IsCoherentOnSite
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf
          ((smallEtaleRingedSite B S hS F hF).over U).O)) (M.over U)) :
    SheafOfModules.IsCoherentOnSite M := by
  refine isCoherentOnSite_of_coversTop_over B S hS F hF M (fun U => U) (fun W => ?_) h
  refine (smallEtaleRingedSite B S hS F hF).J.superset_covering ?_
    ((smallEtaleRingedSite B S hS F hF).J.top_mem W)
  intro Z f _
  exact ⟨Z, ⟨𝟙 Z⟩⟩

/-- **The local-to-global half of Stacks 07UB(4) at the affine charts, on the site.**  A module
on the small étale site of an algebraic space is coherent on that site as soon as its
restriction to the slice at every étale chart with affine underlying scheme is coherent.

The affine étale charts cover the final object of the small étale site by
`AlgebraicGeometry.Space.SmallEtale.coversTop_affineCharts`, which is the Zariski-local fact
that the affine opens of a chart are themselves charts.  The module universe is free. -/
theorem isCoherentOnSite_of_forall_affine_over (M : Modules.{u, m} B S hS F hF)
    (h : ∀ U : (smallEtaleRingedSite B S hS F hF).C,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U)) →
      SheafOfModules.IsCoherentOnSite
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf
          ((smallEtaleRingedSite B S hS F hF).over U).O)) (M.over U)) :
    SheafOfModules.IsCoherentOnSite M :=
  isCoherentOnSite_of_coversTop_over B S hS F hF M _ (SmallEtale.coversTop_affineCharts B S hS F)
    fun U => h U.1 U.2

/-- **The local-to-global half of Stacks 07UB(5).**  A module on an algebraic space is coherent
as soon as its restriction to the slice at one étale chart surjective on points is both
quasi-coherent and coherent on that slice.

The quasi-coherence clause is Stacks 03M0, conditions (1) and (2), in the form
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_over_of_isSurjective`; the coherence clause
is `AlgebraicGeometry.Space.isCoherentOnSite_of_over_of_isSurjective`.  The module universe is
the universe of the structure rings, which the quasi-coherence clause pins. -/
theorem isCoherent_of_over_of_isSurjective (M : Modules.{u, u} B S hS F hF)
    (U : (smallEtaleRingedSite B S hS F hF).C) (hsurj : IsSurjective B S hS U.1.hom)
    (hqc : (M.over U).IsQuasicoherentOnSite)
    (hcoh : SheafOfModules.IsCoherentOnSite
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf
        ((smallEtaleRingedSite B S hS F hF).over U).O)) (M.over U)) :
    IsCoherent B S hS F hF M where
  __ := (isQuasicoherentOnSite_iff_over_of_isSurjective B S hS F hF M U hsurj).2 hqc
  __ := isCoherentOnSite_of_over_of_isSurjective B S hS F hF M U hsurj hcoh

/-- **The local-to-global half of Stacks 07UB(4).**  A module on an algebraic space is coherent
as soon as its restriction to the slice at every étale chart is both quasi-coherent and
coherent on that slice.

The module universe is the universe of the structure rings, which the quasi-coherence clause
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_forall_over` pins. -/
theorem isCoherent_of_forall_over (M : Modules.{u, u} B S hS F hF)
    (hqc : ∀ U : (smallEtaleRingedSite B S hS F hF).C, (M.over U).IsQuasicoherentOnSite)
    (hcoh : ∀ U : (smallEtaleRingedSite B S hS F hF).C,
      SheafOfModules.IsCoherentOnSite
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf
          ((smallEtaleRingedSite B S hS F hF).over U).O)) (M.over U)) :
    IsCoherent B S hS F hF M where
  __ := (isQuasicoherentOnSite_iff_forall_over B S hS F hF M).2 hqc
  __ := isCoherentOnSite_of_forall_over B S hS F hF M hcoh

/-- **The local-to-global half of Stacks 07UB(4) at the affine charts.**  A module on an
algebraic space is coherent as soon as its restriction to the slice at every étale chart with
affine underlying scheme is both quasi-coherent and coherent on that slice.

The quasi-coherence clause is Stacks 03M0, conditions (1) and (4), in the form
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_forall_affine_over`.  The module universe is
the universe of the structure rings, which that clause pins. -/
theorem isCoherent_of_forall_affine_over (M : Modules.{u, u} B S hS F hF)
    (hqc : ∀ U : (smallEtaleRingedSite B S hS F hF).C,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U)) →
      (M.over U).IsQuasicoherentOnSite)
    (hcoh : ∀ U : (smallEtaleRingedSite B S hS F hF).C,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U)) →
      SheafOfModules.IsCoherentOnSite
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf
          ((smallEtaleRingedSite B S hS F hF).over U).O)) (M.over U)) :
    IsCoherent B S hS F hF M where
  __ := (isQuasicoherentOnSite_iff_forall_affine_over B S hS F hF M).2 hqc
  __ := isCoherentOnSite_of_forall_affine_over B S hS F hF M hcoh

end AlgebraicGeometry.Space

end
