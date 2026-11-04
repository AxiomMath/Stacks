module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleBlowup
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleEtaPerfect
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleLocallyFree
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.FiniteFreeRepresentation
import StacksCore.Tactic.StacksAttribute

/-!
# Blowing up complexes, II: perfectness of the décalage on the modification

Let `(X, D, M)` be a triple as in Situation 0F8S and let `b : X' ⟶ X` be a morphism which is
*good* for the triple in the sense of condition (1) of Stacks tag 0GTY: the pullback
`D' = b⁻¹D` of the effective Cartier divisor is defined and the pulled-back triple
`(X', D', Lb^*M)` is good.  Stacks tag 0F8U asserts that `Q = Lη_{ℐ'} Lb^*M` is then a perfect
object of `D(𝒪_{X'})`.

The source proof is one line: it is tag 0GTY for `b` together with tag 0GTW for the pulled-back
triple.  This file gives that deduction twice, from the two forms in which tag 0GTW's conclusion
is available in this library.

* From tag 0GTX, which is tag 0GTW's conclusion for a good triple whose object is represented
  by a locally bounded complex of finite locally free modules.  The first half of this file
  shows that such a complex is perfect, so the deduction is complete once that representability
  of `Lb^*M` is assumed; it is the hypothesis `hrep` of
  `AlgebraicGeometry.ComplexAndDivisorSituation.isPerfect_etaDerivedPullbackObject`.
* From the formalization of tag 0GTW itself in `GoodTripleEtaPerfect.lean`, which has no
  hypothesis on the object but carries the second assertion of tag 0GTV as data and asks for
  affine charts with principal determinantal ideals off the divisor.  Those two become the
  hypotheses `hcomp` and `hoff` of the second result below.

## Main definitions

* `AlgebraicGeometry.ComplexAndDivisorSituation.etaDerivedPullbackObject`: the object
  `Q = Lη_{ℐ'} Lb^*M` of `D(𝒪_{X'})`, for a morphism `b` whose pullback of the divisor is
  defined.

## Main results

* `Stacks.BlowUpComplexes.exists_isStrictlyPerfect_restrictComplex_of_isLocallyBounded`: a
  locally bounded complex of finite locally free `𝒪_X`-modules is strictly perfect on a
  neighbourhood of every point.
* `Stacks.BlowUpComplexes.isPerfectComplex_of_isLocallyBoundedFiniteLocallyFree` and
  `Stacks.BlowUpComplexes.isPerfect_of_isLocallyBoundedFiniteLocallyFree`: such a complex is
  perfect, and so is the object of the derived category it represents.

## What of tag 0F8U is proved here

Tag 0F8U rests on two inputs: the existence of the morphism `b` of tag 0GTY, and tag 0GTW.

* The existence half of tag 0GTY is not formalized — see the discussion in
  `GoodTripleBlowup.lean` — so `b` is carried here as a morphism together with
  `AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodOver`, which is exactly condition (1) of
  that tag.  This is a generalization, not a weakening: the morphism of tag 0GTY satisfies
  `IsGoodOver` by `AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowup.isGoodOver`, so
  both results below apply to it.
* Tag 0GTW is available only in the two qualified forms listed above, and each qualification is
  inherited by the corresponding result here and named in its `@[stacks 0F8U ...]` attribute.
  Nothing here proves the unqualified statement of tag 0F8U.

## Implementation notes

Three definitionally equal spellings of restriction of modules to an open subspace meet in the
first half of the file: `AlgebraicGeometry.RingedSpace.restrictModules`, at which
`AlgebraicGeometry.RingedSpace.IsPerfectComplex` is written;
`AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules`, at which
`Stacks.Chow.IsLocallyBoundedFiniteLocallyFree` is written; and
`StrictlyPerfect.restrictModules`, at which the comparison
`StrictlyPerfect.restrictModulesOfLEIso` between restricting in one step and in two is written.
`Stacks.BlowUpComplexes.isZero_restrictModules_of_le` is stated at the first of the three and
proved from the third, which is what lets the local-boundedness hypothesis be used at the
smaller open produced by intersecting it with the finitely many freeness neighbourhoods.

The neighbourhood on which the complex is strictly perfect is the intersection of the open on
which the complex is bounded with the finitely many opens on which the terms in the bounded
range are free.  Outside that range the terms already restrict to zero, and a zero object is a
direct summand of a finite free module, so no freeness neighbourhood is needed there.

`Q` is formed at the standard model of the derived category of `𝒪_{X'}`-modules, which is the
model at which `Stacks.Divisors.Eta.derivedEtaData` is constructed and the one that
`AlgebraicGeometry.ComplexAndDivisorSituation.pullback` installs on the pulled-back triple; the
triple `(X, D, M)` itself may carry an arbitrary model, and `Lb^*M` is transported to the
standard one by `AlgebraicGeometry.ComplexAndDivisorSituation.derivedPullbackObject`.

Tag 0GTW is stated at the model of `D(𝒪_X)` that the triple carries, read at the
`AlgebraicGeometry.Scheme.Modules` spelling by
`AlgebraicGeometry.ComplexAndDivisorSituation.modulesHasDerivedCategory`.  For the pulled-back
triple that model *is* the standard one, which is why `Stacks.Divisors.Eta.derivedEtaData` can
be supplied for its functor-valued hypothesis; no instance has to be registered for this, since
the model in the hypothesis is fixed by the statement of tag 0GTW rather than searched for.

## References

* [Stacks Project, Tag 0F8U](https://stacks.math.columbia.edu/tag/0F8U)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 0GTW](https://stacks.math.columbia.edu/tag/0GTW)
* [Stacks Project, Tag 0GTX](https://stacks.math.columbia.edu/tag/0GTX)
* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open StrictlyPerfect

universe u d

namespace Stacks.BlowUpComplexes

/-! ### Perfectness of a locally bounded complex of finite locally free modules -/

/-- **A module vanishing on an open vanishes on every smaller open.**  Restricting to `U` and
then to `V ≤ U` is restricting to `V`, and the second restriction is additive, hence carries a
zero object to a zero object. -/
theorem isZero_restrictModules_of_le {X : RingedSpace.{u, u}} {V U : Opens X.carrier}
    (h : V ≤ U) (M : OXMod.{u, u} X)
    (hM : IsZero ((AlgebraicGeometry.RingedSpace.restrictModules X U).obj M)) :
    IsZero ((AlgebraicGeometry.RingedSpace.restrictModules X V).obj M) :=
  IsZero.of_iso (Functor.map_isZero (StrictlyPerfect.restrictModulesOfLE.{u} h) hM)
    ((StrictlyPerfect.restrictModulesOfLEIso.{u} h).app M).symm

/-- **A locally bounded complex of finite locally free modules is strictly perfect near every
point.**  On a neighbourhood of `x` the complex is bounded, say with nonzero terms only in
degrees between `a` and `b`; each of the finitely many terms in that range is free on a
further neighbourhood, and the intersection of all of these works.  Outside the range the terms
restrict to zero, which is a direct summand of a finite free module. -/
theorem exists_isStrictlyPerfect_restrictComplex_of_isLocallyBounded {X : RingedSpace.{u, u}}
    (P : CochainComplex (OXMod.{u, u} X) ℤ)
    (hP : Stacks.Chow.IsLocallyBoundedFiniteLocallyFree P) (x : X.carrier) :
    ∃ V : Opens X.carrier, x ∈ V ∧
      IsStrictlyPerfect (AlgebraicGeometry.RingedSpace.restrictComplex P V) := by
  classical
  obtain ⟨U, hxU, a, b, hbd⟩ := hP.2 x
  choose V hxV n hfree using fun j : ℤ =>
    AlgebraicGeometry.RingedSpace.exists_free_iso_over_near (hP.1 j) x
  set J := {j : ℤ // j ∈ Finset.Icc a b}
  refine ⟨U ⊓ ⨅ j : J, V j.1, ⟨hxU, ?_⟩, ?_, ?_⟩
  · simp only [Opens.coe_iInf]
    exact Set.mem_iInter.mpr fun j => hxV j.1
  · refine (Finset.finite_toSet (Finset.Icc a b)).subset fun i hi => ?_
    by_contra hnot
    have houtside : i < a ∨ b < i := by
      simpa only [Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] using hnot
    exact hi (isZero_restrictModules_of_le inf_le_left (P.X i) (hbd i houtside))
  · intro i
    by_cases hi : i ∈ Finset.Icc a b
    · have hle : U ⊓ ⨅ j : J, V j.1 ≤ V i :=
        inf_le_right.trans (iInf_le (fun j : J => V j.1) (⟨i, hi⟩ : J))
      obtain ⟨e⟩ := AlgebraicGeometry.RingedSpace.nonempty_free_iso_over_of_le
        (P.X i) hle (n i) (hfree i).some
      obtain ⟨e'⟩ := AlgebraicGeometry.RingedSpace.nonempty_restrictModules_obj_iso_finiteFree
        (P.X i) (U ⊓ ⨅ j : J, V j.1) (n i) e
      exact (isDirectSummandOfFiniteFree_iff_retract _).mpr
        ⟨n i, ⟨⟨e'.hom, e'.inv, by simp⟩⟩⟩
    · have houtside : i < a ∨ b < i := by
        simpa only [Finset.mem_Icc, not_and_or, not_le] using hi
      exact isDirectSummandOfFiniteFree_of_isZero
        (isZero_restrictModules_of_le inf_le_left (P.X i) (hbd i houtside))

/-- **A locally bounded complex of finite locally free `𝒪_X`-modules is perfect.**  The
neighbourhoods produced by
`Stacks.BlowUpComplexes.exists_isStrictlyPerfect_restrictComplex_of_isLocallyBounded` cover `X`,
and on each of them the complex *is* strictly perfect, so the quasi-isomorphism required by
Stacks 08CM may be taken to be the identity. -/
theorem isPerfectComplex_of_isLocallyBoundedFiniteLocallyFree {X : RingedSpace.{u, u}}
    (P : CochainComplex (OXMod.{u, u} X) ℤ)
    (hP : Stacks.Chow.IsLocallyBoundedFiniteLocallyFree P) :
    AlgebraicGeometry.RingedSpace.IsPerfectComplex P := by
  classical
  choose V hV hsp using
    exists_isStrictlyPerfect_restrictComplex_of_isLocallyBounded P hP
  exact ⟨X.carrier, V, top_unique fun x _ => Opens.mem_iSup.mpr ⟨x, hV x⟩,
    fun x => ⟨AlgebraicGeometry.RingedSpace.restrictComplex P (V x), hsp x, 𝟙 _,
      inferInstance⟩⟩

/-- An object of `D(𝒪_X)` represented by a locally bounded complex of finite locally free
`𝒪_X`-modules is perfect. -/
theorem isPerfect_of_isLocallyBoundedFiniteLocallyFree {X : RingedSpace.{u, u}}
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] (K : DerivedCategory (OXMod.{u, u} X))
    (hK : ∃ P : CochainComplex (OXMod.{u, u} X) ℤ,
      Stacks.Chow.IsLocallyBoundedFiniteLocallyFree P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ K)) :
    AlgebraicGeometry.RingedSpace.IsPerfect K := by
  obtain ⟨P, hP, e⟩ := hK
  exact ⟨P, isPerfectComplex_of_isLocallyBoundedFiniteLocallyFree P hP, e⟩

end Stacks.BlowUpComplexes

namespace AlgebraicGeometry.ComplexAndDivisorSituation

attribute [local instance 10000] HasDerivedCategory.standard

/-- The object `Q = Lη_{ℐ'} Lb^*M` of `D(𝒪_{X'})` attached to a triple `(X, D, M)` as in
Situation 0F8S and a morphism `b : X' ⟶ X` along which the pullback `D' = b⁻¹D` of the
effective Cartier divisor is defined: the derived décalage, by the ideal sheaf `ℐ'` of `D'`, of
the derived pullback `Lb^*M`. -/
def etaDerivedPullbackObject (S : ComplexAndDivisorSituation.{u, d}) {X' : Scheme.{u}}
    (b : X' ⟶ S.X) (hb : Stacks.Divisors.IsPullbackDefined b S.D) :
    DerivedCategory X'.Modules :=
  (@Stacks.Divisors.Eta.derivedEtaData X' (S.D.comap b) hb).functor.obj
    (S.derivedPullbackObject b)

end AlgebraicGeometry.ComplexAndDivisorSituation

end
