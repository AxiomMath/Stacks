module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.Triangulated
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Defined
public import StacksFrontier.AlgebraicGeometry.Chow.ChowGroupsEnvelopes.Stability
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleLocallyFree
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.AlongAnIsomorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
public import StacksCore.Tactic.StacksAttribute

/-!
# Criteria for the Chern classes of a perfect derived object to be defined

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S` and let `E` be a perfect object of `D(𝒪_X)`. Stacks 0GUE lists
cases in which the Chern classes of `E` are defined, that is, in which the condition of
Stacks 0F9E (1) holds. This file proves three of them:

* (1) the condition itself: an envelope `f : Y ⟶ X` with `Lf^*E` represented by a locally
  bounded complex of finite locally free `𝒪_Y`-modules;
* (2) `E` is represented by a bounded complex of finite locally free `𝒪_X`-modules;
* (5) `E` is the derived pullback of an object whose Chern classes are defined.

## Main results

* `Stacks.Chow.hasDefinedChernClasses_of_envelope` — Stacks 0GUE (1).
* `Stacks.Chow.hasDefinedChernClasses_of_bounded_isFiniteLocallyFree` — Stacks 0GUE (2).
* `Stacks.Chow.hasDefinedChernClasses_of_derivedPullback` — Stacks 0GUE (5).

## Implementation notes

For (2) the envelope is the identity of `X`, which is proper and completely decomposed, and
`L(𝟙 X)^* ≅ 𝟭`; a bounded complex is locally bounded with the global bounds taken on the open
`⊤` at every point.

For (5) the envelope is the base change of the given one along `g`, an envelope by Stacks 0GU7,
and the representing complex is the degreewise pullback of the given one along the other
projection of the pullback square. That the degreewise pullback computes the derived pullback is
where K-flatness of a locally bounded complex of finite locally free modules enters.

None of the three needs the Chow base situation, the local-finite-type hypothesis or
perfectness of `E`: the condition of Stacks 0F9E (1) is about the derived category of `X` alone,
and so are the three proofs.

## References

* [Stacks Project, Tag 0GUE](https://stacks.math.columbia.edu/tag/0GUE)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 0GU7](https://stacks.math.columbia.edu/tag/0GU7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StrictlyPerfect

universe u

namespace Stacks.Chow

-- The standard model of the derived category is the one every derived-pullback statement used
-- below is stated at. The priority beats the locally small model: that one is a global
-- instance, so without it the statements here would be about an unrelated model.
attribute [local instance 10000] HasDerivedCategory.standard

/-- **Stacks 0GUE (1).** If some envelope `f : Y ⟶ X` has `Lf^*E` isomorphic to a locally
bounded complex of finite locally free `𝒪_Y`-modules, then the Chern classes of `E` are
defined. -/
@[stacks 0GUE "clause (1): the envelope condition of Tag 0F9E (1) itself"]
theorem hasDefinedChernClasses_of_envelope {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : IsEnvelope f) (E : DerivedCategory X.Modules) (P : CochainComplex Y.Modules ℤ)
    (hP : IsLocallyBoundedFiniteLocallyFree P)
    (hrep : Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      f.toLRSHom.toShHom).obj E ≅ DerivedCategory.Q.obj P)) :
    HasDefinedChernClasses E :=
  ⟨⟨Y, f, hf, P, hP, hrep⟩⟩

/-- A bounded complex of finite locally free `𝒪_X`-modules is locally bounded: the global
bounds work on the open `⊤` around every point. -/
theorem isLocallyBoundedFiniteLocallyFree_of_bounded {X : Scheme.{u}}
    (P : CochainComplex X.Modules ℤ) (hP : CochainComplex.bounded X.Modules P)
    (hflf : ∀ n : ℤ, SheafOfModules.IsFiniteLocallyFree
      (R := structureSheafOfRings X.toRingedSpace) (P.X n)) :
    IsLocallyBoundedFiniteLocallyFree P := by
  obtain ⟨lo, hi, hlo, hhi⟩ := (CochainComplex.bounded_iff P).mp hP
  refine ⟨hflf, fun x => ⟨⊤, Set.mem_univ x, lo, hi, fun n hn => ?_⟩⟩
  refine Functor.map_isZero _ ?_
  rcases hn with hn | hn
  · exact P.isZero_of_isStrictlyGE lo n hn
  · exact P.isZero_of_isStrictlyLE hi n hn

/-- **Stacks 0GUE (2).** If `E` is represented by a bounded complex of finite locally free
`𝒪_X`-modules, then the Chern classes of `E` are defined: the identity of `X` is an envelope and
`L(𝟙 X)^* ≅ 𝟭`. -/
@[stacks 0GUE "clause (2): a bounded complex of finite locally free modules representing `E`"]
theorem hasDefinedChernClasses_of_bounded_isFiniteLocallyFree {X : Scheme.{u}}
    (E : DerivedCategory X.Modules) (P : CochainComplex X.Modules ℤ)
    (hP : CochainComplex.bounded X.Modules P)
    (hflf : ∀ n : ℤ, SheafOfModules.IsFiniteLocallyFree
      (R := structureSheafOfRings X.toRingedSpace) (P.X n))
    (hrep : Nonempty (DerivedCategory.Q.obj P ≅ E)) :
    HasDefinedChernClasses E :=
  hasDefinedChernClasses_of_envelope (𝟙 X) ⟨inferInstance, isCompletelyDecomposed_id X⟩ E P
    (isLocallyBoundedFiniteLocallyFree_of_bounded P hP hflf)
    ⟨(Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIso X.toRingedSpace).app E ≪≫
      hrep.some.symm⟩

/-- **Stacks 0GUE (5).** If `E` is isomorphic to the derived pullback of an object `E'` whose
Chern classes are defined, then the Chern classes of `E` are defined: the base change of an
envelope of `E'` is an envelope, and the degreewise pullback of a locally bounded complex of
finite locally free modules is one again and computes the derived pullback.

At `i = Iso.refl` this is the well-definedness that clause (2) of Stacks 0FAC presupposes when it
writes `c_p(Lg^*E)`. -/
@[stacks 0GUE "clause (5): `E` is the derived pullback of an object whose Chern classes are \
defined"]
theorem hasDefinedChernClasses_of_derivedPullback {X X' : Scheme.{u}} (g : X ⟶ X')
    (E : DerivedCategory X.Modules) (E' : DerivedCategory X'.Modules)
    (hE' : HasDefinedChernClasses E')
    (i : E ≅ (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      g.toLRSHom.toShHom).obj E') :
    HasDefinedChernClasses E := by
  obtain ⟨H⟩ := hE'
  obtain ⟨j⟩ := H.representation
  let p := pullback.fst H.f g
  let q := pullback.snd H.f g
  have hsq : q.toLRSHom.toShHom ≫ g.toLRSHom.toShHom =
      p.toLRSHom.toShHom ≫ H.f.toLRSHom.toShHom :=
    congrArg (fun f => f.toLRSHom.toShHom) (pullback.condition (f := H.f) (g := g)).symm
  refine hasDefinedChernClasses_of_envelope q
    (isEnvelope_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback H.f g) H.envelope) E
    (((Scheme.Modules.pullback p).mapHomologicalComplex (ComplexShape.up ℤ)).obj H.P)
    (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback p H.P H.locallyBounded)
    ⟨(Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback q.toLRSHom.toShHom).mapIso i ≪≫
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        q.toLRSHom.toShHom g.toLRSHom.toShHom).app E' ≪≫
      (eqToIso (Cohomology.DerivedPullbackAlongIso.derivedPullback_eq_of_eq hsq)).app E' ≪≫
      ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        p.toLRSHom.toShHom H.f.toLRSHom.toShHom).app E').symm ≪≫
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        p.toLRSHom.toShHom).mapIso j ≪≫
      Cohomology.derivedPullbackIsoPullbackOfKFlat p.toLRSHom.toShHom H.P
        (Stacks.BlowUpComplexes.kFlatComplex_of_isLocallyBoundedFiniteLocallyFree H.P
          H.locallyBounded)⟩

end Stacks.Chow

end
