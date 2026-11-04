module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.NoetherianComponentEnvelope
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.CriteriaComponents
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.CriteriaQuasiCompact

/-!
# The Chern classes of the perfect object of Situation 0GUJ are defined

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project. Situation 0GUJ asks, in
its condition (3), for one of four finiteness alternatives (a)-(d) on the perfect object `E` of
`D(𝒪_X)`. Each of them makes the Chern classes of `E` defined, by the clauses of Stacks 0GUE:
(a) by clause (4), `Stacks.Chow.hasDefinedChernClasses_of_compactSpace`; (b) by clause (3),
`Stacks.Chow.hasDefinedChernClasses_of_isCompact_irreducibleComponents`; (c) by clause (1) for the
identity envelope; (d) by clauses (3) and (5).

## Main results

* `Stacks.Chow.hasDefinedChernClasses_of_derivedPullback_of_isCompact` — alternative (d) of
  Situation 0GUJ (3): `E` is the pullback of a perfect object on a scheme locally of finite type
  over the base whose irreducible components are quasi-compact.
* `Stacks.Chow.LocalizedSituation.hasDefinedChernClasses` — the Chern classes of the perfect
  object of Situation 0GUJ are defined.

## References

* [Stacks Project, Tag 0GUE](https://stacks.math.columbia.edu/tag/0GUE)
* [Stacks Project, Tag 0GUJ](https://stacks.math.columbia.edu/tag/0GUJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StrictlyPerfect

universe u

namespace Stacks.Chow

-- The standard model of the derived category.
attribute [local instance 10000] HasDerivedCategory.standard

/-- **Alternative (d) of Situation 0GUJ (3).** Let `X'` be locally of finite type over the base
of chapter 42 of the Stacks Project, let `g : X ⟶ X'` be a morphism of schemes and let `E` be the
derived pullback of a perfect object `E'` of `D(𝒪_{X'})`. If the irreducible components of `X'`
are quasi-compact, then the Chern classes of `E` are defined: those of `E'` are, by
Stacks 0GUE (3), and Stacks 0GUE (5) passes them to `E`. The source asks moreover that `X` be
locally of finite type over the base and `g` a morphism over it; neither is used. -/
theorem hasDefinedChernClasses_of_derivedPullback_of_isCompact (C : ChowSituation.{u})
    {X X' : Scheme.{u}} (a' : X' ⟶ C.S) [LocallyOfFiniteType a'] (g : X ⟶ X')
    (E' : DerivedCategory X'.Modules)
    (hE' : Cohomology.PerfectComplexes.IsPerfect (X := X'.toRingedSpace) E')
    (hX' : ∀ Z ∈ irreducibleComponents X', IsCompact Z) (E : DerivedCategory X.Modules)
    (i : Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      g.toLRSHom.toShHom).obj E' ≅ E)) :
    HasDefinedChernClasses E :=
  hasDefinedChernClasses_of_derivedPullback g E E'
    (hasDefinedChernClasses_of_isCompact_irreducibleComponents C a' hX' E' hE') i.some.symm

/-- **The Chern classes of the perfect object of Situation 0GUJ are defined**, under each of the
four finiteness alternatives of its condition (3): (a) by Stacks 0GUE (4), (b) by Stacks 0GUE (3),
(c) by Stacks 0GUE (1) for the identity envelope, and (d) by
`Stacks.Chow.hasDefinedChernClasses_of_derivedPullback_of_isCompact`. -/
theorem LocalizedSituation.hasDefinedChernClasses (S : LocalizedSituation.{u}) :
    HasDefinedChernClasses S.E := by
  rcases S.finiteness with h | h | ⟨P, hP, ⟨e⟩⟩ | ⟨X', a', g, E', ha', -, hE', hi, hX'⟩
  · exact hasDefinedChernClasses_of_compactSpace S.base S.a S.E S.perfect
  · exact hasDefinedChernClasses_of_isCompact_irreducibleComponents S.base S.a h S.E S.perfect
  · exact hasDefinedChernClasses_of_envelope (𝟙 S.X) ⟨inferInstance, isCompletelyDecomposed_id _⟩
      S.E P hP ⟨(Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIso
        S.X.toRingedSpace).app S.E ≪≫ e.symm⟩
  · exact hasDefinedChernClasses_of_derivedPullback_of_isCompact S.base a' g E' hE' hX' S.E hi

end Stacks.Chow

end
