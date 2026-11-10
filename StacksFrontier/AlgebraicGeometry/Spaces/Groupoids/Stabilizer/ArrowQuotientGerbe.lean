module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.GerbeCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.MorphismsToAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.ArrowQuotientRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.CoveringMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.GroupoidBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FinalBootstrapTheorem

/-!
# The quotient stack is a gerbe over `U/(R/S)` (Stacks 06QJ)

Let `G` be a groupoid in algebraic spaces over `B`, with object space `U` and arrow space `R`,
let `S ⟶ U` be its stabilizer group algebraic space, and let `R' = R/S` be the quotient of the
arrow space by the stabilizer action of
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.ArrowQuotient`, with
`s', t' : R' ⟶ U` the descended source and target. As soon as the stabilizer and the source and
the target of `G` are flat and locally of finite presentation, this file produces

    X = U/R'

as an algebraic space, reads `G` as a groupoid over `X` along the invariant morphism `U ⟶ X`, and
proves that the structure arrow

    [U/R] ⟶ X

of Stacks 044R of that re-based groupoid makes `[U/R]` a gerbe over `X`.

This is the second half of the source's proof of **Stacks 06QJ**, the implication (2) `⟹` (1).
The first half — that clause (2) makes the stabilizer of a presentation flat and locally of
finite presentation — is in `StacksFrontier.AlgebraicGeometry.Stacks.PresentationStabilizerFlat`,
and the transport of the gerbe along the presenting equivalence is in
`StacksFrontier.AlgebraicGeometry.Stacks.GerbeOfFlatInertia`.

## Main definitions

All of these live in the namespace `AlgebraicGeometry.GroupoidInAlgebraicSpaces`.

* `arrowStabilizerQuotientSpace`: the algebraic space `X = U/R'`, given its algebraicity.
* `toArrowStabilizerQuotientSpace`: the invariant morphism `U ⟶ X`.
* `arrowStabilizerQuotientSpaceToBase`: the structure morphism `X ⟶ B`.
* `overArrowStabilizerQuotient`: `G` read as a groupoid in algebraic spaces over `X`.

## Main results

* `isAlgebraicSpace_arrowStabilizerQuotientSheaf`: **Stacks 04S6** at `j' = (t', s')`, which is
  an equivalence relation by
  `isEquivalenceRelation_arrowStabilizerQuotientPreRelation` and whose two morphisms are flat and
  locally of finite presentation by **Stacks 06NR**: the quotient sheaf `U/R'` is an algebraic
  space.
* `target_comp_toArrowStabilizerQuotientSpace`: `U ⟶ X` is invariant, which is what
  `overArrowStabilizerQuotient` needs, and
  `quotientStack_overArrowStabilizerQuotient`: the quotient stack is unchanged by the re-basing.
* `exists_covering_lift_objects_toArrowStabilizerQuotientSpace`: **Stacks 06PG** in sieve form —
  a section of `X` comes from `U` on an fppf covering.
* `exists_covering_hom_arrows_of_toArrowStabilizerQuotientSpace_eq`: **Stacks 046O** in sieve
  form — two sections of `U` with the same image in `X` are the source and the target of an
  arrow of `R` on an fppf covering.
* `isGerbeOver_quotientStackToBase_overArrowStabilizerQuotient`: **Stacks 06QJ**, the geometric
  half of the implication (2) `⟹` (1): `[U/R] ⟶ X` is a gerbe.

## Implementation notes

The re-basing of `G` over `X` is `AlgebraicGeometry.GroupoidInAlgebraicSpaces.overInvariantTarget`
(**Stacks 048G**): the object and arrow spaces, the source, the target and the composition are
unchanged and only the two structure morphisms to the base move, so the underlying groupoid in
presheaves — and therefore the quotient stack, which is a function of it alone — is literally the
same term. That is why no comparison of quotient stacks appears anywhere below: the gerbe
criterion is read at the re-based groupoid and its conclusion is a statement about a functor out
of `quotientStack G` on the nose.

The criterion used is `AlgebraicGeometry.Stack.isGerbeOver_quotientStackToBase_of_locallyFull`,
whose fullness clause is *local*: two sections of `U` with the same image in the base need only
become the source and the target of an arrow of `R` after an fppf covering. That is what
Stacks 046O supplies, and it is why the stricter
`AlgebraicGeometry.Stack.isGerbeOver_quotientStackToBase` does not apply.

Both hypotheses of the criterion are produced as *sieves*. Surjectivity is local surjectivity of
`U ⟶ U/R'` (**Stacks 06PG**) read through `CategoryTheory.Presheaf.imageSieve`, whose arrows are
by definition the local lifts asked for. Local fullness composes three steps: Stacks 046O turns
equality in the quotient sheaf into a `CategoryTheory.PreZeroHypercover` carrying, over each of
its members, a section of `R'` with the two prescribed endpoints;
`AlgebraicGeometry.Space.fppf_hypercover_sieve_mem` turns that family into a covering sieve; and
over each arrow of the generated sieve the section of `R'` lifts to an arrow of `R` on a further
covering, by local surjectivity of `π : R ⟶ R'`. The two coverings are composed by
`CategoryTheory.GrothendieckTopology.exists_covering_of_refine`, so the conclusion is a single
covering sieve as the criterion wants.

Nothing here uses that `R'` or `X` is an algebraic space apart from the step that produces them:
the two sieve statements are about the quotient *sheaf*, and only the criterion's conclusion is
phrased at the algebraic space.

## References

* [Stacks Project, Tag 043C](https://stacks.math.columbia.edu/tag/043C)
* [Stacks Project, Tag 044J](https://stacks.math.columbia.edu/tag/044J)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 046O](https://stacks.math.columbia.edu/tag/046O)
* [Stacks Project, Tag 048E](https://stacks.math.columbia.edu/tag/048E)
* [Stacks Project, Tag 048G](https://stacks.math.columbia.edu/tag/048G)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 06NR](https://stacks.math.columbia.edu/tag/06NR)
* [Stacks Project, Tag 06PE](https://stacks.math.columbia.edu/tag/06PE)
* [Stacks Project, Tag 06PG](https://stacks.math.columbia.edu/tag/06PG)
* [Stacks Project, Tag 06PH](https://stacks.math.columbia.edu/tag/06PH)
* [Stacks Project, Tag 06QJ](https://stacks.math.columbia.edu/tag/06QJ)
* [Stacks Project, Tag 0DUH](https://stacks.math.columbia.edu/tag/0DUH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

open AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- If the stabilizer of `G` is flat and locally of finite presentation over `U`, and the source
and target of `G` are flat and locally of finite presentation, then the quotient sheaf `U/R'` of
the pre-relation `j' = (t', s')` is an algebraic space. -/
theorem isAlgebraicSpace_arrowStabilizerQuotientSheaf (G : GroupoidInAlgebraicSpaces C S hS B)
    (hSflat : Space.IsFlat C S hS (stabilizer G).hom)
    (hSfp : Space.IsLocallyOfFinitePresentation C S hS (stabilizer G).hom)
    (hsflat : Space.IsFlat C S hS G.source.hom)
    (htflat : Space.IsFlat C S hS G.target.hom)
    (hslfp : Space.IsLocallyOfFinitePresentation C S hS G.source.hom)
    (htlfp : Space.IsLocallyOfFinitePresentation C S hS G.target.hom) :
    IsAlgebraicSpace C S hS
      (Space.quotientSheaf (arrowStabilizerQuotientPreRelation G)).obj := by
  have _inst : IsEquivalenceRelation (arrowStabilizerQuotientPreRelation G).target
      (arrowStabilizerQuotientPreRelation G).source :=
    isEquivalenceRelation_arrowStabilizerQuotientPreRelation G
  refine Bootstrap04S6.isAlgebraicSpace_quotient_preRelation C S hS B.property
    (isAlgebraicSpace_arrowStabilizerQuotient G hSflat hSfp) G.objects.property
    (arrowStabilizerQuotientPreRelation G) ?_ ?_ ?_ ?_
  · rw [arrowStabilizerQuotientPreRelation_source_left]
    exact isFlat_arrowStabilizerQuotientSource G hSflat hSfp hsflat
  · rw [arrowStabilizerQuotientPreRelation_target_left]
    exact isFlat_arrowStabilizerQuotientTarget G hSflat hSfp htflat
  · rw [arrowStabilizerQuotientPreRelation_source_left]
    exact isLocallyOfFinitePresentation_arrowStabilizerQuotientSource G hSflat hSfp hslfp
  · rw [arrowStabilizerQuotientPreRelation_target_left]
    exact isLocallyOfFinitePresentation_arrowStabilizerQuotientTarget G hSflat hSfp htlfp

section

variable (G : GroupoidInAlgebraicSpaces C S hS B)
  (hX : IsAlgebraicSpace C S hS
    (Space.quotientSheaf (arrowStabilizerQuotientPreRelation G)).obj)

/-- The algebraic space `X = U/R'`: the quotient sheaf of `j' = (t', s')` of **Stacks 044J**,
together with its algebraicity. -/
noncomputable abbrev arrowStabilizerQuotientSpace : AlgebraicSpaces C S hS :=
  ⟨(Space.quotientSheaf (arrowStabilizerQuotientPreRelation G)).obj, hX⟩

/-- The canonical morphism `U ⟶ X = U/R'`. -/
noncomputable abbrev toArrowStabilizerQuotientSpace :
    G.objects ⟶ arrowStabilizerQuotientSpace G hX :=
  ObjectProperty.homMk (Space.toQuotientSheaf (arrowStabilizerQuotientPreRelation G))

/-- The structure morphism `X = U/R' ⟶ B` of **Stacks 044J**. -/
noncomputable abbrev arrowStabilizerQuotientSpaceToBase :
    arrowStabilizerQuotientSpace G hX ⟶ B :=
  ObjectProperty.homMk
    (Space.quotientSheafToBase B.property.isSheaf (arrowStabilizerQuotientPreRelation G)).hom

/-- `U ⟶ X = U/R'` is a morphism over `B`: the structure morphism of `X` extends that of `U`. -/
theorem toArrowStabilizerQuotientSpace_comp_arrowStabilizerQuotientSpaceToBase :
    toArrowStabilizerQuotientSpace G hX ≫ arrowStabilizerQuotientSpaceToBase G hX =
      G.objectsToBase :=
  ObjectProperty.hom_ext _
    (Space.toQuotientSheaf_quotientSheafToBase B.property.isSheaf
      (arrowStabilizerQuotientPreRelation G))

/-- **`U ⟶ X = U/R'` is invariant under the groupoid.** The source and the target of `G` factor
through `π : R ⟶ R'` as `s = π ≫ s'` and `t = π ≫ t'`, and the quotient projection onto `U/R'`
identifies `s'` and `t'`. -/
theorem target_comp_toArrowStabilizerQuotientSpace :
    G.target ≫ toArrowStabilizerQuotientSpace G hX =
      G.source ≫ toArrowStabilizerQuotientSpace G hX := by
  refine ObjectProperty.hom_ext _ ?_
  have h := Space.target_toQuotientSheaf_eq_source (arrowStabilizerQuotientPreRelation G)
  rw [arrowStabilizerQuotientPreRelation_source_left,
    arrowStabilizerQuotientPreRelation_target_left] at h
  change G.target.hom ≫ Space.toQuotientSheaf (arrowStabilizerQuotientPreRelation G) =
    G.source.hom ≫ Space.toQuotientSheaf (arrowStabilizerQuotientPreRelation G)
  rw [← toArrowStabilizerQuotient_comp_target, ← toArrowStabilizerQuotient_comp_source,
    Category.assoc, Category.assoc, h]

/-- **`G` read as a groupoid in algebraic spaces over `X = U/R'`**, along the invariant morphism
`U ⟶ X`. This is **Stacks 048G**: only the two structure morphisms to the base change, so the
underlying groupoid in presheaves, and hence the quotient stack, is unchanged. -/
noncomputable def overArrowStabilizerQuotient :
    GroupoidInAlgebraicSpaces C S hS (arrowStabilizerQuotientSpace G hX) :=
  (overInvariantTarget G (arrowStabilizerQuotientSpaceToBase G hX)
    (toArrowStabilizerQuotientSpace G hX)
    (toArrowStabilizerQuotientSpace_comp_arrowStabilizerQuotientSpaceToBase G hX)
    ((isInvariant_iff G (toArrowStabilizerQuotientSpace G hX)).2
      (target_comp_toArrowStabilizerQuotientSpace G hX))).val

/-- Re-basing over `X = U/R'` leaves the quotient stack unchanged. -/
theorem quotientStack_overArrowStabilizerQuotient :
    quotientStack (overArrowStabilizerQuotient G hX) = quotientStack G := rfl

end

/-- **Stacks 06PG in sieve form.** A section of `X = U/R'` over a test object comes from a
section of `U` after an fppf covering: the quotient projection is a surjection of fppf sheaves,
and the arrows of `CategoryTheory.Presheaf.imageSieve` are by definition the local lifts. -/
theorem exists_covering_lift_objects_toArrowStabilizerQuotientSpace
    (G : GroupoidInAlgebraicSpaces C S hS B) (T : BigFppfOver C S hS)
    (b : (Space.quotientSheaf (arrowStabilizerQuotientPreRelation G)).obj.obj (op T)) :
    ∃ W ∈ BigFppfOver.topology C S hS T,
      ∀ ⦃V : BigFppfOver C S hS⦄ (i : V ⟶ T), W i →
        ∃ a : G.objects.obj.obj (op V),
          (Space.toQuotientSheaf (arrowStabilizerQuotientPreRelation G)).app (op V) a =
            (Space.quotientSheaf (arrowStabilizerQuotientPreRelation G)).obj.map i.op b := by
  have hloc :=
    Space.isLocallySurjective_toQuotientSheaf (arrowStabilizerQuotientPreRelation G)
  exact ⟨Presheaf.imageSieve
      (Space.toQuotientSheaf (arrowStabilizerQuotientPreRelation G)) b,
    hloc.imageSieve_mem b, fun _ _ hi => hi⟩

/-- **Stacks 046O in sieve form.** Two sections of `U` over a test object with the same image in
`X = U/R'` become, after an fppf covering, the source and the target of an arrow of `R`.

Stacks 046O produces a covering family carrying a section of `R' = R/S` with the two prescribed
endpoints over each of its members; that family is turned into a covering sieve by
`AlgebraicGeometry.Space.fppf_hypercover_sieve_mem`, and over each arrow of the generated sieve
the section of `R'` lifts to an arrow of `R` after a further covering, because `π : R ⟶ R'` is a
surjection of fppf sheaves. The two coverings are composed by
`CategoryTheory.GrothendieckTopology.exists_covering_of_refine`. -/
theorem exists_covering_hom_arrows_of_toArrowStabilizerQuotientSpace_eq
    (G : GroupoidInAlgebraicSpaces C S hS B) (T : BigFppfOver C S hS)
    (x y : G.objects.obj.obj (op T))
    (hxy : (Space.toQuotientSheaf (arrowStabilizerQuotientPreRelation G)).app (op T) x =
      (Space.toQuotientSheaf (arrowStabilizerQuotientPreRelation G)).app (op T) y) :
    ∃ W ∈ BigFppfOver.topology C S hS T,
      ∀ ⦃V : BigFppfOver C S hS⦄ (i : V ⟶ T), W i →
        ∃ r : G.arrows.obj.obj (op V),
          G.source.hom.app (op V) r = G.objects.obj.map i.op x ∧
            G.target.hom.app (op V) r = G.objects.obj.map i.op y := by
  obtain ⟨E, hE, hrel⟩ := (Space.toQuotientSheaf_eq_iff_locally_related
    (arrowStabilizerQuotientPreRelation G)
    (isPreEquivalenceRelation_arrowStabilizerQuotientPreRelation G) T x y).1 hxy
  simp only [arrowStabilizerQuotientPreRelation_source_left,
    arrowStabilizerQuotientPreRelation_target_left, Over.mk_left] at hrel
  have _inst := isLocallySurjective_toArrowStabilizerQuotient G
  refine (BigFppfOver.topology C S hS).exists_covering_of_refine
    (Space.fppf_hypercover_sieve_mem hS T E hE) ?_
  rintro V f ⟨Y, h, g, hg, rfl⟩
  rcases hg with ⟨k⟩
  obtain ⟨rk, hrks, hrkt⟩ := hrel k
  refine ⟨Presheaf.imageSieve (toArrowStabilizerQuotient G)
      ((arrowStabilizerQuotient G).obj.map h.op rk),
    Presheaf.imageSieve_mem (BigFppfOver.topology C S hS) _ (U := op V) _, ?_⟩
  intro W i hi
  obtain ⟨r, hr⟩ := hi
  refine ⟨r, ?_, ?_⟩
  · rw [← arrowStabilizerQuotientSource_app_toArrowStabilizerQuotient, hr]
    simp [NatTrans.naturality_apply, ← hrks]
  · rw [← arrowStabilizerQuotientTarget_app_toArrowStabilizerQuotient, hr]
    simp [NatTrans.naturality_apply, ← hrkt]

/-- **Stacks 06QJ, the geometric half of the implication (2) `⟹` (1).** The structure arrow
`[U/R] ⟶ X` of **Stacks 044R** of the groupoid read over `X = U/R'` makes the quotient stack a
gerbe over `X`.

The criterion is `AlgebraicGeometry.Stack.isGerbeOver_quotientStackToBase_of_locallyFull`
(**Stacks 06PE** for the 1-morphism of **Stacks 0DUH**); its surjectivity clause is Stacks 06PG
and its local-fullness clause is **Stacks 046O**, both in the sieve form the criterion asks
for. -/
@[stacks 06QJ "the implication (2) implies (1): the quotient stack is a gerbe over U/(R/S)"]
theorem isGerbeOver_quotientStackToBase_overArrowStabilizerQuotient
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (hX : IsAlgebraicSpace C S hS
      (Space.quotientSheaf (arrowStabilizerQuotientPreRelation G)).obj) :
    CategoryTheory.IsGerbeOver (BigFppfOver.topology C S hS)
      (fibredCategory C S hS (arrowStabilizerQuotientSpace G hX).obj).val.p
      (quotientStackToBase (overArrowStabilizerQuotient G hX)).toFunctor :=
  isGerbeOver_quotientStackToBase_of_locallyFull (overArrowStabilizerQuotient G hX)
    (exists_covering_lift_objects_toArrowStabilizerQuotientSpace G)
    (exists_covering_hom_arrows_of_toArrowStabilizerQuotientSpace_eq G)

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
