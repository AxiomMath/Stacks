module

public import StacksFrontier.AlgebraicGeometry.Descent.EffectivityAlongCoproduct
public import StacksFrontier.AlgebraicGeometry.Descent.EffectivityAlongFpqcCovering
public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardCoveringDisjointUnion
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardRefinement

/-!
# Descending types of morphisms over an affine base

Let `P` be a property of morphisms of schemes over a base which is stable under any base change
and preserved by finite disjoint unions, and let `τ` be one of fpqc, fppf, étale, smooth and
syntomic. If every descent datum relative to a surjective morphism of affine schemes which is
flat, flat of finite presentation, étale, smooth or syntomic according to `τ`, and whose member
has `P`, is effective, then every descent datum relative to a `τ`-covering of an *affine* scheme
whose members have `P` is effective.

## Main results

* `AlgebraicGeometry.DescentData.isFamilyEffective_of_isEmpty`: a descent datum relative to an
  empty family is effective.
* `AlgebraicGeometry.DescentData.isFamilyEffective_of_finiteAffine`: effectivity along a finite
  covering by affine schemes, from effectivity along the single morphism out of its disjoint
  union.
* `AlgebraicGeometry.DescentData.isFamilyEffective_affineBase_of_affineSingleton`: the affine
  case of Stacks 02W3 for the fppf, étale, smooth and syntomic coverings.
* `AlgebraicGeometry.DescentData.isFamilyEffective_affineBase_fpqc_of_affineSingleton`: the
  affine case of Stacks 02W3 for the fpqc coverings.

## Implementation notes

The three hypotheses of the source appear as the instance `P.IsStableUnderBaseChange`, as the
hypothesis on disjoint unions — stated for a nonempty finite family, as in the source, the empty
case being handled separately — and as the hypothesis on a single surjective morphism of affine
schemes, stated through `AlgebraicGeometry.DescentData.IsEffective`, the effectivity of a
descent datum relative to one morphism.

The four topologies other than fpqc are quantified over uniformly by
`AlgebraicGeometry.CoveringTopology`, whose associated morphism property
`AlgebraicGeometry.coveringMorphismProperty` is exactly the property the source attaches to `τ`
in its third hypothesis; the covering families are those of
`AlgebraicGeometry.Scheme.precoverage` of that property, which for the fppf and the étale case
is `AlgebraicGeometry.Scheme.fppfPrecoverage`, respectively
`AlgebraicGeometry.Scheme.etalePrecoverage`. The fpqc case is stated separately because the
fpqc coverings carry a quasi-compactness condition and so are not of that form, and because the
standard fpqc refinement is a separate theorem, Stacks 022E.

The reduction has two steps. The given covering of the affine base is refined by a standard
`τ`-covering, Stacks 03XA respectively Stacks 022E, and effectivity comes back along that
refinement because the refining family is an fpqc covering; the refined datum still has `P` on
its members, these being base changes of the original ones. Then the finite covering by affine
schemes is replaced by the single morphism out of its disjoint union, Stacks 023X: the disjoint
union of finitely many affine schemes is affine, the morphism out of it is surjective and has
the property attached to `τ`, and its member is the disjoint union of the original members, so
it has `P` by the disjoint-union hypothesis.

The case of a general base is deduced from these two statements in
`StacksFrontier.AlgebraicGeometry.Descent.DescendingTypesOfMorphismsGeneralBase`: the covering and
the datum are restricted to each affine open `V` of the base, the affine case gives a scheme
`X_V` over `V`, the restriction morphisms `X_{V'} ⟶ X_V` for `V' ⊆ V` come from the full
faithfulness of Stacks 02W0, and the `X_V` are glued by Stacks 01LH.

## References

* [Stacks Project, Tag 022E](https://stacks.math.columbia.edu/tag/022E)
* [Stacks Project, Tag 023X](https://stacks.math.columbia.edu/tag/023X)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
* [Stacks Project, Tag 03XA](https://stacks.math.columbia.edu/tag/03XA)
-/

@[expose] public section

noncomputable section

universe u v

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

namespace DescentData

/-- A descent datum relative to an empty family of morphisms with fixed target is effective. -/
theorem isFamilyEffective_of_isEmpty {ι : Type v} [IsEmpty ι] {S : Scheme.{u}}
    {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S} (D : DescentData f) : D.IsFamilyEffective :=
  ⟨Over.mk (𝟙 S), ⟨{ hom := { hom := fun i ↦ isEmptyElim i, comm := fun i ↦ isEmptyElim i }
                     inv := { hom := fun i ↦ isEmptyElim i, comm := fun i ↦ isEmptyElim i }
                     hom_inv_id := DescentData.hom_ext fun i ↦ isEmptyElim i
                     inv_hom_id := DescentData.hom_ext fun i ↦ isEmptyElim i }⟩⟩

/-- **Effectivity along a finite covering by affine schemes reduces to the morphism out of its
disjoint union.** Let `P` be stable under base change and preserved by nonempty finite disjoint
unions, and suppose every descent datum with `P` on its member, relative to a surjective
`Q`-morphism of affine schemes, is effective. Then every descent datum with `P` on its members,
relative to a finite family of affine schemes over an affine base whose disjoint union maps
surjectively and with `Q` to the base, is effective. -/
theorem isFamilyEffective_of_finiteAffine
    {P Q : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    (hcoprod : ∀ {J : Type u} [Finite J] [Nonempty J] {Y Z : J → Scheme.{u}}
      (g : ∀ j, Y j ⟶ Z j), (∀ j, P (g j)) → P (Limits.Sigma.map g))
    (haffine : ∀ {A T : Scheme.{u}} [IsAffine A] [IsAffine T] (a : A ⟶ T),
      Surjective a → Q a → ∀ E : DescentDatum a, P (E.obj ()).hom → E.IsEffective)
    {S : Scheme.{u}} [IsAffine S] {𝒱 : PreZeroHypercover.{u} S} [Finite 𝒱.I₀]
    (haff : ∀ k, IsAffine (𝒱.X k)) (hsurj : Surjective (Sigma.desc 𝒱.f))
    (hQ : Q (Sigma.desc 𝒱.f)) (E : DescentData 𝒱.f) (hP : ∀ k, P (E.obj k).hom) :
    E.IsFamilyEffective := by
  rcases isEmpty_or_nonempty 𝒱.I₀ with _ | _
  · exact isFamilyEffective_of_isEmpty E
  have : ∀ k, IsAffine (𝒱.X k) := haff
  have : IsAffine (∐ 𝒱.X) := inferInstance
  refine isFamilyEffective_of_coproduct 𝒱.f (isFamilyEffective_of_isEffective
    (haffine (Sigma.desc 𝒱.f) hsurj hQ _ ?_))
  have : IsIso ((familyCoproductEquivalence 𝒱.f).objIso E).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).mapIso
      ((familyCoproductEquivalence 𝒱.f).objIso E)).hom)
  rw [← Over.w ((familyCoproductEquivalence 𝒱.f).objIso E).hom,
    P.cancel_left_of_respectsIso]
  exact hcoprod _ hP

/-- The members of the descent datum pulled back along a refinement still have `P`, being base
changes of the original ones. -/
private theorem property_pullbackFunctor_ofRefinement
    {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange] {S : Scheme.{u}}
    {𝒱 𝒰 : PreZeroHypercover.{u} S} (α : 𝒱.HomOver 𝒰 (𝟙 S)) (D : DescentData 𝒰.f)
    (hP : ∀ i, P (D.obj i).hom) (k : 𝒱.I₀) :
    P (((MorphismOfSchemeFamilies.pullbackFunctor
      (MorphismOfSchemeFamilies.ofRefinement α)).functor.obj D).obj k).hom := by
  rw [(MorphismOfSchemeFamilies.pullbackFunctor
    (MorphismOfSchemeFamilies.ofRefinement α)).obj_eq D]
  exact MorphismProperty.baseChange_obj (α.h₀ k) (D.obj (α.s₀ k)) (hP _)

/-- **Stacks Project, Tag 02W3, the case of an affine base, for the fppf, étale, smooth and
syntomic coverings.** Let `P` be a property of morphisms of schemes over a base which is stable
under any base change and such that a nonempty finite disjoint union of morphisms with `P` again
has `P`. Let `τ` be one of fppf, étale, smooth and syntomic, and suppose that for every
surjective morphism of affine schemes which is flat of finite presentation, étale, smooth or
syntomic according to `τ`, every descent datum relative to it whose member has `P` is effective.
Then every descent datum relative to a `τ`-covering of an affine scheme whose members have `P`
is effective. -/
@[stacks 02W3 "the case of an affine base, for τ = fppf, étale, smooth and syntomic"]
theorem isFamilyEffective_affineBase_of_affineSingleton
    {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    (τ : CoveringTopology) (hτ : τ ≠ .zariski)
    (hcoprod : ∀ {J : Type u} [Finite J] [Nonempty J] {Y Z : J → Scheme.{u}}
      (g : ∀ j, Y j ⟶ Z j), (∀ j, P (g j)) → P (Limits.Sigma.map g))
    (haffine : ∀ {A T : Scheme.{u}} [IsAffine A] [IsAffine T] (a : A ⟶ T),
      Surjective a → coveringMorphismProperty τ a →
      ∀ E : DescentDatum a, P (E.obj ()).hom → E.IsEffective)
    {S : Scheme.{u}} [IsAffine S] (𝒰 : PreZeroHypercover.{u} S)
    (h𝒰 : 𝒰.presieve₀ ∈ Scheme.precoverage (coveringMorphismProperty τ) S)
    (D : DescentData 𝒰.f) (hP : ∀ i, P (D.obj i).hom) :
    D.IsFamilyEffective := by
  obtain ⟨V, φ, hstd⟩ := exists_standardCovering_refinement τ 𝒰 h𝒰
  have : Finite V.I₀ := hstd.finite_index
  have hsingle := IsStandardCovering.singleton_sigmaDesc_mem_precoverage τ hτ V.X V.f hstd
  rw [Scheme.singleton_mem_precoverage_iff] at hsingle
  have hfpqc : Presieve.ofArrows V.X V.f ∈ Scheme.fpqcPrecoverage S :=
    (ofArrows_mem_fpqcPrecoverage_iff_singleton_sigmaDesc_mem V.X V.f).mpr
      (IsStandardCovering.singleton_sigmaDesc_mem_fpqcPrecoverage τ V.X V.f hstd)
  let α : V.HomOver 𝒰 (𝟙 S) := (PreZeroHypercover.homOverIdEquivHom V 𝒰).symm φ
  refine isFamilyEffective_of_refinement_of_fpqcRefiningFamily α hfpqc
    (isFamilyEffective_of_finiteAffine hcoprod haffine hstd.affine_source
      ⟨hsingle.1⟩ hsingle.2 _ fun k ↦ ?_)
  exact property_pullbackFunctor_ofRefinement α D hP k

/-- **Stacks Project, Tag 02W3, the case of an affine base, for the fpqc coverings.** Let `P` be
a property of morphisms of schemes over a base which is stable under any base change and such
that a nonempty finite disjoint union of morphisms with `P` again has `P`. Suppose that for
every surjective flat morphism of affine schemes, every descent datum relative to it whose
member has `P` is effective. Then every descent datum relative to an fpqc covering of an affine
scheme whose members have `P` is effective. -/
@[stacks 02W3 "the case of an affine base, for τ = fpqc"]
theorem isFamilyEffective_affineBase_fpqc_of_affineSingleton
    {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    (hcoprod : ∀ {J : Type u} [Finite J] [Nonempty J] {Y Z : J → Scheme.{u}}
      (g : ∀ j, Y j ⟶ Z j), (∀ j, P (g j)) → P (Limits.Sigma.map g))
    (haffine : ∀ {A T : Scheme.{u}} [IsAffine A] [IsAffine T] (a : A ⟶ T),
      Surjective a → Flat a → ∀ E : DescentDatum a, P (E.obj ()).hom → E.IsEffective)
    {S : Scheme.{u}} [IsAffine S] (𝒰 : PreZeroHypercover.{u} S)
    (h𝒰 : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage S)
    (D : DescentData 𝒰.f) (hP : ∀ i, P (D.obj i).hom) :
    D.IsFamilyEffective := by
  obtain ⟨𝒱, φ, hfin, hfpqc, -⟩ :=
    exists_finite_affineCover_flat_hom_of_mem_fpqcPrecoverage 𝒰 h𝒰
  let W : PreZeroHypercover.{u} S := 𝒱.cover.toPreZeroHypercover
  have : Finite W.I₀ := hfin
  have : ∀ k, Flat (W.f k) := fun k ↦ 𝒱.map_prop k
  let α : W.HomOver 𝒰 (𝟙 S) := (PreZeroHypercover.homOverIdEquivHom W 𝒰).symm φ
  refine isFamilyEffective_of_refinement_of_fpqcRefiningFamily α hfpqc
    (isFamilyEffective_of_finiteAffine (𝒱 := W) hcoprod haffine
      (fun k ↦ show IsAffine (Spec (𝒱.X k)) from inferInstance)
      (Surjective.sigmaDesc_of_union_range_eq_univ
        (Set.iUnion_eq_univ_iff.mpr fun x ↦ ⟨𝒱.idx x, 𝒱.covers x⟩))
      inferInstance _ fun k ↦ ?_)
  exact property_pullbackFunctor_ofRefinement α D hP k

end DescentData

end AlgebraicGeometry

end

end
