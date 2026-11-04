module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EtaleLocalizationStabilizerMembership

/-!
# The stabilizer containment of Stacks 0DTC

Stacks 0DTC asserts, in the splitting situation of Stacks 0DTB at a point `u` of the object
scheme, the existence of an algebraic space `U'`, an étale morphism `g : U' ⟶ U` and a point
`u' : Spec κ(u) ⟶ U'` over `u` such that the restriction `R' = R|_{U'}` is **split** over `u'`.
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationStabilizerMembership.lean`
produces `U'`, `g` and `u'`; this file proves the fourth assertion, that `R'` is split over
`u'`, and assembles the tag.

## The obstruction, and the way around it

`AlgebraicGeometry.Space.FinitePartUniversalOpen.target_eq_of_cutsOut` of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationArrowContainment.lean` derives
the arrow containment of Stacks 03FM from a predicate `P` on arrows which cuts out the open
subspaces named by two sections `x₁`, `x₂` of `U'` and which **depends on an arrow only through
its target**.  For the open of Situation 0DTB that fails: the predicate the membership criterion
forces is membership in the set-theoretic image of `AlgebraicGeometry.stabilizerArrow` over `u`,
and a point of `U ×_S U` whose two projections are both `u` need not lie on the diagonal, so
that predicate is not target-invariant.

The repair is **not** an extensionality principle for
`AlgebraicGeometry.Space.FiniteOpenSubspace` restricted to reduced test objects.  Two
observations remove the obstruction instead.

*The two sections coincide.*  In Stacks 03FM the hypotheses are `s'(r') = u'` and `t'(r') = u'`
for a point `r'` of `|R'|`, two equalities of *points*, which after amalgamation become
restrictions of `u'` along two different morphisms `Spec Ω ⟶ Spec κ(u)`; that is why
`target_eq_of_cutsOut` is stated for a pair `m₁`, `m₂`.  The splitting condition of Stacks 04RK
(2) is instead a condition on a point of the **stabilizer**, whose source and target are equal
*as morphisms* by `AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerArrow_source` and
`stabilizerArrow_target`.  One field extension therefore suffices and `m₁ = m₂`.

*Relative to a fixed source, the predicate is target-invariant.*  Membership in the
stabilizer-supported open is a pointwise condition, hence depends on a test object only through
its topological space, so it may be read on the spectra of the residue fields of the test
object — which are reduced, where
`AlgebraicGeometry.Space.mem_fiberOpen_iff_target_of_isReduced` applies.  That gives
`AlgebraicGeometry.Space.mem_fiberOpen_iff_residue_target`: for a section of the arrow scheme
whose source is a prescribed morphism to `Spec κ(u)`, pointwise membership in the
stabilizer-supported open is the condition that its target agree with that prescribed morphism
on every residue field.  This is manifestly a condition on the target of the arrow *and the
prescribed source*, and in it the arrow enters only through its target.

So the predicate has to be allowed to see the section of `U'` — it is a predicate on *pairs* — and
with `m₁ = m₂` that is enough:
`AlgebraicGeometry.Space.FinitePartUniversalOpen.CutsOutRel` and
`AlgebraicGeometry.Space.FinitePartUniversalOpen.target_eq_of_cutsOutRel` are the two-argument
forms of `CutsOut` and `target_eq_of_cutsOut`, with the same proofs.

## Main definitions

* `AlgebraicGeometry.Space.FinitePartUniversalOpen.CutsOutRel`: a predicate on a *pair* of a
  section of the base and an arrow cuts out the open subspace which a section of `U'` names.
* `AlgebraicGeometry.Space.ResidueTargetEq` and `AlgebraicGeometry.Space.ResidueTargetArrow`:
  the predicate the stabilizer-supported open cuts out — the target of the arrow and the
  prescribed morphism to `Spec κ(u)` agree on every residue field of the test object.
* `AlgebraicGeometry.Space.stabilizerFibreValuedPoint`: **the point `u'` of `|U'|`** in
  Situation 0DTB.
* `AlgebraicGeometry.Space.restrictedSplitting`: **`Z_univ` as a splitting of `R|_{U'}` at
  `u'`**, which is condition (2) of Stacks 04RK.

## Main results

* `AlgebraicGeometry.Space.FinitePartUniversalOpen.target_eq_of_cutsOutRel` and
  `exists_toRestriction_eq_of_cutsOutRel`: the target computation and the arrow containment on
  sections, for a predicate on pairs and a single section of `U'`.
* `AlgebraicGeometry.Space.mem_fiberOpen_iff_residue_target`: **pointwise membership in the
  stabilizer-supported open is agreement of the target with the source on residue fields** — the
  reduced test objects which `mem_fiberOpen_iff_target_of_isReduced` needs are the residue field
  spectra of the test object.
* `AlgebraicGeometry.Space.cutsOutRel_stabilizerFibrePoint`: **that predicate cuts out the open
  subspace which the restriction of `u'` names**.
* `AlgebraicGeometry.Space.targetInvariant_residueTargetArrow`: it depends on an arrow only
  through its target.
* `AlgebraicGeometry.Space.contains_stabilizer_stabilizerFibrePoint`: **the stabilizer
  containment**, the `contains_stabilizer` field of
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Splitting`.
* `AlgebraicGeometry.Space.isSplitAt_stabilizerFibreValuedPoint`: `R|_{U'}` is split at `u'`.
* `Stacks.Groupoids.GroupoidScheme.exists_split_of_splittingSituation`: **Stacks 0DTC**, all
  four assertions, in Situation 0DTB.

## Implementation notes

### Carried hypotheses

The final statement carries only `hS`, `hU`, `hR`, `hP`, `hK` — the standing requirement that
the big fppf site contain the base, object, arrow and composable-pair schemes and `Spec κ(u)` —
together with the fields of `AlgebraicGeometry.Space.SplittingSituation`, which is Situation
0DTB itself: the separatedness and local finite type of the source and target through
`AlgebraicGeometry.Space.realizationFinitePart`, and the finiteness of the fibre of the
stabilizer over `u` with the quasi-finiteness of `s` along it through
`AlgebraicGeometry.Space.SplittingSituation.exists_fiberOpens_stabilizer`.  It is
`AlgebraicGeometry.Space.SplittingSituation` and **not**
`AlgebraicGeometry.Space.StrongSplittingSituation`: the standing hypothesis is the one of the
tag, not the stronger one of Stacks 04RL.

### The chain to the point is retranscribed

`AlgebraicGeometry.Space.objectsPair_restrict_fibrePoint_isBaseChange`,
`exists_lift_universalOpen_fibrePoint_iff` and `base_eq_of_fibrePoint` of
`EtaleLocalizationArrowContainment.lean` take the support hypothesis `hW` of Situation 04RL as
an argument, and a different hypothesis cannot be substituted into a declaration that names `hW`
in its type.  The four declarations
`AlgebraicGeometry.Space.objectsInclusion_app_stabilizerFibrePoint`,
`stabilizerFibrePoint_comp_objectsInclusion`,
`objectsPair_restrict_stabilizerFibrePoint_isBaseChange` and
`base_eq_of_stabilizerFibrePoint` are therefore the same statements for the point of Situation
0DTB, with their proofs transcribed unchanged and the point replaced.

### Why the predicate is stated with `CategoryTheory.Functor.preimage`

`AlgebraicGeometry.Space.ArrowToPoint` of `EtaleLocalizationArrowContainment.lean` quantifies
existentially over a morphism of the site whose Yoneda image is the given morphism of
presheaves.  Here the predicate must be invariant under replacing an arrow by one with the same
target, and an existential statement about the arrow would have to be transported by hand.
Using `CategoryTheory.Functor.preimage` of the full and faithful Yoneda embedding instead makes
the predicate a *function* of the target, so the invariance is
`CategoryTheory.iff_of_eq (congrArg _ h)` and the two layers
`AlgebraicGeometry.Space.ResidueTargetEq`, `ResidueTargetArrow` exist exactly to expose that
function.

*No attribute is attached.*  The Stacks attribute for tag 0DTC belongs on
`Stacks.Groupoids.GroupoidScheme.exists_split_of_splittingSituation`, which proves all four
assertions of the tag in Situation 0DTB.

## References

* [Stacks Project, Tag 03FM](https://stacks.math.columbia.edu/tag/03FM)
* [Stacks Project, Tag 04PE](https://stacks.math.columbia.edu/tag/04PE)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
* [Stacks Project, Tag 04RU](https://stacks.math.columbia.edu/tag/04RU)
* [Stacks Project, Tag 0DTB](https://stacks.math.columbia.edu/tag/0DTB)
* [Stacks Project, Tag 0DTC](https://stacks.math.columbia.edu/tag/0DTC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open GroupoidInAlgebraicSpaces

section Generic

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS B}

namespace FinitePartUniversalOpen

/-- **A predicate on pairs cuts out the open subspace which a section of the object space of the
finite part names** when membership in `Z_univ` over that section, tested on morphisms out of
representable presheaves, is equivalent to it.

This is `AlgebraicGeometry.Space.FinitePartUniversalOpen.CutsOut` with the predicate allowed to
see the section of the base as well as the arrow.  The extra argument is what Situation 0DTB
needs: the open subspace it names is cut out by the condition that the target of the arrow agree
with the prescribed source, which is not a condition on the arrow alone. -/
def CutsOutRel (F : FinitePartUniversalOpen G)
    {Y₀ : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (P : ∀ V' : BigFppfOver C S hS, (yoneda.obj V' ⟶ Y₀) →
      (yoneda.obj V' ⟶ G.arrows.obj) → Prop)
    (m : Y₀ ⟶ F.objects.obj) : Prop :=
  ∀ (V' : BigFppfOver C S hS) (μ : yoneda.obj V' ⟶ F.objects.obj)
    (ψ : yoneda.obj V' ⟶ G.arrows.obj) (φ : yoneda.obj V' ⟶ Y₀), μ = φ ≫ m →
    ∀ hc : μ ≫ F.universalOpen.toBase.hom = ψ ≫ G.source.hom,
      ((∃ n : yoneda.obj V' ⟶ F.universalOpen.subspace.toFunctor,
          n ≫ F.universalOpen.subspace.ι = pullback.lift μ ψ hc) ↔ P V' φ ψ)

/-- **An arrow of `R` satisfying the cutting predicate lifts to `Z_univ`**, with a prescribed
section of the object space as its source and the given arrow as its underlying arrow.  This is
`AlgebraicGeometry.Space.FinitePartUniversalOpen.exists_arrows_of_cutsOut` for a predicate on
pairs. -/
theorem exists_arrows_of_cutsOutRel (F : FinitePartUniversalOpen G)
    {Y₀ : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    {P : ∀ V' : BigFppfOver C S hS, (yoneda.obj V' ⟶ Y₀) →
      (yoneda.obj V' ⟶ G.arrows.obj) → Prop}
    {m : Y₀ ⟶ F.objects.obj} (hm : F.CutsOutRel P m) (V' : BigFppfOver C S hS)
    (μ : yoneda.obj V' ⟶ F.objects.obj) (ψ : yoneda.obj V' ⟶ G.arrows.obj)
    (φ : yoneda.obj V' ⟶ Y₀) (hμ : μ = φ ≫ m)
    (hs : ψ ≫ G.source.hom = μ ≫ F.universalOpen.toBase.hom) (hP : P V' φ ψ) :
    ∃ a : yoneda.obj V' ⟶ F.arrows.obj,
      a ≫ F.source.hom = μ ∧ a ≫ F.arrowMap.hom = ψ := by
  obtain ⟨n, hn⟩ := (hm V' μ ψ φ hμ hs.symm).2 hP
  refine ⟨n, ?_, ?_⟩
  · exact (Category.assoc n F.universalOpen.subspace.ι
      (pullback.fst F.universalOpen.toBase.hom G.source.hom)).symm.trans
      ((congrArg (fun k => k ≫ pullback.fst F.universalOpen.toBase.hom G.source.hom)
        hn).trans (pullback.lift_fst _ _ _))
  · exact (Category.assoc n F.universalOpen.subspace.ι
      (pullback.snd F.universalOpen.toBase.hom G.source.hom)).symm.trans
      ((congrArg (fun k => k ≫ pullback.snd F.universalOpen.toBase.hom G.source.hom)
        hn).trans (pullback.lift_snd _ _ _))

/-- **The target of a lift to `Z_univ` is the section of the object space it starts from.**  Let
`P` be a predicate on pairs which depends on an arrow only through its target, cutting out the
open subspace which a section `x` of the object space of the finite part names, and let `a` be a
section of `Z_univ` whose source is `x` and whose arrow has target the image of `x`.  Then the
target of `a` is `x` again.

This is `AlgebraicGeometry.Space.FinitePartUniversalOpen.target_eq_of_cutsOut` with the two
sections of the object space taken equal and the predicate allowed to see the section of the
base; the proof is the same.  Taking them equal is what the splitting condition of Stacks 04RK
(2) supplies and the strong splitting condition of Stacks 04RK (1) does not: the source and the
target of a point of the stabilizer agree as morphisms, not merely as points. -/
theorem target_eq_of_cutsOutRel (F : FinitePartUniversalOpen G) (V : BigFppfOver C S hS)
    (P : ∀ V' : BigFppfOver C S hS, (yoneda.obj V' ⟶ yoneda.obj V) →
      (yoneda.obj V' ⟶ G.arrows.obj) → Prop)
    (hinv : ∀ (V' : BigFppfOver C S hS) (φ₀ : yoneda.obj V' ⟶ yoneda.obj V)
      (ψ₁ ψ₂ : yoneda.obj V' ⟶ G.arrows.obj),
      ψ₁ ≫ G.target.hom = ψ₂ ≫ G.target.hom → (P V' φ₀ ψ₁ ↔ P V' φ₀ ψ₂))
    (m : yoneda.obj V ⟶ F.objects.obj) (hm : F.CutsOutRel P m)
    (a : yoneda.obj V ⟶ F.arrows.obj) (hsrc : a ≫ F.source.hom = m)
    (htgt : (a ≫ F.arrowMap.hom) ≫ G.target.hom = m ≫ F.universalOpen.toBase.hom) :
    a ≫ F.target.hom = m := by
  have hbase : (F.targetPairAt V a).toBase.hom = (F.objectsPair V m).toBase.hom :=
    ((F.targetPairAt_isBaseChange V a).1.trans
      ((congrArg (fun z => a ≫ z) F.targetPair_toBase_hom).trans
        ((Category.assoc a F.arrowMap.hom G.target.hom).symm.trans htgt))).trans
      (F.objectsPair_isBaseChange V m).1.symm
  have hb : (F.targetPairAt V a).toBase = (F.objectsPair V m).toBase :=
    ObjectProperty.hom_ext _ hbase
  have hcond : pullback.fst (F.targetPairAt V a).toBase.hom G.source.hom ≫
      (F.objectsPair V m).toBase.hom =
      pullback.snd (F.targetPairAt V a).toBase.hom G.source.hom ≫ G.source.hom :=
    (congrArg (fun z => pullback.fst (F.targetPairAt V a).toBase.hom G.source.hom ≫ z)
      hbase).symm.trans pullback.condition
  have key : ∀ (V' : BigFppfOver C S hS) (φ₀ : yoneda.obj V' ⟶ yoneda.obj V)
      (ψ₀ : yoneda.obj V' ⟶ G.arrows.obj)
      (hc₀ : φ₀ ≫ (F.targetPairAt V a).toBase.hom = ψ₀ ≫ G.source.hom)
      (hcR : φ₀ ≫ (F.objectsPair V m).toBase.hom = ψ₀ ≫ G.source.hom),
      (∃ n : yoneda.obj V' ⟶ (F.targetPairAt V a).subspace.toFunctor,
          n ≫ (F.targetPairAt V a).subspace.ι = pullback.lift φ₀ ψ₀ hc₀) ↔
        ∃ n' : yoneda.obj V' ⟶ (F.objectsPair V m).subspace.toFunctor,
          n' ≫ (F.objectsPair V m).subspace.ι = pullback.lift φ₀ ψ₀ hcR := by
    intro V' φ₀ ψ₀ hc₀ hcR
    have hcA : (φ₀ ≫ a) ≫ F.targetPair.toBase.hom = ψ₀ ≫ G.source.hom :=
      (Category.assoc φ₀ a F.targetPair.toBase.hom).trans
        ((congrArg (fun z => φ₀ ≫ z) (F.targetPairAt_isBaseChange V a).1.symm).trans hc₀)
    have hcψ : (φ₀ ≫ m) ≫ F.universalOpen.toBase.hom = ψ₀ ≫ G.source.hom :=
      (Category.assoc φ₀ m F.universalOpen.toBase.hom).trans
        ((congrArg (fun z => φ₀ ≫ z) (F.objectsPair_isBaseChange V m).1.symm).trans hcR)
    obtain ⟨j, hj, hjsnd⟩ := (F.targetPairAt_isBaseChange V a).2
    have stepA := exists_lift_of_pairSquares G.source F.targetPair (F.targetPairAt V a) a j hj
      hjsnd φ₀ ψ₀ hc₀ hcA
    have hcU := F.targetPair_ambient_cond (φ₀ ≫ a) ψ₀ hcA
    have hUU := F.untwist_base_condition (φ₀ ≫ a) ψ₀ hcU
    have hs' : (φ₀ ≫ a) ≫ F.source.hom = φ₀ ≫ m :=
      (Category.assoc φ₀ a F.source.hom).trans (congrArg (fun z => φ₀ ≫ z) hsrc)
    have hUU' : (φ₀ ≫ m) ≫ F.universalOpen.toBase.hom =
        composeMor G ψ₀ ((φ₀ ≫ a) ≫ F.arrowMap.hom) hcU ≫ G.source.hom :=
      (congrArg (fun z => z ≫ F.universalOpen.toBase.hom) hs'.symm).trans hUU
    have hlift : pullback.lift ((φ₀ ≫ a) ≫ F.source.hom)
          (composeMor G ψ₀ ((φ₀ ≫ a) ≫ F.arrowMap.hom) hcU) hUU =
        pullback.lift (φ₀ ≫ m)
          (composeMor G ψ₀ ((φ₀ ≫ a) ≫ F.arrowMap.hom) hcU) hUU' :=
      pullback_lift_congr _ _ _ _ hUU hUU' hs' rfl
    have stepBC : (∃ n' : yoneda.obj V' ⟶ F.targetPair.subspace.toFunctor,
          n' ≫ F.targetPair.subspace.ι = pullback.lift (φ₀ ≫ a) ψ₀ hcA) ↔
        ∃ n'' : yoneda.obj V' ⟶ F.universalOpen.subspace.toFunctor,
          n'' ≫ F.universalOpen.subspace.ι = pullback.lift (φ₀ ≫ m)
            (composeMor G ψ₀ ((φ₀ ≫ a) ≫ F.arrowMap.hom) hcU) hUU' := by
      rw [← hlift]
      exact (exists_lift_iff_mem _ V' _).trans
        ((mem_iff_mem_of_preimage_eq F.targetPair.subspace F.universalOpen.subspace V' _ _
          (F.targetPair_preimage_untwist (φ₀ ≫ a) ψ₀ hcA hcU hUU)).trans
          (exists_lift_iff_mem _ V' _).symm)
    exact stepA.trans (stepBC.trans
      ((hm V' (φ₀ ≫ m) (composeMor G ψ₀ ((φ₀ ≫ a) ≫ F.arrowMap.hom) hcU) φ₀ rfl
          hUU').trans
        ((hinv V' φ₀ (composeMor G ψ₀ ((φ₀ ≫ a) ≫ F.arrowMap.hom) hcU) ψ₀
            (composeMor_comp_target G _ _ hcU)).trans
          ((hm V' (φ₀ ≫ m) ψ₀ φ₀ rfl hcψ).symm.trans
            (F.exists_lift_universalOpen_iff V m φ₀ ψ₀ hcR hcψ).symm))))
  have hpair : F.targetPairAt V a = F.objectsPair V m := by
    refine pair_eq_of_exists_lift_iff G.source _ _ hb hcond ?_
    intro V' k
    have hc₀ : (k ≫ pullback.fst (F.targetPairAt V a).toBase.hom G.source.hom) ≫
        (F.targetPairAt V a).toBase.hom =
        (k ≫ pullback.snd (F.targetPairAt V a).toBase.hom G.source.hom) ≫ G.source.hom :=
      (Category.assoc k (pullback.fst (F.targetPairAt V a).toBase.hom G.source.hom)
          (F.targetPairAt V a).toBase.hom).trans
        ((congrArg (fun z => k ≫ z) pullback.condition).trans
          (Category.assoc k (pullback.snd (F.targetPairAt V a).toBase.hom G.source.hom)
            G.source.hom).symm)
    have hcR : (k ≫ pullback.fst (F.targetPairAt V a).toBase.hom G.source.hom) ≫
        (F.objectsPair V m).toBase.hom =
        (k ≫ pullback.snd (F.targetPairAt V a).toBase.hom G.source.hom) ≫ G.source.hom :=
      (congrArg (fun z => (k ≫ pullback.fst (F.targetPairAt V a).toBase.hom
        G.source.hom) ≫ z) hbase).symm.trans hc₀
    have hk : k = pullback.lift
        (k ≫ pullback.fst (F.targetPairAt V a).toBase.hom G.source.hom)
        (k ≫ pullback.snd (F.targetPairAt V a).toBase.hom G.source.hom) hc₀ :=
      eq_pullback_lift_fst_snd k hc₀
    have hkκ : k ≫ pullback.lift
          (pullback.fst (F.targetPairAt V a).toBase.hom G.source.hom)
          (pullback.snd (F.targetPairAt V a).toBase.hom G.source.hom) hcond =
        pullback.lift (k ≫ pullback.fst (F.targetPairAt V a).toBase.hom G.source.hom)
          (k ≫ pullback.snd (F.targetPairAt V a).toBase.hom G.source.hom) hcR :=
      pullback.hom_ext
        ((Category.assoc k _ _).trans
          ((congrArg (fun z => k ≫ z) (pullback.lift_fst _ _ hcond)).trans
            (pullback.lift_fst _ _ hcR).symm))
        ((Category.assoc k _ _).trans
          ((congrArg (fun z => k ≫ z) (pullback.lift_snd _ _ hcond)).trans
            (pullback.lift_snd _ _ hcR).symm))
    refine Iff.trans (iff_of_eq (congrArg
      (fun z => ∃ n : yoneda.obj V' ⟶ (F.targetPairAt V a).subspace.toFunctor,
        n ≫ (F.targetPairAt V a).subspace.ι = z) hk))
      (Iff.trans (key V' _ _ hc₀ hcR) (iff_of_eq (congrArg
        (fun z => ∃ n' : yoneda.obj V' ⟶ (F.objectsPair V m).subspace.toFunctor,
          n' ≫ (F.objectsPair V m).subspace.ι = z) hkκ.symm)))
  refine F.objects_hom_ext _ _ ?_
  rw [Category.assoc, F.target_comp_objectsInclusion]
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_comp]
  exact Equiv.injective ((finiteOpenSubspacePresheaf C S hS G.source).sections V) hpair

/-- The underlying arrow of a section of `R|_{U'}` with source lift `m` has source `m` followed by
the étale projection `g`. -/
private theorem restriction_arrows_comp_source (F : FinitePartUniversalOpen G)
    {V : BigFppfOver C S hS}
    (w : yoneda.obj V ⟶ (GroupoidInAlgebraicSpaces.restrictionArrows G F.objectProjection).obj)
    {m : yoneda.obj V ⟶ F.objects.obj}
    (hs : w ≫ (GroupoidInAlgebraicSpaces.restrictionSource G F.objectProjection).hom = m) :
    (w ≫ (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows G F.objectProjection).hom) ≫
      G.source.hom = m ≫ F.universalOpen.toBase.hom := by
  rw [← hs, F.universalOpen_toBase_hom, Category.assoc, Category.assoc]
  exact (congrArg (w ≫ ·) (congrArg (fun z : _ ⟶ G.objects => z.hom)
    (GroupoidInAlgebraicSpaces.restriction_condition G F.objectProjection))).symm

/-- The underlying arrow of a section of `R|_{U'}` with target lift `m` has target `m` followed by
the étale projection `g`. -/
private theorem restriction_arrows_comp_target (F : FinitePartUniversalOpen G)
    {V : BigFppfOver C S hS}
    (w : yoneda.obj V ⟶ (GroupoidInAlgebraicSpaces.restrictionArrows G F.objectProjection).obj)
    {m : yoneda.obj V ⟶ F.objects.obj}
    (ht : w ≫ (GroupoidInAlgebraicSpaces.restrictionTarget G F.objectProjection).hom = m) :
    (w ≫ (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows G F.objectProjection).hom) ≫
      G.target.hom = m ≫ F.universalOpen.toBase.hom := by
  rw [← ht, F.universalOpen_toBase_hom, Category.assoc, Category.assoc]
  exact congrArg (w ≫ ·) (congrArg (fun z : _ ⟶ G.objects => z.hom)
    (GroupoidInAlgebraicSpaces.restriction_condition' G F.objectProjection))

/-- **The arrow containment of Stacks 04RK (2), stated on sections.**  Let `P` be a predicate on
pairs depending on an arrow only through its target and cutting out the open subspace which a
section `x` of the object space of the finite part names.  Then every section of the arrow space
of the restriction `R|_{U'}` whose source lift and target lift are both `x` and whose underlying
arrow satisfies `P` comes from a section of `Z_univ` along `(f, t', s') : Z_univ ⟶ R'`.

This is `AlgebraicGeometry.Space.FinitePartUniversalOpen.exists_toRestriction_eq` with the two
sections of the object space taken equal and the predicate allowed to see the section of the
base. -/
theorem exists_toRestriction_eq_of_cutsOutRel (F : FinitePartUniversalOpen G)
    (V : BigFppfOver C S hS)
    (P : ∀ V' : BigFppfOver C S hS, (yoneda.obj V' ⟶ yoneda.obj V) →
      (yoneda.obj V' ⟶ G.arrows.obj) → Prop)
    (hinv : ∀ (V' : BigFppfOver C S hS) (φ₀ : yoneda.obj V' ⟶ yoneda.obj V)
      (ψ₁ ψ₂ : yoneda.obj V' ⟶ G.arrows.obj),
      ψ₁ ≫ G.target.hom = ψ₂ ≫ G.target.hom → (P V' φ₀ ψ₁ ↔ P V' φ₀ ψ₂))
    (m : yoneda.obj V ⟶ F.objects.obj) (hm : F.CutsOutRel P m)
    (w : yoneda.obj V ⟶
      (GroupoidInAlgebraicSpaces.restrictionArrows G F.objectProjection).obj)
    (hs : w ≫ (GroupoidInAlgebraicSpaces.restrictionSource G F.objectProjection).hom = m)
    (ht : w ≫ (GroupoidInAlgebraicSpaces.restrictionTarget G F.objectProjection).hom = m)
    (hP : P V (𝟙 (yoneda.obj V)) (w ≫
      (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows G F.objectProjection).hom)) :
    ∃ b : yoneda.obj V ⟶ F.arrows.obj, b ≫ F.toRestriction.hom = w := by
  obtain ⟨a, hasrc, haarr⟩ := F.exists_arrows_of_cutsOutRel hm V m
    (w ≫ (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows G F.objectProjection).hom)
    (𝟙 (yoneda.obj V)) (Category.id_comp m).symm
    (restriction_arrows_comp_source F w hs) hP
  have hatgt : a ≫ F.target.hom = m :=
    F.target_eq_of_cutsOutRel V P hinv m hm a hasrc
      ((congrArg (fun z => z ≫ G.target.hom) haarr).trans
        (restriction_arrows_comp_target F w ht))
  have key : ∀ {Y : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
      (k : (GroupoidInAlgebraicSpaces.restrictionArrows G F.objectProjection).obj ⟶ Y)
      (j : F.arrows.obj ⟶ Y) (x : yoneda.obj V ⟶ Y), F.toRestriction.hom ≫ k = j →
      a ≫ j = x → w ≫ k = x →
      k.app (Opposite.op V) (yonedaEquiv (a ≫ F.toRestriction.hom)) =
        k.app (Opposite.op V) (yonedaEquiv w) := by
    rintro Y k j x rfl h₁ h₂
    rw [← yonedaEquiv_comp, ← yonedaEquiv_comp]
    exact congrArg yonedaEquiv ((Category.assoc _ _ _).trans (h₁.trans h₂.symm))
  refine ⟨a, yonedaEquiv.injective ?_⟩
  refine restrictionArrows_ext F.objectProjection (Opposite.op V) _ _ ?_ ?_ ?_
  · exact key _ _ _ (congrArg (·.hom) F.toRestriction_comp_restrictionSource) hasrc hs
  · exact key _ _ _ (congrArg (·.hom) F.toRestriction_comp_arrowsToArrows) haarr rfl
  · exact key _ _ _ (congrArg (·.hom) F.toRestriction_comp_restrictionTarget) hatgt ht

end FinitePartUniversalOpen

end Generic

/-! ### The predicate cut out by the stabilizer-supported open -/

section Fibre

variable {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
  (C : BigFppfSite.{u}) (hS : C.Contains S) (hU : C.Contains G.objects.left)
  (hR : C.Contains G.arrows.left) (u : G.objects.left)
  (hK : C.Contains (Spec (G.objects.left.residueField u)))
  (hP : C.Contains (pullback G.source G.target).left)
  (W : (G.source.left.fiber u).Opens)
  (hWfin : AlgebraicGeometry.IsFinite (W.ι ≫ G.source.left.fiberToSpecResidueField u))
  (hWstab : ∀ x : G.source.left.fiber u, x ∈ W ↔ ∃ g : (stabilizer G).left,
    (stabilizer G).hom g = u ∧ stabilizerArrow G g = G.source.left.fiberι u x)

include hWstab in
/-- **Pointwise membership in the stabilizer-supported open is the agreement of the target of the
arrow with its prescribed source on every residue field of the test scheme.**

Membership is a pointwise condition, so it may be tested one point at a time, and at a point `y`
it is a condition on the restriction of the section along `Spec κ(y) ⟶ T`, whose source is the
spectrum of a field and therefore reduced.  On a reduced test scheme
`AlgebraicGeometry.Space.mem_fiberOpen_iff_target_of_isReduced` identifies membership with the
equality of the target and the source as morphisms, and that is the equation stated here.

This is the form in which the condition becomes invariant under replacing an arrow by one with
the same target: the right-hand side mentions the arrow only through `r ≫ t`. -/
theorem mem_fiberOpen_iff_residue_target {T : Scheme.{u}} (r : T ⟶ G.arrows.left)
    (k : T ⟶ Spec (G.objects.left.residueField u))
    (hsrc : r ≫ G.source.left = k ≫ G.objects.left.fromSpecResidueField u) :
    (∀ y : T, ∃ x : G.source.left.fiber u, x ∈ W ∧
        G.source.left.fiberι u x = r y) ↔
      ∀ y : T, T.fromSpecResidueField y ≫ r ≫ G.target.left =
        T.fromSpecResidueField y ≫ k ≫ G.objects.left.fromSpecResidueField u := by
  refine forall_congr' fun y => ?_
  have hs' : (T.fromSpecResidueField y ≫ r) ≫ G.source.left =
      (T.fromSpecResidueField y ≫ k) ≫ G.objects.left.fromSpecResidueField u := by
    rw [Category.assoc, Category.assoc, hsrc]
  have key := mem_fiberOpen_iff_target_of_isReduced G u W hWstab
    (T.fromSpecResidueField y ≫ r) (T.fromSpecResidueField y ≫ k) hs'
  have hassoc : ((T.fromSpecResidueField y ≫ r) ≫ G.target.left =
        (T.fromSpecResidueField y ≫ k) ≫ G.objects.left.fromSpecResidueField u) ↔
      (T.fromSpecResidueField y ≫ r ≫ G.target.left =
        T.fromSpecResidueField y ≫ k ≫ G.objects.left.fromSpecResidueField u) := by
    rw [Category.assoc, Category.assoc]
  have hy : ∀ z, (T.fromSpecResidueField y ≫ r) z = r y := fun z =>
    (Scheme.Hom.comp_apply (T.fromSpecResidueField y) r z).trans
      (congrArg r (Scheme.fromSpecResidueField_apply y z))
  refine Iff.trans ⟨fun hx z => ?_, fun hz => ?_⟩ (key.trans hassoc)
  · obtain ⟨x, hxW, hxr⟩ := hx
    exact ⟨x, hxW, hxr.trans (hy z).symm⟩
  · obtain ⟨x, hxW, hxr⟩ := hz (IsLocalRing.closedPoint _)
    exact ⟨x, hxW, hxr.trans (hy _)⟩

/-- **The predicate which the stabilizer-supported open cuts out**, as a condition on the target
of the arrow and a section of the base: the two agree on every residue field of the test object,
after the base section is composed with the given morphism to `Spec κ(u)`.

The two morphisms of presheaves are read as morphisms of the site through
`CategoryTheory.Functor.preimage` of the Yoneda embedding, which is full and faithful, so that
the condition is a *function* of the target rather than an existential statement about it.  That
is what makes `AlgebraicGeometry.Space.targetInvariant_residueTargetArrow` a rewriting. -/
def ResidueTargetEq (V : BigFppfOver C S hS)
    (h : V ⟶ schemeSiteObject C hS (X := residueOver G u) hK)
    (V' : BigFppfOver C S hS) (φ : yoneda.obj V' ⟶ yoneda.obj V)
    (θ : yoneda.obj V' ⟶ yoneda.obj (schemeSiteObject C hS (X := G.objects) hU)) : Prop :=
  ∀ y : (BigFppfOver.toScheme C S hS).obj V',
    ((BigFppfOver.toScheme C S hS).obj V').fromSpecResidueField y ≫
        (BigFppfOver.toScheme C S hS).map (yoneda.preimage θ) =
      ((BigFppfOver.toScheme C S hS).obj V').fromSpecResidueField y ≫
        (BigFppfOver.toScheme C S hS).map (yoneda.preimage φ ≫ h) ≫
          G.objects.left.fromSpecResidueField u

/-- The predicate of `AlgebraicGeometry.Space.ResidueTargetEq` read on an arrow, through its
target.  This is the predicate on pairs which the stabilizer-supported open of Situation 0DTB
cuts out, in the sense of
`AlgebraicGeometry.Space.FinitePartUniversalOpen.CutsOutRel`. -/
def ResidueTargetArrow (V : BigFppfOver C S hS)
    (h : V ⟶ schemeSiteObject C hS (X := residueOver G u) hK)
    (V' : BigFppfOver C S hS) (φ : yoneda.obj V' ⟶ yoneda.obj V)
    (ψ : yoneda.obj V' ⟶ (G.realization C hS hU hR hP).arrows.obj) : Prop :=
  ResidueTargetEq G C hS hU u hK V h V' φ
    (ψ ≫ (G.realization C hS hU hR hP).target.hom)

/-- **The predicate cut out by the stabilizer-supported open depends on an arrow only through its
target.**  This is the hypothesis `hinv` of
`AlgebraicGeometry.Space.FinitePartUniversalOpen.target_eq_of_cutsOutRel`, and it is what fails
for the predicate on arrows alone: pointwise membership in the image of
`AlgebraicGeometry.stabilizerArrow` over `u` is *not* target-invariant, because a point of
`U ×_S U` with both projections `u` need not lie on the diagonal. -/
theorem targetInvariant_residueTargetArrow (V : BigFppfOver C S hS)
    (h : V ⟶ schemeSiteObject C hS (X := residueOver G u) hK)
    (V' : BigFppfOver C S hS) (φ : yoneda.obj V' ⟶ yoneda.obj V)
    (ψ₁ ψ₂ : yoneda.obj V' ⟶ (G.realization C hS hU hR hP).arrows.obj)
    (hψ : ψ₁ ≫ (G.realization C hS hU hR hP).target.hom =
      ψ₂ ≫ (G.realization C hS hU hR hP).target.hom) :
    ResidueTargetArrow G C hS hU hR u hK hP V h V' φ ψ₁ ↔
      ResidueTargetArrow G C hS hU hR u hK hP V h V' φ ψ₂ :=
  iff_of_eq (congrArg (ResidueTargetEq G C hS hU u hK V h V' φ) hψ)

/-! ### The pair named by the point `u'` of Situation 0DTB -/

variable (F : FinitePartUniversalOpen (G.realization C hS hU hR hP))

include hWstab in
/-- The inclusion of the object space of the finite part carries the point `u'` of Situation
0DTB to the section which the pair `(u, Z_u)` names.  This is
`AlgebraicGeometry.Space.objectsInclusion_app_fibrePoint` for the stabilizer-supported open. -/
theorem objectsInclusion_app_stabilizerFibrePoint :
    F.objectsInclusion.app
        (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
        (etaleLocalStabilizerFibrePoint G C hS hU hR u hK hP W hWfin hWstab F) =
      fibrePresheafSection G C hS hU hR u hK hP W hWfin := by
  have h2 : F.objectsEquiv.hom.app
      (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
      (etaleLocalStabilizerFibrePoint G C hS hU hR u hK hP W hWfin hWstab F) =
      ⟨fibrePresheafSection G C hS hU hR u hK hP W hWfin,
        mem_finitePartWithSection_stabilizer G C hS hU hR u hK hP W hWfin hWstab F⟩ :=
    congrArg (fun k => k.app
      (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
      ⟨fibrePresheafSection G C hS hU hR u hK hP W hWfin,
        mem_finitePartWithSection_stabilizer G C hS hU hR u hK hP W hWfin hWstab F⟩)
      F.objectsEquiv.inv_hom_id
  exact congrArg (fun z => (finitePartWithSection C S hS
      (G.realization C hS hU hR hP).source F.unit F.unit_source).toSubfunctor.ι.app
      (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)) z) h2

include hWstab in
/-- The classifying morphism of the pair `(u, Z_u)` of Situation 0DTB is the point `u'`, read as
a morphism out of the presheaf represented by `Spec κ(u)`, followed by the inclusion of the
object space of the finite part. -/
theorem stabilizerFibrePoint_comp_objectsInclusion :
    yonedaEquiv.symm
          (etaleLocalStabilizerFibrePoint G C hS hU hR u hK hP W hWfin hWstab F) ≫
        F.objectsInclusion =
      (finiteOpenSubspaceEquiv C S hS (G.realization C hS hU hR hP).source
        (AlgebraicGeometry.schemeSpace
          (schemeSiteObject C hS (X := residueOver G u) hK))).1.symm
        (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin) := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
  exact objectsInclusion_app_stabilizerFibrePoint G C hS hU hR u hK hP W hWfin hWstab F

include hWstab in
/-- **The restriction of the point `u'` of Situation 0DTB along a morphism
`Spec k ⟶ Spec κ(u)`.**  The pair which the object space of the finite part names at the
restricted point is the base change of the pair `(u, Z_u)` along that morphism.  This is
`AlgebraicGeometry.Space.objectsPair_restrict_fibrePoint_isBaseChange` for the
stabilizer-supported open. -/
theorem objectsPair_restrict_stabilizerFibrePoint_isBaseChange
    (V : BigFppfOver C S hS) (h : V ⟶ schemeSiteObject C hS (X := residueOver G u) hK) :
    (F.objectsPair V (yoneda.map h ≫ yonedaEquiv.symm
          (etaleLocalStabilizerFibrePoint G C hS hU hR u hK hP W hWfin
            hWstab F))).toBase.hom =
        yoneda.map h ≫
          (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).toBase.hom ∧
      ∃ j : (F.objectsPair V (yoneda.map h ≫ yonedaEquiv.symm
            (etaleLocalStabilizerFibrePoint G C hS hU hR u hK hP W hWfin
              hWstab F))).subspace.toFunctor ⟶
          (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).subspace.toFunctor,
        IsPullback ((F.objectsPair V (yoneda.map h ≫ yonedaEquiv.symm
              (etaleLocalStabilizerFibrePoint G C hS hU hR u hK hP W hWfin
                hWstab F))).subspace.ι ≫
            pullback.fst (F.objectsPair V (yoneda.map h ≫ yonedaEquiv.symm
                (etaleLocalStabilizerFibrePoint G C hS hU hR u hK hP W hWfin
                  hWstab F))).toBase.hom
              (G.realization C hS hU hR hP).source.hom) j (yoneda.map h)
          ((fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).subspace.ι ≫
            pullback.fst
              (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).toBase.hom
              (G.realization C hS hU hR hP).source.hom) ∧
        j ≫ (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).subspace.ι ≫
            pullback.snd
              (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).toBase.hom
              (G.realization C hS hU hR hP).source.hom =
          (F.objectsPair V (yoneda.map h ≫ yonedaEquiv.symm
            (etaleLocalStabilizerFibrePoint G C hS hU hR u hK hP W hWfin
              hWstab F))).subspace.ι ≫
            pullback.snd (F.objectsPair V (yoneda.map h ≫ yonedaEquiv.symm
                (etaleLocalStabilizerFibrePoint G C hS hU hR u hK hP W hWfin
                  hWstab F))).toBase.hom
              (G.realization C hS hU hR hP).source.hom := by
  have hp : (finiteOpenSubspaceEquiv C S hS (G.realization C hS hU hR hP).source
        (AlgebraicGeometry.schemeSpace
          (schemeSiteObject C hS (X := residueOver G u) hK))).1
        (yonedaEquiv.symm (etaleLocalStabilizerFibrePoint G C hS hU hR u hK hP W hWfin
            hWstab F) ≫ F.objectsInclusion) =
      fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin :=
    (congrArg (fun v => (finiteOpenSubspaceEquiv C S hS
          (G.realization C hS hU hR hP).source
          (AlgebraicGeometry.schemeSpace
            (schemeSiteObject C hS (X := residueOver G u) hK))).1 v)
        (stabilizerFibrePoint_comp_objectsInclusion G C hS hU hR u hK hP W hWfin
          hWstab F)).trans
      (Equiv.apply_symm_apply _ _)
  have spec := (finiteOpenSubspaceEquiv C S hS (G.realization C hS hU hR hP).source
      (AlgebraicGeometry.schemeSpace
        (schemeSiteObject C hS (X := residueOver G u) hK))).2
      (yonedaEquiv.symm (etaleLocalStabilizerFibrePoint G C hS hU hR u hK hP W hWfin
          hWstab F) ≫ F.objectsInclusion)
      V (yoneda.map h)
  rwa [hp] at spec

include hWstab in
/-- The point `u'` of Situation 0DTB, read as a morphism out of the presheaf represented by
`Spec κ(u)`, followed by the étale projection `g : U' ⟶ U`, is the canonical morphism
`u : Spec κ(u) ⟶ U`. -/
theorem stabilizerFibrePoint_comp_objectProjection :
    yonedaEquiv.symm
          (etaleLocalStabilizerFibrePoint G C hS hU hR u hK hP W hWfin hWstab F) ≫
        F.objectProjection.hom =
      yoneda.map (residueSiteMap G C hS hU u hK) := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
  exact (objectProjection_stabilizerFibrePoint G C hS hU hR u hK hP W hWfin
    hWstab F).trans (yonedaEquiv_yoneda_map _).symm

include hWstab in
/-- **Membership in `Z_univ` over a restriction of the point `u'` of Situation 0DTB, reduced to
the stabilizer condition on the arrow.**  This is
`AlgebraicGeometry.Space.exists_lift_universalOpen_fibrePoint_iff` for the stabilizer-supported
open: a section of the ambient fibre product whose `U'`-component is a restriction of `u'` lies
in `Z_univ` exactly when its arrow factors through `AlgebraicGeometry.stabilizerArrow` over `u`,
pointwise. -/
theorem exists_lift_universalOpen_stabilizerFibrePoint_iff
    (V : BigFppfOver C S hS) (h : V ⟶ schemeSiteObject C hS (X := residueOver G u) hK)
    (V' : BigFppfOver C S hS) (φ : yoneda.obj V' ⟶ yoneda.obj V)
    (base : V' ⟶ schemeSiteObject C hS (X := residueOver G u) hK)
    (hbase : yoneda.map base = φ ≫ yoneda.map h)
    (arr : V' ⟶ schemeSiteObject C hS (X := G.arrows) hR)
    (hc' : (φ ≫ (yoneda.map h ≫ yonedaEquiv.symm
          (etaleLocalStabilizerFibrePoint G C hS hU hR u hK hP W hWfin hWstab F))) ≫
        F.universalOpen.toBase.hom =
      yoneda.map arr ≫ (G.realization C hS hU hR hP).source.hom) :
    (∃ n : yoneda.obj V' ⟶ F.universalOpen.subspace.toFunctor,
        n ≫ F.universalOpen.subspace.ι =
          pullback.lift (φ ≫ (yoneda.map h ≫ yonedaEquiv.symm
            (etaleLocalStabilizerFibrePoint G C hS hU hR u hK hP W hWfin hWstab F)))
            (yoneda.map arr) hc') ↔
      ∀ p : (BigFppfOver.toScheme C S hS).obj V',
        ∃ g : (stabilizer G).left, (stabilizer G).hom g = u ∧
          stabilizerArrow G g = (BigFppfOver.toScheme C S hS).map arr p := by
  have hbc := objectsPair_restrict_stabilizerFibrePoint_isBaseChange G C hS hU hR u hK hP W
    hWfin hWstab F V h
  have hc : φ ≫ (F.objectsPair V (yoneda.map h ≫ yonedaEquiv.symm
        (etaleLocalStabilizerFibrePoint G C hS hU hR u hK hP W hWfin
          hWstab F))).toBase.hom =
      yoneda.map arr ≫ (G.realization C hS hU hR hP).source.hom :=
    (congrArg (fun z => φ ≫ z) (F.objectsPair_toBase_hom V _)).trans
      ((Category.assoc φ _ F.universalOpen.toBase.hom).symm.trans hc')
  have hc'' : (φ ≫ yoneda.map h) ≫
        (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).toBase.hom =
      yoneda.map arr ≫ (G.realization C hS hU hR hP).source.hom :=
    (Category.assoc φ (yoneda.map h) _).trans
      ((congrArg (fun z => φ ≫ z) hbc.1.symm).trans hc)
  have hcB : yoneda.map base ≫
        (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).toBase.hom =
      yoneda.map arr ≫ (G.realization C hS hU hR hP).source.hom :=
    (congrArg (fun z => z ≫
      (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).toBase.hom) hbase).trans hc''
  have hlift : pullback.lift (φ ≫ yoneda.map h) (yoneda.map arr) hc'' =
      pullback.lift (yoneda.map base) (yoneda.map arr) hcB :=
    pullback_lift_congr _ _ _ _ hc'' hcB hbase.symm rfl
  obtain ⟨jb, hjb, hjbsnd⟩ := hbc.2
  exact (F.exists_lift_universalOpen_iff V _ φ (yoneda.map arr) hc hc').symm.trans
    ((exists_lift_of_pairSquares (G.realization C hS hU hR hP).source
        (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin)
        (F.objectsPair V _) (yoneda.map h) jb hjb hjbsnd φ (yoneda.map arr) hc hc'').trans
      ((iff_of_eq (congrArg (fun z => ∃ n : yoneda.obj V' ⟶
          (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).subspace.toFunctor,
          n ≫ (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).subspace.ι = z)
        hlift)).trans
        (exists_lift_stabilizerFibrePair_iff G C hS hU hR u hK hP W hWfin hWstab V'
          base arr hcB)))

include hWstab in
/-- The base component of a section of the ambient fibre product over a restriction of the point
`u'` of Situation 0DTB, read in the site.  This is
`AlgebraicGeometry.Space.base_eq_of_fibrePoint` for the stabilizer-supported open. -/
theorem base_eq_of_stabilizerFibrePoint
    (V : BigFppfOver C S hS) (h : V ⟶ schemeSiteObject C hS (X := residueOver G u) hK)
    (V' : BigFppfOver C S hS) (φ : yoneda.obj V' ⟶ yoneda.obj V)
    (base : V' ⟶ schemeSiteObject C hS (X := residueOver G u) hK)
    (hbase : yoneda.map base = φ ≫ yoneda.map h) :
    (φ ≫ (yoneda.map h ≫ yonedaEquiv.symm
        (etaleLocalStabilizerFibrePoint G C hS hU hR u hK hP W hWfin hWstab F))) ≫
      F.universalOpen.toBase.hom =
      yoneda.map (base ≫ residueSiteMap G C hS hU u hK) :=
  (Category.assoc φ _ F.universalOpen.toBase.hom).trans
    ((congrArg (fun z => φ ≫ z) (Category.assoc (yoneda.map h) _
        F.universalOpen.toBase.hom)).trans
      ((congrArg (fun z => φ ≫ yoneda.map h ≫ z)
          ((congrArg (fun z => yonedaEquiv.symm (etaleLocalStabilizerFibrePoint G C hS hU hR u
                hK hP W hWfin hWstab F) ≫ z)
            F.universalOpen_toBase_hom).trans
            (stabilizerFibrePoint_comp_objectProjection G C hS hU hR u hK hP W hWfin
              hWstab F))).trans
        ((Category.assoc φ (yoneda.map h)
            (yoneda.map (residueSiteMap G C hS hU u hK))).symm.trans
          ((congrArg (fun z => z ≫ yoneda.map (residueSiteMap G C hS hU u hK))
              hbase.symm).trans
            (yoneda.map_comp base (residueSiteMap G C hS hU u hK)).symm))))

include hWstab in
/-- **An arrow whose target is the restriction of the point `u'` of Situation 0DTB satisfies the
predicate cut out by the stabilizer-supported open.**  Its target is literally the prescribed
source, so the two agree on every residue field.  This is
`AlgebraicGeometry.Space.arrowToPoint_of_target` for the stabilizer-supported open. -/
theorem residueTargetArrow_of_target
    (V : BigFppfOver C S hS) (h : V ⟶ schemeSiteObject C hS (X := residueOver G u) hK)
    (V' : BigFppfOver C S hS) (φ : yoneda.obj V' ⟶ yoneda.obj V)
    (ψ : yoneda.obj V' ⟶ (G.realization C hS hU hR hP).arrows.obj)
    (ht : ψ ≫ (G.realization C hS hU hR hP).target.hom =
      (φ ≫ (yoneda.map h ≫ yonedaEquiv.symm
        (etaleLocalStabilizerFibrePoint G C hS hU hR u hK hP W hWfin hWstab F))) ≫
        F.universalOpen.toBase.hom) :
    ResidueTargetArrow G C hS hU hR u hK hP V h V' φ ψ := by
  obtain ⟨base', hbase'⟩ : ∃ b : V' ⟶ V, yoneda.map b = φ :=
    ⟨yoneda.preimage φ, yoneda.map_preimage φ⟩
  have hbase : yoneda.map (base' ≫ h) = φ ≫ yoneda.map h :=
    (yoneda.map_comp base' h).trans (congrArg (fun z => z ≫ yoneda.map h) hbase')
  have hθ : ψ ≫ (G.realization C hS hU hR hP).target.hom =
      yoneda.map ((base' ≫ h) ≫ residueSiteMap G C hS hU u hK) :=
    ht.trans (base_eq_of_stabilizerFibrePoint G C hS hU hR u hK hP W hWfin hWstab F V h V'
      φ (base' ≫ h) hbase)
  have hpre : yoneda.preimage (ψ ≫ (G.realization C hS hU hR hP).target.hom) =
      (base' ≫ h) ≫ residueSiteMap G C hS hU u hK :=
    yoneda.map_injective ((yoneda.map_preimage _).trans hθ)
  have hprebase : yoneda.preimage φ = base' :=
    yoneda.map_injective ((yoneda.map_preimage φ).trans hbase'.symm)
  have hmap : (BigFppfOver.toScheme C S hS).map
        ((base' ≫ h) ≫ residueSiteMap G C hS hU u hK) =
      (BigFppfOver.toScheme C S hS).map (base' ≫ h) ≫
        G.objects.left.fromSpecResidueField u :=
    (BigFppfOver.toScheme C S hS).map_comp (base' ≫ h) (residueSiteMap G C hS hU u hK)
  refine fun y => ?_
  rw [hpre, hprebase, hmap]
  rfl

include hWstab in
/-- **The predicate of `AlgebraicGeometry.Space.ResidueTargetArrow` cuts out the open subspace
which a restriction of the point `u'` of Situation 0DTB names.**  This is the analogue of
`AlgebraicGeometry.Space.cutsOut_fibrePoint`: the membership criterion for the
stabilizer-supported open is a pointwise condition, and
`AlgebraicGeometry.Space.mem_fiberOpen_iff_residue_target` turns it into the agreement of the
target of the arrow with its prescribed source on residue fields. -/
theorem cutsOutRel_stabilizerFibrePoint
    (V : BigFppfOver C S hS) (h : V ⟶ schemeSiteObject C hS (X := residueOver G u) hK) :
    F.CutsOutRel (ResidueTargetArrow G C hS hU hR u hK hP V h)
      (yoneda.map h ≫ yonedaEquiv.symm
        (etaleLocalStabilizerFibrePoint G C hS hU hR u hK hP W hWfin hWstab F)) := by
  intro V' μ ψ φ hμ hc
  obtain ⟨arr, harr⟩ : ∃ b : V' ⟶ schemeSiteObject C hS (X := G.arrows) hR,
      yoneda.map b = ψ := ⟨yoneda.preimage ψ, yoneda.map_preimage ψ⟩
  obtain ⟨base', hbase'⟩ : ∃ b : V' ⟶ V, yoneda.map b = φ :=
    ⟨yoneda.preimage φ, yoneda.map_preimage φ⟩
  subst hμ
  subst harr
  subst hbase'
  have hbase : yoneda.map (base' ≫ h) = yoneda.map base' ≫ yoneda.map h :=
    yoneda.map_comp base' h
  refine (exists_lift_universalOpen_stabilizerFibrePoint_iff G C hS hU hR u hK hP W hWfin
    hWstab F V h V' (yoneda.map base') (base' ≫ h) hbase arr hc).trans ?_
  have hsite : (base' ≫ h) ≫ residueSiteMap G C hS hU u hK =
      arr ≫ sourceSiteMap G C hS hU hR :=
    yoneda.map_injective
      ((base_eq_of_stabilizerFibrePoint G C hS hU hR u hK hP W hWfin hWstab F V h V'
        (yoneda.map base') (base' ≫ h) hbase).symm.trans
        (hc.trans (yoneda.map_comp arr (sourceSiteMap G C hS hU hR)).symm))
  have hsch : (BigFppfOver.toScheme C S hS).map arr ≫ G.source.left =
      (BigFppfOver.toScheme C S hS).map (base' ≫ h) ≫
        G.objects.left.fromSpecResidueField u := by
    have hmap := congrArg (BigFppfOver.toScheme C S hS).map hsite
    rw [Functor.map_comp, Functor.map_comp] at hmap
    exact hmap.symm
  have hpre : yoneda.preimage (yoneda.map arr ≫ (G.realization C hS hU hR hP).target.hom) =
      arr ≫ targetSiteMap G C hS hU hR :=
    yoneda.map_injective ((yoneda.map_preimage _).trans
      (arr_comp_target G C hS hU hR hP V' arr))
  have hprebase : yoneda.preimage (yoneda.map base') = base' := yoneda.preimage_map _
  have hmap : (BigFppfOver.toScheme C S hS).map (arr ≫ targetSiteMap G C hS hU hR) =
      (BigFppfOver.toScheme C S hS).map arr ≫ G.target.left :=
    (BigFppfOver.toScheme C S hS).map_comp arr (targetSiteMap G C hS hU hR)
  refine Iff.trans (forall_congr' fun p =>
    (mem_fiberOpen_iff_stabilizer G u W hWstab
      ((BigFppfOver.toScheme C S hS).map arr p)).symm) ?_
  refine Iff.trans
    (mem_fiberOpen_iff_residue_target G u W hWstab
      ((BigFppfOver.toScheme C S hS).map arr)
      ((BigFppfOver.toScheme C S hS).map (base' ≫ h)) hsch) ?_
  have e₁ : (BigFppfOver.toScheme C S hS).map
        (yoneda.preimage (yoneda.map arr ≫ (G.realization C hS hU hR hP).target.hom)) =
      (BigFppfOver.toScheme C S hS).map arr ≫ G.target.left :=
    (congrArg (BigFppfOver.toScheme C S hS).map hpre).trans hmap
  have e₂ : (BigFppfOver.toScheme C S hS).map (yoneda.preimage (yoneda.map base') ≫ h) =
      (BigFppfOver.toScheme C S hS).map (base' ≫ h) :=
    congrArg (fun z => (BigFppfOver.toScheme C S hS).map (z ≫ h)) hprebase
  refine forall_congr' fun y => ?_
  have ha := congrArg (fun A => ((BigFppfOver.toScheme C S hS).obj V').fromSpecResidueField y ≫
    A) e₁.symm
  have hb := congrArg (fun B => ((BigFppfOver.toScheme C S hS).obj V').fromSpecResidueField y ≫
    B ≫ G.objects.left.fromSpecResidueField u) e₂.symm
  exact ⟨fun hx => ha.symm.trans (hx.trans hb), fun hx => ha.trans (hx.trans hb.symm)⟩

/-! ### The point `u'` of `|U'|` and the splitting -/

include hWstab in
/-- **The point `u'` of `|U'|` in Situation 0DTB**: the field-valued point of the object space of
the finite part given by the pair `(u, Z_u)` with `Z_u` the stabilizer-supported open, over the
spectrum of the residue field at `u`.

This is `AlgebraicGeometry.Space.fibreValuedPoint` for the open of Situation 0DTB. -/
def stabilizerFibreValuedPoint : FieldValuedPoint C S hS F.objects.obj where
  carrier := G.objects.left.residueField u
  contained := hK
  toBase := G.objects.left.fromSpecResidueField u ≫ G.objects.hom
  value := etaleLocalStabilizerFibrePoint G C hS hU hR u hK hP W hWfin hWstab F

include hWstab in
/-- The object of the site underlying the point `u'` of Situation 0DTB is the spectrum of the
residue field at `u`. -/
theorem stabilizerFibreValuedPoint_siteObject :
    (stabilizerFibreValuedPoint G C hS hU hR u hK hP W hWfin hWstab F).siteObject =
      schemeSiteObject C hS (X := residueOver G u) hK := rfl

include hWstab in
/-- The point `u'` of `|U'|` in Situation 0DTB is the point determined by the section `u'` of
`U'`. -/
theorem stabilizerFibreValuedPoint_eq :
    stabilizerFibreValuedPoint G C hS hU hR u hK hP W hWfin hWstab F =
      residueSectionValuedPoint G C hS u hK F.objects
        (etaleLocalStabilizerFibrePoint G C hS hU hR u hK hP W hWfin hWstab F) := rfl

include hWstab in
/-- **The stabilizer containment of Stacks 0DTC.**  Every point of the stabilizer of the
restriction `R|_{U'}` lying over the point `u'` of Situation 0DTB lies in the image of `Z_univ`.

A representative of such a point is a field-valued point of the stabilizer of `R'`; its
underlying arrow has source and target the *same* morphism to `U'`, by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerArrow_source` and `stabilizerArrow_target`,
so a single field extension makes both of them a restriction of `u'` along one morphism
`Spec Ω ⟶ Spec κ(u)`.  Over that extension
`AlgebraicGeometry.Space.FinitePartUniversalOpen.exists_toRestriction_eq_of_cutsOutRel` produces
the section of `Z_univ`, and restricting a representative does not change the point it defines.

This is the `contains_stabilizer` field of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Splitting`, and the one assertion of Stacks 0DTC
which `Stacks.Groupoids.GroupoidScheme.exists_etale_point_of_splittingSituation` leaves open. -/
theorem contains_stabilizer_stabilizerFibrePoint
    (g : Space.points C S hS (GroupoidInAlgebraicSpaces.stabilizer
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
        F.objectProjection).groupoid).left)
    (hg : Space.pointsMap C S hS (GroupoidInAlgebraicSpaces.stabilizer
          (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
            F.objectProjection).groupoid).left
          (GroupoidInAlgebraicSpaces.stabilizer
            (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
              F.objectProjection).groupoid).hom g =
        (stabilizerFibreValuedPoint G C hS hU hR u hK hP W hWfin hWstab F).class C S hS
          F.objects.obj) :
    ∃ p : Space.points C S hS (Subfunctor.range F.toRestriction.hom).toFunctor,
      Space.pointsMap C S hS (Subfunctor.range F.toRestriction.hom).toFunctor
          (Subfunctor.range F.toRestriction.hom).ι p =
        Space.pointsMap C S hS (GroupoidInAlgebraicSpaces.stabilizer
          (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
            F.objectProjection).groupoid).left
          (GroupoidInAlgebraicSpaces.stabilizerArrow
            (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
              F.objectProjection).groupoid) g := by
  obtain ⟨ζ, hζ⟩ := Quot.exists_rep g
  subst hζ
  obtain ⟨ρ, ⟨f₁, hf₁⟩, ⟨g₁, hg₁⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff C S hS F.objects.obj _ _).1 hg
  have hlift : ∀ σ : (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
        F.objectProjection).groupoid.arrows.obj ⟶ F.objects.obj,
      GroupoidInAlgebraicSpaces.stabilizerArrow
          (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
            F.objectProjection).groupoid ≫ σ =
        (GroupoidInAlgebraicSpaces.stabilizer
          (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
            F.objectProjection).groupoid).hom →
      yonedaEquiv.symm
          ((GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
            F.objectProjection).groupoid.arrows.obj.map f₁.op
            (GroupoidInAlgebraicSpaces.stabilizerArrow
              (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
                F.objectProjection).groupoid |>.app (Opposite.op ζ.siteObject) ζ.value)) ≫ σ =
        yoneda.map g₁ ≫ yonedaEquiv.symm
          (etaleLocalStabilizerFibrePoint G C hS hU hR u hK hP W hWfin hWstab F) := by
    intro σ hσ
    refine (yonedaEquiv_symm_naturality_right _ _ _).trans
      ((congrArg yonedaEquiv.symm ?_).trans (yonedaEquiv_symm_map _ _))
    refine (NatTrans.naturality_apply σ f₁.op _).trans ?_
    exact (congrArg (F.objects.obj.map f₁.op)
      (congrArg (fun z => z.app (Opposite.op ζ.siteObject) ζ.value) hσ)).trans
      (hf₁.trans hg₁.symm)
  have hs' := hlift _ (GroupoidInAlgebraicSpaces.stabilizerArrow_source _)
  have ht' := hlift _ (GroupoidInAlgebraicSpaces.stabilizerArrow_target _)
  have hψt := F.restriction_arrows_comp_target _ ht'
  obtain ⟨b, hb⟩ := F.exists_toRestriction_eq_of_cutsOutRel ρ.siteObject
    (ResidueTargetArrow G C hS hU hR u hK hP ρ.siteObject g₁)
    (targetInvariant_residueTargetArrow G C hS hU hR u hK hP ρ.siteObject g₁)
    (yoneda.map g₁ ≫ yonedaEquiv.symm
      (etaleLocalStabilizerFibrePoint G C hS hU hR u hK hP W hWfin hWstab F))
    (cutsOutRel_stabilizerFibrePoint G C hS hU hR u hK hP W hWfin hWstab F _ g₁)
    (yonedaEquiv.symm
      ((GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
        F.objectProjection).groupoid.arrows.obj.map f₁.op
        (GroupoidInAlgebraicSpaces.stabilizerArrow
          (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
            F.objectProjection).groupoid |>.app (Opposite.op ζ.siteObject) ζ.value)))
    hs' ht'
    (residueTargetArrow_of_target G C hS hU hR u hK hP W hWfin hWstab F _ g₁ _
      (𝟙 (yoneda.obj ρ.siteObject)) _ ((congrArg (· ≫ _) (Category.id_comp _)).trans hψt))
  have hval : F.toRestriction.hom.app (Opposite.op ρ.siteObject) (yonedaEquiv b) =
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
        F.objectProjection).groupoid.arrows.obj.map f₁.op
        (GroupoidInAlgebraicSpaces.stabilizerArrow
          (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
            F.objectProjection).groupoid |>.app (Opposite.op ζ.siteObject) ζ.value) := by
    have hb' := congrArg yonedaEquiv hb
    rw [yonedaEquiv_comp] at hb'
    exact hb'.trans (Equiv.apply_symm_apply yonedaEquiv _)
  refine ⟨Quot.mk _
    { carrier := ρ.carrier
      field := ρ.field
      contained := ρ.contained
      toBase := ρ.toBase
      value := ⟨(GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
        F.objectProjection).groupoid.arrows.obj.map f₁.op
        (GroupoidInAlgebraicSpaces.stabilizerArrow
          (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
            F.objectProjection).groupoid |>.app (Opposite.op ζ.siteObject) ζ.value),
        ⟨yonedaEquiv b, hval⟩⟩ }, ?_⟩
  exact Quot.sound ⟨_, FieldValuedPoint.dominates_refl C S hS _ _, ⟨f₁, rfl⟩⟩

include hWstab in
/-- **`Z_univ` as a splitting of `R|_{U'}` at the point `u'` of Situation 0DTB.**  Together with
the open finite subgroupoid
`AlgebraicGeometry.Space.FinitePartUniversalOpen.restrictedSubgroupoid` — conditions (a) and (b)
of Stacks 04RK — and the stabilizer containment
`AlgebraicGeometry.Space.contains_stabilizer_stabilizerFibrePoint`, this is condition (2) of
Stacks 04RK for the restriction of the realization of a groupoid scheme to the object space of
its finite part, at the point `u' = (u, Z_u)` with `Z_u` the stabilizer-supported open.

This is the fourth assertion of **Stacks 0DTC**. -/
def restrictedSplitting :
    GroupoidInAlgebraicSpaces.Splitting
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
        F.objectProjection).groupoid
      ((stabilizerFibreValuedPoint G C hS hU hR u hK hP W hWfin hWstab F).class C S hS
        F.objects.obj) where
  toOpenFiniteSubgroupoid := F.restrictedSubgroupoid
  contains_stabilizer g hg :=
    contains_stabilizer_stabilizerFibrePoint G C hS hU hR u hK hP W hWfin hWstab F g hg

include hWstab in
/-- **The restriction `R|_{U'}` is split at the point `u'` of Situation 0DTB** in the sense of
Stacks 04RK (2). -/
theorem isSplitAt_stabilizerFibreValuedPoint :
    GroupoidInAlgebraicSpaces.IsSplitAt
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
        F.objectProjection).groupoid
      ((stabilizerFibreValuedPoint G C hS hU hR u hK hP W hWfin hWstab F).class C S hS
        F.objects.obj) :=
  ⟨restrictedSplitting G C hS hU hR u hK hP W hWfin hWstab F⟩

end Fibre

end AlgebraicGeometry.Space

/-! ### Stacks 0DTC -/

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry AlgebraicGeometry.Space

/-- **Stacks Project, Tag 0DTC.**  In the splitting situation of Stacks 0DTB there are an
algebraic space `U'`, an étale morphism `g : U' ⟶ U` of algebraic spaces and a point
`u' : Spec κ(u) ⟶ U'` lying over `u : Spec κ(u) ⟶ U` such that the restriction `R' = R|_{U'}`
of `R` to `U'` is split over `u'`.

`U'` is the object space of the finite part `(R_s/U, e)_fin` of Stacks 04RU, `g` its étale
projection, `u'` the pair `(u, Z_u)` where `Z_u` is the open and closed piece of the fibre
`F_u = R ×_{s, U} Spec κ(u)` supported on the arrows underlying the points of the stabilizer
group scheme over `u`, and the splitting is the universal open `Z_univ` read inside `R|_{U'}`.
Being split is a condition on a point of `|U'|`, so it is asserted at the point of `|U'|` which
the morphism `u' : Spec κ(u) ⟶ U'` determines.

The standing hypothesis is `AlgebraicGeometry.Space.SplittingSituation`, Situation 0DTB, and not
the strictly stronger `AlgebraicGeometry.Space.StrongSplittingSituation` of Stacks 04RL: the
open `Z_u` is supported on the stabilizer, which is in general a proper subset of the arrows
with both endpoints at `u`.  So this is not a formal consequence of Stacks 03FM,
`AlgebraicGeometry.Space.exists_stronglySplit_of_strongSplittingSituation`. -/
@[stacks 0DTC "ALL FOUR ASSERTIONS, in Situation 0DTB: the algebraic space U', the etale \
morphism g : U' -> U, the point u' : Spec k(u) -> U' lying over u, and that the restriction \
R|_{U'} is SPLIT over u' -- all four PRODUCED, none assumed. The situation hypothesis is \
AlgebraicGeometry.Space.SplittingSituation, which carries the 0DTB attribute, and NOT the \
stronger StrongSplittingSituation of Tag 04RL. Beyond Situation 0DTB the only hypotheses are \
that the big fppf site contains the base, object, arrow and composable-pair schemes and \
Spec k(u), which is this library's standing ambient requirement. The supporting open of the \
fibre is the stabilizer-supported one of SplittingSituation.exists_fiberOpens_stabilizer, a \
proper subset in general of the target-condition open that Tag 03FM uses"]
theorem exists_split_of_splittingSituation
    (D : AlgebraicGeometry.Space.SplittingSituation.{u})
    (C : BigFppfSite.{u}) (hS : C.Contains D.S)
    (hU : C.Contains D.groupoid.objects.left)
    (hR : C.Contains D.groupoid.arrows.left)
    (hP : C.Contains (pullback D.groupoid.source D.groupoid.target).left)
    (hK : C.Contains (Spec (D.groupoid.objects.left.residueField D.u))) :
    ∃ (U' : AlgebraicSpaces C D.S hS)
      (g : U' ⟶ (D.groupoid.realization C hS hU hR hP).objects),
      IsEtale C D.S hS g.hom ∧
      ∃ v : U'.obj.obj (Opposite.op
          (schemeSiteObject C hS (X := residueOver D.groupoid D.u) hK)),
        (yonedaSchemePointEquiv C hS hU (Opposite.op
            (schemeSiteObject C hS (X := residueOver D.groupoid D.u) hK))
            (g.hom.app _ v)).left =
          D.groupoid.objects.left.fromSpecResidueField D.u ∧
        GroupoidInAlgebraicSpaces.IsSplitAt
          (GroupoidInAlgebraicSpaces.restrict (D.groupoid.realization C hS hU hR hP)
            g).groupoid
          ((residueSectionValuedPoint D.groupoid C hS D.u hK U' v).class C D.S hS U'.obj) := by
  obtain ⟨W, hWstab, _, _, hWfin⟩ := D.exists_fiberOpens_stabilizer
  exact ⟨(realizationFinitePart D.groupoid C hS hU hR hP).objects,
    (realizationFinitePart D.groupoid C hS hU hR hP).objectProjection,
    (realizationFinitePart D.groupoid C hS hU hR hP).objectProjection_etale,
    etaleLocalStabilizerFibrePoint D.groupoid C hS hU hR D.u hK hP W hWfin hWstab
      (realizationFinitePart D.groupoid C hS hU hR hP),
    lies_over_stabilizerFibrePoint D.groupoid C hS hU hR D.u hK hP W hWfin hWstab
      (realizationFinitePart D.groupoid C hS hU hR hP),
    isSplitAt_stabilizerFibreValuedPoint D.groupoid C hS hU hR D.u hK hP W hWfin hWstab
      (realizationFinitePart D.groupoid C hS hU hR hP)⟩

end Stacks.Groupoids.GroupoidScheme

end
