module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadrupleGlueInputs
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RestrictPullbackBridge
public import StacksFrontier.AlgebraicGeometry.Descent.ModuleGlueChartHom
public import StacksFrontier.AlgebraicGeometry.Descent.ModuleGlueChartPullback
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Invertible

/-!
# The invertible module of a glued quadruple

Let `S` be a scheme and `𝒜` a graded `𝒪_S`-algebra (Situation 01NN), and fix an integer `d`.
`...RelativeProjQcohSheaf.QuadrupleGlues` is step (1) of the proof of Tag 01NV with the site, the
base morphism and the quotient removed: a family of quadruples over the restrictions of
`f : T ⟶ S` to a covering family of opens of `T`, pairwise strictly equivalent over the overlaps,
must come from a quadruple over `f`. Its first ingredient is the **invertible module** of that
quadruple, glued from the invertible modules of the given ones. This file produces it.

`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadrupleGlueInputs` already has the
comparisons and their cocycle condition in the only shape in which two chart modules — sheaves of
modules on two different schemes — can be compared: as an isomorphism of their inverse images
along a pair of morphisms from a common scheme, `...Quadruple.chartWitness`, with
`...Quadruple.chartWitness_trans` on a common refinement of three of the opens.
`Stacks.SheafOfModules.ModulesGlueData.exists_modulesGlueData_of_chartPullbackIso` consumes
exactly such a family, but it states the cocycle condition through
`Stacks.SheafOfModules.chartPullbackRestrict`, which restricts a comparison to a smaller open of
the base by conjugating the inverse image along the inclusion with
`AlgebraicGeometry.Scheme.Modules.pullbackComp` and `...Scheme.Modules.pullbackCongr`, whereas the
quadruple side produces its comparisons conjugated by
`...RelativeProjQcohSheaf.compComparison`. Identifying those two contractions of an iterated
inverse image is the bridge this file begins with.

## The bridge is not `rfl`, and the step that is not formal is already in the tree

`...RelativeProjQcohSheaf.compComparison` is
`Stacks.Sheaves.RingedSpaceDifferentials.modulePullbackComparison`, the comparison map built from
the universal property of a pullback of sheaves of modules;
`AlgebraicGeometry.Scheme.Modules.pullbackComp` is `CategoryTheory.SheafOfModules.pullbackComp`,
built by `CategoryTheory.Adjunction.leftAdjointCompIso` from the composition isomorphism of the
two pushforwards. The two are built from different presentations of the uniqueness of a left
adjoint, so they are *not* equal by `rfl`. What identifies them is
`Stacks.PullbackPseudofunctor.modulePullbackCompIso_hom_app`, which equates the comparison map
with the components of `Stacks.PullbackPseudofunctor.modulePullbackCompIso` by injectivity of the
hom-set bijection of the adjunction; from there
`...PullbackPseudofunctor.modulePullbackCompIso_eq_pullbackComp_symm` is `rfl`.

The equation must be proved in **term** mode. Its two sides are spelled with the two names
`Stacks.RingedSpace.structureRingSheaf` and `Stacks.PullbackPseudofunctor`'s
`structureSheafRing` for one and the same sheaf of rings; those are equal by `rfl` and are not
syntactically equal, so a goal mentioning both is not type-correct at `implicit` transparency and
`rw` refuses it, reporting a pattern rather than the cause. This is the discipline
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackCompMonoidal` records for its own
statements.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.chartGlueIso`: **the comparison of the chart
  modules of a family of quadruples**, ascribed at the
  `Stacks.SheafOfModules.chartPullbackModule` spelling a glueing datum is stated for.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.compComparison_eq_pullbackComp_inv`: **the
  contraction of an iterated inverse image of a quadruple is Mathlib's composition isomorphism
  for the inverse image, read backwards.**
* `...RelativeProjQcohSheaf.Quadruple.witnessOver_pullback_comp`: **the comparison of two
  quadruples pulled back along `c ≫ a` and `c ≫ b` is the inverse image along `c` of the
  comparison along `a` and `b`, conjugated by the two contractions.**
* `...RelativeProjQcohSheaf.Quadruple.pullbackChartRestrict_pullbackWitness` and
  `...RelativeProjQcohSheaf.chartPullbackRestrict_chartWitness`: **restricting the comparison to a
  smaller open of the base gives the comparison there**, in the vocabulary the cocycle hypothesis
  of a glueing datum is stated in.
* `...RelativeProjQcohSheaf.chartGlueIso_cocycle`: **that cocycle hypothesis, discharged.**
* `...RelativeProjQcohSheaf.exists_modulesGlueData_of_quadrupleFamily` and
  `...exists_modulesGlueData_invertible`: **the invertible module of the glued quadruple exists** —
  a glueing datum whose chart modules are the invertible modules of the given quadruples, with
  the glued sheaf of modules invertible.
* `...RelativeProjQcohSheaf.quadrupleGlueData`, with
  `...quadrupleGlueData_mod`, `...isInvertibleModule_quadrupleGlueData_glued` and
  `...quadrupleGlueData_trans_chartSectionsIso`: **the same datum as a named object, together
  with the comparisons of its glued module with the given invertible modules and the fact that
  those comparisons are related to one another by `...Quadruple.chartWitness`.**
* `...RelativeProjQcohSheaf.quadrupleGlueData_restrictFunctor_map_chartAdjunct`: **that same
  relation as an equation of morphisms of sheaves of modules** rather than of maps on sections,
  which is the form a glueing argument whose local data are morphisms of inverse images
  consumes.

## What is still missing from step (1)

The map `ψ` in every integral degree.
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover`
glues it degree by degree, `...RelativeProjQcohSheaf.mul_of_pullbackFamily_mul_cover` and
`...one_of_pullback_map_cover` supply the two laws of a `...RelativeProjQcohSheaf.Twisting`, and
`...RelativeProjQcohSheaf.epi_of_pullbackFamily_comp_epi_cover` supplies the surjectivity of the
degree-one component.

**It is no longer the compatibility hypothesis of the first of those.** It used to be recorded
here that the comparisons `Stacks.SheafOfModules.ModulesGlueData.chartIso` of the glued module
with the chart modules had to be related to one another by `...Quadruple.chartWitness` and that
`...ModulesGlueData.ofChartIso` does not record it. That relation is now
`...RelativeProjQcohSheaf.quadrupleGlueData_trans_chartSectionsIso`, and nothing beyond the
pairwise strict equivalences went into it: at the level of a glueing datum it is
`Stacks.SheafOfModules.ModulesGlueData.trans_chartSectionsIso`, the triangle
`φ i j ∘ φ i = φ j`, which `Stacks.SheafOfModules.OModuleGlueData.trans_chartLinearEquiv`
had all along. What the existence statements lost was only the datum's identity: an
existentially bound datum has an opaque `mod`, so the comparison cannot even be *stated* for it,
which is why `quadrupleGlueData` is a `def`.

**Nor is it the transport of the local maps.** It used to be recorded here that
`(P a).twisting.app i` is a morphism into `(laurent (P a).L).piece i` while
`existsUnique_hom_of_restrict_cover` wants morphisms into the restriction of
`(laurent G.glued).piece i`, and that the comparison between the two — the `i`-th integral
tensor power of the chart comparison, `...RelativeProjQcohSheaf.laurentCongrIso` composed with
`...RelativeProjQcohSheaf.laurentPullback`, with its multiplicativity and its unit
normalisation — was not assembled. It is, in
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullbackCongr`, as
`...RelativeProjQcohSheaf.laurentPullbackCongrIso` with
`...laurentPullbackCongrIso_mul` and `...laurentPullbackCongrIso_zero`; the local datum itself is
`...RelativeProjQcohSheaf.chartLocalApp`, and the multiplicativity and the surjectivity of the
glued family are `...RelativeProjQcohSheaf.mul_of_chartLocal_cover` and
`...epi_of_chartLocal_cover`.

**Nor is it the unit law** `...Twisting.app_one` of the glued family. It used to be recorded here
that `...RelativeProjQcohSheaf.one_of_pullback_map_cover` asks for the inverse image of the
equation while the directory had no `...RelativeProjQcohSheaf.pullbackFamily`-shaped unit
statement matching `...pullbackFamily_mul_iff`. That statement is now
`...RelativeProjQcohSheaf.pullbackFamily_one_iff`, with
`...one_of_pullbackFamily_one_cover` its locality form, and the unit law of the glued family is
`...RelativeProjQcohSheaf.one_of_chartLocal_cover`.

**Nor is it the passage from sections to morphisms.** It used to be recorded here that the
compatibility hypothesis of `existsUnique_hom_of_restrict_cover` is an equation of maps on
sections while `hP` is an equation of morphisms of sheaves of modules, and that the passage
between them was not made. Both halves of it are now in place: the hypothesis for an arbitrary
pair of members reduces to an equation of **morphisms** of inverse images over a common
refinement by `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_ofPullback_eq_of_refinement`,
with `...RelativeProjQcohSheaf.chartLocalApp_eq_ofPullback` putting the local datum in the
`...ModuleHomGlue.ofPullback` form that reduction consumes; and the comparisons of the glued
module with the chart modules are related by `...Quadruple.chartWitness` as an equation of
morphisms, `...RelativeProjQcohSheaf.quadrupleGlueData_restrictFunctor_map_chartAdjunct` below,
which is `...quadrupleGlueData_trans_chartSectionsIso` assembled over the opens inside `V` by
`Stacks.SheafOfModules.ModulesGlueData.ofChartIso_restrictFunctor_map_chartAdjunct`.

**Nor is it the composition law for the chart comparison.** It used to be recorded here that
relating `...RelativeProjQcohSheaf.laurentPullbackCongrIso` along `k ≫ a` to the inverse image
along `k` of the one along `a` needed two halves, of which only
`...RelativeProjQcohSheaf.laurentPullback_comp` was present, the other being the naturality of
`...LaurentCongr.congrIso` in the base scheme. That naturality is now
`...LaurentCongr.congrIso_laurentPullback` of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/LaurentCongrNaturality.lean`, together with
the functoriality `...LaurentCongr.congrIso_trans` of the comparison in its invertible module,
which the composition law also needs and which was absent too; the law itself is
`...RelativeProjQcohSheaf.laurentPullbackCongrIso_comp`, with
`...laurentPullbackCongrIso_pullback` its form at a refinement of a single chart.

What is owed is the assembly of those with the pairwise strict equivalences — which
`...Quadruple.strictlyEquivalentOver_of_common` provides at the refinement. Two vocabulary
crossings are what stand in the way, and neither is a missing law about the comparison: the
identification `a^*G.glued ≅ (P a).L` that `...RelativeProjQcohSheaf.chartLocalApp` consumes has
to be read off `Stacks.SheafOfModules.ModulesGlueData.chartIso`, which is stated for the
*restriction* along `a` rather than the inverse image; and the relation between two such
identifications over a common refinement has to be read off
`...RelativeProjQcohSheaf.quadrupleGlueData_restrictFunctor_map_chartAdjunct`, which is an
equation of morphisms of restrictions over an open of `T` and not of inverse images along the two
morphisms out of the refinement. So no glued family exists yet.

## Implementation notes

`chartGlueIso` and `chartGlueIso_cocycle` are named rather than inlined into
`exists_modulesGlueData_of_quadrupleFamily` because the kernel does not check the inlined form:
with the comparison family and its cocycle written out inside the existence proof, the
declaration fails with `(kernel) deterministic timeout`. Naming each of them keeps every
`rfl`-crossing between the two spellings of the inverse image inside a small declaration.

## No tag is claimed

Nothing here states a clause of a tag. Step (1) is an ingredient of the proof of Tag 01NV, and
this file proves one of its three ingredients, not the step; the tag's carriers are in
`...RelativeProjQcohSheaf.SmallModel` and `...RelativeProjQcohSheaf.Representable`, and their
hypothesis on the Zariski sheaf property of `F_d` is still carried.

## References

* [Stacks Project, Tag 01NV](https://stacks.math.columbia.edu/tag/01NV)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory

open AlgebraicGeometry Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentAlgebraCongr
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentComposition

/-! ### The two contractions of an iterated inverse image -/

/-- **The contraction `(g ≫ f)^*M ⟶ g^*(f^*M)` of an iterated inverse image that a quadruple is
written with is Mathlib's composition isomorphism for the inverse image, read backwards.**

`...RelativeProjQcohSheaf.compComparison` is the comparison map of
`Stacks.Sheaves.RingedSpaceDifferentials.modulePullbackComparison`, built from the universal
property of a pullback of sheaves of modules, while
`AlgebraicGeometry.Scheme.Modules.pullbackComp` is built by
`CategoryTheory.Adjunction.leftAdjointCompIso` from the composition isomorphism of the two
pushforwards; the two are therefore not equal by `rfl`. The step with content is
`Stacks.PullbackPseudofunctor.modulePullbackCompIso_hom_app`, which identifies the comparison map
with the components of `...PullbackPseudofunctor.modulePullbackCompIso` through the injectivity of
the hom-set bijection of the adjunction, and `...modulePullbackCompIso_eq_pullbackComp_symm` is
then `rfl`.

Proved in term mode: the two sides use the two `rfl`-equal but syntactically distinct spellings
`Stacks.RingedSpace.structureRingSheaf` and `structureSheafRing` of the structure sheaf of rings,
so the goal is not type-correct at `implicit` transparency and no `rw` applies to it. -/
theorem compComparison_eq_pullbackComp_inv {T' T S : Scheme.{u}} (g : T' ⟶ T) (f : T ⟶ S)
    (M : SheafOfModules.{u} (structureRingSheaf S.toRingedSpace)) :
    compComparison g f M = (Scheme.Modules.pullbackComp g f).inv.app M :=
  (Stacks.PullbackPseudofunctor.modulePullbackCompIso_hom_app
    (ringedSpaceHom f) (ringedSpaceHom g) M).symm

/-- `...RelativeProjQcohSheaf.compComparison_eq_pullbackComp_inv` in the other direction: the
component of Mathlib's composition isomorphism is the inverse of the contraction. -/
theorem pullbackComp_hom_app_eq_inv_compComparison {T' T S : Scheme.{u}} (g : T' ⟶ T) (f : T ⟶ S)
    (M : SheafOfModules.{u} (structureRingSheaf S.toRingedSpace)) :
    (Scheme.Modules.pullbackComp g f).hom.app M = inv (compComparison g f M) := by
  symm
  apply IsIso.inv_eq_of_hom_inv_id
  rw [compComparison_eq_pullbackComp_inv]
  exact (Scheme.Modules.pullbackComp g f).inv_hom_id_app M

/-- **The component of Mathlib's composition isomorphism for the inverse image is the composition
law `...LaurentComposition.compCmp` this directory carries.** This is
`...RelativeProjQcohSheaf.pullbackComp_hom_app_eq_inv_compComparison` together with
`...RelativeProjQcohSheaf.compComparison_comp_compCmp`. -/
theorem pullbackComp_hom_app_eq_compCmp {T' T S : Scheme.{u}} (g : T' ⟶ T) (f : T ⟶ S)
    (M : SheafOfModules.{u} (structureRingSheaf S.toRingedSpace)) :
    (Scheme.Modules.pullbackComp g f).hom.app M = (compCmp g f M).hom :=
  (pullbackComp_hom_app_eq_inv_compComparison g f M).trans
    (IsIso.inv_eq_of_hom_inv_id (compComparison_comp_compCmp g f M))

namespace Quadruple

variable {T T' T'' S : Scheme.{u}}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}

/-! ### The comparison of two quadruples pulled back twice -/

/-- **The canonical comparison of the two pullbacks in the composition law for quadruples is the
composition law `...LaurentComposition.compCmp` for the inverse image.** The witness exhibited by
`...Quadruple.strictlyEquivalent_pullback_comp` is the comparison induced on Laurent algebras by
that composition law, and `...Quadruple.witness_eq` identifies any witness with the canonical
one. -/
theorem witness_strictlyEquivalent_pullback_comp {f : T ⟶ S} (P : Quadruple f A d)
    (g : T' ⟶ T) (g' : T'' ⟶ T') :
    witness (strictlyEquivalent_pullback_comp P g g') = compCmp g' g P.L :=
  witness_eq _ (γ := laurentCongrIso (compCmp g' g P.L))
    (laurentCongrIso_app_one _) (fun n => Twisting.pullbackApp_comp P.twisting g g' n)

/-- **The comparison of two quadruples pulled back along `c ≫ a` and `c ≫ b` is the inverse image
along `c` of their comparison along `a` and `b`, conjugated by the two contractions of the
iterated inverse image.**

This is the statement the cocycle hypothesis of a glueing datum of sheaves of modules needs: that
hypothesis lives over a triple overlap, which is a smaller open of the base than the double
overlaps the comparisons are given over, and the passage between the two is exactly a further
pullback along the inclusion.

Nothing is chosen: the three steps are the composition law for quadruples on each side and
`...Quadruple.witnessOver_pullback` in the middle, and
`...Quadruple.witnessOver_trans` composes them. -/
theorem witnessOver_pullback_comp {Y Y' : Scheme.{u}} {f : T ⟶ S} {f' : T' ⟶ S}
    {a : Y ⟶ T} {b : Y ⟶ T'} {h : a ≫ f = b ≫ f'}
    {P : Quadruple f A d} {P' : Quadruple f' A d}
    (e : StrictlyEquivalentOver h (P.pullback a) (P'.pullback b)) (c : Y' ⟶ Y)
    {h'' : (c ≫ a) ≫ f = (c ≫ b) ≫ f'}
    (e'' : StrictlyEquivalentOver h'' (P.pullback (c ≫ a)) (P'.pullback (c ≫ b))) :
    pullbackWitness e'' = (compCmp c a P.L).symm ≪≫
      (pullbackFunctor (ringedSpaceHom c)).mapIso (pullbackWitness e) ≪≫ compCmp c b P'.L := by
  have E1 : StrictlyEquivalentOver (rfl : (c ≫ a) ≫ f = (c ≫ a) ≫ f)
      (P.pullback (c ≫ a)) ((P.pullback a).pullback c) :=
    (strictlyEquivalentOver_rfl_iff _ _).mpr
      (strictlyEquivalent_equivalence.symm (strictlyEquivalent_pullback_comp P a c))
  have E2 := e.pullback c
  have E3 : StrictlyEquivalentOver (rfl : c ≫ (b ≫ f') = c ≫ (b ≫ f'))
      ((P'.pullback b).pullback c) (P'.pullback (c ≫ b)) :=
    (strictlyEquivalentOver_rfl_iff _ _).mpr (strictlyEquivalent_pullback_comp P' b c)
  have hE1 : witnessOver E1 = (compCmp c a P.L).symm :=
    (witnessOver_rfl E1).trans
      ((witness_symm (strictlyEquivalent_pullback_comp P a c) _).trans
        (congrArg Iso.symm (witness_strictlyEquivalent_pullback_comp P a c)))
  have hE3 : witnessOver E3 = compCmp c b P'.L :=
    (witnessOver_rfl E3).trans (witness_strictlyEquivalent_pullback_comp P' b c)
  refine Eq.trans (witnessOver_trans (E1.trans E2) E3 e'').symm ?_
  refine Eq.trans (congrArg (fun z => z ≪≫ witnessOver E3)
    (witnessOver_trans E1 E2 (E1.trans E2)).symm) ?_
  refine Eq.trans (Iso.trans_assoc _ _ _) ?_
  have inner : witnessOver E2 ≪≫ witnessOver E3 =
      (pullbackFunctor (ringedSpaceHom c)).mapIso (witnessOver e) ≪≫ compCmp c b P'.L :=
    (congrArg (fun z => z ≪≫ witnessOver E3) (witnessOver_pullback e E2)).trans
      (congrArg (fun z => (pullbackFunctor (ringedSpaceHom c)).mapIso (witnessOver e) ≪≫ z) hE3)
  exact (congrArg (fun z => z ≪≫ witnessOver E2 ≪≫ witnessOver E3) hE1).trans
    (congrArg (fun z => (compCmp c a P.L).symm ≪≫ z) inner)

/-- **Restricting the comparison of two quadruples to a smaller open of the base, in the
vocabulary a glueing datum of sheaves of modules uses, gives the comparison of their pullbacks to
that open.**

`Stacks.AlgebraicGeometry.ModuleHomGlue.pullbackChartRestrict` conjugates the inverse image along
the inclusion by `AlgebraicGeometry.Scheme.Modules.pullbackComp` and `...pullbackCongr`;
`...Quadruple.witnessOver_pullback_comp` produces the same conjugation by
`...RelativeProjQcohSheaf.compComparison` and `...LaurentComposition.compCmp`, and the two agree
by `...RelativeProjQcohSheaf.compComparison_eq_pullbackComp_inv` and
`...pullbackComp_hom_app_eq_compCmp`. The congruence isomorphisms disappear once the two
factorisations of the liftings are substituted away. -/
theorem pullbackChartRestrict_pullbackWitness {X : Scheme.{u}} {V W : X.Opens} (hV : V ≤ W)
    {p : W.toScheme ⟶ T} {q : V.toScheme ⟶ T} (hpq : X.homOfLE hV ≫ p = q)
    {p' : W.toScheme ⟶ T'} {q' : V.toScheme ⟶ T'} (hpq' : X.homOfLE hV ≫ p' = q')
    {f : T ⟶ S} {f' : T' ⟶ S} {P : Quadruple f A d} {P' : Quadruple f' A d}
    {h : p ≫ f = p' ≫ f'} (e : StrictlyEquivalentOver h (P.pullback p) (P'.pullback p'))
    {h' : q ≫ f = q' ≫ f'} (e' : StrictlyEquivalentOver h' (P.pullback q) (P'.pullback q')) :
    ModuleHomGlue.pullbackChartRestrict hV hpq hpq' (pullbackWitness e).hom =
      (pullbackWitness e').hom := by
  subst hpq hpq'
  have hw := congrArg Iso.hom (witnessOver_pullback_comp e (X.homOfLE hV) e')
  simp only [ModuleHomGlue.pullbackChartRestrict, ModuleHomGlue.pullbackCongr_rfl, Iso.refl_inv,
    Iso.refl_hom, pullbackComp_hom_app_eq_compCmp, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom] at hw ⊢
  exact hw.symm

end Quadruple

/-! ### The glueing datum of the chart modules -/

section Glue

variable {T S : Scheme.{u}}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}

open Stacks.SheafOfModules in
/-- **The restriction of `...Quadruple.chartWitness` to a smaller open of the base is
`chartWitness` there.** This is `...Quadruple.pullbackChartRestrict_pullbackWitness` at the chart
liftings of `Stacks.SheafOfModules.chartPullbackRestrict`, whose two factorisation hypotheses are
`AlgebraicGeometry.homOfLE_comp_chartOpenLift`. -/
theorem chartPullbackRestrict_chartWitness (f : T ⟶ S) {ι : Type u}
    (W : ι → T.Opens) (P : (a : ι) → Quadruple ((W a).ι ≫ f) A d)
    (hP : ∀ a b, Quadruple.StrictlyEquivalentOver (overlapBase_eq f W a b)
      ((P a).pullback (T.homOfLE (inf_le_left : W a ⊓ W b ≤ W a)))
      ((P b).pullback (T.homOfLE (inf_le_right : W a ⊓ W b ≤ W b))))
    {V V' : T.Opens} (hV' : V' ≤ V) (i j : ι)
    (hi : V ≤ ((W i).ι).opensRange) (hj : V ≤ ((W j).ι).opensRange) :
    chartPullbackRestrict (fun a => (W a).ι) (fun a => (P a).L) (hi := hi) (hj := hj) hV'
        (Quadruple.chartWitness f W P hP i j (chartOpenLift ((W i).ι) hi)
          (chartOpenLift ((W j).ι) hj) (by rw [chartOpenLift_fac, chartOpenLift_fac])).hom =
      (Quadruple.chartWitness f W P hP i j (chartOpenLift ((W i).ι) (hV'.trans hi))
          (chartOpenLift ((W j).ι) (hV'.trans hj))
          (by rw [chartOpenLift_fac, chartOpenLift_fac])).hom :=
  Quadruple.pullbackChartRestrict_pullbackWitness hV'
    (homOfLE_comp_chartOpenLift ((W i).ι) hi hV')
    (homOfLE_comp_chartOpenLift ((W j).ι) hj hV') _ _

open Stacks.SheafOfModules in
/-- **The comparison of the chart modules of a family of quadruples**, ascribed at the
`Stacks.SheafOfModules.chartPullbackModule` spelling that a glueing datum of sheaves of modules is
stated for. It is `...Quadruple.chartWitness` taken at the two liftings of the overlap of the two
chart images, and the ascription is its only content: the inverse image of sheaves of modules
along a morphism of schemes and the inverse image along the underlying morphism of ringed spaces
are the same functor
(`...RelativeProjQcohSheaf.modulesPullback_eq_pullbackFunctor`). -/
def chartGlueIso (f : T ⟶ S) {ι : Type u}
    (W : ι → T.Opens) (P : (a : ι) → Quadruple ((W a).ι ≫ f) A d)
    (hP : ∀ a b, Quadruple.StrictlyEquivalentOver (overlapBase_eq f W a b)
      ((P a).pullback (T.homOfLE (inf_le_left : W a ⊓ W b ≤ W a)))
      ((P b).pullback (T.homOfLE (inf_le_right : W a ⊓ W b ≤ W b))))
    (i j : ι) :
    chartPullbackModule (fun a => (W a).ι) (fun a => (P a).L) i
        (inf_le_left : chartOverlap (fun a => (W a).ι) i j ≤ ((W i).ι).opensRange) ≅
      chartPullbackModule (fun a => (W a).ι) (fun a => (P a).L) j
        (inf_le_right : chartOverlap (fun a => (W a).ι) i j ≤ ((W j).ι).opensRange) :=
  Quadruple.chartWitness f W P hP i j (chartOpenLift ((W i).ι) inf_le_left)
    (chartOpenLift ((W j).ι) inf_le_right) (by rw [chartOpenLift_fac, chartOpenLift_fac])

open Stacks.SheafOfModules in
/-- **The cocycle condition of
`Stacks.SheafOfModules.ModulesGlueData.exists_modulesGlueData_of_chartPullbackIso`, discharged for
the comparisons of the chart modules of a family of quadruples.** Each of the three restrictions
to the triple overlap is the comparison there
(`...RelativeProjQcohSheaf.chartPullbackRestrict_chartWitness`), and those compose by
`...Quadruple.chartWitness_trans`. No hypothesis beyond the pairwise strict equivalences is
used. -/
theorem chartGlueIso_cocycle (f : T ⟶ S) {ι : Type u}
    (W : ι → T.Opens) (P : (a : ι) → Quadruple ((W a).ι ≫ f) A d)
    (hP : ∀ a b, Quadruple.StrictlyEquivalentOver (overlapBase_eq f W a b)
      ((P a).pullback (T.homOfLE (inf_le_left : W a ⊓ W b ≤ W a)))
      ((P b).pullback (T.homOfLE (inf_le_right : W a ⊓ W b ≤ W b))))
    (i j k : ι) :
    chartPullbackRestrict (fun a => (W a).ι) (fun a => (P a).L)
          (chartTripleOverlap_le_fst (fun a => (W a).ι) i j k)
          (chartGlueIso f W P hP i j).hom ≫
        chartPullbackRestrict (fun a => (W a).ι) (fun a => (P a).L)
          (chartTripleOverlap_le_snd (fun a => (W a).ι) i j k)
          (chartGlueIso f W P hP j k).hom =
      chartPullbackRestrict (fun a => (W a).ι) (fun a => (P a).L)
        (chartTripleOverlap_le_out (fun a => (W a).ι) i j k)
        (chartGlueIso f W P hP i k).hom := by
  have h1 := chartPullbackRestrict_chartWitness f W P hP
    (chartTripleOverlap_le_fst (fun a => (W a).ι) i j k) i j inf_le_left inf_le_right
  have h2 := chartPullbackRestrict_chartWitness f W P hP
    (chartTripleOverlap_le_snd (fun a => (W a).ι) i j k) j k inf_le_left inf_le_right
  have h3 := chartPullbackRestrict_chartWitness f W P hP
    (chartTripleOverlap_le_out (fun a => (W a).ι) i j k) i k inf_le_left inf_le_right
  refine Eq.trans (congrArg (fun z => z ≫ _) h1) (Eq.trans (congrArg (fun z => _ ≫ z) h2) ?_)
  refine Eq.trans ?_ h3.symm
  exact congrArg Iso.hom (Quadruple.chartWitness_trans f W P hP i j k _ _ _ _ _)

/-! ### The glueing datum, named, with its comparisons -/

open Stacks.SheafOfModules in
/-- **The glueing datum of the invertible modules of a family of quadruples.** This is the first
ingredient of `...RelativeProjQcohSheaf.QuadrupleGlues`: the invertible module of the glued
quadruple is the sheaf of modules this datum glues to. No covering hypothesis is needed for the
datum itself; it enters only in
`...RelativeProjQcohSheaf.isInvertibleModule_quadrupleGlueData_glued`.

It is a **named object** rather than an existential, and that is what the next ingredient needs:
a morphism *out of* the glued module has to be built from morphisms on the chart modules, and the
hypothesis of
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` compares them through
the comparisons `Stacks.SheafOfModules.ModulesGlueData.chartSectionsIso`, whose very *type*
mentions the datum's chart modules — so with the datum hidden behind an `∃` the comparison
cannot be stated, let alone proved.

It is a `def` in the `chartModule` spelling, not in the inverse-image one: the kernel wall
recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/ModuleGlueChartPullback.lean` is a cocycle in the
`...SheafOfModules.chartPullbackRestrict` spelling appearing in the binders of a `def`, and
`Stacks.SheafOfModules.ModulesGlueData.ofChartPullbackIso_cocycle` converts that cocycle into the
`...SheafOfModules.chartModuleRestrict` one before it reaches this binder. -/
def quadrupleGlueData (f : T ⟶ S) {ι : Type u}
    (W : ι → T.Opens) (P : (a : ι) → Quadruple ((W a).ι ≫ f) A d)
    (hP : ∀ a b, Quadruple.StrictlyEquivalentOver (overlapBase_eq f W a b)
      ((P a).pullback (T.homOfLE (inf_le_left : W a ⊓ W b ≤ W a)))
      ((P b).pullback (T.homOfLE (inf_le_right : W a ⊓ W b ≤ W b)))) :
    ModulesGlueData T (fun a => (W a).ι) :=
  ModulesGlueData.ofChartIso (fun a => (W a).ι) (fun a => (P a).L)
    (ModulesGlueData.ofChartPullbackIsoFamily _ _ (chartGlueIso f W P hP))
    (ModulesGlueData.ofChartPullbackIso_cocycle _ _ (chartGlueIso f W P hP)
      (chartGlueIso_cocycle f W P hP))

open Stacks.SheafOfModules in
/-- The chart modules of `...RelativeProjQcohSheaf.quadrupleGlueData` are the invertible modules
of the given quadruples. -/
theorem quadrupleGlueData_mod (f : T ⟶ S) {ι : Type u}
    (W : ι → T.Opens) (P : (a : ι) → Quadruple ((W a).ι ≫ f) A d)
    (hP : ∀ a b, Quadruple.StrictlyEquivalentOver (overlapBase_eq f W a b)
      ((P a).pullback (T.homOfLE (inf_le_left : W a ⊓ W b ≤ W a)))
      ((P b).pullback (T.homOfLE (inf_le_right : W a ⊓ W b ≤ W b)))) :
    (quadrupleGlueData f W P hP).mod = fun a => (P a).L := rfl

open Stacks.SheafOfModules in
/-- **The module glued from a family of quadruples over a covering family of opens is
invertible.** The invertibility is
`Stacks.SheafOfModules.ModulesGlueData.isInvertibleModule_glued`, whose covering hypothesis is
the pointwise covering hypothesis of `...RelativeProjQcohSheaf.QuadrupleGlues` read through
`...RelativeProjQcohSheaf.iSup_opensRange_ι_eq_top`. -/
theorem isInvertibleModule_quadrupleGlueData_glued (f : T ⟶ S) {ι : Type u}
    (W : ι → T.Opens) (hW : ∀ x : T, ∃ a, x ∈ W a)
    (P : (a : ι) → Quadruple ((W a).ι ≫ f) A d)
    (hP : ∀ a b, Quadruple.StrictlyEquivalentOver (overlapBase_eq f W a b)
      ((P a).pullback (T.homOfLE (inf_le_left : W a ⊓ W b ≤ W a)))
      ((P b).pullback (T.homOfLE (inf_le_right : W a ⊓ W b ≤ W b)))) :
    Stacks.Ample.IsInvertibleModule T (quadrupleGlueData f W P hP).glued :=
  (quadrupleGlueData f W P hP).isInvertibleModule_glued (iSup_opensRange_ι_eq_top W hW)
    fun a => (P a).isInvertible

open Stacks.SheafOfModules in
/-- **The comparisons of the glued module with the invertible modules of the given quadruples are
related to one another by `...Quadruple.chartWitness`.**

This is the statement that this directory recorded as owed, and it is the compatibility
hypothesis that
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` asks of a family of
local morphisms transported to the glued module: over an open `V` of `T` inside two of the opens
of the family, reading a section of the glued module in the `i`-th quadruple and then applying
the comparison of the two quadruples there gives the same as reading it in the `j`-th.

Nothing beyond the pairwise strict equivalences `hP` enters: the comparison is
`...RelativeProjQcohSheaf.chartGlueIso`, which is `...Quadruple.chartWitness`, and the statement
is `Stacks.SheafOfModules.ModulesGlueData.ofChartIso_trans_chartSectionsIso` for the datum. -/
theorem quadrupleGlueData_trans_chartSectionsIso (f : T ⟶ S) {ι : Type u}
    (W : ι → T.Opens) (P : (a : ι) → Quadruple ((W a).ι ≫ f) A d)
    (hP : ∀ a b, Quadruple.StrictlyEquivalentOver (overlapBase_eq f W a b)
      ((P a).pullback (T.homOfLE (inf_le_left : W a ⊓ W b ≤ W a)))
      ((P b).pullback (T.homOfLE (inf_le_right : W a ⊓ W b ≤ W b))))
    (i j : ι) {V : T.Opens} (hi : V ≤ ((W i).ι).opensRange) (hj : V ≤ ((W j).ι).opensRange)
    (s : ToType ((quadrupleGlueData f W P hP).glued.val.obj (Opposite.op V))) :
    localAppFun (ofChartIsoHom (fun a => (W a).ι) (fun a => (P a).L) i j
          (ModulesGlueData.ofChartPullbackIsoFamily _ _ (chartGlueIso f W P hP) i j)).hom
        V (le_inf hi hj)
        (((quadrupleGlueData f W P hP).chartSectionsIso i hi).hom s) =
      ((quadrupleGlueData f W P hP).chartSectionsIso j hj).hom s :=
  ModulesGlueData.ofChartIso_trans_chartSectionsIso _ _ _ _ i j hi hj s

open Stacks.SheafOfModules in
/-- **The comparisons of the glued module with the invertible modules of the given quadruples
are related to one another by `...Quadruple.chartWitness`, as an equation of morphisms of sheaves
of modules.**

This is `...RelativeProjQcohSheaf.quadrupleGlueData_trans_chartSectionsIso` with the equation on
sections replaced by an equation of morphisms, which is the form a glueing argument whose local
data are morphisms of inverse images can consume: over an open `V` of `T` inside two of the chart
images, the restriction to `V` of the transposed comparison with the `i`-th quadruple, followed
by the comparison of the two quadruples there, is the restriction to `V` of the transposed
comparison with the `j`-th.

Nothing beyond the pairwise strict equivalences `hP` enters, and nothing beyond the sections
statement either: this is
`Stacks.SheafOfModules.ModulesGlueData.ofChartIso_restrictFunctor_map_chartAdjunct` for the
datum, which is `...ModulesGlueData.trans_chartAdjunct` assembled over the opens inside `V`. -/
theorem quadrupleGlueData_restrictFunctor_map_chartAdjunct (f : T ⟶ S) {ι : Type u}
    (W : ι → T.Opens) (P : (a : ι) → Quadruple ((W a).ι ≫ f) A d)
    (hP : ∀ a b, Quadruple.StrictlyEquivalentOver (overlapBase_eq f W a b)
      ((P a).pullback (T.homOfLE (inf_le_left : W a ⊓ W b ≤ W a)))
      ((P b).pullback (T.homOfLE (inf_le_right : W a ⊓ W b ≤ W b))))
    (i j : ι) {V : T.Opens} (hV : V ≤ chartOverlap (fun a => (W a).ι) i j) :
    (Scheme.Modules.restrictFunctor V.ι).map
          ((quadrupleGlueData f W P hP).chartAdjunct i) ≫
        restrictLocal (ofChartIsoHom (fun a => (W a).ι) (fun a => (P a).L) i j
          (ModulesGlueData.ofChartPullbackIsoFamily _ _ (chartGlueIso f W P hP) i j)).hom hV =
      (Scheme.Modules.restrictFunctor V.ι).map
        ((quadrupleGlueData f W P hP).chartAdjunct j) :=
  ModulesGlueData.ofChartIso_restrictFunctor_map_chartAdjunct _ _ _ _ i j hV

/-- **A family of quadruples over the restrictions of `f : T ⟶ S` to a family of opens of `T`,
pairwise strictly equivalent over the overlaps, is the family of chart modules of a glueing datum
of sheaves of modules on `T`.** The existential form of
`...RelativeProjQcohSheaf.quadrupleGlueData` and `...quadrupleGlueData_mod`, for a consumer that
needs no comparison. -/
theorem exists_modulesGlueData_of_quadrupleFamily (f : T ⟶ S) {ι : Type u}
    (W : ι → T.Opens) (P : (a : ι) → Quadruple ((W a).ι ≫ f) A d)
    (hP : ∀ a b, Quadruple.StrictlyEquivalentOver (overlapBase_eq f W a b)
      ((P a).pullback (T.homOfLE (inf_le_left : W a ⊓ W b ≤ W a)))
      ((P b).pullback (T.homOfLE (inf_le_right : W a ⊓ W b ≤ W b)))) :
    ∃ G : Stacks.SheafOfModules.ModulesGlueData T (fun a => (W a).ι),
      G.mod = fun a => (P a).L :=
  ⟨quadrupleGlueData f W P hP, quadrupleGlueData_mod f W P hP⟩

/-- **The invertible module of the glued quadruple exists.** The existential form of
`...RelativeProjQcohSheaf.quadrupleGlueData`, `...quadrupleGlueData_mod` and
`...isInvertibleModule_quadrupleGlueData_glued` together. -/
theorem exists_modulesGlueData_invertible (f : T ⟶ S) {ι : Type u}
    (W : ι → T.Opens) (hW : ∀ x : T, ∃ a, x ∈ W a)
    (P : (a : ι) → Quadruple ((W a).ι ≫ f) A d)
    (hP : ∀ a b, Quadruple.StrictlyEquivalentOver (overlapBase_eq f W a b)
      ((P a).pullback (T.homOfLE (inf_le_left : W a ⊓ W b ≤ W a)))
      ((P b).pullback (T.homOfLE (inf_le_right : W a ⊓ W b ≤ W b)))) :
    ∃ G : Stacks.SheafOfModules.ModulesGlueData T (fun a => (W a).ι),
      G.mod = (fun a => (P a).L) ∧ Stacks.Ample.IsInvertibleModule T G.glued :=
  ⟨quadrupleGlueData f W P hP, quadrupleGlueData_mod f W P hP,
    isInvertibleModule_quadrupleGlueData_glued f W hW P hP⟩

end Glue

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
