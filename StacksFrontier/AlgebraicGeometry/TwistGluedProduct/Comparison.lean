module

public import StacksFrontier.AlgebraicGeometry.NestedCocycleTail.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistCocycle.Pointwise
public import StacksFrontier.AlgebraicGeometry.ProjTwistCompTwistMap.Generic
public import StacksFrontier.AlgebraicGeometry.ThetaMultiplicative.Basic
public import StacksFrontier.AlgebraicGeometry.TwistRigidity.Pointwise

/-!
# Tag 01NR's glued twist comparison is multiplicative

`StacksFrontier/AlgebraicGeometry/TwistDataConstruction/Absolute.lean` records two obstructions to a
product on the glued twists of a relative projective spectrum: the nested cocycle
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle`, and the multiplicativity of
the glued comparison `Stacks.AlgebraicGeometry.ChartTransRelativeProj.cmpGen` between two charts.
The first is now discharged by `Stacks.AlgebraicGeometry.ProjTwistCocycle.isNestedCocycle`. **This
file discharges the second**, together with the corresponding statement for the unit section.

## Main results

The chain runs from Tag 01NO's chart-level comparison to the glued one.

* `Stacks.AlgebraicGeometry.TwistGluedProduct.restrictTwistIso_val_app_preimage`: **the pointwise
  value of Tag 01NO's chart-level comparison `…ChartTransRelativeProj.restrictTwistIso` on a
  section.** It is Tag 01MY's fibre comparison `…ProjTwistCompare.twistFibreMap` applied to the
  value of the section at the image point, and nothing else. This is the statement the whole file
  turns on, and nothing in either tree had it:
  `StacksFrontier/AlgebraicGeometry/ChartCocycleRigidity/Basic.lean` records that the only
  declarations whose statements mention `restrictTwistIso` are its definition, the `pushNested`
  and `cmpNested` computations, and two unproved predicates.
* `Stacks.AlgebraicGeometry.TwistGluedProduct.chartLeg_val_preimage` and `chartLeg_val`: the same
  read through `…NestedCocycleTail.chartLeg`, which is the form `cmpNested` is computed in. Every
  statement below is in that spelling, for the reason recorded in the implementation notes.
* `Stacks.AlgebraicGeometry.TwistGluedProduct.chartLeg_mul` and `chartLeg_one`: the chart-level
  comparison carries the canonical product of two absolute twist sections to the product of their
  images, and the unit section to the unit section.
* `Stacks.AlgebraicGeometry.TwistGluedProduct.cmpNested_mul` and `cmpNested_one`: the same for the
  pushed-forward comparison `…ChartTransRelativeProj.cmpNested` of a **base-nested** pair of affine
  opens, read on sections over an open of the relative projective spectrum.
* `Stacks.AlgebraicGeometry.TwistGluedProduct.meetLoc_mul` and `meetLoc_one`: the same for
  `…ChartTransRelativeProj.meetLoc`, the comparison through a third chart which the glued one is
  glued from. Both are
  instances of the generic cancellation lemmas `isMul_of_model` and `isOne_of_model`.
* `Stacks.AlgebraicGeometry.TwistGluedProduct.cmpGen_mul` and `cmpGen_one`: **the deliverable.**
  The glued comparison `…ChartTransRelativeProj.cmpGen`, for a pair of affine opens of the base
  whose inverse images are nested, respects the canonical product in all integer degrees and the
  unit section in degree zero.

Auxiliary statements: the generic ones, with every ingredient a variable, are
`restrictIso_val_app_map`, `transpose_val_app`, `restrict_val_app_eq_transpose`, `chartLeg_apply`,
`isMul_of_model`, `isOne_of_model`, `push_resLE_val`, `push_resLE_product` and
`push_resLE_unit`; at the instance, `restrictTwistIso_hom_eq`, `image_mem_of_image_le`,
`resLE_cmpGen_eq_meetLoc`, `resLE_cmpGen_mul` and `resLE_cmpGen_one`.

## Implementation notes: the route, and why this one

**Everything is pointwise.** A section of `twistingSheaf 𝒜 n` over an open is a dependent family
of homogeneous fractions, so two sections are equal as soon as their values agree at every point;
and `…TwistRigidity.absoluteTwistProduct_apply` says the canonical product has, at each point, the
product of the two values. Since Tag 01MY's fibre comparison is a **ring homomorphism**,
multiplicativity and unitality of anything computed pointwise by it are `map_mul` and `map_one`.

The one thing missing was that pointwise computation for `restrictTwistIso`. It is obtained here by
crossing to the adjoint transpose, where the computation already existed:

* `restrictTwistIso` is `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` followed by
  Tag 01NO's isomorphism on the pullback. The unit of the pullback--pushforward adjunction factors
  through the unit of the restriction adjunction across that first factor
  (`…ProjTwistTheta.restrictUnit_comp_map_restrictFunctorIsoPullback`, read on sections as
  `…ProjTwistCompTwistMap.pullbackSectionOn_eq_restrictIso`), so the chart comparison on a
  restricted section **is** the adjoint transpose of Tag 01NO's isomorphism on the section
  upstairs: that is `restrict_val_app_eq_transpose`.
* `…ProjTwistCocycle.transpose_projInclusionTwistIso` identifies that transpose with
  `…ProjTwistCocycle.twistTranspose` at Tag 01MY's twist map, and
  `…ProjTwistCocycle.twistTranspose_app_val` computes *that* at a point as the fibre comparison.

Composing the two gives the value over the preimage `p ⁻¹ᵁ T₀` of an open of the larger chart
(`restrictTwistIso_val_app_preimage`). Every consumer below meets it there: the open of the
smaller chart is `chart W hW ⁻¹ᵁ V`, which `…NestedCocycleReduction.chart_preimage_eq` identifies
with `p ⁻¹ᵁ (chart U hU ⁻¹ᵁ V)`. So `chartLeg_val` takes that identification of opens as a free
hypothesis and substitutes it away, and no transport of opens is ever performed underneath a
`val.app`.

The alternative route, transporting
`…TwistMultCompat.projInclusionTwistIso_preserves_products` — Tag 01NO's own
multiplication-compatibility assertion, which is an equation of morphisms on the **tensor sheaf**
of the pullbacks — across the `restrictFunctorIsoPullback` factor and onto sections, is not
used: it requires reading a `tensorSheafMap` on sections through a sheafification, and the
pointwise route above needs no tensor sheaf at all.

**Elaboration costs.**

* Supplying the factorisation of `restrictTwistIso` as an *implicit* argument determined by `rfl`
  is a `whnf` timeout: the comparison is then spelled as the composite in the conclusion and has to
  be matched against `restrictTwistIso` underneath a `val.app`. The delta step is therefore taken
  once, at the level of morphisms, by `restrictTwistIso_hom_eq`, and the subject of
  `restrict_val_app_eq_transpose` is an explicit argument.
* Extending the value from `p ⁻¹ᵁ T₀` to an arbitrary open `T` with a free inclusion
  `p ''ᵁ T ⟶ T₀` by one naturality step along `T ≤ p ⁻¹ᵁ T₀` does not work.
  Assembled at the instance from `PresheafOfModules.naturality_apply` and
  `…NestedCocycleReduction.restrict_val_map` it is `maximum recursion depth`; packaged as a
  generic lemma with every ingredient a variable it elaborates and is then a **kernel**
  deterministic timeout. Taking the identification of opens as a hypothesis and substituting it
  away costs nothing and loses no generality: see the paragraph above.
* **The decisive cost is the statement shape, not the proof.** A declaration whose *statement*
  applies `(restrictTwistIso …).hom.val.app (op T)` to a section of the twist over `p ''ᵁ T`
  obliges the kernel to identify the two readings of the restricted sections, which
  `StacksFrontier/AlgebraicGeometry/ChartCocycleRigidity/DegreeSection.lean` puts at about two
  minutes apiece; one occurrence per declaration is affordable and three are a kernel timeout.
  Every statement below is therefore spelled with `…NestedCocycleTail.chartLeg`, whose *declared*
  domain is the restricted sections, so the identification is paid once inside `chartLeg`'s own
  definition and the kernel only ever substitutes into it. That is exactly the remedy that file's
  "what does help" paragraph prescribes.
* For the same reason `…ChartCocycleRigidity.IsLegMultiplicative` is **not** discharged here even
  though `chartLeg_mul` is its content: that predicate is stated with three occurrences of the
  costly shape, so a declaration proving it cannot be checked at the stock kernel budget. Closing
  it needs the predicate itself restated through `chartLeg`, in the file that defines it.
* **The cancellation step must take the local isomorphisms, not functions coerced from them.**
  `meetLoc` is a comparison through a third chart cancelled against another, so its
  multiplicativity is a statement about nine comparisons and three products. Stated over plain
  functions — the nine comparisons passed as `fun x => e.app V hV x` — it exceeds the
  elaborator's recursion depth, because the nine carrier types then have to be inferred from the
  lambdas and each is a `↥` of a pushed-forward twist at a concrete chart. Stated over
  `TopCat.Sheaf.LocalModuleEquiv`, as `isMul_of_model` and `isOne_of_model` are, the types are
  read off the comparisons' own types and nothing is inferred. Two intermediate
  spellings fail: the chain written with `Eq.trans` on
  `…ChartTransRelativeProj.IsComposite` and `cmpNested_mul` (`maximum recursion depth` at the
  first `Eq.trans`), and the same with the products wrapped in a `def` declared at the
  pushed-forward spelling (`maximum recursion depth` again, now in the wrapper's own transport).
* One limit is raised: since the Lean v4.35.0 bump the kernel check of
  `restrictTwistIso_val_app_preimage`'s proof exceeds the stock budget (its statement alone
  checks), so that declaration carries `set_option maxHeartbeats 800000`. Nothing else is raised.

**What is not done.** `Stacks.AlgebraicGeometry.RelativeProjTwists.ChartData` and `TwistData` are
still absent, and nothing here supplies them: the glued pieces are one sheaf of modules per integer
degree, their quasi-coherence is not proved, the homogeneous-section map `ψ` of a `TwistData` and
its three compatibilities are not constructed, and the associativity, commutativity and unit laws
of the glued product -- which are statements about the glued sheaves, not about the comparison --
are not proved here either. What this file closes is exactly the named blocker: the comparison
between two charts is multiplicative, so a product defined chart by chart is well defined.

No `stacks` attribute is attached to any declaration below. Tag 01NO's
multiplication-compatibility assertion is already carried by
`…TwistMultCompat.projInclusionTwistIso_preserves_products`, and Tag 01NR asks for a complete
twist datum, which this is not.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ChartTransNonNested
open Stacks.AlgebraicGeometry.ChartTransRelativeProj
open Stacks.AlgebraicGeometry.NestedCocycleReduction
open Stacks.AlgebraicGeometry.NestedCocycleTail
open Stacks.AlgebraicGeometry.ProjInclusionTwist
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.ProjTwistCocycle
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.ProjTwistCompTwistMap
open Stacks.AlgebraicGeometry.PullbackUnit
open Stacks.AlgebraicGeometry.PushforwardCocycle
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.TwistGluedProduct

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w

/-! ### Generic readings on sections -/

/-- **The restriction-to-pullback comparison on a restricted section** is the image of the section
under the unit of the pullback--pushforward adjunction. The inclusion of opens is a free
argument. -/
public theorem restrictIso_val_app_map {X Y : Scheme.{u}} (p : Y ⟶ X)
    [IsOpenImmersion p] (M : X.Modules) (T₀ : X.Opens)
    (i : p ''ᵁ (p ⁻¹ᵁ T₀) ⟶ T₀) (s : M.val.obj (op T₀)) :
    ((Scheme.Modules.restrictFunctorIsoPullback p).app M).hom.val.app (op (p ⁻¹ᵁ T₀))
        (M.val.map i.op s) = pullbackSectionOn p M T₀ s := by
  refine Eq.trans ?_ (pullbackSectionOn_eq_restrictIso p M T₀ s).symm
  refine congrArg (((Scheme.Modules.restrictFunctorIsoPullback p).app M).hom.val.app
    (op (p ⁻¹ᵁ T₀))) ?_
  exact (map_val_congr M i (homOfLE (p.image_preimage_le T₀)) s).trans
    (restrictAdjunction_unit_val_app p M T₀ s).symm

/-- **The adjoint transpose on a section**: the unit of the adjunction followed by the component of
the morphism at the preimage. -/
public theorem transpose_val_app {X Y : Scheme.{u}} (p : Y ⟶ X) (M : X.Modules)
    {N : Y.Modules} (φ : (Scheme.Modules.pullback p).obj M ⟶ N) (T₀ : X.Opens)
    (s : M.val.obj (op T₀)) :
    (transpose p M φ).val.app (op T₀) s =
      φ.val.app (op (p ⁻¹ᵁ T₀)) (pullbackSectionOn p M T₀ s) := rfl

/-- **An isomorphism presented as the restriction-to-pullback comparison followed by a morphism out
of the pullback, read on a restricted section, is the adjoint transpose.** The subject `e` is an
explicit argument identified by an equation of *morphisms*: with the factorisation supplied
implicitly by `rfl` instead, the comparison is spelled as the composite in the conclusion and has
to be matched against its own name underneath a `val.app`, which is a `whnf` timeout. -/
public theorem restrict_val_app_eq_transpose {X Y : Scheme.{u}} (p : Y ⟶ X)
    [IsOpenImmersion p] {M : X.Modules} {N : Y.Modules}
    (φ : (Scheme.Modules.pullback p).obj M ⟶ N)
    (e : (Scheme.Modules.restrictFunctor p).obj M ⟶ N)
    (he : e = ((Scheme.Modules.restrictFunctorIsoPullback p).app M).hom ≫ φ)
    (T₀ : X.Opens) (i : p ''ᵁ (p ⁻¹ᵁ T₀) ⟶ T₀) (s : M.val.obj (op T₀)) :
    e.val.app (op (p ⁻¹ᵁ T₀)) (M.val.map i.op s)
      = (transpose p M φ).val.app (op T₀) s :=
  (comp_val_app_of _ φ he (p ⁻¹ᵁ T₀) (restrictIso_val_app_map p M T₀ i s)).trans
    (transpose_val_app p M φ T₀ s).symm

/-- **The leg of a chart comparison, read on a section.** One delta step on
`Stacks.AlgebraicGeometry.NestedCocycleTail.chartLeg`, at the level of variables. -/
public theorem chartLeg_apply {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] {M : X.Modules}
    {N : Y.Modules} (e : (Scheme.Modules.restrictFunctor g).obj M ≅ N) {T : Y.Opens}
    {T₀ : X.Opens} (j : g ''ᵁ T ⟶ T₀) (t : M.val.obj (op T₀)) :
    chartLeg g e j t = e.hom.val.app (op T) (M.val.map j.op t) := rfl

/-- **A comparison which cancels against a comparison through a model is multiplicative when both
of those are.**

The nine comparisons are *local isomorphisms*, not functions coerced from them, and the three
products are functions on the sections the local isomorphisms are already indexed by. That is the
one structural decision this lemma carries: with the comparisons passed as coerced functions
instead, the nine carrier types have to be inferred from the lambdas, which at a concrete chart of
a relative projective spectrum exceeds the elaborator's recursion depth. Here they are read off
the local isomorphisms' own types, and nothing is inferred. -/
public theorem isMul_of_model {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    {Mi Mj Mij Ni Nj Nij Qi Qj Qij : PresheafOfModules.{u} 𝒪} {W₀ V : Opens X} (hV : V ≤ W₀)
    (ei : TopCat.Sheaf.LocalModuleEquiv Mi Ni W₀)
    (ej : TopCat.Sheaf.LocalModuleEquiv Mj Nj W₀)
    (eij : TopCat.Sheaf.LocalModuleEquiv Mij Nij W₀)
    (bi : TopCat.Sheaf.LocalModuleEquiv Ni Qi W₀)
    (bj : TopCat.Sheaf.LocalModuleEquiv Nj Qj W₀)
    (bij : TopCat.Sheaf.LocalModuleEquiv Nij Qij W₀)
    (ai : TopCat.Sheaf.LocalModuleEquiv Mi Qi W₀)
    (aj : TopCat.Sheaf.LocalModuleEquiv Mj Qj W₀)
    (aij : TopCat.Sheaf.LocalModuleEquiv Mij Qij W₀)
    (pM : Mi.obj (op V) → Mj.obj (op V) → Mij.obj (op V))
    (pN : Ni.obj (op V) → Nj.obj (op V) → Nij.obj (op V))
    (pQ : Qi.obj (op V) → Qj.obj (op V) → Qij.obj (op V))
    (hi : IsComposite ei bi ai V hV hV) (hj : IsComposite ej bj aj V hV hV)
    (hij : IsComposite eij bij aij V hV hV)
    (hA : ∀ x y, aij.app V hV (pM x y) = pQ (ai.app V hV x) (aj.app V hV y))
    (hB : ∀ u v, bij.app V hV (pN u v) = pQ (bi.app V hV u) (bj.app V hV v))
    (x : Mi.obj (op V)) (y : Mj.obj (op V)) :
    eij.app V hV (pM x y) = pN (ei.app V hV x) (ej.app V hV y) :=
  (bij.app V hV).injective (((hij (pM x y)).trans (hA x y)).trans
    ((congrArg₂ pQ (hi x) (hj y)).symm.trans (hB (ei.app V hV x) (ej.app V hV y)).symm))

/-- **The same for a unit section.** -/
public theorem isOne_of_model {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    {M N Q : PresheafOfModules.{u} 𝒪} {W₀ V : Opens X} (hV : V ≤ W₀)
    (e : TopCat.Sheaf.LocalModuleEquiv M N W₀) (b : TopCat.Sheaf.LocalModuleEquiv N Q W₀)
    (a : TopCat.Sheaf.LocalModuleEquiv M Q W₀) (uM : M.obj (op V)) (uN : N.obj (op V))
    (uQ : Q.obj (op V)) (hc : IsComposite e b a V hV hV) (hA : a.app V hV uM = uQ)
    (hB : b.app V hV uN = uQ) : e.app V hV uM = uN :=
  (b.app V hV).injective ((hc uM).trans (hA.trans hB.symm))

/-! ### The twisting sheaves, read at a point -/

section Pointwise

variable {R : Type u} {σ : Type w} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {X : Scheme.{u}} (g : AlgebraicGeometry.Proj 𝒜 ⟶ X)

/-- **Restriction in a twisting sheaf pushed forward along a morphism out of the projective
spectrum reindexes the family of values**, and does nothing else. -/
public theorem push_resLE_val (n : ℤ) {V V' : X.Opens} (hV : V' ≤ V)
    (x : (pushforwardVal g (twistingSheaf 𝒜 n)).obj (op V)) (y : ↥(g ⁻¹ᵁ V')) :
    ((pushforwardVal g (twistingSheaf 𝒜 n)).resLE hV x).1 y = x.1 ⟨y.1, hV y.2⟩ := rfl

/-- **The canonical product of two absolute twist sections commutes with restriction in the
pushforward.** Both sides have, at every point, the product of the two values. -/
public theorem push_resLE_product (i j : ℤ) {V V' : X.Opens} (hV : V' ≤ V)
    (a : (twistingSheaf 𝒜 i).val.obj (op (g ⁻¹ᵁ V)))
    (b : (twistingSheaf 𝒜 j).val.obj (op (g ⁻¹ᵁ V))) :
    (pushforwardVal g (twistingSheaf 𝒜 (i + j))).resLE hV
        (absoluteTwistProduct 𝒜 i j (g ⁻¹ᵁ V) a b)
      = absoluteTwistProduct 𝒜 i j (g ⁻¹ᵁ V')
          ((pushforwardVal g (twistingSheaf 𝒜 i)).resLE hV a)
          ((pushforwardVal g (twistingSheaf 𝒜 j)).resLE hV b) := by
  refine Subtype.ext (funext fun y => ?_)
  refine Eq.trans (push_resLE_val 𝒜 g (i + j) hV _ y) ?_
  refine Eq.trans (TwistRigidity.absoluteTwistProduct_apply 𝒜 i j (g ⁻¹ᵁ V) a b
    ⟨y.1, hV y.2⟩) ?_
  refine Eq.trans ?_ (TwistRigidity.absoluteTwistProduct_apply 𝒜 i j (g ⁻¹ᵁ V') _ _ y).symm
  exact congrArg₂ (· * ·) (push_resLE_val 𝒜 g i hV a y).symm (push_resLE_val 𝒜 g j hV b y).symm

/-- **The unit section commutes with restriction in the pushforward.** Both sides have the value
`1` at every point. -/
public theorem push_resLE_unit {V V' : X.Opens} (hV : V' ≤ V) :
    (pushforwardVal g (twistingSheaf 𝒜 0)).resLE hV (absoluteTwistUnit 𝒜 (g ⁻¹ᵁ V))
      = absoluteTwistUnit 𝒜 (g ⁻¹ᵁ V') := by
  refine Subtype.ext (funext fun y => ?_)
  refine Eq.trans (push_resLE_val 𝒜 g 0 hV _ y) ?_
  refine Eq.trans (ThetaMultiplicative.absoluteTwistUnit_apply 𝒜 (g ⁻¹ᵁ V) ⟨y.1, hV y.2⟩) ?_
  exact (ThetaMultiplicative.absoluteTwistUnit_apply 𝒜 (g ⁻¹ᵁ V') y).symm

end Pointwise

/-! ### Tag 01NO's chart-level comparison, at a point -/

section Chart

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (W U : S.Opens) (h : W ≤ U)
  (hW : IsAffineOpen W) (hU : IsAffineOpen U)

/-- Tag 01NO's chart comparison is the restriction-to-pullback comparison followed by Tag 01NO's
isomorphism on the pullback: one delta step, taken at the level of morphisms. -/
public theorem restrictTwistIso_hom_eq (n : ℤ) :
    (restrictTwistIso A W U h hW hU n).hom =
      ((Scheme.Modules.restrictFunctorIsoPullback
            (projInclusionMap A W U h hW hU)).app (twistingSheaf (A.grading U) n)).hom ≫
        (projInclusionTwistIso A W U h hW hU n).hom := rfl

set_option maxHeartbeats 800000 in
/-- **The pointwise value of Tag 01NO's chart comparison, over the preimage of an open of the
larger chart.** -/
public theorem restrictTwistIso_val_app_preimage (n : ℤ)
    (T₀ : (AlgebraicGeometry.Proj (A.grading U)).Opens)
    (i : projInclusionMap A W U h hW hU ''ᵁ
      (projInclusionMap A W U h hW hU ⁻¹ᵁ T₀) ⟶ T₀)
    (s : (twistingSheaf (A.grading U) n).val.obj (op T₀))
    (y : ↥(projInclusionMap A W U h hW hU ⁻¹ᵁ T₀))
    (hm : (y.1 : AlgebraicGeometry.Proj (A.grading W)) ∈
      mapDomain (A.grading U) (A.grading W) (A.res h))
    (hbp : basePoint (A.grading U) (A.grading W) (A.res h) ⟨y.1, hm⟩ ∈ T₀) :
    ((restrictTwistIso A W U h hW hU n).hom.val.app
          (op (projInclusionMap A W U h hW hU ⁻¹ᵁ T₀))
          ((twistingSheaf (A.grading U) n).val.map i.op s)).1 y
      = twistFibreMap (A.grading U) (A.grading W) (A.res h) ⟨y.1, hm⟩
          (s.1 ⟨basePoint (A.grading U) (A.grading W) (A.res h) ⟨y.1, hm⟩, hbp⟩) := by
  have h1 := restrict_val_app_eq_transpose (projInclusionMap A W U h hW hU)
    (projInclusionTwistIso A W U h hW hU n).hom (restrictTwistIso A W U h hW hU n).hom
    (restrictTwistIso_hom_eq A W U h hW hU n) T₀ i s
  have h2 := Stacks.AlgebraicGeometry.ChartTransRelativeProj.app_apply_of_morphism_eq
    (transpose_projInclusionTwistIso A W U h hW hU n) T₀ s
  refine Eq.trans (TwistRigidity.twist_val_congr (A.grading W) (h1.trans h2) y) ?_
  exact twistTranspose_app_val (A.grading U) (A.grading W) (A.res h)
    (projInclusionTopSection A W U h hW hU) (projInclusionMap A W U h hW hU)
    (projInclusionMap_eq_comp A W U h hW hU) (projInclusionTopSection_ι A W U h hW hU)
    n T₀ s y hm hbp

/-- **The pointwise value of one leg of Tag 01NO's chart comparison, over the preimage of an open
of the larger chart.** Read through `Stacks.AlgebraicGeometry.NestedCocycleTail.chartLeg`, which
is the form `…ChartTransRelativeProj.cmpNested` is computed in and the form every statement below
uses: `chartLeg` has the restricted sections as its *declared* domain, so no statement below asks
the kernel to identify the two readings of them. -/
public theorem chartLeg_val_preimage (n : ℤ)
    (T₀ : (AlgebraicGeometry.Proj (A.grading U)).Opens)
    (i : projInclusionMap A W U h hW hU ''ᵁ
      (projInclusionMap A W U h hW hU ⁻¹ᵁ T₀) ⟶ T₀)
    (s : (twistingSheaf (A.grading U) n).val.obj (op T₀))
    (y : ↥(projInclusionMap A W U h hW hU ⁻¹ᵁ T₀))
    (hm : (y.1 : AlgebraicGeometry.Proj (A.grading W)) ∈
      mapDomain (A.grading U) (A.grading W) (A.res h))
    (hbp : basePoint (A.grading U) (A.grading W) (A.res h) ⟨y.1, hm⟩ ∈ T₀) :
    (chartLeg (projInclusionMap A W U h hW hU)
          (restrictTwistIso A W U h hW hU n) i s).1 y
      = twistFibreMap (A.grading U) (A.grading W) (A.res h) ⟨y.1, hm⟩
          (s.1 ⟨basePoint (A.grading U) (A.grading W) (A.res h) ⟨y.1, hm⟩, hbp⟩) :=
  (TwistRigidity.twist_val_congr (A.grading W)
      (chartLeg_apply (projInclusionMap A W U h hW hU)
        (restrictTwistIso A W U h hW hU n) i s) y).trans
    (restrictTwistIso_val_app_preimage A W U h hW hU n T₀ i s y hm hbp)

/-- **The pointwise value of one leg of Tag 01NO's chart comparison over an open of the smaller
chart which is the preimage of an open of the larger one**, with that identification of opens
supplied as a free hypothesis rather than by its canonical proof.

The identification is substituted away, which costs nothing. Deducing the statement for an
unrelated open instead, by one naturality step along `T ≤ p ⁻¹ᵁ T₀`, elaborates and is then a
**kernel** deterministic timeout; see the implementation notes. No generality is lost: every
consumer below meets the hypothesis. -/
public theorem chartLeg_val (n : ℤ)
    {T : (AlgebraicGeometry.Proj (A.grading W)).Opens}
    {T₀ : (AlgebraicGeometry.Proj (A.grading U)).Opens}
    (hq : T = projInclusionMap A W U h hW hU ⁻¹ᵁ T₀)
    (j : projInclusionMap A W U h hW hU ''ᵁ T ⟶ T₀)
    (s : (twistingSheaf (A.grading U) n).val.obj (op T₀)) (y : ↥T)
    (hm : (y.1 : AlgebraicGeometry.Proj (A.grading W)) ∈
      mapDomain (A.grading U) (A.grading W) (A.res h))
    (hbp : basePoint (A.grading U) (A.grading W) (A.res h) ⟨y.1, hm⟩ ∈ T₀) :
    (chartLeg (projInclusionMap A W U h hW hU)
          (restrictTwistIso A W U h hW hU n) j s).1 y
      = twistFibreMap (A.grading U) (A.grading W) (A.res h) ⟨y.1, hm⟩
          (s.1 ⟨basePoint (A.grading U) (A.grading W) (A.res h) ⟨y.1, hm⟩, hbp⟩) := by
  subst hq
  exact chartLeg_val_preimage A W U h hW hU n T₀ j s y hm hbp

/-- The image, under the transition morphism, of a point of an open of the smaller chart lies in
any open containing the image of that open. -/
public theorem image_mem_of_image_le
    (T : (AlgebraicGeometry.Proj (A.grading W)).Opens)
    (T₀ : (AlgebraicGeometry.Proj (A.grading U)).Opens)
    (j : projInclusionMap A W U h hW hU ''ᵁ T ⟶ T₀) (y : ↥T)
    (hm : (y.1 : AlgebraicGeometry.Proj (A.grading W)) ∈
      mapDomain (A.grading U) (A.grading W) (A.res h)) :
    basePoint (A.grading U) (A.grading W) (A.res h) ⟨y.1, hm⟩ ∈ T₀ := by
  have hb := basePoint_of_section (A.grading U) (A.grading W) (A.res h)
    (projInclusionTopSection A W U h hW hU) (projInclusionMap A W U h hW hU)
    (projInclusionMap_eq_comp A W U h hW hU) (projInclusionTopSection_ι A W U h hW hU) y.1 hm
  have himg : (projInclusionMap A W U h hW hU).base y.1 ∈ T₀ := j.le ⟨y.1, y.2, rfl⟩
  rw [hb]
  exact himg

/-- **Tag 01NO's chart comparison carries the canonical product of two absolute twist sections to
the product of their images.** The fibre comparison is a ring homomorphism and the product is
pointwise, so this is `map_mul` at every point. -/
public theorem chartLeg_mul (i j : ℤ)
    {T : (AlgebraicGeometry.Proj (A.grading W)).Opens}
    {T₀ : (AlgebraicGeometry.Proj (A.grading U)).Opens}
    (hq : T = projInclusionMap A W U h hW hU ⁻¹ᵁ T₀)
    (k : projInclusionMap A W U h hW hU ''ᵁ T ⟶ T₀)
    (a : (twistingSheaf (A.grading U) i).val.obj (op T₀))
    (b : (twistingSheaf (A.grading U) j).val.obj (op T₀)) :
    chartLeg (projInclusionMap A W U h hW hU) (restrictTwistIso A W U h hW hU (i + j)) k
        (absoluteTwistProduct (A.grading U) i j T₀ a b)
      = absoluteTwistProduct (A.grading W) i j T
          (chartLeg (projInclusionMap A W U h hW hU) (restrictTwistIso A W U h hW hU i) k a)
          (chartLeg (projInclusionMap A W U h hW hU) (restrictTwistIso A W U h hW hU j) k b) := by
  refine Subtype.ext (funext fun y => ?_)
  have hm := mem_mapDomain_of_section (A.grading U) (A.grading W) (A.res h)
    (projInclusionTopSection A W U h hW hU) (projInclusionTopSection_ι A W U h hW hU) y.1
  have hbp := image_mem_of_image_le A W U h hW hU T T₀ k y hm
  refine Eq.trans (chartLeg_val A W U h hW hU (i + j) hq k _ y hm hbp) ?_
  refine Eq.trans (congrArg (twistFibreMap (A.grading U) (A.grading W) (A.res h) ⟨y.1, hm⟩)
    (TwistRigidity.absoluteTwistProduct_apply (A.grading U) i j T₀ a b
      ⟨basePoint (A.grading U) (A.grading W) (A.res h) ⟨y.1, hm⟩, hbp⟩)) ?_
  refine Eq.trans
    (map_mul (twistFibreMap (A.grading U) (A.grading W) (A.res h) ⟨y.1, hm⟩) _ _) ?_
  refine Eq.trans ?_ (TwistRigidity.absoluteTwistProduct_apply (A.grading W) i j T _ _ y).symm
  exact congrArg₂ (· * ·)
    (chartLeg_val A W U h hW hU i hq k a y hm hbp).symm
    (chartLeg_val A W U h hW hU j hq k b y hm hbp).symm

/-- **Tag 01NO's chart comparison carries the unit section of the degree-zero twist to the unit
section.** The fibre comparison is a ring homomorphism and the unit section has the value `1` at
every point, so this is `map_one` at every point. -/
public theorem chartLeg_one
    {T : (AlgebraicGeometry.Proj (A.grading W)).Opens}
    {T₀ : (AlgebraicGeometry.Proj (A.grading U)).Opens}
    (hq : T = projInclusionMap A W U h hW hU ⁻¹ᵁ T₀)
    (k : projInclusionMap A W U h hW hU ''ᵁ T ⟶ T₀) :
    chartLeg (projInclusionMap A W U h hW hU) (restrictTwistIso A W U h hW hU 0) k
        (absoluteTwistUnit (A.grading U) T₀)
      = absoluteTwistUnit (A.grading W) T := by
  refine Subtype.ext (funext fun y => ?_)
  have hm := mem_mapDomain_of_section (A.grading U) (A.grading W) (A.res h)
    (projInclusionTopSection A W U h hW hU) (projInclusionTopSection_ι A W U h hW hU) y.1
  have hbp := image_mem_of_image_le A W U h hW hU T T₀ k y hm
  refine Eq.trans (chartLeg_val A W U h hW hU 0 hq k _ y hm hbp) ?_
  refine Eq.trans (congrArg (twistFibreMap (A.grading U) (A.grading W) (A.res h) ⟨y.1, hm⟩)
    (ThetaMultiplicative.absoluteTwistUnit_apply (A.grading U) T₀
      ⟨basePoint (A.grading U) (A.grading W) (A.res h) ⟨y.1, hm⟩, hbp⟩)) ?_
  exact (map_one (twistFibreMap (A.grading U) (A.grading W) (A.res h) ⟨y.1, hm⟩)).trans
    (ThetaMultiplicative.absoluteTwistUnit_apply (A.grading W) T y).symm

end Chart

/-! ### The pushed-forward comparison of a base-nested pair -/

section Nested

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (W U : S.Opens) (h : W ≤ U)
  (hW : IsAffineOpen W) (hU : IsAffineOpen U)

/-- **The pushed-forward comparison of a base-nested pair respects the canonical product**, on the
sections over every open of the relative projective spectrum inside the inverse image of the
smaller affine open. -/
public theorem cmpNested_mul (i j : ℤ) (V : (relativeProj A).scheme.Opens)
    (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ W)
    (a : (twistingSheaf (A.grading U) i).val.obj
      (op ((relativeProj A).chart U hU ⁻¹ᵁ V)))
    (b : (twistingSheaf (A.grading U) j).val.obj
      (op ((relativeProj A).chart U hU ⁻¹ᵁ V))) :
    (cmpNested A W U h hW hU (i + j)).app V hV
        (absoluteTwistProduct (A.grading U) i j ((relativeProj A).chart U hU ⁻¹ᵁ V) a b)
      = absoluteTwistProduct (A.grading W) i j ((relativeProj A).chart W hW ⁻¹ᵁ V)
          ((cmpNested A W U h hW hU i).app V hV a)
          ((cmpNested A W U h hW hU j).app V hV b) := by
  refine Eq.trans (cmpNested_app_val A W U h hW hU (i + j) V hV _) ?_
  refine Eq.trans (chartLeg_mul A W U h hW hU i j (chart_preimage_eq A W U h hW hU V)
    (homOfLE (image_preimage_le_preimage A W U h hW hU V)) a b) ?_
  exact congrArg₂ (absoluteTwistProduct (A.grading W) i j
      ((relativeProj A).chart W hW ⁻¹ᵁ V))
    (cmpNested_app_val A W U h hW hU i V hV a).symm
    (cmpNested_app_val A W U h hW hU j V hV b).symm

/-- **The pushed-forward comparison of a base-nested pair carries the unit section to the unit
section.** -/
public theorem cmpNested_one (V : (relativeProj A).scheme.Opens)
    (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ W) :
    (cmpNested A W U h hW hU 0).app V hV
        (absoluteTwistUnit (A.grading U) ((relativeProj A).chart U hU ⁻¹ᵁ V))
      = absoluteTwistUnit (A.grading W) ((relativeProj A).chart W hW ⁻¹ᵁ V) :=
  (cmpNested_app_val A W U h hW hU 0 V hV _).trans
    (chartLeg_one A W U h hW hU (chart_preimage_eq A W U h hW hU V)
      (homOfLE (image_preimage_le_preimage A W U h hW hU V)))

end Nested

/-! ### The comparison through a third chart -/

section Meet

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (W U : S.Opens) (hW : IsAffineOpen W)
  (hU : IsAffineOpen U)

/-- **The comparison through a third chart respects the canonical product.** `meetLoc` is the
comparison with the member's own chart followed by the inverse of the other one, and the member's
comparison with the smaller chart is injective, so this is `isMul_of_model` at `cmpNested_mul`
for the two nested pairs `m ⊆ U` and `m ⊆ W`. -/
public theorem meetLoc_mul (i j : ℤ) (m : meetIndex W U)
    (V : (relativeProj A).scheme.Opens)
    (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ (m.1.1 : S.Opens))
    (a : (twistingSheaf (A.grading U) i).val.obj
      (op ((relativeProj A).chart U hU ⁻¹ᵁ V)))
    (b : (twistingSheaf (A.grading U) j).val.obj
      (op ((relativeProj A).chart U hU ⁻¹ᵁ V))) :
    (meetLoc A W U hW hU (i + j) m).app V hV
        (absoluteTwistProduct (A.grading U) i j ((relativeProj A).chart U hU ⁻¹ᵁ V) a b)
      = absoluteTwistProduct (A.grading W) i j ((relativeProj A).chart W hW ⁻¹ᵁ V)
          ((meetLoc A W U hW hU i m).app V hV a)
          ((meetLoc A W U hW hU j m).app V hV b) :=
  isMul_of_model hV
    (meetLoc A W U hW hU i m) (meetLoc A W U hW hU j m) (meetLoc A W U hW hU (i + j) m)
    (cmpNested A (m.1.1 : S.Opens) W (m.2.trans inf_le_left) m.1.2 hW i)
    (cmpNested A (m.1.1 : S.Opens) W (m.2.trans inf_le_left) m.1.2 hW j)
    (cmpNested A (m.1.1 : S.Opens) W (m.2.trans inf_le_left) m.1.2 hW (i + j))
    (cmpNested A (m.1.1 : S.Opens) U (m.2.trans inf_le_right) m.1.2 hU i)
    (cmpNested A (m.1.1 : S.Opens) U (m.2.trans inf_le_right) m.1.2 hU j)
    (cmpNested A (m.1.1 : S.Opens) U (m.2.trans inf_le_right) m.1.2 hU (i + j))
    (absoluteTwistProduct (A.grading U) i j ((relativeProj A).chart U hU ⁻¹ᵁ V))
    (absoluteTwistProduct (A.grading W) i j ((relativeProj A).chart W hW ⁻¹ᵁ V))
    (absoluteTwistProduct (A.grading (m.1.1 : S.Opens)) i j
      ((relativeProj A).chart (m.1.1 : S.Opens) m.1.2 ⁻¹ᵁ V))
    (isComposite_meetLoc A W U hW hU i m (m.2.trans inf_le_left) (m.2.trans inf_le_right) V hV)
    (isComposite_meetLoc A W U hW hU j m (m.2.trans inf_le_left) (m.2.trans inf_le_right) V hV)
    (isComposite_meetLoc A W U hW hU (i + j) m (m.2.trans inf_le_left)
      (m.2.trans inf_le_right) V hV)
    (cmpNested_mul A (m.1.1 : S.Opens) U (m.2.trans inf_le_right) m.1.2 hU i j V hV)
    (cmpNested_mul A (m.1.1 : S.Opens) W (m.2.trans inf_le_left) m.1.2 hW i j V hV) a b

/-- **The comparison through a third chart carries the unit section to the unit section.** -/
public theorem meetLoc_one (m : meetIndex W U) (V : (relativeProj A).scheme.Opens)
    (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ (m.1.1 : S.Opens)) :
    (meetLoc A W U hW hU 0 m).app V hV
        (absoluteTwistUnit (A.grading U) ((relativeProj A).chart U hU ⁻¹ᵁ V))
      = absoluteTwistUnit (A.grading W) ((relativeProj A).chart W hW ⁻¹ᵁ V) :=
  isOne_of_model hV (meetLoc A W U hW hU 0 m)
    (cmpNested A (m.1.1 : S.Opens) W (m.2.trans inf_le_left) m.1.2 hW 0)
    (cmpNested A (m.1.1 : S.Opens) U (m.2.trans inf_le_right) m.1.2 hU 0)
    (absoluteTwistUnit (A.grading U) ((relativeProj A).chart U hU ⁻¹ᵁ V))
    (absoluteTwistUnit (A.grading W) ((relativeProj A).chart W hW ⁻¹ᵁ V))
    (absoluteTwistUnit (A.grading (m.1.1 : S.Opens))
      ((relativeProj A).chart (m.1.1 : S.Opens) m.1.2 ⁻¹ᵁ V))
    (isComposite_meetLoc A W U hW hU 0 m (m.2.trans inf_le_left) (m.2.trans inf_le_right) V hV)
    (cmpNested_one A (m.1.1 : S.Opens) U (m.2.trans inf_le_right) m.1.2 hU V hV)
    (cmpNested_one A (m.1.1 : S.Opens) W (m.2.trans inf_le_left) m.1.2 hW V hV)

end Meet

/-! ### The glued comparison -/

section Glue

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (W U : S.Opens) (hW : IsAffineOpen W)
  (hU : IsAffineOpen U)
  (hpre : (relativeProj A).toBase ⁻¹ᵁ W ≤ (relativeProj A).toBase ⁻¹ᵁ U)

/-- **Over an open inside the inverse image of an affine open of the base below both, the glued
comparison restricted from a larger open is the member's own comparison through its own chart.**
This is the naturality of the glued comparison followed by
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.cmpGen_agreeOn_meetLoc`, and it is the only
handle the glueing step uses. -/
public theorem resLE_cmpGen_eq_meetLoc (n : ℤ) (hcoc : IsNestedCocycle A n)
    (p : S.affineOpens) (hpW : (p.1 : S.Opens) ≤ W) (hpU : (p.1 : S.Opens) ≤ U)
    (V V₀ : (relativeProj A).scheme.Opens) (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ W)
    (hV₀ : V₀ ≤ V) (hV₀p : V₀ ≤ (relativeProj A).toBase ⁻¹ᵁ (p.1 : S.Opens))
    (t : (twistingSheaf (A.grading U) n).val.obj
      (op ((relativeProj A).chart U hU ⁻¹ᵁ V))) :
    (pushforwardVal ((relativeProj A).chart W hW) (twistingSheaf (A.grading W) n)).resLE hV₀
        ((cmpGen A W U hW hU n hpre hcoc).app V hV t)
      = (meetLoc A W U hW hU n ⟨p, le_inf hpW hpU⟩).app V₀ hV₀p
          ((pushforwardVal ((relativeProj A).chart U hU)
            (twistingSheaf (A.grading U) n)).resLE hV₀ t) := by
  refine Eq.trans ((cmpGen A W U hW hU n hpre hcoc).naturality hV hV₀ t).symm ?_
  exact cmpGen_agreeOn_meetLoc A W U hW hU n hpre hcoc p hpW hpU V₀ (hV₀.trans hV) hV₀p _

/-- **The glued comparison respects the canonical product over one member of the cover.** Both
sides are restricted to the inverse image of an affine open of the base below both, where the
glued comparison is that member's own comparison through its own chart.

Split off from `cmpGen_mul` so that no declaration carries both the covering argument and this
chain: assembled into one declaration the pair is a `whnf` timeout. -/
public theorem resLE_cmpGen_mul (i j : ℤ) (hci : IsNestedCocycle A i) (hcj : IsNestedCocycle A j)
    (hcij : IsNestedCocycle A (i + j)) (p : S.affineOpens) (hpW : (p.1 : S.Opens) ≤ W)
    (hpU : (p.1 : S.Opens) ≤ U) (V V₀ : (relativeProj A).scheme.Opens)
    (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ W) (hV₀ : V₀ ≤ V)
    (hV₀p : V₀ ≤ (relativeProj A).toBase ⁻¹ᵁ (p.1 : S.Opens))
    (a : (twistingSheaf (A.grading U) i).val.obj
      (op ((relativeProj A).chart U hU ⁻¹ᵁ V)))
    (b : (twistingSheaf (A.grading U) j).val.obj
      (op ((relativeProj A).chart U hU ⁻¹ᵁ V))) :
    (pushforwardVal ((relativeProj A).chart W hW)
          (twistingSheaf (A.grading W) (i + j))).resLE hV₀
        ((cmpGen A W U hW hU (i + j) hpre hcij).app V hV
          (absoluteTwistProduct (A.grading U) i j ((relativeProj A).chart U hU ⁻¹ᵁ V) a b))
      = (pushforwardVal ((relativeProj A).chart W hW)
          (twistingSheaf (A.grading W) (i + j))).resLE hV₀
          (absoluteTwistProduct (A.grading W) i j ((relativeProj A).chart W hW ⁻¹ᵁ V)
            ((cmpGen A W U hW hU i hpre hci).app V hV a)
            ((cmpGen A W U hW hU j hpre hcj).app V hV b)) := by
  have h₀ := resLE_cmpGen_eq_meetLoc A W U hW hU hpre (i + j) hcij p hpW hpU V V₀ hV hV₀ hV₀p
    (absoluteTwistProduct (A.grading U) i j ((relativeProj A).chart U hU ⁻¹ᵁ V) a b)
  have hₐ := resLE_cmpGen_eq_meetLoc A W U hW hU hpre i hci p hpW hpU V V₀ hV hV₀ hV₀p a
  have h_b := resLE_cmpGen_eq_meetLoc A W U hW hU hpre j hcj p hpW hpU V V₀ hV hV₀ hV₀p b
  have hprodU := push_resLE_product (A.grading U) ((relativeProj A).chart U hU) i j hV₀ a b
  have hprodW := push_resLE_product (A.grading W) ((relativeProj A).chart W hW) i j hV₀
    ((cmpGen A W U hW hU i hpre hci).app V hV a)
    ((cmpGen A W U hW hU j hpre hcj).app V hV b)
  have hmeet := meetLoc_mul A W U hW hU i j ⟨p, le_inf hpW hpU⟩ V₀ hV₀p
    ((pushforwardVal ((relativeProj A).chart U hU) (twistingSheaf (A.grading U) i)).resLE hV₀ a)
    ((pushforwardVal ((relativeProj A).chart U hU) (twistingSheaf (A.grading U) j)).resLE hV₀ b)
  refine h₀.trans ?_
  refine Eq.trans (congrArg
    (fun z => (meetLoc A W U hW hU (i + j) ⟨p, le_inf hpW hpU⟩).app V₀ hV₀p z) hprodU) ?_
  refine hmeet.trans ?_
  refine Eq.trans ?_ hprodW.symm
  exact congrArg₂ (absoluteTwistProduct (A.grading W) i j
      ((relativeProj A).chart W hW ⁻¹ᵁ V₀)) hₐ.symm h_b.symm

/-- Two sections of the pushed-forward twist over `V` are equal when their restrictions to the
inverse images of the affine opens of the base below both `W` and `U` are. -/
private theorem eq_of_resLE_eq (n : ℤ) (V : (relativeProj A).scheme.Opens)
    (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ W) (hVU : V ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    (x y : (pushforwardVal ((relativeProj A).chart W hW) (twistingSheaf (A.grading W) n)).obj
      (op V))
    (h : ∀ r : {r : S.affineOpens // (r.1 : S.Opens) ≤ W ⊓ U},
      (pushforwardVal ((relativeProj A).chart W hW) (twistingSheaf (A.grading W) n)).resLE
          (inf_le_left : V ⊓ (relativeProj A).toBase ⁻¹ᵁ (r.1.1 : S.Opens) ≤ V) x
        = (pushforwardVal ((relativeProj A).chart W hW) (twistingSheaf (A.grading W) n)).resLE
          (inf_le_left : V ⊓ (relativeProj A).toBase ⁻¹ᵁ (r.1.1 : S.Opens) ≤ V) y) :
    x = y :=
  TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf (isSheaf_pushChart A W hW n)
    (fun r : {r : S.affineOpens // (r.1 : S.Opens) ≤ W ⊓ U} =>
      V ⊓ (relativeProj A).toBase ⁻¹ᵁ (r.1.1 : S.Opens)) (fun _ => inf_le_left)
    (TopCat.Sheaf.le_iSup_inf_of_le (le_iSup_preimage_inf A W U V hV hVU)) h

/-- **The glued comparison respects the canonical product**, in all integer degrees, on the
sections over every open of the relative projective spectrum inside the inverse image of the
smaller affine open.

Checked on the cover of the open by the inverse images of the affine opens of the base below both,
with `resLE_cmpGen_mul` supplying the equation over each member. -/
public theorem cmpGen_mul (i j : ℤ) (hci : IsNestedCocycle A i) (hcj : IsNestedCocycle A j)
    (hcij : IsNestedCocycle A (i + j)) (V : (relativeProj A).scheme.Opens)
    (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ W)
    (a : (twistingSheaf (A.grading U) i).val.obj
      (op ((relativeProj A).chart U hU ⁻¹ᵁ V)))
    (b : (twistingSheaf (A.grading U) j).val.obj
      (op ((relativeProj A).chart U hU ⁻¹ᵁ V))) :
    (cmpGen A W U hW hU (i + j) hpre hcij).app V hV
        (absoluteTwistProduct (A.grading U) i j ((relativeProj A).chart U hU ⁻¹ᵁ V) a b)
      = absoluteTwistProduct (A.grading W) i j ((relativeProj A).chart W hW ⁻¹ᵁ V)
          ((cmpGen A W U hW hU i hpre hci).app V hV a)
          ((cmpGen A W U hW hU j hpre hcj).app V hV b) :=
  eq_of_resLE_eq A W U hW (i + j) V hV (hV.trans hpre) _ _ fun r =>
    resLE_cmpGen_mul A W U hW hU hpre i j hci hcj hcij r.1
      (r.2.trans (inf_le_left : W ⊓ U ≤ W)) (r.2.trans (inf_le_right : W ⊓ U ≤ U)) V
      (V ⊓ (relativeProj A).toBase ⁻¹ᵁ (r.1.1 : S.Opens)) hV inf_le_left inf_le_right a b

/-- **The glued comparison carries the unit section of the degree-zero twist to the unit section
over one member of the cover.** -/
public theorem resLE_cmpGen_one (hcoc : IsNestedCocycle A 0) (p : S.affineOpens)
    (hpW : (p.1 : S.Opens) ≤ W) (hpU : (p.1 : S.Opens) ≤ U)
    (V V₀ : (relativeProj A).scheme.Opens) (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ W)
    (hV₀ : V₀ ≤ V) (hV₀p : V₀ ≤ (relativeProj A).toBase ⁻¹ᵁ (p.1 : S.Opens)) :
    (pushforwardVal ((relativeProj A).chart W hW) (twistingSheaf (A.grading W) 0)).resLE hV₀
        ((cmpGen A W U hW hU 0 hpre hcoc).app V hV
          (absoluteTwistUnit (A.grading U) ((relativeProj A).chart U hU ⁻¹ᵁ V)))
      = (pushforwardVal ((relativeProj A).chart W hW)
          (twistingSheaf (A.grading W) 0)).resLE hV₀
          (absoluteTwistUnit (A.grading W) ((relativeProj A).chart W hW ⁻¹ᵁ V)) := by
  have h₀ := resLE_cmpGen_eq_meetLoc A W U hW hU hpre 0 hcoc p hpW hpU V V₀ hV hV₀ hV₀p
    (absoluteTwistUnit (A.grading U) ((relativeProj A).chart U hU ⁻¹ᵁ V))
  have hunitU := push_resLE_unit (A.grading U) ((relativeProj A).chart U hU) hV₀
  have hunitW := push_resLE_unit (A.grading W) ((relativeProj A).chart W hW) hV₀
  have hmeet := meetLoc_one A W U hW hU ⟨p, le_inf hpW hpU⟩ V₀ hV₀p
  refine h₀.trans ?_
  refine Eq.trans (congrArg
    (fun z => (meetLoc A W U hW hU 0 ⟨p, le_inf hpW hpU⟩).app V₀ hV₀p z) hunitU) ?_
  exact hmeet.trans hunitW.symm

/-- **The glued comparison carries the unit section of the degree-zero twist to the unit
section.** Checked on the same cover. -/
public theorem cmpGen_one (hcoc : IsNestedCocycle A 0) (V : (relativeProj A).scheme.Opens)
    (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ W) :
    (cmpGen A W U hW hU 0 hpre hcoc).app V hV
        (absoluteTwistUnit (A.grading U) ((relativeProj A).chart U hU ⁻¹ᵁ V))
      = absoluteTwistUnit (A.grading W) ((relativeProj A).chart W hW ⁻¹ᵁ V) :=
  eq_of_resLE_eq A W U hW 0 V hV (hV.trans hpre) _ _ fun r =>
    resLE_cmpGen_one A W U hW hU hpre hcoc r.1
      (r.2.trans (inf_le_left : W ⊓ U ≤ W)) (r.2.trans (inf_le_right : W ⊓ U ≤ U)) V
      (V ⊓ (relativeProj A).toBase ⁻¹ᵁ (r.1.1 : S.Opens)) hV inf_le_left inf_le_right

end Glue

end Stacks.AlgebraicGeometry.TwistGluedProduct

end
