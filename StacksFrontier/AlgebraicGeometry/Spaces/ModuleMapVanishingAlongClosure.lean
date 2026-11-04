module

public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldGlobalSectionVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartMapMainClauseAffineTest
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapFibreOverBasePoint
public import StacksFrontier.RingTheory.Flat.ProjectiveMapSmulTopIdeal

/-!
# Vanishing of a map of modules on the fibres over a set, and over the closure of that set

Let `S = \Spec(R)` be an affine scheme in a big fppf site, let `X` be an algebraic space over `S`
and let `u : ℱ ⟶ 𝒢` be a map of quasi-coherent `𝒪_X`-modules with `𝒢` flat over `S` — the standing
data of Stacks 0CWA, `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation`.  For a point `s` of
the base, `u_s` is the pullback of `u` to the fibre `X_s`.  Stacks 0CWB asserts, for `X` locally of
finite presentation over `S` and `𝒢` of finite presentation, that `u_s = 0` holds at every point
`s` of the closure of a set `T` of points at which it holds.

This file carries out the source's argument *given the projectivity its geometric input produces*:
the whole proof, except for the étale localisation that makes the sections of `𝒢` projective.

## Main definitions

* `AlgebraicGeometry.Space.basePointIdeal`: the ideal of global functions on the base vanishing at
  a point, i.e. the kernel of the pullback of global functions along `\Spec κ(s) ⟶ S`.

## Main results

* `AlgebraicGeometry.Space.basePointIdeal_le_of_mem_closure`: an ideal contained in the ideal of a
  point of a set is contained in the ideal of every point of its closure.
* `Space.ModuleMapFlatTargetSituation.forall_mem_basePointIdeal_smul_top_of_fibreMapEqZero`:
  `u_s = 0` forces every value of `u` over an affine étale chart `V` of `X` into
  `𝔭_s · 𝒢(V)`.
* `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.fibreMapEqZero_of_forall_mem_smul_top`: the
  converse direction through a closed subscheme — an ideal killing the image of `u` over every
  affine chart and vanishing at `s` forces `u_s = 0`.
* `Space.ModuleMapFlatTargetSituation.fibreMapEqZero_of_mem_closure_of_projective_sections`:
  **the conclusion of Stacks 0CWB, granted projectivity of the sections of `𝒢` over every affine
  étale chart of `X`.**

## Implementation notes

**The shape of the argument.**  Both directions between `u_s = 0` and a condition on the sections
over the affine étale charts of `X` are already in the library, and they are the two ends of this
file:

* `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.val_app_mem_ker_smul_top_of_isZeroAt`
  turns the vanishing of `u_T` at an **affine** test object `T` into the statement that
  `\ker(\Gamma(S, ⊤) ⟶ \Gamma(T, ⊤))` contains every value of `u` over every affine chart.  The
  test object `\Spec κ(t)` is affine and
  `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.fibreTest` is literally
  `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.baseTest` at it, so the forward direction
  is that lemma with no further work; the ideal it produces is `basePointIdeal`.
* `Space.ModuleMapFlatTargetSituation.isZeroAt_specQuotient_of_forall_mem_smul_top`
  turns an ideal `J` killing the image of `u` over every affine chart into the vanishing of `u` on
  `\Spec(\Gamma(S, ⊤)/J)`, and vanishing is stable under base change
  (`AlgebraicGeometry.Space.ModuleMapSituation.isZeroAt_of_hom`), so it descends to `\Spec κ(s)` as
  soon as `J` vanishes at `s`.

Between the two sits the algebra of the source's last paragraph.  With `𝒢(V)` projective over
`\Gamma(S, ⊤)` the ideals killing the image of `u` over `V` are exactly those containing one least
ideal, `Stacks.Flattening.exists_least_ideal_forall_mem_smul_top`, which is the flattening ideal
`I` of Stacks 083L.  The hypothesis gives `I ⊆ 𝔭_t` for every `t ∈ T`; a function in `I` therefore
vanishes on `T`, hence on its closure, hence at `s`; so `I ⊆ 𝔭_s` and `𝔭_s` kills the image of `u`
over `V`.  The topological step is
`AlgebraicGeometry.Scheme.appTop_fromSpecResidueField_eq_zero_of_mem_closure`: the locus where a
global function vanishes is the complement of its basic open.

**Why the ideal rather than the residue field.**  The source phrases the algebra over the residue
fields: `u ⊗_R κ(t) = 0` for `t ∈ T` gives `u ⊗_R κ(s) = 0`.  Here the condition is carried by the
ideal `𝔭_t` instead, as `u(ℱ(V)) ⊆ 𝔭_t · 𝒢(V)`, which is the vanishing of `u ⊗_R R/𝔭_t`.  Nothing
is lost and nothing is gained: for `𝒢(V)` flat over `R` — which it is, by
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.flat_sections_G` — the quotient `R/𝔭` injects
into `κ(𝔭)` after tensoring with `𝒢(V)`, so the two conditions agree, and that equivalence is
exactly what the library's two endpoint lemmas have already performed in each direction.  Working
with the ideal keeps both endpoints usable verbatim.

**The interface to the remaining work.**  All of the geometry is in
`Space.ModuleMapFlatTargetSituation.fibreMapEqZero_of_mem_closure_of_forall_chart`,
whose only hypothesis beyond the situation is, for each **affine** étale chart `V` of `X`, one
implication of commutative algebra: that `u(ℱ(V)) ⊆ 𝔭_t · 𝒢(V)` for all `t ∈ T` gives
`u(ℱ(V)) ⊆ 𝔭_s · 𝒢(V)`.  Two discharges of that implication are available:

* over `\Gamma(S, ⊤)` directly, when `𝒢(V)` is a projective `\Gamma(S, ⊤)`-module —
  `fibreMapEqZero_of_mem_closure_of_projective_sections` below;
* **étale locally over the base**, which is the form Stacks 0CVY produces —
  `Stacks.Flattening.forall_mem_ker_smul_top_of_projective_of_isOpenMap`, which asks only for
  projectivity of `𝒢(V)` over a ring `R'` whose map `\Spec R' ⟶ \Spec \Gamma(S, ⊤)` is open, with
  `R' ⊗_{\Gamma(S, ⊤)} κ(s)` reduced — both of which hold for `R' = \Gamma(E', ⊤)` with `E' ⟶ S`
  étale and affine, the latter by
  `AlgebraicGeometry.isReduced_appTop_tensorProduct_residueField`.

**Why no tag is claimed here.**  Stacks 0CWB does not assume projectivity of the sections at
all; it *derives* it, étale locally, from `X` being locally of finite presentation over `S` and
`𝒢` being of finite presentation, by Stacks 0CVY.  Registering the tag on a statement of this
file would therefore be registering it on an input the source proves.  The tag is registered,
unconditionally, at
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.fibreMapEqZero_of_mem_closure`, which
closes the three steps that stood between Stacks 0CVY and the chart hypothesis above: the
chartwise finite-presentation passage is
`AlgebraicGeometry.Space.isFinitePresentation_restrictToChart`; the module of 0CVY's conclusion
is identified with the sections over a chart, and `Module.Projective` carried across the
identification, by
`AlgebraicGeometry.Space.projective_sections_of_projective_pullback_restrictToChart`; and the
every-chart quantifier is replaced by one chart per point of `|X|` in
`Space.ModuleMapFlatTargetSituation.fibreMapEqZero_of_mem_closure_of_forall_point`,
which is the shape Stacks 0CVY produces.

## References

* [Stacks Project, Tag 0CWB](https://stacks.math.columbia.edu/tag/0CWB)
* [Stacks Project, Tag 0CWA](https://stacks.math.columbia.edu/tag/0CWA)
* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
* [Stacks Project, Tag 083L](https://stacks.math.columbia.edu/tag/083L)
* [Stacks Project, Tag 0CVY](https://stacks.math.columbia.edu/tag/0CVY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The ideal of a point of the base -/

/-- **The ideal of global functions on the base vanishing at a point**: the kernel of the pullback
of global functions along the structure morphism of `\Spec κ(s)` over the base.  Spelt through the
object `AlgebraicGeometry.Space.specResidueFieldOver` of the big fppf category, so that it is
literally the ideal that
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.val_app_mem_ker_smul_top_of_isZeroAt`
produces at the test object `\Spec κ(s)`. -/
def basePointIdeal (s : S) : Ideal Γ(S, ⊤) :=
  RingHom.ker (show Γ(S, ⊤) →+*
      (Γ((BigFppfOver.toScheme B S hS).obj (specResidueFieldOver B S hS s), ⊤) : Type u) from
    (B.inclusion.map (specResidueFieldOver B S hS s).hom).appTop.hom)

/-- Membership in `AlgebraicGeometry.Space.basePointIdeal` is the vanishing of the pullback of the
function along `\Spec κ(s) ⟶ S`. -/
theorem mem_basePointIdeal_iff (s : S) (f : Γ(S, ⊤)) :
    f ∈ basePointIdeal B S hS s ↔ (S.fromSpecResidueField s).appTop.hom f = 0 :=
  RingHom.mem_ker

/-- **`AlgebraicGeometry.Space.basePointIdeal` is the kernel of evaluation of global functions at
the point.**  Both are cut out by the complement of the basic open: the pullback along
`\Spec κ(s) ⟶ S` by `AlgebraicGeometry.Scheme.appTop_fromSpecResidueField_eq_zero_iff`, the
evaluation by `AlgebraicGeometry.Scheme.evaluation_eq_zero_iff_notMem_basicOpen`.

This is the identification a consumer needs in order to read `basePointIdeal` as
`\ker(\Gamma(S, ⊤) ⟶ κ(s))` for the `\Gamma(S, ⊤)`-algebra structure on the residue field that
`AlgebraicGeometry.isReduced_appTop_tensorProduct_residueField` and
`Stacks.Flattening.forall_mem_ker_smul_top_of_projective_of_isOpenMap` use. -/
theorem basePointIdeal_eq_ker_Γevaluation (s : S) :
    basePointIdeal B S hS s = RingHom.ker (S.Γevaluation s).hom :=
  Ideal.ext fun f =>
    (((mem_basePointIdeal_iff B S hS s f).trans
          (Scheme.appTop_fromSpecResidueField_eq_zero_iff S s f)).trans
        (S.evaluation_eq_zero_iff_notMem_basicOpen (U := ⊤) s trivial f).symm).trans
      RingHom.mem_ker.symm

/-- A global function lying in the ideal of every point of a set lies in the ideal of every point of
its closure. -/
private theorem mem_basePointIdeal_of_mem_closure {T : Set S} {s : S} (hs : s ∈ closure T)
    {f : Γ(S, ⊤)} (hf : ∀ t ∈ T, f ∈ basePointIdeal B S hS t) : f ∈ basePointIdeal B S hS s :=
  (mem_basePointIdeal_iff B S hS s f).mpr
    (Scheme.appTop_fromSpecResidueField_eq_zero_of_mem_closure S f T hs fun t ht =>
      (mem_basePointIdeal_iff B S hS t f).mp (hf t ht))

/-- **An ideal of functions vanishing at every point of a set vanishes at every point of its
closure.**

The locus where one global function vanishes is closed
(`AlgebraicGeometry.Scheme.isClosed_setOf_appTop_fromSpecResidueField_eq_zero`), so this is the
pointwise statement applied to each element of the ideal. -/
theorem basePointIdeal_le_of_mem_closure {I : Ideal Γ(S, ⊤)} (T : Set S) {s : S}
    (hs : s ∈ closure T) (hI : ∀ t ∈ T, I ≤ basePointIdeal B S hS t) :
    I ≤ basePointIdeal B S hS s := fun _ hf =>
  mem_basePointIdeal_of_mem_closure B S hS hs fun t ht => hI t ht hf

namespace ModuleMapFlatTargetSituation

variable [IsAffine S] (D : ModuleMapFlatTargetSituation B S hS)

/-- The test scheme of the fibre over a point of the base is the test scheme of the object
`\Spec κ(s)` of the big fppf category: both are the unique morphism to the final algebraic space
over the base. -/
theorem fibreTest_eq_baseTest (s : S) :
    D.fibreTest B S hS s = D.baseTest B S hS (specResidueFieldOver B S hS s) := rfl

/-! ### From `u_s = 0` to the sections over the affine charts -/

/-- **`u_s = 0` forces every value of `u` over an affine étale chart of `X` into `𝔭_s · 𝒢(V)`**,
where `𝔭_s` is the ideal of functions on the base vanishing at `s`.

This is
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.val_app_mem_ker_smul_top_of_isZeroAt` at the
affine test object `\Spec κ(s)`; the fibre test scheme of `s` is the base test scheme of that
object by `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.fibreTest_eq_baseTest`. -/
theorem forall_mem_basePointIdeal_smul_top_of_fibreMapEqZero (s : S)
    (hzero : D.FibreMapEqZero B S hS s) (V : SmallEtale B S hS D.X.1)
    (hV : IsAffine (chartScheme V)) :
    letI : Module Γ(S, ⊤) (D.G.val.obj (op V) : Type u) :=
      Module.compHom _ (chartToBaseRingHom B S hS D.X V)
    ∀ m : D.F.val.obj (op V),
      (D.u.val.app (op V)).hom m ∈
        basePointIdeal B S hS s •
          (⊤ : Submodule Γ(S, ⊤) (D.G.val.obj (op V) : Type u)) :=
  D.val_app_mem_ker_smul_top_of_isZeroAt B S hS (specResidueFieldOver B S hS s) V hzero
    (isAffine_Spec (S.residueField s)) hV

/-! ### From the sections over the affine charts back to `u_s = 0` -/

/-- **An ideal killing the image of `u` over every affine étale chart of `X` and vanishing at `s`
forces `u_s = 0`.**

The ideal cuts out a closed subscheme `Z = \Spec(\Gamma(S, ⊤)/J)` of the base over which `u`
becomes zero (`isZeroAt_specQuotient_of_forall_mem_smul_top`),
and vanishing after base change is stable under further base change, so it descends along the
factorisation of `\Spec κ(s) ⟶ S` through `Z` that `J ⊆ 𝔭_s` provides. -/
theorem fibreMapEqZero_of_forall_mem_smul_top (s : S) (J : Ideal Γ(S, ⊤))
    (hJ : J ≤ basePointIdeal B S hS s)
    (h : ∀ V : SmallEtale B S hS D.X.1,
      IsAffine ((SmallEtale.toOver B S hS D.X.1 ⋙ BigFppfOver.toScheme B S hS).obj V) →
      letI : Module Γ(S, ⊤) (D.G.val.obj (op V) : Type u) :=
        Module.compHom _ (chartToBaseRingHom B S hS D.X V)
      ∀ m : D.F.val.obj (op V), (D.u.val.app (op V)).hom m ∈
        J • (⊤ : Submodule Γ(S, ⊤) (D.G.val.obj (op V) : Type u))) :
    D.FibreMapEqZero B S hS s := by
  obtain ⟨ψ⟩ := exists_hom_specQuotientOver B S hS J (specResidueFieldOver B S hS s) hJ
  refine (D.toModuleMapSituation B S hS).isZeroAt_of_hom (modulePullbackSystem B S hS)
    (T := D.specQuotientTest B S hS J) (T' := D.fibreTest B S hS s) ?_
    (isZeroAt_specQuotient_of_forall_mem_smul_top B S hS D J h)
  exact CostructuredArrow.homMk ψ ((terminalSpace_isTerminal B S hS).hom_ext _ _)

/-! ### The geometric reduction of Stacks 0CWB -/

/-- **The geometric reduction of Stacks 0CWB.**  In the situation of Stacks 0CWA, let `T` be a set
of points of the base, let `s` be a point of its closure, and suppose `u_t = 0` for every `t ∈ T`.
If for every **affine** étale chart `V` of `X` the ideal condition passes from the points of `T` to
`s` — that is, if `u(ℱ(V)) ⊆ 𝔭_t · 𝒢(V)` for all `t ∈ T` implies `u(ℱ(V)) ⊆ 𝔭_s · 𝒢(V)` — then
`u_s = 0`.

Everything geometric in the source's proof is here, and the hypothesis `hchart` is exactly the
commutative algebra of its last paragraph, one chart at a time.  Two discharges of `hchart` are
available and are recorded in the implementation notes of this file; the source's own, through
Stacks 0CVY, is not, which is why no tag is claimed.

The forward direction of the chart condition comes from
`forall_mem_basePointIdeal_smul_top_of_fibreMapEqZero`
and the backward one from
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.fibreMapEqZero_of_forall_mem_smul_top`. -/
theorem fibreMapEqZero_of_mem_closure_of_forall_chart
    (T : Set S) (s : S)
    (hchart : ∀ V : SmallEtale B S hS D.X.1, IsAffine (chartScheme V) →
      letI : Module Γ(S, ⊤) (D.G.val.obj (op V) : Type u) :=
        Module.compHom _ (chartToBaseRingHom B S hS D.X V)
      (∀ t ∈ T, ∀ m : D.F.val.obj (op V), (D.u.val.app (op V)).hom m ∈
          basePointIdeal B S hS t •
            (⊤ : Submodule Γ(S, ⊤) (D.G.val.obj (op V) : Type u))) →
        ∀ m : D.F.val.obj (op V), (D.u.val.app (op V)).hom m ∈
          basePointIdeal B S hS s •
            (⊤ : Submodule Γ(S, ⊤) (D.G.val.obj (op V) : Type u)))
    (hT : ∀ t ∈ T, D.FibreMapEqZero B S hS t) :
    D.FibreMapEqZero B S hS s :=
  D.fibreMapEqZero_of_forall_mem_smul_top B S hS s (basePointIdeal B S hS s) le_rfl
    fun V hV => hchart V hV fun t ht =>
      D.forall_mem_basePointIdeal_smul_top_of_fibreMapEqZero B S hS t (hT t ht) V hV

/-! ### The conclusion of Stacks 0CWB, granted projectivity of the sections -/

/-- **The conclusion of Stacks 0CWB, granted projectivity of the sections of `𝒢` over the affine
étale charts of `X`.**

In the situation of Stacks 0CWA, let `T` be a set of points of the base and let `s` be a point of
its closure.  Assume that for every affine étale chart `V` of `X` the sections `𝒢(V)` form a
projective `\Gamma(S, ⊤)`-module.  If `u_t = 0` for every `t ∈ T`, then `u_s = 0`.

This is the source's proof of Stacks 0CWB downstream of its geometric input.  For each affine chart
`V`, the flattening ideal of Stacks 083L of the map of sections over `V` is the least ideal killing
the image of that map; it is contained in the ideal `𝔭_t` of each `t ∈ T`, hence consists of
functions vanishing on `T`, hence of functions vanishing at `s`, hence is contained in `𝔭_s`.  So
`𝔭_s` kills the image of `u` over every affine chart, and that gives `u_s = 0`.

The hypothesis `hproj` is **not** one of the hypotheses of Stacks 0CWB: the source derives
projectivity étale locally over the base from finite presentation, by Stacks 0CVY.  See the
implementation notes of this file. -/
theorem fibreMapEqZero_of_mem_closure_of_projective_sections
    (hproj : ∀ V : SmallEtale B S hS D.X.1, IsAffine (chartScheme V) →
      letI : Module Γ(S, ⊤) (D.G.val.obj (op V) : Type u) :=
        Module.compHom _ (chartToBaseRingHom B S hS D.X V)
      Module.Projective Γ(S, ⊤) (D.G.val.obj (op V) : Type u))
    (T : Set S) (s : S) (hs : s ∈ closure T)
    (hT : ∀ t ∈ T, D.FibreMapEqZero B S hS t) :
    D.FibreMapEqZero B S hS s := by
  refine D.fibreMapEqZero_of_mem_closure_of_forall_chart B S hS T s (fun V hV hfwd => ?_) hT
  let := chartBaseAlgebra B S hS D.X V
  let : Module Γ(S, ⊤) (D.F.val.obj (op V) : Type u) :=
    Module.compHom _ (chartToBaseRingHom B S hS D.X V)
  let : Module Γ(S, ⊤) (D.G.val.obj (op V) : Type u) :=
    Module.compHom _ (chartToBaseRingHom B S hS D.X V)
  have := isScalarTower_chartRing_sections B S hS D.X D.F V
  have := isScalarTower_chartRing_sections B S hS D.X D.G V
  exact Stacks.Flattening.forall_mem_smul_top_of_forall_le
    ((D.u.val.app (op V)).hom.restrictScalars Γ(S, ⊤)) (hproj V hV)
    (fun t : T => basePointIdeal B S hS t.1) (basePointIdeal B S hS s)
    (fun t => hfwd t.1 t.2)
    fun _ ha => mem_basePointIdeal_of_mem_closure B S hS hs fun t ht => ha ⟨t, ht⟩

end ModuleMapFlatTargetSituation

end AlgebraicGeometry.Space

end
