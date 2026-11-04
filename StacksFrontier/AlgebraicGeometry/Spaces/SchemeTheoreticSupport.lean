module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceFromQuasicoherentIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSectionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteEpi
public import StacksFrontier.RingTheory.Ideal.Annihilator.FlatBaseChange

/-!
# The scheme-theoretic support of a finite type quasi-coherent module on an algebraic space

Let `X` be an algebraic space over a scheme `S` and let `F` be a finite type quasi-coherent
`𝒪_X`-module on its small étale site.  Stacks 07U0 asserts that there is a smallest closed
subspace `i : Z → X` from which `F` is a direct image, and Stacks 07U1 names it the *scheme
theoretic support* of `F`.

The regular functions on an étale chart which kill every section of `F` over every chart
refining it form an ideal, and those ideals assemble into a sheaf of ideals `Ann(F) ⊆ 𝒪_X`.  On
an affine chart `Ann(F)` is the annihilator of the module of sections there, and flat base
change for annihilators of finite modules makes it cartesian on affine charts, hence
quasi-coherent by Descent, Proposition 03DX(2); so by the surjectivity half of Stacks 03MB it
cuts out a closed subspace of `X`.  That closed subspace is the scheme-theoretic support: a
closed subspace is one from which `F` is a direct image exactly when its defining ideal
annihilates `F`, which by the order-reversing bijection of Stacks 03MB happens exactly when it
is contained in the smallest one.

## Main definitions

* `AlgebraicGeometry.Space.annihilatorIdealAt` is the ideal of regular functions on an étale
  chart killing every section of `F` over every chart over it, and
  `AlgebraicGeometry.Space.annihilatorIdealSheaf` is the resulting sheaf of ideals of `𝒪_X`.
* `AlgebraicGeometry.Space.closedSubspaceToSpace` and
  `AlgebraicGeometry.Space.closedSubspaceInclusion` read a closed subspace of `X` as an
  algebraic space and its inclusion as a morphism of algebraic spaces.
* `AlgebraicGeometry.Space.annihilatingClosedSubspaces` is the family of closed subspaces of `X`
  whose defining ideal annihilates `F`, and
  `AlgebraicGeometry.Space.schemeTheoreticSupport` is **Stacks 07U1**, its intersection.
* `AlgebraicGeometry.Space.IsQuasicoherentEssImagePushforward` is the essential-image assertion
  of Stacks 04CJ part (3) at a closed immersion, proved for every closed immersion by
  `AlgebraicGeometry.Space.isQuasicoherentEssImagePushforward_of_isClosedImmersion`.

## Main results

* `AlgebraicGeometry.Space.annihilatorIdealAt_map` and
  `AlgebraicGeometry.Space.mem_annihilatorIdealAt_of_sieve` are the two conditions making the
  chartwise annihilators a sheaf submodule of `𝒪_X`: stability under étale restriction and
  locality of membership; `AlgebraicGeometry.Space.smul_eq_zero_of_mem_annihilatorIdealAt` is
  that a function in the annihilator kills the sections over the chart itself.
* `AlgebraicGeometry.Space.mem_annihilatorIdealAt_of_isAffine` and
  `AlgebraicGeometry.Space.chartIdeal_annihilatorIdealSheaf_eq_annihilator`: on an affine chart
  the annihilator ideal is the annihilator of the module of sections.
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_annihilatorIdealSheaf` and
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_annihilatorIdealSheaf`: the annihilator ideal
  sheaf of a finite type quasi-coherent module is quasi-coherent.
* `AlgebraicGeometry.Space.schemeTheoreticSupport_eq_of_definingIdealSheaf_eq` and
  `AlgebraicGeometry.Space.exists_isClosedSubspace_schemeTheoreticSupport`: the
  scheme-theoretic support is the closed subspace cut out by the annihilator ideal sheaf.
* `AlgebraicGeometry.Space.isQuasicoherentEssImagePushforward_of_isClosedImmersion`: that
  assertion, for every closed immersion.
* `AlgebraicGeometry.Space.exists_module_on_schemeTheoreticSupport`: **Stacks 07U0**, the
  existence of the quasi-coherent module on the scheme-theoretic support whose direct image is
  `F`, together with the closed-subspace structure of that support.
* `AlgebraicGeometry.Space.schemeTheoreticSupport_le`: **Stacks 07U0**, minimality.
* `AlgebraicGeometry.Space.module_on_closedSubspace_unique`: **Stacks 07U0, part (2)**, and
  `AlgebraicGeometry.Space.isFiniteTypeOnSite_module_on_closedSubspace`: **part (3)**.

## Implementation notes

Finite type enters only through finiteness of the sections over an affine chart, so it is taken
in the sectionwise form `CategoryTheory.PresheafOfModules.IsFiniteType` of Stacks 03DL(5), which
is the form `AlgebraicGeometry.Space.moduleFinite_sections_of_isFiniteType` consumes; part (3)
takes the categorical `SheafOfModules.IsFiniteTypeOnSite`, which is the form the support
statements of Stacks 07TZ use.

**Nothing is assumed.**  The existence of the module on the scheme-theoretic support is the
essential-image assertion of Stacks 04CJ, part (3) — equivalently the essential-image assertion
of Stacks 04E5, part (2) — and it is available unconditionally: a module annihilated by the
ideal cutting out a closed subspace is a direct image by
`AlgebraicGeometry.Space.essImage_modulePushforward_of_annihilatedByKerIdeal`, and the module it
is a direct image of is quasi-coherent by Stacks 03GA, because Stacks 04CJ, part (2) identifies
it with the inverse image.  That is
`AlgebraicGeometry.Space.isQuasicoherentEssImagePushforward_of_isClosedImmersion` below.
Minimality, uniqueness and finite type of the module are unconditional as well, and so is the
whole construction of the closed subspace.

**The route taken is not the source's.** Stacks 07U0 is proved there by descending the
scheme-theoretic support of `φ^*F` along a presentation `φ : U → X`, which needs the
equivalence of quasi-coherent modules with glueing data on a presentation, Stacks 03M3; no
declaration in this tree carries that tag.  The annihilator ideal is an equivalent and cheaper
route, available because Descent, Proposition 03DX(2) and both halves of Stacks 03MB are
unconditional.

**Where the remaining clauses are.**  Part (1) is proved in
`StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupportEtaleChart`, as the étale case of
Stacks 089C, and in `StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupportChartComparison`,
with the scheme-theoretic support of the restriction to the chart taken in the sense of schemes.
Part (4) is proved for the module on the ambient space in
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperModuleSupport` and for the module on the
support in the first of those two modules.

## References

* [Stacks Project, Lemma 67.15.3 (Tag 07U0)](https://stacks.math.columbia.edu/tag/07U0)
* [Stacks Project, Definition 67.15.4 (Tag 07U1)](https://stacks.math.columbia.edu/tag/07U1)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- The ideal of regular functions on an étale chart `U` of `X` which annihilate every section
of `F` over every étale chart over `U`. -/
def annihilatorIdealAt (F : Modules.{u, u} B S hS X.1 X.2)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    Ideal (ToType
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj
        U)) where
  carrier := {a | ∀ (W : (SmallEtale B S hS X.1)ᵒᵖ) (g : U ⟶ W) (t : F.val.obj W),
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.map
      g).hom a • t = 0}
  add_mem' {a b} ha hb := by
    intro W g t
    rw [map_add, add_smul, ha W g t, hb W g t, add_zero]
  zero_mem' := by
    intro W g t
    rw [map_zero, zero_smul]
  smul_mem' c a ha := by
    intro W g t
    rw [smul_eq_mul, map_mul, mul_smul, ha W g t, smul_zero]

/-- Membership in the annihilator ideal at a chart, unfolded. -/
theorem mem_annihilatorIdealAt_iff (F : Modules.{u, u} B S hS X.1 X.2)
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : ToType
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj
        U)) :
    a ∈ annihilatorIdealAt B S hS X F U ↔
      ∀ (W : (SmallEtale B S hS X.1)ᵒᵖ) (g : U ⟶ W) (t : F.val.obj W),
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O).obj.map g).hom a • t = 0 :=
  Iff.rfl

/-- A function in the annihilator ideal at a chart kills the sections of `F` over that chart:
the defining condition at the identity morphism of the chart. -/
theorem smul_eq_zero_of_mem_annihilatorIdealAt (F : Modules.{u, u} B S hS X.1 X.2)
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : ToType
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj
        U))
    (ha : a ∈ annihilatorIdealAt B S hS X F U) (t : F.val.obj U) :
    a • t = 0 := by
  have e : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O).obj.map (𝟙 U)).hom a = a :=
    congrArg (fun φ => RingCat.Hom.hom φ a)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj.map_id U)
  exact (congrArg (· • t) e).symm.trans (ha U (𝟙 U) t)

/-- **The annihilator ideals are stable under étale restriction.** -/
theorem annihilatorIdealAt_map (F : Modules.{u, u} B S hS X.1 X.2)
    {U V : (SmallEtale B S hS X.1)ᵒᵖ} (f : U ⟶ V)
    (a : ToType
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj
        U))
    (ha : a ∈ annihilatorIdealAt B S hS X F U) :
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.map
      f).hom a ∈ annihilatorIdealAt B S hS X F V := by
  intro W g t
  have e : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O).obj.map (f ≫ g)).hom a =
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj.map g).hom
        (((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O).obj.map f).hom a) :=
    congrArg (fun φ => RingCat.Hom.hom φ a)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj.map_comp f g)
  exact (congrArg (· • t) e).symm.trans (ha W (f ≫ g) t)

/-- **Membership in the annihilator ideal is local on the small étale site.**  A regular
function whose restriction along every arrow of a covering sieve annihilates the sections of
`F` already annihilates them, because a section of `F` vanishing on a covering vanishes. -/
theorem mem_annihilatorIdealAt_of_sieve (F : Modules.{u, u} B S hS X.1 X.2)
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (s : ToType
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj
        U))
    (T : Sieve U.unop) (hT : T ∈ SmallEtale.topology B S hS X.1 U.unop)
    (h : ∀ (W : (SmallEtale B S hS X.1)ᵒᵖ) (m : U ⟶ W), T m.unop →
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj.map m).hom s ∈
        annihilatorIdealAt B S hS X F W) :
    s ∈ annihilatorIdealAt B S hS X F U := by
  intro W g t
  have hsep : Presheaf.IsSheaf (SmallEtale.topology B S hS X.1) F.val.presheaf := F.isSheaf
  refine hsep.isSeparated W.unop (T.pullback g.unop)
    ((SmallEtale.topology B S hS X.1).pullback_stable g.unop hT) _ 0 ?_
  intro W' g' hg'
  have hzero := smul_eq_zero_of_mem_annihilatorIdealAt B S hS X F (op W') _
    (h (op W') (g ≫ g'.op) hg') (F.val.map g'.op t)
  have hsm : F.val.map g'.op (((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O).obj.map g).hom s • t) = 0 :=
    (F.val.map_smul g'.op _ t).trans hzero
  exact hsm.trans (map_zero _).symm

/-- **The annihilator ideal sheaf of an `𝒪_X`-module.**  The chartwise annihilator ideals of
`AlgebraicGeometry.Space.annihilatorIdealAt` are the sections of a sheaf of ideals of the
structure sheaf `𝒪_X` on the small étale ringed site of `X`. -/
def annihilatorIdealSheaf (F : Modules.{u, u} B S hS X.1 X.2) :
    (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule where
  obj U := annihilatorIdealAt B S hS X F U
  map f a ha := annihilatorIdealAt_map B S hS X F f a ha
  isSheaf {U} s hs :=
    mem_annihilatorIdealAt_of_sieve B S hS X F U s _ hs fun _ _ hm => hm

/-- The sections of the annihilator ideal sheaf over an étale chart are the annihilator ideal
at that chart. -/
theorem annihilatorIdealSheaf_obj (F : Modules.{u, u} B S hS X.1 X.2)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    (annihilatorIdealSheaf B S hS X F).obj U = annihilatorIdealAt B S hS X F U :=
  rfl

/-! ### The annihilator ideal on an affine chart -/

/-- A regular function on an affine étale chart annihilating the sections of a quasi-coherent
module there has its restriction to a smaller affine chart annihilating the sections there: the
sections over the smaller chart are spanned by the restrictions of the sections over the larger
one, by Descent, Proposition 03DX(2). -/
private theorem smul_chartRestrict_eq_zero_of_isAffine (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) {U V : SmallEtale B S hS X.1}
    (hU : IsAffine (chartScheme U)) (hV : IsAffine (chartScheme V)) (g : V ⟶ U)
    (a : chartRing B S hS X.1 X.2 U) (ha : ∀ y : F.val.obj (op U), a • y = 0)
    (t : F.val.obj (op V)) :
    chartRestrict (hF := X.2) g a • t = 0 := by
  have hcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 F hF
    U V hU hV g
  have hspan := (chartBaseChange_surjective_iff_span_eq_top F g).1 hcart.2
  have hle : Submodule.span (chartRing B S hS X.1 X.2 V)
      (Set.range fun x : F.val.obj (op U) => chartRestrictLinear F g x) ≤
      LinearMap.ker (LinearMap.lsmul (chartRing B S hS X.1 X.2 V) (F.val.obj (op V))
        (chartRestrict (hF := X.2) g a)) := by
    rw [Submodule.span_le]
    rintro y ⟨x, rfl⟩
    have hy := chartRestrictLinear_smul F g a x
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.lsmul_apply]
    rw [← hy, ha x, map_zero]
  rw [hspan] at hle
  exact LinearMap.mem_ker.1 (hle Submodule.mem_top)

/-- **A regular function on an affine étale chart annihilating the sections of a quasi-coherent
module there lies in the annihilator ideal.**  Every chart over the affine chart is covered by
affine charts, where the previous statement applies, and a section of `F` vanishing on a
covering vanishes. -/
theorem mem_annihilatorIdealAt_of_isAffine (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (U : SmallEtale B S hS X.1)
    (hU : IsAffine (chartScheme U)) (a : chartRing B S hS X.1 X.2 U)
    (ha : ∀ y : F.val.obj (op U), a • y = 0) :
    a ∈ annihilatorIdealAt B S hS X F (op U) := by
  have hcd : (AffineEtale.inclusion B S hS X.1).IsCoverDense
      (SmallEtale.topology B S hS X.1) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS X.1 X.2).2.isCoverDense'
  have hsep : Presheaf.IsSheaf (SmallEtale.topology B S hS X.1) F.val.presheaf := F.isSheaf
  intro W g t
  obtain ⟨W⟩ := W
  refine hsep.isSeparated W _
    ((AffineEtale.inclusion B S hS X.1).is_cover_of_isCoverDense
      (SmallEtale.topology B S hS X.1) W) _ 0 ?_
  rintro Y f ⟨A, l, n, ⟨rfl⟩⟩
  have hinner := smul_chartRestrict_eq_zero_of_isAffine B S hS X F hF hU A.property
    (n ≫ g.unop) a ha (chartRestrictLinear F n t)
  have hcomp : chartRestrict (hF := X.2) (n ≫ g.unop) a =
      chartRestrict (hF := X.2) n (chartRestrict (hF := X.2) g.unop a) :=
    DFunLike.congr_fun (chartRestrict_comp (hF := X.2) g.unop n) a
  have e3 := (congrArg
    (fun r : chartRing B S hS X.1 X.2 ((AffineEtale.inclusion B S hS X.1).obj A) =>
      r • chartRestrictLinear F n t) hcomp).symm.trans hinner
  have e2 := chartRestrictLinear_smul F n (chartRestrict (hF := X.2) g.unop a) t
  have e1 := chartRestrictLinear_comp F n l
    (((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O).obj.map g).hom a • t)
  exact (e1.trans ((congrArg (chartRestrictLinear F l) (e2.trans e3)).trans
    (map_zero _))).trans (map_zero _).symm

/-- **On an affine étale chart the annihilator ideal of a quasi-coherent module is the
annihilator of its module of sections.** -/
theorem chartIdeal_annihilatorIdealSheaf_eq_annihilator (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (U : SmallEtale B S hS X.1)
    (hU : IsAffine (chartScheme U)) :
    chartIdeal B S hS X (annihilatorIdealSheaf B S hS X F) U =
      Module.annihilator (chartRing B S hS X.1 X.2 U) (F.val.obj (op U)) :=
  le_antisymm
    (fun a ha => Module.mem_annihilator.2 fun y =>
      smul_eq_zero_of_mem_annihilatorIdealAt B S hS X F (op U) a ha y)
    (fun a ha => mem_annihilatorIdealAt_of_isAffine B S hS X F hF U hU a
      fun y => Module.mem_annihilator.1 ha y)

/-! ### Quasi-coherence of the annihilator ideal sheaf -/

/-- **The annihilator ideal sheaf of a quasi-coherent module of finite type is cartesian on
affine charts.**

For a sheaf of ideals the cartesian condition is surjectivity of the base change comparison,
which for the annihilator says that the annihilator of the sections over the smaller chart is
generated by the restrictions of the annihilator of the sections over the larger one.  That is
flat base change for annihilators of finite modules: the restriction map of regular functions
between affine charts is flat, the sections over the larger chart form a finite module, and the
sections over the smaller chart are their base change by Descent, Proposition 03DX(2). -/
theorem isCartesianOnAffineCharts_annihilatorIdealSheaf (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite)
    (hft : PresheafOfModules.IsFiniteType (smallEtaleRingedSite B S hS X.1 X.2).J F.val) :
    IsCartesianOnAffineCharts (annihilatorIdealSheaf B S hS X F).toSheafOfModules := by
  have hcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 F hF
  refine isCartesianOnAffineCharts_submodule_unit_of_surjective B S hS X _
    fun U V hU hV f => surjective_sectionsBaseChange_of_chartIdeal_le_map B S hS X _ f ?_
  let _ := chartAlgebra (hF := X.2) f
  let _ := chartSectionsModule F f
  have _ := chartSections_isScalarTower F f
  have _hflat : Module.Flat (chartRing B S hS X.1 X.2 U) (chartRing B S hS X.1 X.2 V) :=
    moduleFlat_chartRing_of_isAffine f hU hV
  have _hfin : Module.Finite (chartRing B S hS X.1 X.2 U) (F.val.obj (op U)) :=
    moduleFinite_sections_of_isFiniteType B S hS X.1 X.2 hcart hft hU
  have he : Module.annihilator (chartRing B S hS X.1 X.2 V) (F.val.obj (op V)) =
      Module.annihilator (chartRing B S hS X.1 X.2 V)
        (TensorProduct (chartRing B S hS X.1 X.2 U) (chartRing B S hS X.1 X.2 V)
          (F.val.obj (op U))) :=
    (LinearEquiv.annihilator_eq
      (LinearEquiv.ofBijective (sectionsBaseChange F f) (hcart U V hU hV f))).symm
  rw [chartIdeal_annihilatorIdealSheaf_eq_annihilator B S hS X F hF V hV,
    chartIdeal_annihilatorIdealSheaf_eq_annihilator B S hS X F hF U hU, he,
    ← ann_extension_eq_ann_baseChange_module, chartAlgebra_algebraMap]

/-- **The annihilator ideal sheaf of a quasi-coherent module of finite type is quasi-coherent.**
This is the converse implication of Descent, Proposition 03DX(2) applied to
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_annihilatorIdealSheaf`. -/
theorem isQuasicoherentOnSite_annihilatorIdealSheaf (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite)
    (hft : PresheafOfModules.IsFiniteType (smallEtaleRingedSite B S hS X.1 X.2).J F.val) :
    (annihilatorIdealSheaf B S hS X F).toSheafOfModules.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
    (isCartesianOnAffineCharts_annihilatorIdealSheaf B S hS X F hF hft)

/-! ### The scheme-theoretic support -/

/-- A closed subspace of an algebraic space `X`, read as an algebraic space over `S`. -/
abbrev closedSubspaceToSpace (Z : ClosedSubspaces B S hS X.1) : AlgebraicSpaces B S hS :=
  ⟨Z.1.toFunctor, Z.2.1⟩

/-- The inclusion of a closed subspace of `X`, as a morphism of algebraic spaces over `S`. -/
abbrev closedSubspaceInclusion (Z : ClosedSubspaces B S hS X.1) :
    closedSubspaceToSpace B S hS X Z ⟶ X :=
  ObjectProperty.homMk Z.1.ι

/-- **The defining ideal of a closed subspace whose inclusion makes `F` a direct image lies in
the annihilator ideal of `F`.**  The ideal cutting out the closed subspace annihilates `F` by
the first half of Stacks 04CJ, part (3), and that is exactly the annihilator condition on every
chart over the one in question. -/
theorem definingIdealSheaf_le_annihilatorIdealSheaf (F : Modules.{u, u} B S hS X.1 X.2)
    (Z : ClosedSubspaces B S hS X.1)
    (hann : AnnihilatedByKerIdeal B S hS (closedSubspaceInclusion B S hS X Z) F) :
    definingIdealSheaf B S hS X Z ≤ annihilatorIdealSheaf B S hS X F := by
  intro U a ha W g t
  refine hann W _ ((SheafOfModules.mem_kerIdeal _ W _).2 ?_) t
  exact definingIdealAt_map B S hS X Z g a ha

/-- The closed subspaces of `X` whose defining ideal annihilates `F`.  Equivalently, by
Stacks 04CJ part (3), the closed subspaces from which `F` is a direct image. -/
def annihilatingClosedSubspaces (F : Modules.{u, u} B S hS X.1 X.2) : Set (Subfunctor X.1) :=
  {Z | ∃ hZ : IsClosedSubspace B S hS Z,
    definingIdealSheaf B S hS X ⟨Z, hZ⟩ ≤ annihilatorIdealSheaf B S hS X F}

/-- **Stacks 07U1.** The *scheme theoretic support* of a finite type quasi-coherent
`𝒪_X`-module `F`: the intersection of the closed subspaces of `X` whose defining ideal
annihilates `F`.

By `AlgebraicGeometry.Space.schemeTheoreticSupport_eq_of_definingIdealSheaf_eq` this is the
closed subspace cut out by the annihilator ideal sheaf of `F`, which for a quasi-coherent `F` of
finite type is a quasi-coherent sheaf of ideals; so the intersection is itself a closed subspace
and it is the smallest member of the family, which is the content of Stacks 07U0. -/
@[stacks 07U1]
def schemeTheoreticSupport (F : Modules.{u, u} B S hS X.1 X.2) : Subfunctor X.1 :=
  sInf (annihilatingClosedSubspaces B S hS X F)

/-- **The scheme-theoretic support is the closed subspace cut out by the annihilator ideal
sheaf.**  That subspace lies in the family being intersected, and its defining ideal being the
whole annihilator makes it contained in every other member, by the injectivity half of
Stacks 03MB. -/
theorem schemeTheoreticSupport_eq_of_definingIdealSheaf_eq
    (F : Modules.{u, u} B S hS X.1 X.2) (Z : ClosedSubspaces B S hS X.1)
    (hZ : definingIdealSheaf B S hS X Z = annihilatorIdealSheaf B S hS X F) :
    schemeTheoreticSupport B S hS X F = Z.1 := by
  refine le_antisymm (sInf_le ⟨Z.2, le_of_eq hZ⟩) (le_sInf ?_)
  rintro W ⟨hW, hle⟩
  exact le_of_definingIdealSheaf_le B S hS X Z ⟨W, hW⟩ (hZ ▸ hle)

/-- **The scheme-theoretic support of a quasi-coherent module of finite type is a closed
subspace, and its defining ideal is the annihilator ideal of the module.**

The annihilator ideal sheaf is a quasi-coherent sheaf of ideals, so by the surjectivity half of
Stacks 03MB it cuts out a closed subspace, which the previous statement identifies with the
scheme-theoretic support. -/
theorem exists_isClosedSubspace_schemeTheoreticSupport (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite)
    (hft : PresheafOfModules.IsFiniteType (smallEtaleRingedSite B S hS X.1 X.2).J F.val) :
    ∃ hZ : IsClosedSubspace B S hS (schemeTheoreticSupport B S hS X F),
      definingIdealSheaf B S hS X ⟨schemeTheoreticSupport B S hS X F, hZ⟩ =
        annihilatorIdealSheaf B S hS X F := by
  obtain ⟨Z, hZ⟩ := exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B S hS X _
    (isQuasicoherentOnSite_annihilatorIdealSheaf B S hS X F hF hft)
  have heq := schemeTheoreticSupport_eq_of_definingIdealSheaf_eq B S hS X F Z hZ
  refine ⟨heq ▸ Z.2, ?_⟩
  have : (⟨schemeTheoreticSupport B S hS X F, heq ▸ Z.2⟩ : ClosedSubspaces B S hS X.1) = Z :=
    Subtype.ext heq
  rw [this, hZ]

/-! ### Stacks 07U0 -/

/-- **The essential-image assertion of Stacks 04CJ, part (3)** at a morphism `i` of algebraic
spaces: every quasi-coherent `𝒪_X`-module annihilated by the ideal cutting out the closed
subspace is the direct image along `i` of a quasi-coherent module on it.

This is the assertion of Stacks 04E5, part (2).  It holds for every closed immersion, by
`AlgebraicGeometry.Space.isQuasicoherentEssImagePushforward_of_isClosedImmersion`. -/
def IsQuasicoherentEssImagePushforward {Z : AlgebraicSpaces B S hS} (i : Z ⟶ X) : Prop :=
  ∀ M : Modules.{u, u} B S hS X.1 X.2, M.IsQuasicoherentOnSite →
    AnnihilatedByKerIdeal B S hS i M →
      ∃ G : Modules.{u, u} B S hS Z.1 Z.2, G.IsQuasicoherentOnSite ∧
        Nonempty ((modulePushforward B S hS i).obj G ≅ M)

/-- The inverse image of a module along a closed immersion is isomorphic to any module whose direct
image is that module: the counit of Stacks 04CJ, part (2). -/
private theorem nonempty_modulePullback_iso_of_modulePushforward_iso
    {Z : AlgebraicSpaces B S hS} (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (M : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Z.1 Z.2)
    (e : (modulePushforward B S hS i).obj G ≅ M) :
    Nonempty ((modulePullback B S hS i).obj M ≅ G) :=
  ⟨((modulePullback B S hS i).mapIso e).symm ≪≫ (modulePullbackCounitIso B S hS i hi).app G⟩

/-- **The essential-image assertion of Stacks 04CJ, part (3), for a closed immersion.**  A
quasi-coherent `𝒪_X`-module annihilated by the ideal cutting out a closed subspace `i : Z ⟶ X`
is the direct image along `i` of a *quasi-coherent* module on `Z`.

The module is produced by the essential-image clause of Stacks 08KS,
`AlgebraicGeometry.Space.essImage_modulePushforward_of_annihilatedByKerIdeal`, which is
unconditional.  Quasi-coherence of it is the one thing that clause does not say, and it comes
from Stacks 04CJ, part (2): the counit identifies the module on `Z` with the inverse image
`i^*M`, which is quasi-coherent by Stacks 03GA.

No tag is carried: the essential-image clause whole is
`AlgebraicGeometry.Space.essImage_modulePushforward_iff`, which carries it, and this is that
clause with quasi-coherence tracked through it. -/
theorem isQuasicoherentEssImagePushforward_of_isClosedImmersion {Z : AlgebraicSpaces B S hS}
    (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) :
    IsQuasicoherentEssImagePushforward B S hS X i := by
  intro M hM hann
  obtain ⟨G, ⟨e⟩⟩ := essImage_modulePushforward_of_annihilatedByKerIdeal B S hS i hi M hann
  refine ⟨G, ?_, ⟨e⟩⟩
  obtain ⟨eG⟩ := nonempty_modulePullback_iso_of_modulePushforward_iso B S hS X i hi M G e
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso eG
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS i M hM)

/-- **The ideal cutting out the scheme-theoretic support annihilates `F`.** -/
theorem annihilatedByKerIdeal_schemeTheoreticSupport (F : Modules.{u, u} B S hS X.1 X.2)
    (hZ : IsClosedSubspace B S hS (schemeTheoreticSupport B S hS X F))
    (hid : definingIdealSheaf B S hS X ⟨schemeTheoreticSupport B S hS X F, hZ⟩ =
      annihilatorIdealSheaf B S hS X F) :
    AnnihilatedByKerIdeal B S hS
      (closedSubspaceInclusion B S hS X ⟨schemeTheoreticSupport B S hS X F, hZ⟩) F := by
  intro U a ha t
  have hd : definingIdealAt B S hS X ⟨schemeTheoreticSupport B S hS X F, hZ⟩ U =
      annihilatorIdealAt B S hS X F U := by
    rw [← definingIdealSheaf_obj B S hS X, ← annihilatorIdealSheaf_obj B S hS X, hid]
  refine smul_eq_zero_of_mem_annihilatorIdealAt B S hS X F U a ?_ t
  rw [← hd]
  exact (SheafOfModules.mem_kerIdeal _ U a).1 ha

/-- **Stacks 07U0, existence.**  A finite type quasi-coherent `𝒪_X`-module `F` is the direct
image of a quasi-coherent module on its scheme-theoretic support, which is a closed subspace
of `X`.

That the scheme-theoretic support is a closed subspace, and that the ideal cutting it out is
the annihilator ideal of `F`, are
`AlgebraicGeometry.Space.exists_isClosedSubspace_schemeTheoreticSupport`; so that ideal
annihilates `F`, and
`AlgebraicGeometry.Space.isQuasicoherentEssImagePushforward_of_isClosedImmersion` turns that
into the module. -/
@[stacks 07U0 "existence of the quasi-coherent module on the scheme-theoretic support"]
theorem exists_module_on_schemeTheoreticSupport (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite)
    (hft : PresheafOfModules.IsFiniteType (smallEtaleRingedSite B S hS X.1 X.2).J F.val) :
    ∃ (hZ : IsClosedSubspace B S hS (schemeTheoreticSupport B S hS X F))
      (G : Modules.{u, u} B S hS
        (closedSubspaceToSpace B S hS X ⟨schemeTheoreticSupport B S hS X F, hZ⟩).1
        (closedSubspaceToSpace B S hS X ⟨schemeTheoreticSupport B S hS X F, hZ⟩).2),
      G.IsQuasicoherentOnSite ∧ Nonempty ((modulePushforward B S hS
        (closedSubspaceInclusion B S hS X
          ⟨schemeTheoreticSupport B S hS X F, hZ⟩)).obj G ≅ F) := by
  obtain ⟨hZ, hid⟩ := exists_isClosedSubspace_schemeTheoreticSupport B S hS X F hF hft
  exact ⟨hZ, isQuasicoherentEssImagePushforward_of_isClosedImmersion B S hS X
    (closedSubspaceInclusion B S hS X ⟨schemeTheoreticSupport B S hS X F, hZ⟩) hZ.2
    F hF (annihilatedByKerIdeal_schemeTheoreticSupport B S hS X F hZ hid)⟩

/-- **Stacks 07U0, minimality.**  The scheme-theoretic support of `F` is contained in every
closed subspace of `X` from which `F` is a direct image.

The ideal cutting out such a closed subspace annihilates `F` by the first half of Stacks 04CJ
part (3), so that subspace is a member of the family being intersected. -/
@[stacks 07U0 "minimality: the scheme-theoretic support is contained in every closed subspace \
from which F is a direct image"]
theorem schemeTheoreticSupport_le (F : Modules.{u, u} B S hS X.1 X.2)
    (Z : ClosedSubspaces B S hS X.1)
    (G : Modules.{u, u} B S hS (closedSubspaceToSpace B S hS X Z).1
      (closedSubspaceToSpace B S hS X Z).2)
    (e : (modulePushforward B S hS (closedSubspaceInclusion B S hS X Z)).obj G ≅ F) :
    schemeTheoreticSupport B S hS X F ≤ Z.1 :=
  sInf_le ⟨Z.2, definingIdealSheaf_le_annihilatorIdealSheaf B S hS X F Z
    (annihilatedByKerIdeal_of_essImage_modulePushforward B S hS
      (closedSubspaceInclusion B S hS X Z) ⟨G, ⟨e⟩⟩)⟩

/-- **Stacks 07U0, part (2).**  A module on a closed subspace of `X` whose direct image is `F`
is unique up to a unique isomorphism compatible with the chosen identifications of the direct
images with `F`.

This is full faithfulness of the direct image along a closed immersion, Stacks 04CJ part (2). -/
@[stacks 07U0 "part (2): uniqueness up to unique isomorphism"]
theorem module_on_closedSubspace_unique (F : Modules.{u, u} B S hS X.1 X.2)
    (Z : ClosedSubspaces B S hS X.1)
    (G H : Modules.{u, u} B S hS (closedSubspaceToSpace B S hS X Z).1
      (closedSubspaceToSpace B S hS X Z).2)
    (eG : (modulePushforward B S hS (closedSubspaceInclusion B S hS X Z)).obj G ≅ F)
    (eH : (modulePushforward B S hS (closedSubspaceInclusion B S hS X Z)).obj H ≅ F) :
    ∃! φ : G ≅ H,
      (modulePushforward B S hS (closedSubspaceInclusion B S hS X Z)).map φ.hom ≫ eH.hom =
        eG.hom := by
  have hff := fullyFaithfulModulePushforward B S hS
    (closedSubspaceInclusion B S hS X Z) Z.2.2
  have hpre : (modulePushforward B S hS (closedSubspaceInclusion B S hS X Z)).map
      (hff.preimageIso (eG ≪≫ eH.symm)).hom = eG.hom ≫ eH.inv :=
    hff.map_preimage _
  refine ⟨hff.preimageIso (eG ≪≫ eH.symm), ?_, fun ψ hψ => ?_⟩
  · dsimp only
    rw [hpre, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · refine Iso.ext (hff.map_injective ?_)
    have key : (modulePushforward B S hS (closedSubspaceInclusion B S hS X Z)).map ψ.hom =
        eG.hom ≫ eH.inv := by
      rw [← hψ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [key, hpre]

/-- **Stacks 07U0, part (3).**  A module on a closed subspace of `X` whose direct image is a
module of finite type is itself of finite type.

By Stacks 04CJ part (2) it is isomorphic to the inverse image of `F`, which is of finite type by
Stacks 03DO, and finite type passes along an epimorphism. -/
@[stacks 07U0 "part (3): the module on the closed subspace is of finite type"]
theorem isFiniteTypeOnSite_module_on_closedSubspace (F : Modules.{u, u} B S hS X.1 X.2)
    (hFft : SheafOfModules.IsFiniteTypeOnSite F) (Z : ClosedSubspaces B S hS X.1)
    (G : Modules.{u, u} B S hS (closedSubspaceToSpace B S hS X Z).1
      (closedSubspaceToSpace B S hS X Z).2)
    (e : (modulePushforward B S hS (closedSubspaceInclusion B S hS X Z)).obj G ≅ F) :
    SheafOfModules.IsFiniteTypeOnSite G := by
  obtain ⟨eG⟩ := nonempty_modulePullback_iso_of_modulePushforward_iso B S hS X
    (closedSubspaceInclusion B S hS X Z) Z.2.2 F G e
  have hpf := isFiniteTypeOnSite_modulePullback B S hS
    (closedSubspaceInclusion B S hS X Z) F hFft
  have _ : Epi eG.hom := CategoryTheory.IsIso.epi_of_iso eG.hom
  exact Stacks.SheafOfModules.isFiniteTypeOnSite_of_epi eG.hom hpf

end AlgebraicGeometry.Space

end
