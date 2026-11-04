module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBasicOpenLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyBijective

/-!
# A chartwise rank is a rank, for a module cartesian on affine charts

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `H` be
an `𝒪_F`-module on its small étale site which is **cartesian on affine charts**
(`AlgebraicGeometry.Space.IsCartesianOnAffineCharts`): the sections over a smaller affine chart
are the base change of the sections over the larger one.  Suppose the affine étale charts over
which the sections of `H` form a finite locally free module of rank `s` generate a covering
sieve of every étale chart.  Then `H` is finite locally free of rank `s` in the sense of the
rank clause of Stacks 0409, `AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank`: over the
members of a covering of every chart it is a coproduct of `s` copies of the structure sheaf.

This is the direction of the rank form of Descent, Proposition 03DX (2) that the chart-sections
files of this tree consume.  The converse direction needs no hypothesis
at all and is
`AlgebraicGeometry.Space.freeRankPresieve_mem_topology_of_isFiniteLocallyFreeOfRank`.

**Cartesianness is not a convenience.**  The hypothesis is about the sections over affine
charts, and the conclusion is about the module itself over every chart of a covering; a basis
of `H(V)` says nothing about `H(W)` for `W ⟶ V` unless the latter is the base change of the
former.  The statement with the cartesian hypothesis dropped,
`AlgebraicGeometry.Space.ChartwiseRankImpliesRank`, is therefore not proved here and is not
expected to hold.

## Main results

* `Stacks.SheafOfModules.bijective_sum_app_of_isColimit_cofan`: the sections of the point of a
  finite colimit cofan over an object of the site are the tuples of sections of its legs.
* `Stacks.SheafOfModules.bijective_app_cofanDesc_iff`: a morphism out of the point of a finite
  colimit cofan of copies of the structure sheaf is bijective on the sections over an object
  exactly when the corresponding family of sections is a basis there.
* `Module.nonempty_basis_of_isLocalizedModule_away`: a basis of the canonical localization away
  from an element is a basis of every localization away from it.
* `AlgebraicGeometry.Space.hasEnoughObjects_isAffine_over`: every object of a slice of the small
  étale site is covered by objects whose underlying scheme is affine.
* `AlgebraicGeometry.Space.chartRestrictBasis`: for a cartesian module, the restriction of a
  basis of the sections over an affine chart is a basis of the sections over any smaller affine
  chart.
* `AlgebraicGeometry.Space.exists_basicOpen_chart_basis`: around every point of an affine chart
  over which the sections are finite locally free of rank `s` there is a basic-open chart over
  which they are free with a basis indexed by `Fin s`.
* `AlgebraicGeometry.Space.exists_isColimitCofanUnit_of_basis`: a basis of the sections over an
  affine chart `W` exhibits the restriction of the module to the slice at `W` as a coproduct of
  `s` copies of the structure sheaf.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_chartwise`: **the theorem of this
  file.**
* `AlgebraicGeometry.Space.affineChartSieve_mem_topology`: the affine étale charts over a chart
  generate a covering sieve of it.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_forall_isAffine` and
  `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_forall_isAffine_of_isQuasicoherentOnSite`:
  **the form in which the chartwise rank is used** — the covering-sieve hypothesis is discharged
  from the rank at *every* affine chart, and cartesianness from quasi-coherence.

## Implementation notes

The proof has three independent parts.

*Shrinking.*  `Module.IsFiniteLocallyFreeOfRank` is a covering of the spectrum by basic opens on
which the module becomes free, so the chartwise hypothesis is first refined to the presieve of
affine charts over which the sections are *free* with a basis indexed by `Fin s`.  The
basic-open chart of an affine chart carries the localization of the functions
(`AlgebraicGeometry.Space.isLocalization_away_chartRing_openChart_basicOpen`) and, for a
cartesian module, the localization of the sections
(`AlgebraicGeometry.Space.isLocalizedModule_chartRestrictLinear_openChart_basicOpen`), so the
basis of the canonical localization transports to it.  That transport is
`Module.nonempty_basis_of_isLocalizedModule_away`: the comparison of the two modules supplied
by `IsLocalizedModule.linearEquiv` is linear only over the base ring, and is promoted to the
localization by `LinearEquiv.extendScalarsOfIsLocalization`, which is what makes the two bases
comparable at all.

*Trivialising.*  A basis of the sections over an affine chart `W` gives `s` global sections of
the restriction of the module to the slice at `W`, hence a morphism to it from a coproduct of
`s` copies of the structure sheaf of the slice — the coproduct exists because a preadditive
category with finite products has finite biproducts, with no sheafification.  Over an affine
chart of the slice that morphism is bijective on sections, which is the restricted basis of
`AlgebraicGeometry.Space.chartRestrictBasis` read through
`Stacks.SheafOfModules.bijective_app_cofanDesc_iff`.

*Globalising.*  Affine charts cover every object of the slice, so bijectivity on their sections
makes the morphism locally injective and locally surjective, by the two halves of Stacks 0H6Y
in `StacksFrontier/CategoryTheory/Sites/LocallyBijective.lean`, hence an isomorphism of sheaves of
modules by `Stacks.SheafOfModules.isIso_of_isLocallyBijective`.  Transporting the colimit cofan
across it gives the required presentation.

**Placement.**  `Module.nonempty_basis_of_isLocalizedModule_away` mentions no scheme and no site
and belongs beside `Module.IsFiniteLocallyFreeOfRank` in
`StacksFrontier/RingTheory/Module/LocallyFree/SheafBridge.lean`; it is here because moving a
declaration between modules is a repository-wide change and this file is one landing.
Likewise `Stacks.SheafOfModules.bijective_sum_app_of_isColimit_cofan` and
`Stacks.SheafOfModules.bijective_app_cofanDesc_iff` belong beside
`Stacks.SheafOfModules.exists_piEquiv_of_isColimit_cofan`, whose biproduct calculus they repeat
at the level of one object of the site rather than of the whole sections functor.

## References

* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 00NW](https://stacks.math.columbia.edu/tag/00NW)
* [Stacks Project, Tag 0H6Y](https://stacks.math.columbia.edu/tag/0H6Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v u'

namespace Stacks.SheafOfModules

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {S : Sheaf J RingCat.{u}}

/-- A leg of a colimit cofan followed by the descended morphism is the corresponding leg. -/
private theorem comp_cofanDesc {n : ℕ} {N M : SheafOfModules.{u} S} (p : ∀ _ : Fin n, M ⟶ N)
    (hN : IsColimit (Cofan.mk N p)) {E : SheafOfModules.{u} S} (q : ∀ _ : Fin n, M ⟶ E)
    (i : Fin n) : p i ≫ Cofan.IsColimit.desc hN q = q i := by
  simpa using Cofan.IsColimit.fac hN q i

/-- **The sections of the point of a finite colimit cofan are the tuples of sections of its
legs.**  If a cofan of `n` copies of `E` with point `N` is a colimit, then
`y ↦ ∑ i, (p i)(y i)` is a bijection from the `n`-tuples of sections of `E` over an object onto
the sections of `N` over that object.

A finite coproduct in a preadditive category is a biproduct: each leg `p i` has a retraction
`π i` obtained from the colimit property, and `∑ i, π i ≫ p i = 𝟙 N`, which exhibits
`z ↦ (π i z)` as the two-sided inverse. -/
theorem bijective_sum_app_of_isColimit_cofan {n : ℕ} {E N : SheafOfModules.{u} S}
    (p : ∀ _ : Fin n, E ⟶ N) (hN : IsColimit (Cofan.mk N p)) (X : Cᵒᵖ) :
    Function.Bijective (fun y : Fin n → ToType (E.val.obj X) =>
      ∑ i, (p i).val.app X (y i)) := by
  classical
  set π : Fin n → (N ⟶ E) := fun i =>
    Cofan.IsColimit.desc hN (fun j => if j = i then 𝟙 E else 0) with hπ
  have hfac : ∀ i j, p j ≫ π i = if j = i then 𝟙 E else 0 := fun i j =>
    comp_cofanDesc p hN _ j
  have hfac1 : ∀ i, p i ≫ π i = 𝟙 E := fun i => by simpa using hfac i i
  have hfac0 : ∀ i j, j ≠ i → p j ≫ π i = 0 := fun i j h => by simpa [h] using hfac i j
  have htot : ∑ i, π i ≫ p i = 𝟙 N := by
    refine Cofan.IsColimit.hom_ext hN _ _ (fun j => ?_)
    simp only [cofan_mk_inj, Preadditive.comp_sum]
    rw [Finset.sum_eq_single j]
    · rw [← Category.assoc, hfac1 j, Category.id_comp]
      exact (Category.comp_id (p j)).symm
    · intro i _ hij
      rw [← Category.assoc, hfac0 i j (Ne.symm hij), Limits.zero_comp]
    · exact fun h => absurd (Finset.mem_univ j) h
  refine Function.bijective_iff_has_inverse.2
    ⟨fun z i => (π i).val.app X z, fun y => funext fun i => ?_, fun z => ?_⟩
  · show (π i).val.app X (∑ j, (p j).val.app X (y j)) = y i
    rw [map_sum, Finset.sum_eq_single i]
    · exact congrFun (congrArg (fun φ : E ⟶ E => fun w => (φ.val.app X) w) (hfac1 i)) (y i)
    · intro j _ hji
      exact congrFun (congrArg (fun φ : E ⟶ E => fun w => (φ.val.app X) w) (hfac0 i j hji)) (y j)
    · exact fun h => absurd (Finset.mem_univ i) h
  · show ∑ i, (p i).val.app X ((π i).val.app X z) = z
    have h := app_sum Finset.univ (fun i => π i ≫ p i) X z
    rw [htot] at h
    exact h.symm

/-- **A morphism out of the point of a finite colimit cofan of copies of the structure sheaf is
bijective on the sections over an object exactly when the corresponding family of sections is a
basis there.**  The right-hand side is the assertion that the `n` sections
`(q i)(1)` form a basis of the sections of `M` over `X`, written as bijectivity of the
coefficient map. -/
theorem bijective_app_cofanDesc_iff {n : ℕ} {N M : SheafOfModules.{u} S}
    (p : ∀ _ : Fin n, _root_.SheafOfModules.unit S ⟶ N) (hN : IsColimit (Cofan.mk N p))
    (q : ∀ _ : Fin n, _root_.SheafOfModules.unit S ⟶ M) (X : Cᵒᵖ) :
    Function.Bijective ((Cofan.IsColimit.desc hN q).val.app X) ↔
      Function.Bijective (fun y : Fin n → ToType (S.obj.obj X) =>
        ∑ i, y i • (q i).val.app X (unitOne X)) := by
  have hα : Function.Bijective (fun y : Fin n → ToType (S.obj.obj X) =>
      ∑ i, (p i).val.app X (toUnit X (y i))) :=
    bijective_sum_app_of_isColimit_cofan p hN X
  have hcomp : ((Cofan.IsColimit.desc hN q).val.app X) ∘
      (fun y : Fin n → ToType (S.obj.obj X) => ∑ i, (p i).val.app X (toUnit X (y i))) =
      fun y : Fin n → ToType (S.obj.obj X) => ∑ i, y i • (q i).val.app X (unitOne X) := by
    funext y
    show (Cofan.IsColimit.desc hN q).val.app X (∑ i, (p i).val.app X (toUnit X (y i))) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hqi := comp_cofanDesc p hN q i
    calc (Cofan.IsColimit.desc hN q).val.app X ((p i).val.app X (toUnit X (y i)))
        = (p i ≫ Cofan.IsColimit.desc hN q).val.app X (toUnit X (y i)) := rfl
      _ = (q i).val.app X (toUnit X (y i)) := by rw [hqi]
      _ = y i • (q i).val.app X (unitOne X) := app_unit_eq (q i) X (y i)
  rw [← hcomp]
  exact (Equiv.bijective_comp (Equiv.ofBijective _ hα) _).symm

end Stacks.SheafOfModules

namespace Module

/-- **A basis of the canonical localization away from `g` is a basis of every localization
away from `g`.**  Both the coefficient ring and the module are replaced by arbitrary objects
with the universal property, which is how the sections of a module over a basic-open chart
present themselves.

The two coefficient rings are identified by `IsLocalization.algEquiv` and the two modules by
`IsLocalizedModule.linearEquiv`; the latter is only linear over the base ring, and is promoted
to the localization by `LinearEquiv.extendScalarsOfIsLocalization`. -/
theorem nonempty_basis_of_isLocalizedModule_away {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] (g : R)
    {A : Type*} [CommRing A] [Algebra R A] [IsLocalization.Away g A]
    {N : Type*} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (h : M →ₗ[R] N) [IsLocalizedModule.Away g h] {ι : Type*}
    (b : Basis ι (Localization.Away g) (LocalizedModule (Submonoid.powers g) M)) :
    Nonempty (Basis ι A N) := by
  let e : Localization.Away g ≃ₐ[R] A := Localization.algEquiv (Submonoid.powers g) A
  let : Module (Localization.Away g) N := Module.compHom N e.toRingEquiv.toRingHom
  have : IsScalarTower R (Localization.Away g) N :=
    IsScalarTower.of_algebraMap_smul fun r x =>
      show e (algebraMap R (Localization.Away g) r) • x = r • x by
        rw [AlgEquiv.commutes, algebraMap_smul]
  let φ : LocalizedModule (Submonoid.powers g) M ≃ₗ[R] N :=
    IsLocalizedModule.linearEquiv (Submonoid.powers g)
      (LocalizedModule.mkLinearMap (Submonoid.powers g) M) h
  exact ⟨(b.map (φ.extendScalarsOfIsLocalization (Submonoid.powers g)
    (Localization.Away g))).mapCoeffs e.toRingEquiv fun _ _ => rfl⟩

end Module

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### Affine charts cover a slice -/

/-- Every point of the scheme of an étale chart `U` is the image of a point of the scheme of the
chart cut out by an affine open of `U`. -/
private theorem exists_affineOpen_chart_map_eq (U : SmallEtale B S hS F)
    (z : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U)) :
    ∃ (O : (chartScheme U).affineOpens)
      (w : (BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (openChart B S hS F U O.1))),
      (BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map (openChartInclusion B S hS F U O.1)) w = z := by
  obtain ⟨-, ⟨O, hO, rfl⟩, hzO, -⟩ :=
    (chartScheme U).isBasis_affineOpens.exists_subset_of_mem_open
      (show z ∈ (⊤ : Set _) from trivial) isOpen_univ
  exact ⟨⟨O, hO⟩, ⟨z, hzO⟩, by rw [toScheme_map_toOver_map_openChartInclusion]; rfl⟩

/-- **Every object of a slice of the small étale site of an algebraic space is covered by
objects whose underlying scheme is affine.**  The covering family is indexed by the affine
opens of the scheme of the object, which lie in the universe of the morphisms of the site, as
`CategoryTheory.GrothendieckTopology.HasEnoughObjects` demands. -/
theorem hasEnoughObjects_isAffine_over (W : SmallEtale B S hS F) :
    ((SmallEtale.topology B S hS F).over W).HasEnoughObjects
      (fun T : Over W => IsAffine (chartScheme T.left)) := by
  intro T
  refine ⟨(chartScheme T.left).affineOpens,
    fun O => Over.mk (openChartInclusion B S hS F T.left O.1 ≫ T.hom),
    fun O => Over.homMk (openChartInclusion B S hS F T.left O.1) rfl, ?_, fun O => O.2⟩
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  refine smallEtale_sieve_of_pointwise_covering B S hS F T.left _ fun z => ?_
  obtain ⟨O, w, hw⟩ := exists_affineOpen_chart_map_eq B S hS F T.left z
  exact ⟨openChart B S hS F T.left O.1, openChartInclusion B S hS F T.left O.1,
    Sieve.ofArrows_mk _ _ O, w, hw⟩

/-! ### The restriction of a basis of sections along a morphism of affine charts -/

/-- **For a module cartesian on affine charts, a basis of the sections over an affine chart
restricts to a basis of the sections over any smaller affine chart.**

The base change comparison is bijective by cartesianness, a basis base changes to a basis of
the tensor product (`Module.Basis.baseChange`), and the comparison carries `1 ⊗ x` to the
restriction of `x`. -/
noncomputable def chartRestrictBasis (H : Modules.{u, u} B S hS F hF)
    (hH : IsCartesianOnAffineCharts H) {W V : SmallEtale B S hS F}
    (hW : IsAffine (chartScheme W)) (hV : IsAffine (chartScheme V)) (f : V ⟶ W)
    {ι : Type*} (b : Module.Basis ι (chartRing B S hS F hF W) (H.val.obj (op W))) :
    Module.Basis ι (chartRing B S hS F hF V) (H.val.obj (op V)) :=
  letI := chartAlgebra (hF := hF) f
  letI := chartSectionsModule H f
  haveI := chartSections_isScalarTower H f
  (b.baseChange (chartRing B S hS F hF V)).map
    (LinearEquiv.ofBijective (sectionsBaseChange H f) (hH W V hW hV f))

/-- The `i`-th vector of the basis `chartRestrictBasis H hH hW hV f b` is the restriction along
`f` of the `i`-th vector of `b`. -/
theorem chartRestrictBasis_apply (H : Modules.{u, u} B S hS F hF)
    (hH : IsCartesianOnAffineCharts H) {W V : SmallEtale B S hS F}
    (hW : IsAffine (chartScheme W)) (hV : IsAffine (chartScheme V)) (f : V ⟶ W)
    {ι : Type*} (b : Module.Basis ι (chartRing B S hS F hF W) (H.val.obj (op W))) (i : ι) :
    chartRestrictBasis B S hS F hF H hH hW hV f b i = H.val.map f.op (b i) := by
  let := chartAlgebra (hF := hF) f
  let := chartSectionsModule H f
  have := chartSections_isScalarTower H f
  show sectionsBaseChange H f ((b.baseChange (chartRing B S hS F hF V)) i) = _
  rw [Module.Basis.baseChange_apply]
  exact chartBaseChange_one_tmul H f (b i)

/-! ### A basis of the sections over an affine chart trivializes the module on the slice -/

/-- **A module cartesian on affine charts whose sections over an affine chart `W` are free of
rank `s` is, on the slice at `W`, a coproduct of `s` copies of the structure sheaf.**

The basis vectors are sections of the restriction of the module to the slice, so they define a
morphism from the coproduct of `s` copies of the structure sheaf.  Over an affine chart of the
slice the restricted basis is again a basis
(`AlgebraicGeometry.Space.chartRestrictBasis`), so that morphism is bijective on the sections
there; the affine charts cover every object of the slice, so it is locally bijective, hence an
isomorphism of sheaves of modules. -/
theorem exists_isColimitCofanUnit_of_basis (H : Modules.{u, u} B S hS F hF)
    (hH : IsCartesianOnAffineCharts H)
    {W : (smallEtaleRingedSite B S hS F hF).C}
    (hW : IsAffine (chartScheme W)) {s : ℕ}
    (b : Module.Basis (Fin s) (chartRing B S hS F hF W) (H.val.obj (op W))) :
    ∃ ι : ∀ _ : Fin s, SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O).over W) ⟶ H.over W,
      Nonempty (IsColimit (Cofan.mk (H.over W) ι)) := by
  classical
  let R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O
  let sect : Fin s → (H.over W).sections := fun i =>
    PresheafOfModules.sectionsMk (fun T => H.val.map (T.unop.hom).op (b i)) (by
      intro T T' g
      show H.val.map (g.unop.left).op (H.val.map (T.unop.hom).op (b i)) =
        H.val.map (T'.unop.hom).op (b i)
      rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w g.unop])
  let q : ∀ _ : Fin s, SheafOfModules.unit (R.over W) ⟶ H.over W :=
    fun i => (H.over W).unitHomEquiv.symm (sect i)
  have : HasFiniteBiproducts (SheafOfModules.{u} (R.over W)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have hP : IsColimit (Cofan.mk (∐ fun _ : Fin s => SheafOfModules.unit (R.over W))
      (Limits.Sigma.ι fun _ : Fin s => SheafOfModules.unit (R.over W))) :=
    coproductIsCoproduct _
  set φ := Cofan.IsColimit.desc hP q with hφ
  have hbas : ∀ (T : Over W) (hT : IsAffine (chartScheme T.left)) (i : Fin s),
      (q i).val.app (op T) (Stacks.SheafOfModules.unitOne (op T)) =
        chartRestrictBasis B S hS F hF H hH hW hT T.hom b i := fun T hT i => by
    rw [Stacks.SheafOfModules.unitHomEquiv_symm_app_unitOne]
    exact (chartRestrictBasis_apply B S hS F hF H hH hW hT T.hom b i).symm
  have hbij : ∀ T : Over W, IsAffine (chartScheme T.left) →
      Function.Bijective (φ.val.app (op T)) := by
    intro T hT
    rw [hφ, Stacks.SheafOfModules.bijective_app_cofanDesc_iff]
    have hfun : (fun y : Fin s → ToType ((R.over W).obj.obj (op T)) =>
        ∑ i, y i • (q i).val.app (op T) (Stacks.SheafOfModules.unitOne (op T))) =
        (chartRestrictBasis B S hS F hF H hH hW hT T.hom b).equivFun.symm :=
      funext fun y => Eq.trans
        (Finset.sum_congr rfl fun i _ => congrArg (fun z => y i • z) (hbas T hT i))
        (Module.Basis.equivFun_symm_apply _ y).symm
    rw [hfun]
    exact (chartRestrictBasis B S hS F hF H hH hW hT T.hom b).equivFun.symm.bijective
  have : PresheafOfModules.IsLocallyInjective
      ((smallEtaleRingedSite B S hS F hF).J.over W) φ.val :=
    Presheaf.isLocallyInjective_of_hasEnoughObjects_injective _ _
      (hasEnoughObjects_isAffine_over B S hS F W) fun T hT => (hbij T hT).injective
  have : PresheafOfModules.IsLocallySurjective
      ((smallEtaleRingedSite B S hS F hF).J.over W) φ.val :=
    Presheaf.isLocallySurjective_of_hasEnoughObjects_surjective _ _
      (hasEnoughObjects_isAffine_over B S hS F W) fun T hT => (hbij T hT).surjective
  have : IsIso φ := Stacks.SheafOfModules.isIso_of_isLocallyBijective φ
  exact ⟨fun i => Limits.Sigma.ι (fun _ : Fin s => SheafOfModules.unit (R.over W)) i ≫ φ,
    ⟨IsColimit.ofIsoColimit hP (Cocones.ext (asIso φ) fun ⟨_⟩ => rfl)⟩⟩

/-! ### Shrinking to a basic-open chart on which the sections are free -/

/-- **Around every point of an affine chart over which the sections are finite locally free of
rank `s` there is a basic-open chart over which they are free with a basis indexed by
`Fin s`.**

The elements cutting out the trivializing basic opens span the unit ideal, so one of them is
invertible at the point; over the basic-open chart it cuts out, the functions are the
localization away from that element
(`AlgebraicGeometry.Space.isLocalization_away_chartRing_openChart_basicOpen`) and the sections
are the corresponding localized module
(`AlgebraicGeometry.Space.isLocalizedModule_chartRestrictLinear_openChart_basicOpen`), so the
basis transports by `Module.nonempty_basis_of_isLocalizedModule_away`. -/
theorem exists_basicOpen_chart_basis (H : Modules.{u, u} B S hS F hF)
    (hH : IsCartesianOnAffineCharts H) {V : SmallEtale B S hS F}
    (hV : IsAffine (chartScheme V)) {s : ℕ}
    (hfree : Module.IsFiniteLocallyFreeOfRank (chartRing B S hS F hF V)
      (H.val.obj (op V)) s)
    (z : chartScheme V) :
    ∃ g : chartRing B S hS F hF V, z ∈ (chartScheme V).basicOpen g ∧
      Nonempty (Module.Basis (Fin s)
        (chartRing B S hS F hF (openChart B S hS F V ((chartScheme V).basicOpen g)))
        (H.val.obj (op (openChart B S hS F V ((chartScheme V).basicOpen g))))) := by
  obtain ⟨κ, gf, hspan, hbas⟩ := hfree
  have hle : (⊤ : (chartScheme V).Opens) ≤
      ⨆ f : (Set.range gf), (chartScheme V).basicOpen f.1 :=
    (isAffineOpen_top (chartScheme V)).self_le_iSup_basicOpen_iff.mpr hspan
  obtain ⟨f, hzf⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (hle (show z ∈ (⊤ : (chartScheme V).Opens) from trivial))
  obtain ⟨i, hi⟩ := f.2
  refine ⟨gf i, by rwa [hi], ?_⟩
  let := chartAlgebra (hF := hF)
    (openChartInclusion B S hS F V ((chartScheme V).basicOpen (gf i)))
  let := chartSectionsModule H
    (openChartInclusion B S hS F V ((chartScheme V).basicOpen (gf i)))
  have := chartSections_isScalarTower H
    (openChartInclusion B S hS F V ((chartScheme V).basicOpen (gf i)))
  have := isLocalization_away_chartRing_openChart_basicOpen B S hS hF V hV (gf i)
  have := isLocalizedModule_chartRestrictLinear_openChart_basicOpen B S hS hF H hH V hV (gf i)
  exact Module.nonempty_basis_of_isLocalizedModule_away (gf i)
    (chartRestrictLinear H
      (openChartInclusion B S hS F V ((chartScheme V).basicOpen (gf i)))) (hbas i).some

/-! ### A chartwise rank is a rank -/

/-- The affine étale charts over which the sections of `H` are free with a basis indexed by
`Fin s`.  The proof of
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_chartwise` refines the chartwise
hypothesis to the presieve of these. -/
private def BasisChart (H : Modules.{u, u} B S hS F hF) (s : ℕ)
    (V : SmallEtale B S hS F) : Prop :=
  IsAffine (chartScheme V) ∧
    Nonempty (Module.Basis (Fin s) (chartRing B S hS F hF V) (H.val.obj (op V)))

/-- **The converse direction of the rank form of Descent, Proposition 03DX (2), for a module
cartesian on affine charts.**  If the affine étale charts over which the sections of `H` form
a finite locally free module of rank `s` generate a covering sieve of every étale chart, then
`H` is finite locally free of rank `s` in the sense of the rank clause of Stacks 0409.

Cartesianness is what makes this true, and it enters twice: it shrinks an affine chart to a
basic-open chart on which the sections are genuinely free, and it makes the restriction of a
basis of the sections a basis again over every smaller affine chart. -/
theorem isFiniteLocallyFreeOfRank_of_chartwise (H : Modules.{u, u} B S hS F hF)
    (hH : IsCartesianOnAffineCharts H) (s : ℕ)
    (hcov : ∀ U : SmallEtale B S hS F,
      Sieve.generate (fun (V : SmallEtale B S hS F) (_ : V ⟶ U) =>
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V) ∧
          Module.IsFiniteLocallyFreeOfRank (chartRing B S hS F hF V)
            (H.val.obj (op V)) s) ∈ SmallEtale.topology B S hS F U) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS F hF) H s := by
  classical
  have key : ∀ U : SmallEtale B S hS F, ∃ (I : Type (u + 1)) (V : I → SmallEtale B S hS F)
      (f : ∀ i, V i ⟶ U), Sieve.ofArrows V f ∈ SmallEtale.topology B S hS F U ∧
        ∀ i, BasisChart B S hS F hF H s (V i) := by
    intro U
    have hgen : Sieve.generate (fun (V : SmallEtale B S hS F) (_ : V ⟶ U) =>
        BasisChart B S hS F hF H s V) ∈ SmallEtale.topology B S hS F U := by
      refine smallEtale_sieve_of_pointwise_covering B S hS F U _ fun z => ?_
      obtain ⟨V₁, g₁, hg₁, z₁, hz₁⟩ := exists_mem_sieve_scheme_point B S hS F U (hcov U) z
      obtain ⟨V, t, m, ⟨hVaff, hVfree⟩, hfac⟩ := hg₁
      obtain ⟨g, hzg, hbasis⟩ := exists_basicOpen_chart_basis B S hS F hF H hH hVaff hVfree
        ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map t) z₁)
      have hz₂ : ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map t) ≫
          (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map m)) z₁ = z := by
        rwa [← Functor.map_comp, ← Functor.map_comp, hfac]
      have hι : (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map
            (openChartInclusion B S hS F V ((chartScheme V).basicOpen g)))
            ⟨_, hzg⟩ =
          (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map t) z₁ := by
        rw [toScheme_map_toOver_map_openChartInclusion]
        rfl
      refine ⟨openChart B S hS F V ((chartScheme V).basicOpen g),
        openChartInclusion B S hS F V ((chartScheme V).basicOpen g) ≫ m,
        ⟨_, 𝟙 _, _, ⟨isAffine_chartScheme_openChart_basicOpen B S hS F V hVaff g, hbasis⟩,
          Category.id_comp _⟩,
        ⟨_, hzg⟩, ?_⟩
      rw [Functor.map_comp, Functor.map_comp]
      exact Eq.trans (congrArg ⇑((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map m)) hι) hz₂
    refine ⟨Σ V : SmallEtale B S hS F, {f : V ⟶ U // BasisChart B S hS F hF H s V},
      fun i => i.1, fun i => i.2.1, ?_, fun i => i.2.2⟩
    refine (SmallEtale.topology B S hS F).superset_covering ?_ hgen
    rintro Z g ⟨V, t, m, hm, rfl⟩
    refine Sieve.downward_closed _ ?_ t
    exact Sieve.ofArrows_mk _ _ (⟨V, m, hm⟩ : Σ V : SmallEtale B S hS F,
      {f : V ⟶ U // BasisChart B S hS F hF H s V})
  intro U
  obtain ⟨I, V, f, hcovI, hBas⟩ := key U
  exact ⟨I, V, f, hcovI, fun i => exists_isColimitCofanUnit_of_basis B S hS F hF H hH
    (hBas i).1 (hBas i).2.some⟩

/-! ### Discharging the covering hypothesis -/

/-- **The affine étale charts over an étale chart generate a covering sieve of it.**  The
affine opens of the chart's scheme cover it, and each of them is again an étale chart, affine
because the open is.

This is the non-slice companion of
`AlgebraicGeometry.Space.hasEnoughObjects_isAffine_over`, and it is what turns a rank known at
*every* affine chart into the covering-sieve hypothesis of
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_chartwise`. -/
theorem affineChartSieve_mem_topology (U : SmallEtale B S hS F) :
    Sieve.generate (fun (V : SmallEtale B S hS F) (_ : V ⟶ U) =>
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V)) ∈
      SmallEtale.topology B S hS F U := by
  refine smallEtale_sieve_of_pointwise_covering B S hS F U _ fun z => ?_
  obtain ⟨O, w, hw⟩ := exists_affineOpen_chart_map_eq B S hS F U z
  exact ⟨openChart B S hS F U O.1, openChartInclusion B S hS F U O.1,
    ⟨_, 𝟙 _, _, O.2, Category.id_comp _⟩, w, hw⟩

/-- **A module cartesian on affine charts whose sections over every affine étale chart are
finite locally free of rank `s` is finite locally free of rank `s`.**

This is `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_chartwise` with its covering-sieve
hypothesis discharged by `AlgebraicGeometry.Space.affineChartSieve_mem_topology`: affine charts
already cover every chart, so a rank holding at all of them generates the required sieve. -/
theorem isFiniteLocallyFreeOfRank_of_forall_isAffine (H : Modules.{u, u} B S hS F hF)
    (hH : IsCartesianOnAffineCharts H) (s : ℕ)
    (haff : ∀ V : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V) →
        Module.IsFiniteLocallyFreeOfRank (chartRing B S hS F hF V) (H.val.obj (op V)) s) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS F hF) H s :=
  isFiniteLocallyFreeOfRank_of_chartwise B S hS F hF H hH s fun U =>
    (SmallEtale.topology B S hS F).superset_covering
      (fun V g hg => by
        obtain ⟨Z, p, q, hq, rfl⟩ := hg
        exact ⟨Z, p, q, ⟨hq, haff Z hq⟩, rfl⟩)
      (affineChartSieve_mem_topology B S hS F U)

/-- **A quasi-coherent module whose sections over every affine étale chart are finite locally
free of rank `s` is finite locally free of rank `s`.**

Quasi-coherence supplies cartesianness on affine charts by the forward implication of
Descent, Proposition 03DX (2),
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`, and
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_forall_isAffine` concludes. -/
theorem isFiniteLocallyFreeOfRank_of_forall_isAffine_of_isQuasicoherentOnSite
    (H : Modules.{u, u} B S hS F hF) (hH : H.IsQuasicoherentOnSite) (s : ℕ)
    (haff : ∀ V : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V) →
        Module.IsFiniteLocallyFreeOfRank (chartRing B S hS F hF V) (H.val.obj (op V)) s) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS F hF) H s :=
  isFiniteLocallyFreeOfRank_of_forall_isAffine B S hS F hF H
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF H hH) s haff

end AlgebraicGeometry.Space

end
