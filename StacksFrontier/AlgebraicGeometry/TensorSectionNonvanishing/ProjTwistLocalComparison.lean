module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DegreeZeroLocalizationArbitraryDegree
public import StacksFrontier.AlgebraicGeometry.ProjGradedModuleQcoh.ChartSections
public import StacksFrontier.AlgebraicGeometry.ProjQuasiCoherentRecovery.Basic
public import StacksFrontier.AlgebraicGeometry.TensorSectionNonvanishing.ProjTwistScalarTriviality
public import StacksFrontier.RingTheory.GradedAlgebra.VeroneseModuleAwayDegreeOne
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.TensorOfGeneratorTorsors

/-!
# The local comparison map on a standard open, for the twisted global sections

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a graded ring, `X = Proj 𝒮`, let `ℱ` be an arbitrary sheaf of
`𝒪_X`-modules and let `M = ⨁_{i ≥ 0} Γ(X, ℱ(i))` be the graded `S`-module of twisted global
sections. For `f ∈ 𝒮 d` homogeneous of positive degree, the sections of the associated sheaf `M̃`
over the standard open `D₊(f)` are the degree-zero fractions `x / f ^ n` with `x` homogeneous of
degree `n d`, and the comparison map of Tag 03GM (2) sends such a fraction to the section of `ℱ`
obtained by restricting `x` to `D₊(f)` and dividing by the trivializing section `f ^ n`.

This file builds that map, `Γ(D₊(f), M̃) → Γ(D₊(f), ℱ)`, and proves it linear over
`Γ(D₊(f), 𝒪)`.

## The two steps

Division by `f ^ n` is the inverse of multiplication by `f ^ n`, which is bijective on the
sections over any open inside `D₊(f)` by
`Stacks.AlgebraicGeometry.ProjTwistRestriction.bijective_mulTrivSection`. Composing it with the
restriction of the degree-`n d` component of `M` gives the map `numerSection` on numerators, and
`numerSection_pow_smul` is its compatibility with multiplying numerator and denominator by `f`,
so `Stacks.SheafOfModules.degreeZeroLocalizationLiftOfDegree` descends it to the degree-zero
localization `M₍f₎`.

That lift is *semilinear* over a ring map out of `HomogeneousLocalization.Away 𝒮 f`, while a
comparison map on a chart has to be linear over `Γ(D₊(f), 𝒪)`. The ring map in question is
`AlgebraicGeometry.Proj.awayToSection`, which is an isomorphism for `f` of positive degree
(`AlgebraicGeometry.ProjectiveSpectrum.Proj.isIso_awayToSection`), and the action of
`HomogeneousLocalization.Away 𝒮 f` on the sections over `D₊(f)` is by definition the action of
`Γ(D₊(f), 𝒪)` pulled back along it
(`AlgebraicGeometry.ProjectiveSpectrum.Proj.standardOpenModule`). So linearity follows from
semilinearity by surjectivity of the ring map, which is `map_smul_of_semilinear` below.

Two charts `D₊(g) ⊆ D₊(f)` are then compared: the fraction `x / f ^ n` is rewritten with
denominator a power of `g` using `ProjectiveSpectrum.exists_pow_eq_mul_of_basicOpen_le_degree`,
which supplies a homogeneous `c` with `g ^ b = c f` *together with its degree*, so the two chart
maps agree on the overlap. With that, the chart maps form a
`Stacks.AlgebraicGeometry.ProjTwistComparison.StandardOpenHomData` and glue to a morphism
`M̃ ⟶ ℱ`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistLocalComparison.linearMapOfSemilinear`: the transfer of
  linearity along a surjective ring map.
* `Stacks.AlgebraicGeometry.ProjTwistLocalComparison.divTriv`: division by the trivializing
  section `f ^ n`, the inverse of `mulTrivSection`.
* `Stacks.AlgebraicGeometry.ProjTwistLocalComparison.numerSection`: the map on numerators.
* `Stacks.AlgebraicGeometry.ProjTwistLocalComparison.chartHom`: **the comparison map
  `Γ(D₊(f), M̃) ⟶ Γ(D₊(f), ℱ)` on a chart**, a morphism of modules over `Γ(D₊(f), 𝒪)`.
* `Stacks.AlgebraicGeometry.ProjTwistLocalComparison.comparison`: **the morphism `M̃ ⟶ ℱ`** it
  glues to.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistLocalComparison.twistScalarSheafMap_trivializingSection_smul`
  and `twistSheafScalarMap_mulTrivSection_smul`: **multiplication by a homogeneous `r` of degree
  `m d` is multiplication by the degree-zero fraction `r / f ^ m` followed by multiplication by
  `f ^ m`**, on the trivializing sections of `𝒪(n d)` and on the sections `t ⊗ f ^ n` of
  `ℱ(n d)`. This is what makes the comparison map semilinear.
* `Stacks.AlgebraicGeometry.ProjTwistLocalComparison.numerSection_pow_smul`: the numerator maps
  are compatible with multiplying numerator and denominator by `f`.
* `Stacks.AlgebraicGeometry.ProjTwistLocalComparison.mulTrivSection_chartHom`: **the
  fraction-wise formula** — the image of a section given by the fraction `x / f ^ n` is the
  section whose product with `f ^ n` is the restriction of the degree-`n d` component of `x`.
* `Stacks.AlgebraicGeometry.ProjTwistLocalComparison.chartHom_restrict`: **the chart maps agree
  on overlaps.**
* `Stacks.AlgebraicGeometry.ProjTwistLocalComparison.existsUnique_comparison`: the glued morphism
  is the only one restricting to the chart maps.
* `Stacks.AlgebraicGeometry.ProjTwistLocalComparison.chartHom_congr`: **the chart map does not
  depend on the degree in which `f` is homogeneous**, so a formula proved at a given degree
  witness may be read off the chart map of a positive-degree element, whose witness is chosen by
  `Exists.choose`.
* `Stacks.AlgebraicGeometry.ProjTwistLocalComparison.isIso_comparison`: **the glued morphism is
  an isomorphism as soon as every chart map is bijective on sections**, and
  `Stacks.AlgebraicGeometry.ProjTwistLocalComparison.isIso_comparison_of_bijective_chartHom`, the
  same statement with that hypothesis asked for at a given degree rather than a chosen one.

## Where the tag's second assertion is proved

**No `stacks` attribute is attached in this file**, because what is built here is the morphism
together with the reduction of the assertion to local bijectivity, and neither of those is the
whole tag. The local bijectivity itself — the hypothesis `hloc` of `isIso_comparison` and
`isIso_comparison_of_bijective_chartHom` below, which is the source's omitted injectivity and
surjectivity argument — **is proved**, in
`StacksFrontier/AlgebraicGeometry/TensorSectionNonvanishing/ProjTwistChartBijective.lean`
(`Stacks.AlgebraicGeometry.ProjTwistChartBijective.bijective_chartHom_of_cover`), and the whole of
Tag 03GM is carried by
`Stacks.AlgebraicGeometry.ProjTwistComparisonIso.gradedModule_and_isIso_comparison`. Tag 0B5I's
comparison is a different statement: that tag's `M` is the ℤ-graded `⨁_{n ∈ ℤ} Γ(X, ℱ(n))`, while
the module here is the ℕ-graded `⨁_{d ≥ 0} Γ(X, ℱ(d))` of Tag 03GM.

**Which route supplies `hloc`.** The source proves 03GM (2) on `ℙⁿ_R` directly: it writes
`ℱ|_{U_i} = Ñ_i` on the charts `U_i = D₊(T_i)` of the degree-**one** coordinates and runs a
localization-and-cocycle argument, and that is the route taken here.

* The globalization step,
  `Stacks.AlgebraicGeometry.ProjQuasiCoherentRecovery.isIso_of_bijective_app_onBasis`, asks for
  bijectivity on a **basis** — *every* homogeneous `g` of positive degree `e`, with `e` arbitrary
  — and the degree-one charts suffice for this. The chart argument needs a finite
  cover by standard opens of elements of **the degree of the element being localized at**, and at
  degree `e` such a cover is given by the `e`-th powers of the degree-one elements, whose standard
  opens are the *same* opens (`ProjectiveSpectrum.basicOpen_pow`). So finitely many degree-one
  elements whose standard opens cover `Proj 𝒮` settle `hloc` at every positive degree at once;
  this is
  `Stacks.AlgebraicGeometry.ProjTwistChartBijective.isIso_comparison_of_degreeOneCover`.
* At a single chart the source's two omitted halves are the `hsurj` and `hinj` of
  `Stacks.SheafOfModules.bijective_degreeZeroLocalizationLiftOfDegree_of_degree` for the family
  `numerSection`, and that is the criterion they are supplied to. They are proved in the 03GM
  spelling, out of the affine statements for a quasi-coherent sheaf over a basic open
  (`Stacks.ModuleSectionExtension.exists_pow_smul_eq_zero`, `exists_pow_smul_eq_res` and
  `exists_pow_smul_eq_of_res_eq`) at the chart identification
  `Stacks.ProjChartBasicOpen.basicOpen_awayToSection_mk`, rather than transported from part (2) of
  [Stacks, Tag 01PW] (`Stacks.SheafOfModules.sectionLocalizationMap_bijective`, read on a chart of
  `Proj 𝒮` by `bijective_sectionLocalizationMap_degreeSection` in the namespace
  `Stacks.AlgebraicGeometry.ProjChartNonvanishingOpen`).
  That transport would need a comparison of the ℕ-graded module of Tag 03GM with the ℤ-graded
  section module of [Stacks, Tag 01CV], which `bijective_chartHom_of_degreewise` below reduces to
  a degreewise comparison but which no declaration in the tree supplies; working in the 03GM
  spelling throughout avoids it.

## References

* [Stacks Project, Tag 03GM](https://stacks.math.columbia.edu/tag/03GM)
* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory DirectSum
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistScalarSheafMap twistSheafScalarMap)
open Stacks.AlgebraicGeometry.ProjTrivialization (trivializingSection trivializingFun
  projRingSheaf)
open Stacks.AlgebraicGeometry.ProjTwistRestriction (mulTrivSection twistRestrictIso
  bijective_mulTrivSection twistRestrictIso_hom_val_app_mulTrivSection
  twistSheafScalarMap_mulTrivSection_pow twistSheafScalarMap_mulTrivSection
  eq_of_mulTrivSection_twistSheafScalarMap)
open Stacks.AlgebraicGeometry.ProjTwistSectionModule (twistSections twistSectionModule
  moduleGrading associatedTwistSectionSheaf gsmul smul_of)
open Stacks.Cohomology.Generators (toTensorSheafSection_restrict toTensorSheafSection_smul_left
  toTensorSheafSection_smul_right)
open Stacks.SheafOfModules.TensorStalkRingedSpace (toTensorSheafSection
  tensorSheafMap_app_toTensorSheafSection)
open scoped Stacks.GradedLocalization
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.ProjTwistLocalComparison

universe u w

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

/-! ### Transfer of linearity along a surjective ring map -/

section Transfer

variable {R' K A N : Type*} [Ring R'] [Semiring K]
  [AddCommGroup A] [AddCommGroup N] [Module K A] [Module K N] [Module R' A]

/-- **Transfer of linearity along a surjective ring map.** If the `R'`-action on `A` is the
`K`-action pulled back along `φ` and an additive map is semilinear over `φ`, then it is
`K`-linear, because every scalar of `K` is a value of `φ`. -/
theorem map_smul_of_semilinear (φ : R' →+* K) (hφ : Function.Surjective φ)
    (hcomp : ∀ (a : R') (z : A), a • z = φ a • z) (ψ : A →+ N)
    (hψ : ∀ (a : R') (z : A), ψ (a • z) = φ a • ψ z) (c : K) (z : A) :
    ψ (c • z) = c • ψ z := by
  obtain ⟨a, rfl⟩ := hφ c
  exact ((congrArg ψ (hcomp a z)).symm.trans (hψ a z))

/-- The `K`-linear map an additive map semilinear over a surjective `φ` is. -/
def linearMapOfSemilinear (φ : R' →+* K) (hφ : Function.Surjective φ)
    (hcomp : ∀ (a : R') (z : A), a • z = φ a • z) (ψ : A →+ N)
    (hψ : ∀ (a : R') (z : A), ψ (a • z) = φ a • ψ z) : A →ₗ[K] N where
  toFun := ψ
  map_add' := ψ.map_add
  map_smul' := map_smul_of_semilinear φ hφ hcomp ψ hψ

/-- `linearMapOfSemilinear φ hφ hcomp ψ hψ` agrees with `ψ` pointwise. -/
@[simp] theorem linearMapOfSemilinear_apply (φ : R' →+* K) (hφ : Function.Surjective φ)
    (hcomp : ∀ (a : R') (z : A), a • z = φ a • z) (ψ : A →+ N)
    (hψ : ∀ (a : R') (z : A), ψ (a • z) = φ a • ψ z) (z : A) :
    linearMapOfSemilinear φ hφ hcomp ψ hψ z = ψ z := rfl

end Transfer

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

variable {f : S} {d : ℕ}

/-! ### Multiplication by and division by a power of the trivializing section -/

section Division

variable (F : SheafOfModules.{u} (projRingSheaf 𝒮))

/-- **Division by `f ^ n`** on the sections over an open `W ⊆ D₊(f)`: the inverse of
multiplication by `f ^ n`, read off the isomorphism `ℱ(nd)|_{D₊(f)} ≅ ℱ|_{D₊(f)}`. -/
def divTriv (hf : f ∈ 𝒮 d) (n : ℕ) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (y : (twistSheafOfModules 𝒮 F ((n : ℤ) * d)).val.obj (op W)) : F.val.obj (op W) :=
  (twistRestrictIso 𝒮 hf (n : ℤ) F).hom.val.app (op (Over.mk (homOfLE hW))) y

/-- Division by `f ^ n` is additive. -/
theorem divTriv_add (hf : f ∈ 𝒮 d) (n : ℕ) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (y z : (twistSheafOfModules 𝒮 F ((n : ℤ) * d)).val.obj (op W)) :
    divTriv 𝒮 F hf n hW (y + z) = divTriv 𝒮 F hf n hW y + divTriv 𝒮 F hf n hW z :=
  map_add _ _ _

/-- Dividing by `f ^ n` and multiplying back by `f ^ n` is the identity. -/
theorem mulTrivSection_divTriv (hf : f ∈ 𝒮 d) (n : ℕ)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (y : (twistSheafOfModules 𝒮 F ((n : ℤ) * d)).val.obj (op W)) :
    mulTrivSection 𝒮 hf (n : ℤ) F hW (divTriv 𝒮 F hf n hW y) = y := by
  obtain ⟨t, rfl⟩ := (bijective_mulTrivSection 𝒮 hf (n : ℤ) F hW).2 y
  exact congrArg (mulTrivSection 𝒮 hf (n : ℤ) F hW)
    (twistRestrictIso_hom_val_app_mulTrivSection 𝒮 hf (n : ℤ) F hW t)

/-- Multiplication by `f ^ n` is linear in the section. -/
theorem mulTrivSection_smul (hf : f ∈ 𝒮 d) (n : ℤ)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W)) (t : F.val.obj (op W)) :
    mulTrivSection 𝒮 hf n F hW (r • t) = r • mulTrivSection 𝒮 hf n F hW t :=
  toTensorSheafSection_smul_left (AlgebraicGeometry.Proj 𝒮).toRingedSpace F
    (twistingSheaf 𝒮 (n * d)) W r t (trivializingSection 𝒮 hf n hW)

/-- Multiplication by `f ^ n` commutes with restriction to a smaller open. -/
theorem mulTrivSection_restrict (hf : f ∈ 𝒮 d) (n : ℤ)
    {W V : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (hV : V ≤ W) (t : F.val.obj (op W)) :
    (twistSheafOfModules 𝒮 F (n * d)).val.map (homOfLE hV).op
        (mulTrivSection 𝒮 hf n F hW t) =
      mulTrivSection 𝒮 hf n F (hV.trans hW) ((F.val.map (homOfLE hV).op).hom t) :=
  toTensorSheafSection_restrict (AlgebraicGeometry.Proj 𝒮).toRingedSpace F
    (twistingSheaf 𝒮 (n * d)) hV t (trivializingSection 𝒮 hf n hW)

end Division


/-! ### Multiplication by a homogeneous scalar of the form `r / f ^ m` -/

section Scalar

/-- Localizing multiplication by a ring element and evaluating on a fraction multiplies the
numerator. An alias of `Stacks.AlgebraicGeometry.ProjTwistRestriction.map_mul_mk`. -/
private alias map_mul_mk := Stacks.AlgebraicGeometry.ProjTwistRestriction.map_mul_mk

/-- **Multiplication by a homogeneous `r` of degree `m d` carries the trivializing section
`f ^ n` of `𝒪(nd)` to the degree-zero fraction `r / f ^ m` times the trivializing section
`f ^ (n + m)` of `𝒪((n+m)d)`.** The scalar is given by its values in the local rings, so the
statement applies both to `r / f ^ m` on `D₊(f)` and to its restriction to a smaller open. -/
theorem twistScalarSheafMap_trivializingSection_smul (hf : f ∈ 𝒮 d) {m n j : ℕ} {r : S}
    (hr : r ∈ 𝒮 (m * d)) (hj : j = n + m)
    (hdeg : ((m * d : ℕ) : ℤ) + (n : ℤ) * d = (j : ℤ) * d)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (c : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W))
    (hc : ∀ x : W, HomogeneousLocalization.val (c.1 x) =
      Localization.mk r ⟨f ^ m,
        x.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hW x.2) m⟩) :
    (twistScalarSheafMap 𝒮 (m * d) ((n : ℤ) * d) ((j : ℤ) * d) hdeg ⟨r, hr⟩).val.app (op W)
        (trivializingSection 𝒮 hf (n : ℤ) hW) =
      c • trivializingSection 𝒮 hf (j : ℤ) hW := by
  subst hj
  have hn : ((n : ℤ)).toNat = n := by omega
  have hn' : (-(n : ℤ)).toNat = 0 := by omega
  have hnm : (((n + m : ℕ) : ℤ)).toNat = n + m := by omega
  have hnm' : (-((n + m : ℕ) : ℤ)).toNat = 0 := by omega
  apply Subtype.ext
  funext x
  show LocalizedModule.map x.1.asHomogeneousIdeal.toIdeal.primeCompl
      (LinearMap.mul S S r) (trivializingFun 𝒮 (n : ℤ) hW x) =
    HomogeneousLocalization.val (c.1 x) * trivializingFun 𝒮 ((n + m : ℕ) : ℤ) hW x
  rw [trivializingFun, map_mul_mk, hc x, trivializingFun, Localization.mk_mul]
  refine Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq ?_)
  simp only [hn, hn', hnm, hnm', pow_zero, pow_add, mul_one, one_mul, Submonoid.coe_mul]
  ring

/-- **The same law after tensoring with `ℱ`**: multiplication by a homogeneous `r` of degree
`m d` carries `t ⊗ f ^ n` to `(r / f ^ m) t ⊗ f ^ (n + m)`. -/
theorem twistSheafScalarMap_mulTrivSection_smul (hf : f ∈ 𝒮 d) {m n j : ℕ} {r : S}
    (hr : r ∈ 𝒮 (m * d)) (hj : j = n + m)
    (hdeg : ((m * d : ℕ) : ℤ) + (n : ℤ) * d = (j : ℤ) * d)
    (F : SheafOfModules.{u} (projRingSheaf 𝒮))
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (c : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W))
    (hc : ∀ x : W, HomogeneousLocalization.val (c.1 x) =
      Localization.mk r ⟨f ^ m,
        x.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hW x.2) m⟩)
    (t : F.val.obj (op W)) :
    (twistSheafScalarMap 𝒮 F (m * d) ((n : ℤ) * d) ((j : ℤ) * d) hdeg ⟨r, hr⟩).val.app (op W)
        (mulTrivSection 𝒮 hf (n : ℤ) F hW t) =
      mulTrivSection 𝒮 hf (j : ℤ) F hW (c • t) := by
  refine Eq.trans (tensorSheafMap_app_toTensorSheafSection
      (AlgebraicGeometry.Proj 𝒮).toRingedSpace F (twistingSheaf 𝒮 ((n : ℤ) * d)) F
      (twistingSheaf 𝒮 ((j : ℤ) * d)) (𝟙 F) _ W t
      (trivializingSection 𝒮 hf (n : ℤ) hW)) ?_
  refine Eq.trans (congrArg (fun y => toTensorSheafSection
      (AlgebraicGeometry.Proj 𝒮).toRingedSpace F (twistingSheaf 𝒮 ((j : ℤ) * d))
      (op W) (t ⊗ₜ[(AlgebraicGeometry.Proj 𝒮).toRingedSpace.presheaf.obj (op W)] y))
    (twistScalarSheafMap_trivializingSection_smul 𝒮 hf hr hj hdeg hW c hc)) ?_
  refine Eq.trans (toTensorSheafSection_smul_right (AlgebraicGeometry.Proj 𝒮).toRingedSpace F
    (twistingSheaf 𝒮 ((j : ℤ) * d)) W c t (trivializingSection 𝒮 hf (j : ℤ) hW)) ?_
  exact (toTensorSheafSection_smul_left (AlgebraicGeometry.Proj 𝒮).toRingedSpace F
    (twistingSheaf 𝒮 ((j : ℤ) * d)) W c t (trivializingSection 𝒮 hf (j : ℤ) hW)).symm

end Scalar

/-! ### The maps on numerators -/

section Numerator

variable (F : SheafOfModules.{u} (projRingSheaf 𝒮))

/-- The degree-`k` component of an element of `⨁_{i ≥ 0} Γ(X, ℱ(i))`. -/
def degreeComponent (k : ℕ) : twistSectionModule 𝒮 F →+ twistSections 𝒮 F k :=
  (DirectSum.component ℤ ℕ (twistSections 𝒮 F) k).toAddMonoidHom

/-- The degree-`k` component of `DirectSum.of _ k s` is `s`. -/
@[simp] theorem degreeComponent_of (k : ℕ) (s : twistSections 𝒮 F k) :
    degreeComponent 𝒮 F k (DirectSum.of (twistSections 𝒮 F) k s) = s :=
  DirectSum.of_eq_same k s

/-- The action of a homogeneous element on a homogeneous element of `M`, with the target degree
a parameter. -/
theorem smul_of' {e k j : ℕ} {a : S} (ha : a ∈ 𝒮 e) (hj : j = e + k)
    (s : twistSections 𝒮 F k) :
    a • DirectSum.of (twistSections 𝒮 F) k s =
      DirectSum.of (twistSections 𝒮 F) j (gsmul 𝒮 F ha k j hj s) := by
  subst hj
  exact smul_of 𝒮 F ⟨a, ha⟩ s

/-- The action of a homogeneous element on the global sections of a twist is the global sections
of the morphism of twists it induces.

Both morphisms of twists tensor `ℱ` with multiplication by `a` on the twisting sheaves, but they
are assembled differently: `gsmul` goes through
`Stacks.AlgebraicGeometry.ProjTwistSectionModule.twistMul`, which is the image under the functor
`(Tensor.sheafTensor 𝒪).obj ℱ`, while `twistSheafScalarMap` is the image under the uncurried
bifunctor of the pair `(𝟙 ℱ, ·)`. The two agree because both sheafify the same presheaf-level
`tensorHom`, which is `Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map`; the equation is
named here so that the identification is checked once on variables rather than once per use
site below. -/
theorem gsmul_eq {e k j : ℕ} {a : S} (ha : a ∈ 𝒮 e) (hj : j = e + k)
    (hk : (e : ℤ) + (k : ℤ) = (j : ℤ)) (s : twistSections 𝒮 F k) :
    gsmul 𝒮 F ha k j hj s =
      (twistSheafScalarMap 𝒮 F e (k : ℤ) (j : ℤ) hk ⟨a, ha⟩).val.app (op ⊤) s :=
  (congrArg (fun α : twistSheafOfModules 𝒮 F (k : ℤ) ⟶ twistSheafOfModules 𝒮 F (j : ℤ) =>
      (α.val.app (op ⊤)).hom s)
    (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map.{u, u, u, u, u}
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮) (𝟙 F)
      (twistScalarSheafMap 𝒮 e (k : ℤ) (j : ℤ) hk ⟨a, ha⟩))).symm

/-- The restriction to `W` of the degree-`j` component of `r • x`, for `x` homogeneous of
degree `k` and `r` homogeneous of degree `i` with `j = i + k`: it is multiplication by `r` on the
twists, applied to the restriction of `x`. -/
private theorem restrict_degreeComponent_smul {i k j : ℕ} {r : S} (hr : r ∈ 𝒮 i)
    (hj : j = i + k) (hdeg : (i : ℤ) + (k : ℤ) = (j : ℤ)) (s : twistSections 𝒮 F k)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} :
    (twistSheafOfModules 𝒮 F (j : ℤ)).val.map (homOfLE (le_top : W ≤ ⊤)).op
        (degreeComponent 𝒮 F j (r • DirectSum.of (twistSections 𝒮 F) k s)) =
      (twistSheafScalarMap 𝒮 F i (k : ℤ) (j : ℤ) hdeg ⟨r, hr⟩).val.app (op W)
        ((twistSheafOfModules 𝒮 F (k : ℤ)).val.map (homOfLE (le_top : W ≤ ⊤)).op s) := by
  have h4 : degreeComponent 𝒮 F j (r • DirectSum.of (twistSections 𝒮 F) k s) =
      (twistSheafScalarMap 𝒮 F i (k : ℤ) (j : ℤ) hdeg ⟨r, hr⟩).val.app (op ⊤) s := by
    rw [smul_of' 𝒮 F hr hj s, degreeComponent_of]
    exact gsmul_eq 𝒮 F hr hj hdeg s
  refine Eq.trans (congrArg ((twistSheafOfModules 𝒮 F (j : ℤ)).val.map
    (homOfLE (le_top : W ≤ ⊤)).op) h4) ?_
  exact (PresheafOfModules.naturality_apply
    (twistSheafScalarMap 𝒮 F i (k : ℤ) (j : ℤ) hdeg ⟨r, hr⟩).val
    (homOfLE (le_top : W ≤ ⊤)).op s).symm

/-- **The numerator map**: the degree-`n d` component of an element of `M`, restricted to
`W ⊆ D₊(f)` and divided by `f ^ n`. This is the family that Tag 0B5I's local comparison lifts
to the degree-zero localization. -/
def numerSection (hf : f ∈ 𝒮 d) (n : ℕ) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) :
    twistSectionModule 𝒮 F →+ F.val.obj (op W) :=
  AddMonoidHom.mk'
    (fun x => divTriv 𝒮 F hf n hW
      ((twistSheafOfModules 𝒮 F ((n : ℤ) * d)).val.map (homOfLE (le_top : W ≤ ⊤)).op
        (degreeComponent 𝒮 F (n * d) x)))
    (fun x y => by
      simp only [map_add]
      exact divTriv_add 𝒮 F hf n hW _ _)

/-- Multiplying the numerator map back by `f ^ n` recovers the restriction of the degree-`n d`
component. -/
theorem mulTrivSection_numerSection (hf : f ∈ 𝒮 d) (n : ℕ)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (x : twistSectionModule 𝒮 F) :
    mulTrivSection 𝒮 hf (n : ℤ) F hW (numerSection 𝒮 F hf n hW x) =
      (twistSheafOfModules 𝒮 F ((n : ℤ) * d)).val.map (homOfLE (le_top : W ≤ ⊤)).op
        (degreeComponent 𝒮 F (n * d) x) :=
  mulTrivSection_divTriv 𝒮 F hf n hW _

/-- Multiplying the numerator map of a homogeneous element back by `f ^ n` recovers its
restriction. -/
private theorem mulTrivSection_numerSection_of (hf : f ∈ 𝒮 d) (n : ℕ)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (s : twistSections 𝒮 F (n * d)) :
    mulTrivSection 𝒮 hf (n : ℤ) F hW
        (numerSection 𝒮 F hf n hW (DirectSum.of (twistSections 𝒮 F) (n * d) s)) =
      (twistSheafOfModules 𝒮 F ((n : ℤ) * d)).val.map (homOfLE (le_top : W ≤ ⊤)).op s := by
  rw [mulTrivSection_numerSection, degreeComponent_of]

/-- **The numerator maps are compatible with multiplying numerator and denominator by `f`**:
this is what makes them descend to the degree-zero localization. -/
theorem numerSection_pow_smul (hf : f ∈ 𝒮 d) (n k : ℕ)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (x : twistSectionModule 𝒮 F) (hx : x ∈ moduleGrading 𝒮 F ((n * d : ℕ) : ℤ)) :
    numerSection 𝒮 F hf (n + k) hW (f ^ k • x) = numerSection 𝒮 F hf n hW x := by
  obtain ⟨s, rfl⟩ := hx
  have hpow : f ^ k ∈ 𝒮 (k * d) := by
    simpa [mul_comm] using SetLike.pow_mem_graded k hf
  have hj : (n + k) * d = k * d + n * d := by ring
  have hk : ((k * d : ℕ) : ℤ) + (n : ℤ) * d = ((n + k : ℕ) : ℤ) * d := by
    push_cast
    ring
  refine (bijective_mulTrivSection 𝒮 hf ((n + k : ℕ) : ℤ) F hW).1 ?_
  rw [mulTrivSection_numerSection]
  erw [restrict_degreeComponent_smul 𝒮 F hpow hj hk s]
  erw [← mulTrivSection_numerSection_of 𝒮 F hf n hW s]
  exact twistSheafScalarMap_mulTrivSection_pow 𝒮 hf n k F hW _

end Numerator


/-! ### The comparison map on a chart -/

section Comparison

variable (F : SheafOfModules.{u} (projRingSheaf 𝒮))

/-- **The numerator maps are semilinear** over the comparison map
`A₍f₎ → Γ(D₊(f), 𝒪)`: acting by a homogeneous `r` of degree `m d` on a numerator of degree
`n d` and then dividing by `f ^ (m + n)` is multiplication by the degree-zero fraction
`r / f ^ m`. -/
theorem numerSection_smul (hf : f ∈ 𝒮 d) (m n : ℕ) (r : S) (x : twistSectionModule 𝒮 F)
    (hr : r ∈ 𝒮 (m • d)) (hx : x ∈ moduleGrading 𝒮 F ((n * d : ℕ) : ℤ)) :
    numerSection 𝒮 F hf (m + n) (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f)) (r • x) =
      (ProjectiveSpectrum.Proj.awayToSection 𝒮 f).hom
          (HomogeneousLocalization.Away.mk 𝒮 hf m r hr) •
        numerSection 𝒮 F hf n (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f)) x := by
  obtain ⟨s, rfl⟩ := hx
  have hW : ProjectiveSpectrum.basicOpen 𝒮 f ≤ ProjectiveSpectrum.basicOpen 𝒮 f := le_rfl
  have hr' : r ∈ 𝒮 (m * d) := by simpa [smul_eq_mul] using hr
  have hjj : (m + n) * d = m * d + n * d := by ring
  have hk : ((m * d : ℕ) : ℤ) + (n : ℤ) * d = ((m + n : ℕ) : ℤ) * d := by
    push_cast
    ring
  have hc : ∀ y : ProjectiveSpectrum.basicOpen 𝒮 f,
      HomogeneousLocalization.val
        (((ProjectiveSpectrum.Proj.awayToSection 𝒮 f).hom
          (HomogeneousLocalization.Away.mk 𝒮 hf m r hr)).1 y) =
        Localization.mk r ⟨f ^ m,
          y.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hW y.2) m⟩ := fun _ => rfl
  refine (bijective_mulTrivSection 𝒮 hf ((m + n : ℕ) : ℤ) F hW).1 ?_
  rw [mulTrivSection_numerSection]
  erw [restrict_degreeComponent_smul 𝒮 F hr' hjj hk s]
  erw [← mulTrivSection_numerSection_of 𝒮 F hf n hW s]
  exact twistSheafScalarMap_mulTrivSection_smul 𝒮 hf hr' (Nat.add_comm m n) hk F hW _ hc _

/-- **The comparison map on the chart `D₊(f)`, as an additive map**: the lift of the numerator
maps to the degree-zero localization `M₍f₎`. -/
def chartLift (hf : f ∈ 𝒮 d) :
    GradedModuleDegreeZeroLocalization 𝒮 (moduleGrading 𝒮 F) f →+
      F.val.obj (op (ProjectiveSpectrum.basicOpen 𝒮 f)) :=
  Stacks.SheafOfModules.degreeZeroLocalizationLiftOfDegree 𝒮 (moduleGrading 𝒮 F) hf
    (fun n => numerSection 𝒮 F hf n (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f)))
    (fun n k x hx => numerSection_pow_smul 𝒮 F hf n k _ x hx)

/-- **The value of the chart comparison on a fraction**: the fraction `x / f ^ n` with `x` of
degree `n d` goes to the restriction of `x` divided by `f ^ n`. -/
theorem chartLift_fraction (hf : f ∈ 𝒮 d)
    (z : GradedModuleDegreeZeroLocalization 𝒮 (moduleGrading 𝒮 F) f)
    (n : ℕ) (x : twistSectionModule 𝒮 F) (hx : x ∈ moduleGrading 𝒮 F ((n * d : ℕ) : ℤ))
    (hz : (z : LocalizedModule.Away f (twistSectionModule 𝒮 F)) =
      LocalizedModule.mk (S := Submonoid.powers f) x ⟨f ^ n, by exact ⟨n, rfl⟩⟩) :
    chartLift 𝒮 F hf z =
      numerSection 𝒮 F hf n (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f)) x :=
  Stacks.SheafOfModules.degreeZeroLocalizationLiftOfDegree_fraction 𝒮 (moduleGrading 𝒮 F) hf
    _ _ z n x hx hz

/-- The chart comparison is semilinear over `A₍f₎ → Γ(D₊(f), 𝒪)`. -/
theorem chartLift_smul (hf : f ∈ 𝒮 d) (a : HomogeneousLocalization.Away 𝒮 f)
    (z : GradedModuleDegreeZeroLocalization 𝒮 (moduleGrading 𝒮 F) f) :
    chartLift 𝒮 F hf (a • z) =
      (ProjectiveSpectrum.Proj.awayToSection 𝒮 f).hom a • chartLift 𝒮 F hf z :=
  Stacks.SheafOfModules.degreeZeroLocalizationLiftOfDegree_smul 𝒮 (moduleGrading 𝒮 F) hf
    _ _ (ProjectiveSpectrum.Proj.awayToSection 𝒮 f).hom
    (fun m n r x hr hx => numerSection_smul 𝒮 F hf m n r x hr hx) a z

end Comparison


/-! ### The comparison map as a morphism of modules on the chart -/

section ChartHom

variable (F : SheafOfModules.{u} (projRingSheaf 𝒮))

/-- The chart comparison, read on the sections of `M̃` over `D₊(f)` through the standard-open
identification with `M₍f₎`. -/
def chartAddHom (hf : f ∈ 𝒮 d) (hd : 0 < d) :
    (associatedModuleSheaf 𝒮 (moduleGrading 𝒮 F)).val.obj
        (op (ProjectiveSpectrum.basicOpen 𝒮 f)) →+
      F.val.obj (op (ProjectiveSpectrum.basicOpen 𝒮 f)) :=
  (chartLift 𝒮 F hf).comp
    (associatedModuleSheafStandardOpenEquiv 𝒮 (moduleGrading 𝒮 F)
      hf hd).toLinearMap.toAddMonoidHom

/-- The chart comparison is semilinear over the comparison map `A₍f₎ → Γ(D₊(f), 𝒪)`. -/
theorem chartAddHom_smul (hf : f ∈ 𝒮 d) (hd : 0 < d) (a : HomogeneousLocalization.Away 𝒮 f)
    (z : (associatedModuleSheaf 𝒮 (moduleGrading 𝒮 F)).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒮 f))) :
    chartAddHom 𝒮 F hf hd (a • z) =
      (ProjectiveSpectrum.Proj.awayToSection 𝒮 f).hom a • chartAddHom 𝒮 F hf hd z := by
  show chartLift 𝒮 F hf
      (associatedModuleSheafStandardOpenEquiv 𝒮 (moduleGrading 𝒮 F) hf hd (a • z)) = _
  rw [map_smul]
  exact chartLift_smul 𝒮 F hf a _

/-- **The comparison map on the chart `D₊(f)`**, as a morphism of modules over
`Γ(D₊(f), 𝒪)`: the linearity is the transfer of the semilinearity above along the surjection
`A₍f₎ → Γ(D₊(f), 𝒪)`. -/
def chartHom (hf : f ∈ 𝒮 d) (hd : 0 < d) :
    (associatedModuleSheaf 𝒮 (moduleGrading 𝒮 F)).val.obj
        (op (ProjectiveSpectrum.basicOpen 𝒮 f)) ⟶
      F.val.obj (op (ProjectiveSpectrum.basicOpen 𝒮 f)) :=
  ModuleCat.ofHom (R := ((ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj
      (op (ProjectiveSpectrum.basicOpen 𝒮 f))))
    { toFun := fun z => chartAddHom 𝒮 F hf hd z
      map_add' := fun z w => map_add (chartAddHom 𝒮 F hf hd) z w
      map_smul' := fun c z => map_smul_of_semilinear
        (ProjectiveSpectrum.Proj.awayToSection 𝒮 f).hom
        (ProjectiveSpectrum.Proj.surjective_awayToSection 𝒮 hf hd) (fun _ _ => rfl)
        (chartAddHom 𝒮 F hf hd) (chartAddHom_smul 𝒮 F hf hd) c z }

/-- `chartHom 𝒮 F hf hd` agrees with `chartAddHom 𝒮 F hf hd` pointwise. -/
@[simp] theorem chartHom_apply (hf : f ∈ 𝒮 d) (hd : 0 < d)
    (z : (associatedModuleSheaf 𝒮 (moduleGrading 𝒮 F)).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒮 f))) :
    chartHom 𝒮 F hf hd z = chartAddHom 𝒮 F hf hd z := rfl

/-- A sheaf of modules has only the zero section over an empty open: the sheaf condition for the
empty covering makes that module of sections a terminal, hence zero, abelian group. -/
private theorem eq_zero_of_isTerminal {B : AddCommGrpCat.{u}} (h : Limits.IsTerminal B)
    (x : ToType B) : x = 0 := by
  have hid : (𝟙 B) = 0 := h.hom_ext _ _
  have h2 := ConcreteCategory.congr_hom hid x
  simp only [ConcreteCategory.id_apply] at h2
  rw [h2]
  simp

/-- **A sheaf of modules on `Proj 𝒮` has a single section over an empty open.** -/
theorem subsingleton_sections_of_eq_bot {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W = ⊥) :
    Subsingleton (F.val.obj (op W)) := by
  have hterm : Limits.IsTerminal
      (((SheafOfModules.toSheaf (projRingSheaf 𝒮)).obj F).obj.obj (op W)) :=
    TopCat.Sheaf.isTerminalOfEqEmpty _ hW
  exact ⟨fun a b => (eq_zero_of_isTerminal hterm a).trans
    (eq_zero_of_isTerminal hterm b).symm⟩

/-- **The chart comparison does not depend on the degree in which `f` is homogeneous.** A nonzero
`f` is homogeneous in one degree only, so the two witnesses are the same and the two maps are the
same by proof irrelevance; and `D₊(0)` is empty, so for `f = 0` the two maps are maps into a
module with a single element.

This is what lets a formula proved for `chartHom 𝒮 F hf hd` at a given degree witness be read
off the comparison map attached to a positive-degree element, whose witness is chosen by
`Exists.choose`. -/
theorem chartHom_congr {d' : ℕ} (hf : f ∈ 𝒮 d) (hd : 0 < d) (hf' : f ∈ 𝒮 d') (hd' : 0 < d') :
    chartHom 𝒮 F hf hd = chartHom 𝒮 F hf' hd' := by
  by_cases h0 : f = 0
  · subst h0
    have hbot : ProjectiveSpectrum.basicOpen 𝒮 (0 : S) = ⊥ := by simp
    have hsub := subsingleton_sections_of_eq_bot 𝒮 F hbot
    exact ModuleCat.hom_ext (LinearMap.ext fun z => Subsingleton.elim _ _)
  · have hdd : d = d' := DirectSum.degree_eq_of_mem_mem 𝒮 hf hf' h0
    subst hdd
    rfl

/-- **The fraction-wise formula for the comparison map on a chart.** If the section `z` of `M̃`
over `D₊(f)` is the fraction `x / f ^ n` with `x` homogeneous of degree `n d`, then the image of
`z` is the section of `ℱ` whose product with the trivializing section `f ^ n` is the restriction
of the degree-`n d` component of `x`. By
`Stacks.AlgebraicGeometry.ProjTwistRestriction.bijective_mulTrivSection` that pins the image
down. -/
theorem mulTrivSection_chartHom (hf : f ∈ 𝒮 d) (hd : 0 < d)
    (z : (associatedModuleSheaf 𝒮 (moduleGrading 𝒮 F)).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒮 f)))
    (n : ℕ) (x : twistSectionModule 𝒮 F) (hx : x ∈ moduleGrading 𝒮 F ((n * d : ℕ) : ℤ))
    (hz : ((associatedModuleSheafStandardOpenEquiv 𝒮 (moduleGrading 𝒮 F) hf hd z :
        GradedModuleDegreeZeroLocalization 𝒮 (moduleGrading 𝒮 F) f) :
        LocalizedModule.Away f (twistSectionModule 𝒮 F)) =
      LocalizedModule.mk (S := Submonoid.powers f) x ⟨f ^ n, by exact ⟨n, rfl⟩⟩) :
    mulTrivSection 𝒮 hf (n : ℤ) F
          (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f)) (chartHom 𝒮 F hf hd z) =
      (twistSheafOfModules 𝒮 F ((n : ℤ) * d)).val.map
        (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒮 f ≤ ⊤)).op
        (degreeComponent 𝒮 F (n * d) x) := by
  refine Eq.trans (congrArg (mulTrivSection 𝒮 hf (n : ℤ) F
    (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f)))
    ((chartHom_apply 𝒮 F hf hd z).trans (chartLift_fraction 𝒮 F hf _ n x hx hz))) ?_
  exact mulTrivSection_numerSection 𝒮 F hf n _ x

/-- Every section of `M̃` over `D₊(f)` is a fraction `x / f ^ n` with `x` homogeneous of degree
`n d`. -/
theorem exists_fraction (hf : f ∈ 𝒮 d) (hd : 0 < d)
    (z : (associatedModuleSheaf 𝒮 (moduleGrading 𝒮 F)).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒮 f))) :
    ∃ (n : ℕ) (x : twistSectionModule 𝒮 F), x ∈ moduleGrading 𝒮 F ((n * d : ℕ) : ℤ) ∧
      ((associatedModuleSheafStandardOpenEquiv 𝒮 (moduleGrading 𝒮 F) hf hd z :
          GradedModuleDegreeZeroLocalization 𝒮 (moduleGrading 𝒮 F) f) :
          LocalizedModule.Away f (twistSectionModule 𝒮 F)) =
        LocalizedModule.mk (S := Submonoid.powers f) x ⟨f ^ n, by exact ⟨n, rfl⟩⟩ :=
  Stacks.SheafOfModules.degreeZeroLocalization_exists_fraction_of_degree 𝒮
    (moduleGrading 𝒮 F) hf _

/-- **The chart comparison is bijective exactly when its lift out of the degree-zero localization
is.** The two differ by the standard-open identification of the sections of `M̃` over `D₊(f)` with
`M₍f₎`, which is an isomorphism, so the hypothesis `hloc` of
`Stacks.AlgebraicGeometry.ProjTwistLocalComparison.isIso_comparison_of_bijective_chartHom` is a
statement about `chartLift` alone. -/
theorem bijective_chartHom_iff_bijective_chartLift (hf : f ∈ 𝒮 d) (hd : 0 < d) :
    Function.Bijective (chartHom 𝒮 F hf hd).hom ↔
      Function.Bijective (chartLift 𝒮 F hf) :=
  Equiv.bijective_comp
    (associatedModuleSheafStandardOpenEquiv 𝒮 (moduleGrading 𝒮 F) hf hd).toEquiv
    (chartLift 𝒮 F hf)

/-- **The chart comparison is bijective as soon as the graded module of twisted global sections
is compared degreewise with another graded module whose own fraction map to `Γ(D₊(f), ℱ)` is
bijective.**

The data is that of
`Stacks.SheafOfModules.bijective_degreeZeroLocalizationLiftOfDegree_of_degreewise`: a second
graded ring `A'` with a homogeneous element `f'` of degree `d'`, a graded `A'`-module `B'`, an
additive map `g` out of its degree-zero localization at `f'` which is bijective and whose value
on the fraction `x' / f' ^ n` is `e' n x'`, and a family `ψ` whose `n`-th member carries a twisted
global section of degree `n · d` to a numerator of degree `n · d'`, bijectively,
compatibly with multiplication by `f` and `f'`, and carrying `e' n ∘ ψ` to the numerator map
`numerSection` — that is, "divide by the trivializing section `f ^ n`" on this side agrees with
`e' n` on the other.

**No comparison of the graded rings is asked for.** With the data below supplied for every
positive-degree homogeneous element, `hloc` holds and
`Stacks.AlgebraicGeometry.ProjTwistLocalComparison.isIso_comparison_of_bijective_chartHom`
applies. This is **not** the route by which Tag 03GM's second assertion is proved — that is
`Stacks.AlgebraicGeometry.ProjTwistChartBijective.bijective_chartHom_of_cover`, which argues in
the 03GM spelling and needs no second graded module. The statement is kept because it is the
route to the *same* local bijectivity out of part (2) of [Stacks, Tag 01PW], and so remains the
cheapest way to reach a chart bijectivity statement for an invertible module other than a twist
of `Proj`. It is applied nowhere in the tree. -/
theorem bijective_chartHom_of_degreewise {R' M' σ' τ' : Type*}
    [CommRing R'] [AddCommGroup M'] [Module R' M']
    [SetLike σ' R'] [AddSubgroupClass σ' R'] (A' : ℕ → σ') [GradedRing A']
    [SetLike τ' M'] [AddSubgroupClass τ' M'] (B' : ℤ → τ') [DirectSum.Decomposition B']
    [SetLike.GradedSMul A' B'] (hf : f ∈ 𝒮 d) (hd : 0 < d) {f' : R'} {d' : ℕ}
    (hf' : f' ∈ A' d')
    (e' : ℕ → M' →+ F.val.obj (op (ProjectiveSpectrum.basicOpen 𝒮 f)))
    (g : GradedModuleDegreeZeroLocalization A' B' f' →+
      F.val.obj (op (ProjectiveSpectrum.basicOpen 𝒮 f)))
    (hg : ∀ (z' : GradedModuleDegreeZeroLocalization A' B' f') (n : ℕ) (x' : M'),
      x' ∈ B' ((n * d' : ℕ) : ℤ) →
      (z' : LocalizedModule.Away f' M') =
        LocalizedModule.mk (S := Submonoid.powers f') x' ⟨f' ^ n, by exact ⟨n, rfl⟩⟩ →
      g z' = e' n x')
    (hgbij : Function.Bijective g) (ψ : ℕ → twistSectionModule 𝒮 F →+ M')
    (hψmem : ∀ (n : ℕ) (x : twistSectionModule 𝒮 F),
      x ∈ moduleGrading 𝒮 F ((n * d : ℕ) : ℤ) → ψ n x ∈ B' ((n * d' : ℕ) : ℤ))
    (hψpow : ∀ (n k : ℕ) (x : twistSectionModule 𝒮 F),
      x ∈ moduleGrading 𝒮 F ((n * d : ℕ) : ℤ) → ψ (n + k) (f ^ k • x) = f' ^ k • ψ n x)
    (hψsurj : ∀ (n : ℕ) (x' : M'), x' ∈ B' ((n * d' : ℕ) : ℤ) →
      ∃ x : twistSectionModule 𝒮 F, x ∈ moduleGrading 𝒮 F ((n * d : ℕ) : ℤ) ∧ ψ n x = x')
    (hψinj : ∀ (n : ℕ) (x : twistSectionModule 𝒮 F),
      x ∈ moduleGrading 𝒮 F ((n * d : ℕ) : ℤ) → ψ n x = 0 → x = 0)
    (hcomm : ∀ (n : ℕ) (x : twistSectionModule 𝒮 F),
      x ∈ moduleGrading 𝒮 F ((n * d : ℕ) : ℤ) →
      e' n (ψ n x) =
        numerSection 𝒮 F hf n (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f)) x) :
    Function.Bijective (chartHom 𝒮 F hf hd).hom :=
  (bijective_chartHom_iff_bijective_chartLift 𝒮 F hf hd).mpr
    (Stacks.SheafOfModules.bijective_degreeZeroLocalizationLiftOfDegree_of_degreewise
      𝒮 (moduleGrading 𝒮 F) hf A' B' hf' _ _ e' g hg hgbij ψ hψmem hψpow hψsurj hψinj hcomm)

end ChartHom


/-! ### Restriction of a fraction section to a smaller standard open -/

section Restriction

variable {M : Type u} {τ : Type*} [AddCommGroup M] [Module S M]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

/-- **Restricting a fraction section rewrites the fraction.** If `g ^ m = f ^ n c`, the section
of `M̃` over `D₊(f)` given by the fraction `x / f ^ n` restricts, on `D₊(g) ⊆ D₊(f)`, to the
section given by `c x / g ^ m`: the two fractions agree in every fibre, because the denominators
differ by exactly `c`. -/
theorem restrict_degreeZeroToSection_mk {g : S} (hfg : ProjectiveSpectrum.basicOpen 𝒮 g ≤
      ProjectiveSpectrum.basicOpen 𝒮 f)
    {m n : ℕ} {c : S} (hgm : g ^ m = f ^ n * c) {x : M}
    (A : GradedModuleDegreeZeroLocalization 𝒮 𝒨 f)
    (A' : GradedModuleDegreeZeroLocalization 𝒮 𝒨 g)
    (hA : (A : LocalizedModule.Away f M) =
      LocalizedModule.mk (S := Submonoid.powers f) x ⟨f ^ n, by exact ⟨n, rfl⟩⟩)
    (hA' : (A' : LocalizedModule.Away g M) =
      LocalizedModule.mk (S := Submonoid.powers g) (c • x) ⟨g ^ m, by exact ⟨m, rfl⟩⟩) :
    (associatedModuleSheaf 𝒮 𝒨).val.map (homOfLE hfg).op
        (degreeZeroToSection 𝒮 𝒨 f A) =
      degreeZeroToSection 𝒮 𝒨 g A' := by
  apply Subtype.ext
  funext y
  show moduleToFiber 𝒮 f ⟨y.1, hfg y.2⟩ A.1 = moduleToFiber 𝒮 g y A'.1
  rw [hA, hA', moduleToFiber_mk, moduleToFiber_mk]
  refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
  show (1 : S) • (g ^ m : S) • x = (1 : S) • (f ^ n : S) • (c • x)
  rw [one_smul, one_smul, hgm, mul_smul]

/-- The standard-open identification of the restriction of a fraction section. -/
theorem standardOpenEquiv_restrict_mk {g : S} {e : ℕ} (hf : f ∈ 𝒮 d) (hd : 0 < d)
    (hg : g ∈ 𝒮 e) (he : 0 < e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒮 g ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    {m n : ℕ} {c : S} (hgm : g ^ m = f ^ n * c) {x : M}
    (z : (associatedModuleSheaf 𝒮 𝒨).val.obj (op (ProjectiveSpectrum.basicOpen 𝒮 f)))
    (A' : GradedModuleDegreeZeroLocalization 𝒮 𝒨 g)
    (hz : ((associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf hd z :
        GradedModuleDegreeZeroLocalization 𝒮 𝒨 f) : LocalizedModule.Away f M) =
      LocalizedModule.mk (S := Submonoid.powers f) x ⟨f ^ n, by exact ⟨n, rfl⟩⟩)
    (hA' : (A' : LocalizedModule.Away g M) =
      LocalizedModule.mk (S := Submonoid.powers g) (c • x) ⟨g ^ m, by exact ⟨m, rfl⟩⟩) :
    associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hg he
        ((associatedModuleSheaf 𝒮 𝒨).val.map (homOfLE hfg).op z) = A' := by
  have hzz : degreeZeroToSection 𝒮 𝒨 f
      (associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf hd z) = z :=
    (associatedModuleSheafStandardOpenEquiv_symm_apply 𝒮 𝒨 hf hd _).symm.trans
      ((associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf hd).symm_apply_apply z)
  rw [← hzz, restrict_degreeZeroToSection_mk 𝒮 𝒨 hfg hgm _ A' hz hA',
    associatedModuleSheafStandardOpenEquiv_degreeZeroToSection]

end Restriction


/-! ### Compatibility of the chart comparisons with restriction -/

section Compatibility

variable (F : SheafOfModules.{u} (projRingSheaf 𝒮))

/-- Two successive restrictions of a section of a twist are the restriction along the
composite.

Not `private`: `Stacks.AlgebraicGeometry.ProjTwistIntegerComparison` needs it for the
integer-graded comparison, and it says nothing about the graded module, so it is shared rather
than cloned. -/
theorem map_map {k : ℤ} {U V W : Opens (ProjectiveSpectrum.top 𝒮)} (hVU : V ≤ U)
    (hWV : W ≤ V) (u : (twistSheafOfModules 𝒮 F k).val.obj (op U)) :
    (twistSheafOfModules 𝒮 F k).val.map (homOfLE hWV).op
        ((twistSheafOfModules 𝒮 F k).val.map (homOfLE hVU).op u) =
      (twistSheafOfModules 𝒮 F k).val.map (homOfLE (hWV.trans hVU)).op u :=
  (CategoryTheory.congr_fun ((twistSheafOfModules 𝒮 F k).val.map_comp
    (homOfLE hVU).op (homOfLE hWV).op) u).symm

/-- The arithmetic behind rewriting a fraction with denominator a power of `f` as one with
denominator a power of `g`: from `g ^ b = c f` with `c` homogeneous of degree `b e - d` one gets
`g ^ (n b) = f ^ n c ^ n` with `c ^ n` homogeneous of degree `n (b e - d)`, and the degrees add
up to `n b e`. -/
private theorem pow_degree_data {g : S} {e b : ℕ} (hf : f ∈ 𝒮 d) (hg : g ∈ 𝒮 e)
    (hdbe : d ≤ b * e) {c : S} (hcmem : c ∈ 𝒮 (b * e - d)) (hgb : g ^ b = c * f) (n : ℕ) :
    c ^ n ∈ 𝒮 (n * (b * e - d)) ∧ g ^ (n * b) = f ^ n * c ^ n ∧
      n * b * e = n * (b * e - d) + n * d ∧
      ((n * (b * e - d) : ℕ) : ℤ) + (n : ℤ) * (d : ℤ) = ((n * b : ℕ) : ℤ) * (e : ℤ) := by
  have h1 : b * e - d + d = b * e := Nat.sub_add_cancel hdbe
  have h2 : n * (b * e - d) + n * d = n * b * e := by
    calc n * (b * e - d) + n * d = n * (b * e - d + d) := by ring
      _ = n * (b * e) := by rw [h1]
      _ = n * b * e := by ring
  refine ⟨by simpa [smul_eq_mul] using SetLike.pow_mem_graded n hcmem, ?_, h2.symm, ?_⟩
  · rw [mul_comm n b, pow_mul, hgb, mul_pow, mul_comm]
  · have h3 := congrArg (fun k : ℕ => (k : ℤ)) h2
    push_cast at h3
    push_cast
    linarith

/-- The data rewriting a fraction with denominator `f ^ n` as one with denominator a power of
`g`, for `D₊(g) ⊆ D₊(f)`.

Not `private`: `Stacks.AlgebraicGeometry.ProjTwistIntegerComparison` needs it for the
integer-graded comparison, and it is pure arithmetic of the graded ring, so it is shared rather
than cloned. -/
theorem exists_rewrite_data {g : S} {e : ℕ} (hf : f ∈ 𝒮 d) (hd : 0 < d)
    (hg : g ∈ 𝒮 e) (he : 0 < e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒮 g ≤ ProjectiveSpectrum.basicOpen 𝒮 f) (n : ℕ) :
    ∃ (b : ℕ) (c : S), c ^ n ∈ 𝒮 (n * (b * e - d)) ∧ g ^ (n * b) = f ^ n * c ^ n ∧
      n * b * e = n * (b * e - d) + n * d ∧
      ((n * (b * e - d) : ℕ) : ℤ) + (n : ℤ) * (d : ℤ) = ((n * b : ℕ) : ℤ) * (e : ℤ) := by
  obtain ⟨b, _, hdbe, c, hcmem, hgb⟩ :=
    ProjectiveSpectrum.exists_pow_eq_mul_of_basicOpen_le_degree 𝒮 hf hd hg he hfg
  exact ⟨b, c, pow_degree_data 𝒮 hf hg hdbe hcmem hgb n⟩

/-- The chart comparisons agree on an overlap, with the rewritten fraction supplied. -/
private theorem chartHom_restrict_aux {g : S} {e : ℕ} (hf : f ∈ 𝒮 d) (hd : 0 < d)
    (hg : g ∈ 𝒮 e) (he : 0 < e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒮 g ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (z : (associatedModuleSheaf 𝒮 (moduleGrading 𝒮 F)).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒮 f)))
    (n b : ℕ) {c : S} (hc : c ^ n ∈ 𝒮 (n * (b * e - d)))
    (hgm : g ^ (n * b) = f ^ n * c ^ n)
    (hj : n * b * e = n * (b * e - d) + n * d)
    (hdeg : ((n * (b * e - d) : ℕ) : ℤ) + (n : ℤ) * (d : ℤ) = ((n * b : ℕ) : ℤ) * (e : ℤ))
    (s : twistSections 𝒮 F (n * d))
    (hz : ((associatedModuleSheafStandardOpenEquiv 𝒮 (moduleGrading 𝒮 F) hf hd z :
        GradedModuleDegreeZeroLocalization 𝒮 (moduleGrading 𝒮 F) f) :
        LocalizedModule.Away f (twistSectionModule 𝒮 F)) =
      LocalizedModule.mk (S := Submonoid.powers f)
        (DirectSum.of (twistSections 𝒮 F) (n * d) s) ⟨f ^ n, by exact ⟨n, rfl⟩⟩) :
    chartHom 𝒮 F hg he
        ((associatedModuleSheaf 𝒮 (moduleGrading 𝒮 F)).val.map (homOfLE hfg).op z) =
      (F.val.map (homOfLE hfg).op).hom (chartHom 𝒮 F hf hd z) := by
  have hxs : DirectSum.of (twistSections 𝒮 F) (n * d) s ∈
      moduleGrading 𝒮 F ((n * d : ℕ) : ℤ) := ⟨s, rfl⟩
  have hcx : c ^ n • DirectSum.of (twistSections 𝒮 F) (n * d) s ∈
      moduleGrading 𝒮 F ((n * b * e : ℕ) : ℤ) :=
    ⟨gsmul 𝒮 F hc (n * d) (n * b * e) hj s, (smul_of' 𝒮 F hc hj s).symm⟩
  have hz' : associatedModuleSheafStandardOpenEquiv 𝒮 (moduleGrading 𝒮 F) hg he
      ((associatedModuleSheaf 𝒮 (moduleGrading 𝒮 F)).val.map (homOfLE hfg).op z) =
      ⟨LocalizedModule.mk (S := Submonoid.powers g)
          (c ^ n • DirectSum.of (twistSections 𝒮 F) (n * d) s)
          ⟨g ^ (n * b), by exact ⟨n * b, rfl⟩⟩,
        Stacks.SheafOfModules.mk_mem_degreeZeroLocalization_of_degree 𝒮
          (moduleGrading 𝒮 F) hg (n * b) _ hcx⟩ :=
    standardOpenEquiv_restrict_mk 𝒮 (moduleGrading 𝒮 F) hf hd hg he hfg hgm z _ hz rfl
  refine (bijective_mulTrivSection 𝒮 hg ((n * b : ℕ) : ℤ) F
    (le_refl (ProjectiveSpectrum.basicOpen 𝒮 g))).1 ?_
  refine Eq.trans ((mulTrivSection_chartHom 𝒮 F hg he _ (n * b) _ hcx (by rw [hz'])).trans
    (restrict_degreeComponent_smul 𝒮 F hc hj hdeg s
      (W := ProjectiveSpectrum.basicOpen 𝒮 g))) ?_
  refine Eq.trans ?_ (twistSheafScalarMap_mulTrivSection 𝒮 hf hg hc n (n * b) hgm hdeg F hfg
    (le_refl (ProjectiveSpectrum.basicOpen 𝒮 g)) _)
  refine congrArg (fun y =>
    (twistSheafScalarMap 𝒮 F (n * (b * e - d)) ((n : ℤ) * d) (((n * b : ℕ) : ℤ) * e) hdeg
      ⟨c ^ n, hc⟩).val.app (op (ProjectiveSpectrum.basicOpen 𝒮 g)) y) ?_
  refine Eq.trans ?_ (mulTrivSection_restrict 𝒮 F hf (n : ℤ)
    (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f)) hfg (chartHom 𝒮 F hf hd z))
  refine Eq.trans ?_ (congrArg ((twistSheafOfModules 𝒮 F ((n : ℤ) * d)).val.map
    (homOfLE hfg).op) (mulTrivSection_chartHom 𝒮 F hf hd z n _ hxs hz).symm)
  refine Eq.trans ?_ (map_map 𝒮 F (le_top : ProjectiveSpectrum.basicOpen 𝒮 f ≤ ⊤) hfg _).symm
  exact congrArg ((twistSheafOfModules 𝒮 F ((n : ℤ) * d)).val.map
    (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒮 g ≤ ⊤)).op)
    (degreeComponent_of 𝒮 F (n * d) s).symm

/-- The chart comparisons agree on an overlap, for a section given as a fraction. -/
private theorem chartHom_restrict_of_fraction {g : S} {e : ℕ} (hf : f ∈ 𝒮 d) (hd : 0 < d)
    (hg : g ∈ 𝒮 e) (he : 0 < e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒮 g ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (z : (associatedModuleSheaf 𝒮 (moduleGrading 𝒮 F)).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒮 f)))
    (n : ℕ) (s : twistSections 𝒮 F (n * d))
    (hz : ((associatedModuleSheafStandardOpenEquiv 𝒮 (moduleGrading 𝒮 F) hf hd z :
        GradedModuleDegreeZeroLocalization 𝒮 (moduleGrading 𝒮 F) f) :
        LocalizedModule.Away f (twistSectionModule 𝒮 F)) =
      LocalizedModule.mk (S := Submonoid.powers f)
        (DirectSum.of (twistSections 𝒮 F) (n * d) s) ⟨f ^ n, by exact ⟨n, rfl⟩⟩) :
    chartHom 𝒮 F hg he
        ((associatedModuleSheaf 𝒮 (moduleGrading 𝒮 F)).val.map (homOfLE hfg).op z) =
      (F.val.map (homOfLE hfg).op).hom (chartHom 𝒮 F hf hd z) := by
  obtain ⟨b, c, hc, hgm, hj, hdeg⟩ := exists_rewrite_data 𝒮 hf hd hg he hfg n
  exact chartHom_restrict_aux 𝒮 F hf hd hg he hfg z n b hc hgm hj hdeg s hz

/-- **The chart comparisons agree on overlaps.** For `D₊(g) ⊆ D₊(f)` with `f` and `g`
homogeneous of positive degrees, the comparison attached to `g` applied to the restriction of a
section of `M̃` is the restriction of the comparison attached to `f`. This is the compatibility
with restriction that glues the chart comparisons into one morphism `M̃ ⟶ ℱ`.

The fraction `x / f ^ n` representing the section is rewritten with denominator a power of `g`
by `ProjectiveSpectrum.exists_pow_eq_mul_of_basicOpen_le_degree`: `g ^ b = c f` with `c`
homogeneous, hence `g ^ (n b) = c ^ n f ^ n`, and both sides are then multiplication by `c ^ n`
applied to the restriction of `x`. -/
theorem chartHom_restrict {g : S} {e : ℕ} (hf : f ∈ 𝒮 d) (hd : 0 < d) (hg : g ∈ 𝒮 e)
    (he : 0 < e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒮 g ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (z : (associatedModuleSheaf 𝒮 (moduleGrading 𝒮 F)).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒮 f))) :
    chartHom 𝒮 F hg he
        ((associatedModuleSheaf 𝒮 (moduleGrading 𝒮 F)).val.map (homOfLE hfg).op z) =
      (F.val.map (homOfLE hfg).op).hom (chartHom 𝒮 F hf hd z) := by
  obtain ⟨n, x, hx, hz⟩ := exists_fraction 𝒮 F hf hd z
  obtain ⟨s, rfl⟩ := hx
  exact chartHom_restrict_of_fraction 𝒮 F hf hd hg he hfg z n s hz

end Compatibility


/-! ### The glued comparison morphism -/

section Glued

open Stacks.AlgebraicGeometry.ProjTwistComparison (PositiveElem positiveBasicOpen
  StandardOpenHomData homOfStandardOpenHomData homOfStandardOpenHomData_app
  eq_homOfStandardOpenHomData isBasis_positiveBasicOpen)

variable (F : SheafOfModules.{u} (projRingSheaf 𝒮))

/-- The comparison map on the standard open of a positive-degree homogeneous element: the chart
comparison for a degree witnessing that the element is homogeneous of positive degree. -/
def positiveChartHom (p : PositiveElem 𝒮) :
    (associatedTwistSectionSheaf 𝒮 F).val.obj (op (positiveBasicOpen 𝒮 p)) ⟶
      F.val.obj (op (positiveBasicOpen 𝒮 p)) :=
  chartHom 𝒮 F p.2.choose_spec.2 p.2.choose_spec.1

/-- The comparison maps on the positive-degree standard opens are compatible with
restriction. -/
theorem positiveChartHom_restrict (p q : PositiveElem 𝒮)
    (h : positiveBasicOpen 𝒮 q ≤ positiveBasicOpen 𝒮 p)
    (z : (associatedTwistSectionSheaf 𝒮 F).val.obj (op (positiveBasicOpen 𝒮 p))) :
    positiveChartHom 𝒮 F q
        ((associatedTwistSectionSheaf 𝒮 F).val.map (homOfLE h).op z) =
      F.val.map (homOfLE h).op (positiveChartHom 𝒮 F p z) :=
  chartHom_restrict 𝒮 F p.2.choose_spec.2 p.2.choose_spec.1 q.2.choose_spec.2
    q.2.choose_spec.1 h z

/-- The local datum the chart comparisons form. -/
def standardOpenHomData : StandardOpenHomData 𝒮 (moduleGrading 𝒮 F) F where
  app := positiveChartHom 𝒮 F
  app_restrict := positiveChartHom_restrict 𝒮 F

/-- **The comparison morphism `M̃ ⟶ ℱ`** of Tag 03GM (2), glued from the chart comparisons.

This is the morphism alone. Tag 03GM's second assertion is that it is an isomorphism for `ℱ`
quasi-coherent on `ℙᵐ_R`, which is the local bijectivity of each `positiveChartHom`; that is the
source's omitted injectivity and surjectivity argument, and it is proved in
`StacksFrontier/AlgebraicGeometry/TensorSectionNonvanishing/ProjTwistChartBijective.lean`. No
`stacks` attribute is attached here because a morphism is not the tag; the whole tag is carried
by `Stacks.AlgebraicGeometry.ProjTwistComparisonIso.gradedModule_and_isIso_comparison`. -/
def comparison : associatedTwistSectionSheaf 𝒮 F ⟶ F :=
  homOfStandardOpenHomData 𝒮 (moduleGrading 𝒮 F) F (standardOpenHomData 𝒮 F)

/-- The comparison morphism restricts on each positive-degree standard open to the chart
comparison. -/
theorem comparison_app (p : PositiveElem 𝒮) :
    (comparison 𝒮 F).val.app (op (positiveBasicOpen 𝒮 p)) = positiveChartHom 𝒮 F p :=
  homOfStandardOpenHomData_app 𝒮 (moduleGrading 𝒮 F) F (standardOpenHomData 𝒮 F) p

/-- **The comparison morphism is the only one restricting to the chart comparisons.** -/
theorem existsUnique_comparison :
    ∃! φ : associatedTwistSectionSheaf 𝒮 F ⟶ F,
      ∀ p : PositiveElem 𝒮,
        φ.val.app (op (positiveBasicOpen 𝒮 p)) = positiveChartHom 𝒮 F p :=
  ⟨comparison 𝒮 F, comparison_app 𝒮 F,
    fun φ hφ => eq_homOfStandardOpenHomData 𝒮 (moduleGrading 𝒮 F) F
      (standardOpenHomData 𝒮 F) φ hφ⟩

/-- The comparison map attached to a positive-degree homogeneous element is the chart comparison
for the degree chosen by the construction. -/
theorem positiveChartHom_eq (p : PositiveElem 𝒮) :
    positiveChartHom 𝒮 F p = chartHom 𝒮 F p.2.choose_spec.2 p.2.choose_spec.1 := rfl

/-- The comparison morphism restricted to the standard open of a homogeneous element of positive
degree. The fraction-wise formula for the right-hand side is
`Stacks.AlgebraicGeometry.ProjTwistLocalComparison.mulTrivSection_chartHom`; it is stated at the
degree the construction chooses, which for a nonzero `f` is the only degree in which `f` is
homogeneous. -/
theorem comparison_app_basicOpen (hf : f ∈ 𝒮 d) (hd : 0 < d) :
    (comparison 𝒮 F).val.app (op (ProjectiveSpectrum.basicOpen 𝒮 f)) =
      positiveChartHom 𝒮 F ⟨f, ⟨d, hd, hf⟩⟩ :=
  comparison_app 𝒮 F ⟨f, ⟨d, hd, hf⟩⟩

/-- **The comparison morphism is an isomorphism as soon as every chart comparison is bijective
on sections.** The local bijectivity `hloc` is the source's omitted injectivity and surjectivity
argument, proved in
`StacksFrontier/AlgebraicGeometry/TensorSectionNonvanishing/ProjTwistChartBijective.lean`, and the
passage from it to invertibility of `M̃ ⟶ ℱ` is the globalization step
`Stacks.AlgebraicGeometry.ProjQuasiCoherentRecovery.isIso_of_bijective_app_onBasis`. -/
theorem isIso_comparison
    (hloc : ∀ p : PositiveElem 𝒮, Function.Bijective (positiveChartHom 𝒮 F p).hom) :
    IsIso (comparison 𝒮 F) := by
  refine Stacks.AlgebraicGeometry.ProjQuasiCoherentRecovery.isIso_of_bijective_app_onBasis
    (associatedTwistSectionSheaf 𝒮 F) F (positiveBasicOpen 𝒮)
    (isBasis_positiveBasicOpen 𝒮) (comparison 𝒮 F) fun p => ?_
  rw [comparison_app 𝒮 F p]
  exact hloc p

/-- **The comparison map attached to a positive-degree element is the chart comparison for any
degree in which the element is homogeneous**, not only for the degree `Exists.choose` picks out
of its positivity witness. -/
theorem positiveChartHom_eq_chartHom (p : PositiveElem 𝒮) (hf : (p.1 : S) ∈ 𝒮 d) (hd : 0 < d) :
    positiveChartHom 𝒮 F p = chartHom 𝒮 F hf hd :=
  chartHom_congr 𝒮 F p.2.choose_spec.2 p.2.choose_spec.1 hf hd

/-- Bijectivity of the comparison map attached to a positive-degree element follows from
bijectivity of the chart comparison at any degree in which the element is homogeneous. -/
theorem bijective_positiveChartHom (p : PositiveElem 𝒮) (hf : (p.1 : S) ∈ 𝒮 d) (hd : 0 < d)
    (h : Function.Bijective (chartHom 𝒮 F hf hd).hom) :
    Function.Bijective (positiveChartHom 𝒮 F p).hom := by
  rw [positiveChartHom_eq_chartHom 𝒮 F p hf hd]
  exact h

/-- **The glued morphism is an isomorphism as soon as the chart comparison of every
positive-degree homogeneous element is bijective on sections**, the hypothesis stated with the
degree given rather than chosen. This is the form in which Tag 03GM's second assertion is
supplied by
`Stacks.AlgebraicGeometry.ProjTwistChartBijective.isIso_comparison_of_degreeOneCover`: a proof of
local bijectivity works with a homogeneous element together with its degree, which
`Stacks.AlgebraicGeometry.ProjTwistLocalComparison.isIso_comparison` does not accept. -/
theorem isIso_comparison_of_bijective_chartHom
    (hloc : ∀ {g : S} {e : ℕ} (hg : g ∈ 𝒮 e) (he : 0 < e),
      Function.Bijective (chartHom 𝒮 F hg he).hom) :
    IsIso (comparison 𝒮 F) :=
  isIso_comparison 𝒮 F fun p =>
    bijective_positiveChartHom 𝒮 F p p.2.choose_spec.2 p.2.choose_spec.1
      (hloc p.2.choose_spec.2 p.2.choose_spec.1)

end Glued

end Stacks.AlgebraicGeometry.ProjTwistLocalComparison

end
