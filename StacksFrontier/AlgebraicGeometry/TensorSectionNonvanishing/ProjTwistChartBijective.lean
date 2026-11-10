module

public import StacksFrontier.AlgebraicGeometry.ModuleSectionExtension.Localization
public import StacksFrontier.AlgebraicGeometry.TensorSectionNonvanishing.ProjTwistChartTrivializationCompare
public import StacksFrontier.AlgebraicGeometry.VeryAmpleAffineBase.ChartBasicOpen

/-!
# The chart comparison of Tag 03GM is bijective

Let `S = ⨁_{k ≥ 0} 𝒮 k` be a graded ring, `X = Proj 𝒮`, let `ℱ` be a **quasi-coherent** sheaf of
`𝒪_X`-modules and let `M = ⨁_{m ≥ 0} Γ(X, ℱ(m))` be the graded `S`-module of twisted global
sections. For `f ∈ 𝒮 d` homogeneous of positive degree,
`Stacks.AlgebraicGeometry.ProjTwistLocalComparison.chartHom` is the comparison map
`Γ(D₊(f), M̃) → Γ(D₊(f), ℱ)`, which sends the degree-zero fraction `x / f ^ n` to the section
whose product with the trivializing section `f ^ n` is `x|_{D₊(f)}`.

This file proves that map **bijective**, given a finite family `g : ι → S` of homogeneous
elements *of the same degree `d` as `f`* whose standard opens cover `X`. That is the injectivity
and surjectivity argument the source of [Stacks, Tag 03GM] omits, and it is the hypothesis `hloc`
of `Stacks.AlgebraicGeometry.ProjTwistLocalComparison.isIso_comparison_of_bijective_chartHom`.

## The two halves

Everything happens on the charts `D₊(g i)`, which are affine
(`AlgebraicGeometry.Proj.isAffineOpen_basicOpen`), and the open cut out of `D₊(g i)` by `f` is
the nonvanishing locus of the degree-zero fraction `f / g i`
(`Stacks.ProjChartBasicOpen.basicOpen_awayToSection_mk`), so the affine statements about a
quasi-coherent sheaf over a basic open --
`Stacks.ModuleSectionExtension.exists_pow_smul_eq_zero`, `exists_pow_smul_eq_res` and
`exists_pow_smul_eq_of_res_eq` -- apply directly. Equal degrees is what lets the trivialization
by `f ^ n` and the trivialization by `g i ^ n` be compared, by
`Stacks.AlgebraicGeometry.ProjTwistRestriction.mulTrivSection_eq_pow_smul`.

* **Injectivity.** If the numerator of `x` on `D₊(f)` vanishes then, on each chart, the numerator
  of `x` is killed by a power of `f / g i`; a uniform exponent `k` exists because `ι` is finite,
  and then `f ^ k · x` restricts to zero on every chart, hence vanishes.
* **Surjectivity.** A section `t` over `D₊(f)` becomes, on each chart, the restriction of a
  section `a i` after multiplication by `f / g i` to a uniform power `N`. The `a i` need not
  agree on the overlaps, but their difference vanishes on the part of the overlap where `f` does
  not vanish, so one further uniform power `k` of `f / g i` makes them agree. The resulting
  sections of `ℱ((N + k)d)` glue, and the glued twisted global section has numerator `t`.

## Main results

* `exists_pow_smul_eq_zero_of_numerSection_eq_zero`: **the injectivity half.**
* `exists_numerSection_eq`: **the surjectivity half.**
* `bijective_chartHom_of_cover`: the chart comparison is bijective.
* `isIso_comparison_of_degreeOneCover`: the comparison morphism `M̃ ⟶ ℱ` is an isomorphism when
  finitely many degree-one elements cover `Proj 𝒮`.
* `chartFrac`: the degree-zero fraction `f / g` on the chart `D₊(g)`, and `basicOpen_chartFrac`,
  its nonvanishing locus.

## References

* [Stacks Project, Tag 03GM](https://stacks.math.columbia.edu/tag/03GM)
* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
-/

@[expose] public noncomputable section
open CategoryTheory TopologicalSpace Opposite MonoidalCategory DirectSum
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTrivialization (projRingSheaf)
open Stacks.AlgebraicGeometry.ProjTwistRestriction (mulTrivSection bijective_mulTrivSection
  mulTrivSection_eq_pow_smul)
open Stacks.AlgebraicGeometry.ProjTwistSectionModule (twistSections twistSectionModule
  moduleGrading gsmul)
open Stacks.AlgebraicGeometry.ProjTwistLocalComparison
open scoped TensorProduct

universe u w

namespace Stacks.AlgebraicGeometry.ProjTwistChartBijective

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (F : SheafOfModules.{u} (projRingSheaf 𝒮)) {f : S} {d : ℕ}

/-- The numerator map commutes with restriction to a smaller open. -/
theorem numerSection_restrict (hf : f ∈ 𝒮 d) (n : ℕ)
    {W V : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (hV : V ≤ W) (x : twistSectionModule 𝒮 F) :
    (F.val.map (homOfLE hV).op).hom (numerSection 𝒮 F hf n hW x) =
      numerSection 𝒮 F hf n (hV.trans hW) x := by
  refine (bijective_mulTrivSection 𝒮 hf (n : ℤ) F (hV.trans hW)).1 ?_
  refine Eq.trans (mulTrivSection_restrict 𝒮 F hf (n : ℤ) hW hV
      (numerSection 𝒮 F hf n hW x)).symm ?_
  refine Eq.trans (congrArg ((twistSheafOfModules 𝒮 F ((n : ℤ) * d)).val.map (homOfLE hV).op)
    (mulTrivSection_numerSection 𝒮 F hf n hW x)) ?_
  refine Eq.trans (map_map 𝒮 F (le_top : W ≤ ⊤) hV _) ?_
  exact (mulTrivSection_numerSection 𝒮 F hf n (hV.trans hW) x).symm

/-- Trivialization by a power of `f` sends the zero section to zero. -/
theorem mulTrivSection_zero (hf : f ∈ 𝒮 d) (n : ℤ)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) :
    mulTrivSection 𝒮 hf n F hW 0 = 0 := by
  have h := mulTrivSection_smul 𝒮 F hf n hW 0 0
  simpa using h

/-- The numerator map at the chart of `f` and at the chart of a `g` of the same degree differ by
the degree-zero fraction `f / g`. -/
theorem numerSection_chart_compare {g : S} (hf : f ∈ 𝒮 d) (hg : g ∈ 𝒮 d) (n : ℕ)
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hWf : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) (hWg : W ≤ ProjectiveSpectrum.basicOpen 𝒮 g)
    (c : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W))
    (hc : ∀ y : W, HomogeneousLocalization.val (c.1 y) = Localization.mk f ⟨g, hWg y.2⟩)
    (x : twistSectionModule 𝒮 F) :
    numerSection 𝒮 F hg n hWg x = c ^ n • numerSection 𝒮 F hf n hWf x := by
  refine (bijective_mulTrivSection 𝒮 hg (n : ℤ) F hWg).1 ?_
  refine (mulTrivSection_numerSection 𝒮 F hg n hWg x).trans ?_
  refine Eq.trans (mulTrivSection_numerSection 𝒮 F hf n hWf x).symm ?_
  exact mulTrivSection_eq_pow_smul 𝒮 hf hg n F hWf hWg c hc _

/-- A section of a twist over `⊤` vanishing on each member of an open cover is zero. -/
theorem twistSection_eq_zero_of_cover {k : ℤ} {ι : Type*}
    (V : ι → Opens (ProjectiveSpectrum.top 𝒮))
    (hcov : ∀ y : ProjectiveSpectrum.top 𝒮, ∃ i, y ∈ V i)
    (u : (twistSheafOfModules 𝒮 F k).val.obj (op (⊤ : Opens (ProjectiveSpectrum.top 𝒮))))
    (h : ∀ i, (twistSheafOfModules 𝒮 F k).val.map (homOfLE (le_top : V i ≤ ⊤)).op u = 0) :
    u = 0 := by
  apply TopCat.Presheaf.IsSheaf.section_ext
    (U := op (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) (twistSheafOfModules 𝒮 F k).isSheaf
  intro y _
  obtain ⟨i, hi⟩ := hcov y
  exact ⟨V i, le_top, hi, (h i).trans (map_zero _).symm⟩


/-- The degree-zero fraction `f / g`, a section of the structure sheaf on the chart `D₊(g)`,
for `f` and `g` homogeneous of the same degree `d`. -/
def chartFrac {g : S} (hf : f ∈ 𝒮 d) (hg : g ∈ 𝒮 d) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj
      (op (ProjectiveSpectrum.basicOpen 𝒮 g)) :=
  (ProjectiveSpectrum.Proj.awayToSection 𝒮 g).hom
    (HomogeneousLocalization.Away.mk 𝒮 hg 1 f (by simpa using hf))

/-- The value of `f / g` in the local ring at a point of an open inside `D₊(g)`. -/
theorem val_chartFrac_restrict {g : S} (hf : f ∈ 𝒮 d) (hg : g ∈ 𝒮 d)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 g) (y : W) :
    HomogeneousLocalization.val
        ((((ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.map (homOfLE hW).op)
          (chartFrac 𝒮 hf hg)).1 y) = Localization.mk f ⟨g, hW y.2⟩ := by
  refine Eq.trans (show HomogeneousLocalization.val
      ((((ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.map (homOfLE hW).op)
        (chartFrac 𝒮 hf hg)).1 y) =
      Localization.mk f ⟨g ^ 1,
        (y.1).asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hW y.2) 1⟩ from rfl) ?_
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp))

/-- **The nonvanishing locus of `f / g` on the chart `D₊(g)` is the overlap `D₊(g) ∩ D₊(f)`.** -/
theorem basicOpen_chartFrac {g : S} (hf : f ∈ 𝒮 d) (hd : 0 < d) (hg : g ∈ 𝒮 d) :
    (AlgebraicGeometry.Proj 𝒮).basicOpen (chartFrac 𝒮 hf hg) =
      ProjectiveSpectrum.basicOpen 𝒮 g ⊓ ProjectiveSpectrum.basicOpen 𝒮 f :=
  Stacks.ProjChartBasicOpen.basicOpen_awayToSection_mk 𝒮 hg hd 1 f _

/-- The degree-zero fraction `f ^ k / g ^ k` is the `k`-th power of `f / g`. -/
theorem awayToSection_mk_pow {g : S} (hf : f ∈ 𝒮 d) (hg : g ∈ 𝒮 d) (k : ℕ)
    (hfk : f ^ k ∈ 𝒮 (k • d)) :
    (ProjectiveSpectrum.Proj.awayToSection 𝒮 g).hom
        (HomogeneousLocalization.Away.mk 𝒮 hg k (f ^ k) hfk) = chartFrac 𝒮 hf hg ^ k := by
  rw [chartFrac, ← map_pow]
  refine congrArg (ProjectiveSpectrum.Proj.awayToSection 𝒮 g).hom ?_
  refine HomogeneousLocalization.val_injective _ ?_
  rw [HomogeneousLocalization.val_pow, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, Localization.mk_pow]
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp))


/-- Restriction of a section of the structure sheaf of `Proj 𝒮` to a smaller open. -/
abbrev resO {V W : Opens (ProjectiveSpectrum.top 𝒮)} (hVW : V ≤ W)
    (c : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W)) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op V) :=
  ((ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.map (homOfLE hVW).op) c

/-- Two sections of the structure sheaf of `Proj 𝒮` with the same value in every local ring are
equal. -/
theorem structureSheaf_ext {W : Opens (ProjectiveSpectrum.top 𝒮)}
    {a b : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W)}
    (h : ∀ y : W, HomogeneousLocalization.val (a.1 y) = HomogeneousLocalization.val (b.1 y)) :
    a = b :=
  Subtype.ext (funext fun y => HomogeneousLocalization.val_injective _ (h y))

/-- **The chart fractions multiply as fractions do**: on an open inside `D₊(g) ∩ D₊(h)` the
product of `h / g` and `f / h` is `f / g`. -/
theorem resO_chartFrac_mul {g h : S} (hf : f ∈ 𝒮 d) (hg : g ∈ 𝒮 d) (hh : h ∈ 𝒮 d)
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hWg : W ≤ ProjectiveSpectrum.basicOpen 𝒮 g) (hWh : W ≤ ProjectiveSpectrum.basicOpen 𝒮 h) :
    resO 𝒮 hWg (chartFrac 𝒮 hh hg) * resO 𝒮 hWh (chartFrac 𝒮 hf hh) =
      resO 𝒮 hWg (chartFrac 𝒮 hf hg) := by
  refine structureSheaf_ext 𝒮 (fun y => ?_)
  have hmul : (resO 𝒮 hWg (chartFrac 𝒮 hh hg) * resO 𝒮 hWh (chartFrac 𝒮 hf hh)).1 y =
      (resO 𝒮 hWg (chartFrac 𝒮 hh hg)).1 y * (resO 𝒮 hWh (chartFrac 𝒮 hf hh)).1 y := rfl
  rw [hmul, HomogeneousLocalization.val_mul, val_chartFrac_restrict 𝒮 hh hg hWg y,
    val_chartFrac_restrict 𝒮 hf hh hWh y, val_chartFrac_restrict 𝒮 hf hg hWg y,
    Localization.mk_mul]
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by
    simp only [Submonoid.coe_mul]
    ring))


/-- Restriction of a section of a sheaf of modules on `Proj 𝒮` to a smaller open. -/
abbrev resM {V W : Opens (ProjectiveSpectrum.top 𝒮)} (hVW : V ≤ W)
    (x : F.val.obj (op W)) : F.val.obj (op V) :=
  (F.val.map (homOfLE hVW).op).hom x

/-- Restriction of sections of `ℱ` is semilinear along restriction of the structure sheaf. -/
theorem resM_smul {V W : Opens (ProjectiveSpectrum.top 𝒮)} (hVW : V ≤ W)
    (c : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W)) (x : F.val.obj (op W)) :
    resM 𝒮 F hVW (c • x) = resO 𝒮 hVW c • resM 𝒮 F hVW x :=
  PresheafOfModules.map_smul F.val (homOfLE hVW).op c x

/-- Restriction of sections of the structure sheaf commutes with powers. -/
theorem resO_pow {V W : Opens (ProjectiveSpectrum.top 𝒮)} (hVW : V ≤ W)
    (c : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W)) (n : ℕ) :
    resO 𝒮 hVW (c ^ n) = resO 𝒮 hVW c ^ n :=
  map_pow ((ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.map (homOfLE hVW).op).hom c n

/-- Restriction of `c ^ n • x` is `resO c ^ n • resM x`. -/
private theorem resM_pow_smul {V W : Opens (ProjectiveSpectrum.top 𝒮)} (hVW : V ≤ W)
    (c : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W)) (n : ℕ)
    (x : F.val.obj (op W)) :
    resM 𝒮 F hVW (c ^ n • x) = resO 𝒮 hVW c ^ n • resM 𝒮 F hVW x := by
  rw [resM_smul, resO_pow]

/-- **Chart-wise extension: Tag 01P7 on the chart `D₊(g)`.** A section of `ℱ` over `D₊(f)`
becomes, after multiplication by a high enough power of `f / g`, the restriction of a section
over the whole chart. -/
theorem exists_chart_numerator
    (hqc : SheafOfModules.IsQuasicoherent
      (R := (AlgebraicGeometry.Proj 𝒮).ringCatSheaf) F) {g : S}
    (hf : f ∈ 𝒮 d) (hd : 0 < d) (hg : g ∈ 𝒮 d)
    (hbo : (AlgebraicGeometry.Proj 𝒮).basicOpen (chartFrac 𝒮 hf hg) ≤
      ProjectiveSpectrum.basicOpen 𝒮 g)
    (hlef : (AlgebraicGeometry.Proj 𝒮).basicOpen (chartFrac 𝒮 hf hg) ≤
      ProjectiveSpectrum.basicOpen 𝒮 f)
    (t : F.val.obj (op (ProjectiveSpectrum.basicOpen 𝒮 f))) :
    ∃ e : ℕ, ∀ N : ℕ, e ≤ N →
      ∃ a : F.val.obj (op (ProjectiveSpectrum.basicOpen 𝒮 g)),
        resM 𝒮 F hbo a =
          resO 𝒮 hbo (chartFrac 𝒮 hf hg) ^ N • resM 𝒮 F hlef t := by
  have := hqc
  obtain ⟨e, b, hb⟩ :
      ∃ (e : ℕ) (b : F.val.obj (op (ProjectiveSpectrum.basicOpen 𝒮 g))),
        resO 𝒮 hbo (chartFrac 𝒮 hf hg) ^ e • resM 𝒮 F hlef t = resM 𝒮 F hbo b :=
    Stacks.ModuleSectionExtension.exists_pow_smul_eq_res
      (X := AlgebraicGeometry.Proj 𝒮) F
      (AlgebraicGeometry.Proj.isAffineOpen_basicOpen 𝒮 g hg hd)
      (chartFrac 𝒮 hf hg) (resM 𝒮 F hlef t)
  refine ⟨e, fun N hN => ⟨chartFrac 𝒮 hf hg ^ (N - e) • b, ?_⟩⟩
  refine (resM_pow_smul 𝒮 F _ _ _ _).trans ?_
  rw [← hb, smul_smul, ← pow_add, Nat.sub_add_cancel hN]


/-- Restriction of a section of a twist of `ℱ` to a smaller open. -/
abbrev resT (k : ℤ) {V W : Opens (ProjectiveSpectrum.top 𝒮)} (hVW : V ≤ W)
    (y : (twistSheafOfModules 𝒮 F k).val.obj (op W)) :
    (twistSheafOfModules 𝒮 F k).val.obj (op V) :=
  (twistSheafOfModules 𝒮 F k).val.map (homOfLE hVW).op y

/-- Two sections of a twist over an open which agree on every member of a cover of it are
equal. -/
theorem twistSection_eq_of_cover {k : ℤ} {ι : Type*} (W : Opens (ProjectiveSpectrum.top 𝒮))
    (V : ι → Opens (ProjectiveSpectrum.top 𝒮)) (hV : ∀ i, V i ≤ W)
    (hcov : ∀ y : ProjectiveSpectrum.top 𝒮, y ∈ W → ∃ i, y ∈ V i)
    (a b : (twistSheafOfModules 𝒮 F k).val.obj (op W))
    (h : ∀ i, resT 𝒮 F k (hV i) a = resT 𝒮 F k (hV i) b) : a = b := by
  apply TopCat.Presheaf.IsSheaf.section_ext (U := op W) (twistSheafOfModules 𝒮 F k).isSheaf
  intro y hy
  obtain ⟨i, hi⟩ := hcov y hy
  exact ⟨V i, hV i, hi, h i⟩

/-- **A compatible family of sections of a twist over an open cover of `Proj 𝒮` glues.** -/
theorem exists_glue {k : ℤ} {ι : Type u} (V : ι → Opens (ProjectiveSpectrum.top 𝒮))
    (hsup : (⨆ i, V i) = (⊤ : Opens (ProjectiveSpectrum.top 𝒮)))
    (a : ∀ i, (twistSheafOfModules 𝒮 F k).val.obj (op (V i)))
    (ha : TopCat.Presheaf.IsCompatible (twistSheafOfModules 𝒮 F k).val.presheaf V a) :
    ∃ b : (twistSheafOfModules 𝒮 F k).val.obj (op (⊤ : Opens (ProjectiveSpectrum.top 𝒮))),
      ∀ i, resT 𝒮 F k (le_top : V i ≤ ⊤) b = a i := by
  obtain ⟨b, hb, -⟩ := TopCat.Presheaf.IsSheaf.isSheafUniqueGluing
    (twistSheafOfModules 𝒮 F k).isSheaf V a ha
  refine ⟨(twistSheafOfModules 𝒮 F k).val.presheaf.map (eqToHom hsup.symm).op b, fun i => ?_⟩
  have hcomp : (eqToHom hsup.symm).op ≫ (homOfLE (le_top : V i ≤ ⊤)).op =
      (Opens.leSupr V i).op := Subsingleton.elim _ _
  change (twistSheafOfModules 𝒮 F k).val.presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op
      ((twistSheafOfModules 𝒮 F k).val.presheaf.map (eqToHom hsup.symm).op b) = a i
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, hcomp]
  exact hb i

/-- Restricting a section of the structure sheaf twice is restricting it once. -/
theorem resO_resO {U V W : Opens (ProjectiveSpectrum.top 𝒮)} (hVU : V ≤ U) (hWV : W ≤ V)
    (c : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op U)) :
    resO 𝒮 hWV (resO 𝒮 hVU c) = resO 𝒮 (hWV.trans hVU) c :=
  (CategoryTheory.congr_fun ((ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.map_comp
    (homOfLE hVU).op (homOfLE hWV).op) c).symm

/-- Restricting a section of `ℱ` twice is restricting it once. -/
theorem resM_resM {U V W : Opens (ProjectiveSpectrum.top 𝒮)} (hVU : V ≤ U) (hWV : W ≤ V)
    (x : F.val.obj (op U)) :
    resM 𝒮 F hWV (resM 𝒮 F hVU x) = resM 𝒮 F (hWV.trans hVU) x :=
  (CategoryTheory.congr_fun (F.val.map_comp (homOfLE hVU).op (homOfLE hWV).op) x).symm

/-- Restricting `resO c ^ n • resM t` to a smaller open restricts both factors. -/
private theorem resM_resO_pow_smul {Z V U W : Opens (ProjectiveSpectrum.top 𝒮)} (hZV : Z ≤ V)
    (hVU : V ≤ U) (hVW : V ≤ W)
    (c : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op U)) (n : ℕ) (t : F.val.obj (op W)) :
    resM 𝒮 F hZV (resO 𝒮 hVU c ^ n • resM 𝒮 F hVW t) =
      resO 𝒮 (hZV.trans hVU) c ^ n • resM 𝒮 F (hZV.trans hVW) t := by
  rw [resM_pow_smul, resO_resO, resM_resM]

/-- `D₊(g) ∩ D₊(h)` is an affine open of `Proj 𝒮` when `g` and `h` are homogeneous of the same
positive degree. -/
theorem isAffineOpen_inf_basicOpen {g h : S} (hd : 0 < d) (hg : g ∈ 𝒮 d) (hh : h ∈ 𝒮 d) :
    IsAffineOpen (X := AlgebraicGeometry.Proj 𝒮)
      (ProjectiveSpectrum.basicOpen 𝒮 g ⊓ ProjectiveSpectrum.basicOpen 𝒮 h) := by
  have hmem : g * h ∈ 𝒮 (d + d) := SetLike.mul_mem_graded hg hh
  have hpos : 0 < d + d := by omega
  have h0 := AlgebraicGeometry.Proj.isAffineOpen_basicOpen 𝒮 (g * h) hmem hpos
  rwa [AlgebraicGeometry.Proj.basicOpen_mul] at h0


/-- On the chart `D₊(g)` the numerator of a twisted global section vanishing on `D₊(f)` is
killed by a power of `f / g`. -/
theorem exists_pow_smul_numerSection_eq_zero
    (hqc : SheafOfModules.IsQuasicoherent
      (R := (AlgebraicGeometry.Proj 𝒮).ringCatSheaf) F) {g : S}
    (hf : f ∈ 𝒮 d) (hd : 0 < d) (hg : g ∈ 𝒮 d) (n : ℕ) (x : twistSectionModule 𝒮 F)
    (h0 : numerSection 𝒮 F hf n (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f)) x = 0) :
    ∃ e : ℕ, chartFrac 𝒮 hf hg ^ e •
      numerSection 𝒮 F hg n (le_refl (ProjectiveSpectrum.basicOpen 𝒮 g)) x = 0 := by
  have := hqc
  have hVeq := basicOpen_chartFrac 𝒮 hf hd hg
  have hleg : (AlgebraicGeometry.Proj 𝒮).basicOpen (chartFrac 𝒮 hf hg) ≤
      ProjectiveSpectrum.basicOpen 𝒮 g := by rw [hVeq]; exact inf_le_left
  have hlef : (AlgebraicGeometry.Proj 𝒮).basicOpen (chartFrac 𝒮 hf hg) ≤
      ProjectiveSpectrum.basicOpen 𝒮 f := by rw [hVeq]; exact inf_le_right
  have hzero : numerSection 𝒮 F hf n hlef x = 0 := by
    rw [← numerSection_restrict 𝒮 F hf n (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f)) hlef x,
      h0, map_zero]
    rfl
  have hres : (F.val.map (homOfLE hleg).op).hom
      (numerSection 𝒮 F hg n (le_refl (ProjectiveSpectrum.basicOpen 𝒮 g)) x) = 0 := by
    refine Eq.trans (numerSection_restrict 𝒮 F hg n
      (le_refl (ProjectiveSpectrum.basicOpen 𝒮 g)) hleg x) ?_
    refine Eq.trans (numerSection_chart_compare 𝒮 F hf hg n hlef hleg
      (((ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.map (homOfLE hleg).op)
        (chartFrac 𝒮 hf hg)) (val_chartFrac_restrict 𝒮 hf hg hleg) x) ?_
    rw [hzero, smul_zero]
    rfl
  exact Stacks.ModuleSectionExtension.exists_pow_smul_eq_zero F
    (AlgebraicGeometry.Proj.isAffineOpen_basicOpen 𝒮 g hg hd) (chartFrac 𝒮 hf hg) _ hres

/-- **The injectivity half of the omitted argument of Tag 03GM.** A twisted global section of
degree `n d` whose numerator on `D₊(f)` vanishes is killed by a power of `f`. -/
theorem exists_pow_smul_eq_zero_of_numerSection_eq_zero
    (hqc : SheafOfModules.IsQuasicoherent
      (R := (AlgebraicGeometry.Proj 𝒮).ringCatSheaf) F)
    {ι : Type*} [Finite ι] {g : ι → S}
    (hf : f ∈ 𝒮 d) (hd : 0 < d) (hg : ∀ i, g i ∈ 𝒮 d)
    (hcov : ∀ y : ProjectiveSpectrum.top 𝒮, ∃ i, y ∈ ProjectiveSpectrum.basicOpen 𝒮 (g i))
    (n : ℕ) (x : twistSectionModule 𝒮 F) (hx : x ∈ moduleGrading 𝒮 F ((n * d : ℕ) : ℤ))
    (h0 : numerSection 𝒮 F hf n (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f)) x = 0) :
    ∃ k : ℕ, f ^ k • x = 0 := by
  classical
  obtain ⟨s, rfl⟩ := hx
  choose e he using fun i : ι =>
    exists_pow_smul_numerSection_eq_zero 𝒮 F hqc hf hd (hg i) n _ h0
  obtain ⟨k, hk⟩ := Finite.exists_le e
  refine ⟨k, ?_⟩
  have hek : ∀ i : ι, chartFrac 𝒮 hf (hg i) ^ k •
      numerSection 𝒮 F (hg i) n (le_refl (ProjectiveSpectrum.basicOpen 𝒮 (g i)))
        (DirectSum.of (twistSections 𝒮 F) (n * d) s) = 0 := by
    intro i
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (hk i)
    rw [hm, add_comm, pow_add, mul_smul, he i, smul_zero]
  have hfk : f ^ k ∈ 𝒮 (k * d) := by
    simpa [mul_comm] using SetLike.pow_mem_graded k hf
  have hfk' : f ^ k ∈ 𝒮 (k • d) := SetLike.pow_mem_graded k hf
  have hj : (k + n) * d = k * d + n * d := by ring
  have hgs : gsmul 𝒮 F hfk (n * d) ((k + n) * d) hj s = 0 := by
    refine twistSection_eq_zero_of_cover 𝒮 F
      (fun i => ProjectiveSpectrum.basicOpen 𝒮 (g i)) hcov _ (fun i => ?_)
    have hdc : degreeComponent 𝒮 F ((k + n) * d)
        (f ^ k • DirectSum.of (twistSections 𝒮 F) (n * d) s) =
        gsmul 𝒮 F hfk (n * d) ((k + n) * d) hj s := by
      rw [smul_of' 𝒮 F hfk hj s, degreeComponent_of]
    have hnum : numerSection 𝒮 F (hg i) (k + n)
        (le_refl (ProjectiveSpectrum.basicOpen 𝒮 (g i)))
        (f ^ k • DirectSum.of (twistSections 𝒮 F) (n * d) s) = 0 := by
      refine Eq.trans (numerSection_smul 𝒮 F (hg i) k n (f ^ k)
        (DirectSum.of (twistSections 𝒮 F) (n * d) s) hfk' ⟨s, rfl⟩) ?_
      rw [awayToSection_mk_pow 𝒮 hf (hg i) k hfk']
      exact hek i
    refine Eq.trans (congrArg ((twistSheafOfModules 𝒮 F (((k + n : ℕ) : ℤ) * d)).val.map
      (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒮 (g i) ≤ ⊤)).op) hdc.symm) ?_
    refine Eq.trans (mulTrivSection_numerSection 𝒮 F (hg i) (k + n)
      (le_refl (ProjectiveSpectrum.basicOpen 𝒮 (g i)))
      (f ^ k • DirectSum.of (twistSections 𝒮 F) (n * d) s)).symm ?_
    rw [hnum]
    exact mulTrivSection_zero 𝒮 F (hg i) ((k + n : ℕ) : ℤ) _
  rw [smul_of' 𝒮 F hfk hj s, hgs, map_zero]


/-- **The local numerators of a section over `D₊(f)`, with a uniform denominator exponent and
agreeing on the overlaps after one further multiplication.** -/
theorem exists_chart_family
    (hqc : SheafOfModules.IsQuasicoherent
      (R := (AlgebraicGeometry.Proj 𝒮).ringCatSheaf) F)
    {ι : Type u} [Finite ι] {g : ι → S}
    (hf : f ∈ 𝒮 d) (hd : 0 < d) (hg : ∀ i, g i ∈ 𝒮 d)
    (hbo : ∀ i : ι, (AlgebraicGeometry.Proj 𝒮).basicOpen (chartFrac 𝒮 hf (hg i)) ≤
      ProjectiveSpectrum.basicOpen 𝒮 (g i))
    (hlef : ∀ i : ι, (AlgebraicGeometry.Proj 𝒮).basicOpen (chartFrac 𝒮 hf (hg i)) ≤
      ProjectiveSpectrum.basicOpen 𝒮 f)
    (hij : ∀ i j : ι, ProjectiveSpectrum.basicOpen 𝒮 (g i) ⊓
      ProjectiveSpectrum.basicOpen 𝒮 (g j) ≤ ProjectiveSpectrum.basicOpen 𝒮 (g i))
    (hji : ∀ i j : ι, ProjectiveSpectrum.basicOpen 𝒮 (g i) ⊓
      ProjectiveSpectrum.basicOpen 𝒮 (g j) ≤ ProjectiveSpectrum.basicOpen 𝒮 (g j))
    (t : F.val.obj (op (ProjectiveSpectrum.basicOpen 𝒮 f))) :
    ∃ (N : ℕ) (a : ∀ i : ι, F.val.obj (op (ProjectiveSpectrum.basicOpen 𝒮 (g i)))),
      (∀ (i : ι) {Z : Opens (ProjectiveSpectrum.top 𝒮)}
        (hZg : Z ≤ ProjectiveSpectrum.basicOpen 𝒮 (g i))
        (hZf : Z ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
        (_ : Z ≤ (AlgebraicGeometry.Proj 𝒮).basicOpen (chartFrac 𝒮 hf (hg i))),
          resM 𝒮 F hZg (a i) =
            resO 𝒮 hZg (chartFrac 𝒮 hf (hg i)) ^ N • resM 𝒮 F hZf t) ∧
      ∀ i j : ι, ∃ k : ℕ,
        resO 𝒮 (hij i j) (chartFrac 𝒮 hf (hg i)) ^ k • resM 𝒮 F (hij i j) (a i) =
          resO 𝒮 (hij i j) (chartFrac 𝒮 hf (hg i)) ^ k •
            (resO 𝒮 (hij i j) (chartFrac 𝒮 (hg j) (hg i)) ^ N •
              resM 𝒮 F (hji i j) (a j)) := by
  classical
  have := hqc
  choose e he using fun i : ι =>
    exists_chart_numerator 𝒮 F hqc hf hd (hg i) (hbo i) (hlef i) t
  obtain ⟨N, hN⟩ := Finite.exists_le e
  choose a ha using fun i : ι => he i N (hN i)
  have hS1 : ∀ (i : ι) {Z : Opens (ProjectiveSpectrum.top 𝒮)}
      (hZg : Z ≤ ProjectiveSpectrum.basicOpen 𝒮 (g i))
      (hZf : Z ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
      (_ : Z ≤ (AlgebraicGeometry.Proj 𝒮).basicOpen (chartFrac 𝒮 hf (hg i))),
      resM 𝒮 F hZg (a i) =
        resO 𝒮 hZg (chartFrac 𝒮 hf (hg i)) ^ N • resM 𝒮 F hZf t := by
    intro i Z hZg hZf hZ
    rw [← resM_resM 𝒮 F (hbo i) hZ (a i), ha i]
    exact resM_resO_pow_smul 𝒮 F hZ (hbo i) (hlef i) _ N t
  refine ⟨N, a, hS1, fun i j => ?_⟩
  have hqeq : (AlgebraicGeometry.Proj 𝒮).basicOpen
        (resO 𝒮 (hij i j) (chartFrac 𝒮 hf (hg i))) =
      (ProjectiveSpectrum.basicOpen 𝒮 (g i) ⊓ ProjectiveSpectrum.basicOpen 𝒮 (g j)) ⊓
        (AlgebraicGeometry.Proj 𝒮).basicOpen (chartFrac 𝒮 hf (hg i)) :=
    AlgebraicGeometry.Scheme.basicOpen_res (X := AlgebraicGeometry.Proj 𝒮)
      (f := chartFrac 𝒮 hf (hg i)) (homOfLE (hij i j)).op
  have hqle : (AlgebraicGeometry.Proj 𝒮).basicOpen
      (resO 𝒮 (hij i j) (chartFrac 𝒮 hf (hg i))) ≤
      ProjectiveSpectrum.basicOpen 𝒮 (g i) ⊓ ProjectiveSpectrum.basicOpen 𝒮 (g j) :=
    (le_of_eq hqeq).trans inf_le_left
  have hqZi : (AlgebraicGeometry.Proj 𝒮).basicOpen
      (resO 𝒮 (hij i j) (chartFrac 𝒮 hf (hg i))) ≤
      (AlgebraicGeometry.Proj 𝒮).basicOpen (chartFrac 𝒮 hf (hg i)) :=
    (le_of_eq hqeq).trans inf_le_right
  have hqgi := hqle.trans (hij i j)
  have hqgj := hqle.trans (hji i j)
  have hqf := hqZi.trans (hlef i)
  have hqZj : (AlgebraicGeometry.Proj 𝒮).basicOpen
      (resO 𝒮 (hij i j) (chartFrac 𝒮 hf (hg i))) ≤
      (AlgebraicGeometry.Proj 𝒮).basicOpen (chartFrac 𝒮 hf (hg j)) := by
    rw [basicOpen_chartFrac 𝒮 hf hd (hg j)]
    exact le_inf hqgj hqf
  have hagree : resM 𝒮 F hqle (resM 𝒮 F (hij i j) (a i)) =
      resM 𝒮 F hqle (resO 𝒮 (hij i j) (chartFrac 𝒮 (hg j) (hg i)) ^ N •
        resM 𝒮 F (hji i j) (a j)) := by
    refine (resM_resM 𝒮 F _ _ _).trans ((hS1 i hqgi hqf hqZi).trans ?_)
    refine Eq.trans ?_ (resM_resO_pow_smul 𝒮 F hqle (hij i j) (hji i j) _ N _).symm
    refine Eq.trans ?_ (congrArg (fun y => _ • y) (hS1 j hqgj hqf hqZj)).symm
    rw [smul_smul, ← mul_pow, resO_chartFrac_mul 𝒮 hf (hg i) (hg j) hqgi hqgj]
  exact Stacks.ModuleSectionExtension.exists_pow_smul_eq_of_res_eq
    (X := AlgebraicGeometry.Proj 𝒮) F (isAffineOpen_inf_basicOpen 𝒮 hd (hg i) (hg j))
    (resO 𝒮 (hij i j) (chartFrac 𝒮 hf (hg i))) _ _ hagree


/-- If finitely many opens have supremum `⊤`, every point lies in one of them. -/
private theorem exists_mem_of_iSup_eq_top {ι : Type*} {V : ι → Opens (ProjectiveSpectrum.top 𝒮)}
    (hsup : (⨆ i, V i) = ⊤) (y : ProjectiveSpectrum.top 𝒮) : ∃ i, y ∈ V i :=
  Opens.mem_iSup.mp (hsup ▸ trivial)

/-- The local twisted section a chart numerator defines, after one further multiplication by
`f / g i`. -/
theorem resM_pow_chartFrac_smul_eq {ι : Type u} {g : ι → S}
    (hf : f ∈ 𝒮 d) (hg : ∀ i, g i ∈ 𝒮 d) (N k : ℕ)
    (a : ∀ i : ι, F.val.obj (op (ProjectiveSpectrum.basicOpen 𝒮 (g i))))
    (t : F.val.obj (op (ProjectiveSpectrum.basicOpen 𝒮 f))) (i : ι)
    {Z : Opens (ProjectiveSpectrum.top 𝒮)}
    (hZg : Z ≤ ProjectiveSpectrum.basicOpen 𝒮 (g i))
    (hZf : Z ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (hS1 : resM 𝒮 F hZg (a i) =
      resO 𝒮 hZg (chartFrac 𝒮 hf (hg i)) ^ N • resM 𝒮 F hZf t) :
    resM 𝒮 F hZg (chartFrac 𝒮 hf (hg i) ^ k • a i) =
      resO 𝒮 hZg (chartFrac 𝒮 hf (hg i)) ^ (N + k) • resM 𝒮 F hZf t := by
  refine (resM_pow_smul 𝒮 F _ _ _ _).trans ?_
  rw [hS1, smul_smul, ← pow_add, Nat.add_comm]

/-- **The surjectivity half of the omitted argument of Tag 03GM.** -/
theorem exists_numerSection_eq
    (hqc : SheafOfModules.IsQuasicoherent
      (R := (AlgebraicGeometry.Proj 𝒮).ringCatSheaf) F)
    {ι : Type u} [Finite ι] {g : ι → S}
    (hf : f ∈ 𝒮 d) (hd : 0 < d) (hg : ∀ i, g i ∈ 𝒮 d)
    (hsup : (⨆ i, ProjectiveSpectrum.basicOpen 𝒮 (g i)) =
      (⊤ : Opens (ProjectiveSpectrum.top 𝒮)))
    (t : F.val.obj (op (ProjectiveSpectrum.basicOpen 𝒮 f))) :
    ∃ (n : ℕ) (x : twistSectionModule 𝒮 F), x ∈ moduleGrading 𝒮 F ((n * d : ℕ) : ℤ) ∧
      numerSection 𝒮 F hf n (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f)) x = t := by
  classical
  have := hqc
  have hbo : ∀ i : ι, (AlgebraicGeometry.Proj 𝒮).basicOpen (chartFrac 𝒮 hf (hg i)) ≤
      ProjectiveSpectrum.basicOpen 𝒮 (g i) := fun i =>
    (le_of_eq (basicOpen_chartFrac 𝒮 hf hd (hg i))).trans inf_le_left
  have hlef : ∀ i : ι, (AlgebraicGeometry.Proj 𝒮).basicOpen (chartFrac 𝒮 hf (hg i)) ≤
      ProjectiveSpectrum.basicOpen 𝒮 f := fun i =>
    (le_of_eq (basicOpen_chartFrac 𝒮 hf hd (hg i))).trans inf_le_right
  have hij : ∀ i j : ι, ProjectiveSpectrum.basicOpen 𝒮 (g i) ⊓
      ProjectiveSpectrum.basicOpen 𝒮 (g j) ≤ ProjectiveSpectrum.basicOpen 𝒮 (g i) :=
    fun _ _ => inf_le_left
  have hji : ∀ i j : ι, ProjectiveSpectrum.basicOpen 𝒮 (g i) ⊓
      ProjectiveSpectrum.basicOpen 𝒮 (g j) ≤ ProjectiveSpectrum.basicOpen 𝒮 (g j) :=
    fun _ _ => inf_le_right
  obtain ⟨N, a, hS1, hpair⟩ := exists_chart_family 𝒮 F hqc hf hd hg hbo hlef hij hji t
  choose kk hkk using hpair
  obtain ⟨k, hk⟩ := Finite.exists_le fun p : ι × ι => kk p.1 p.2
  have hpk : ∀ i j : ι,
      resO 𝒮 (hij i j) (chartFrac 𝒮 hf (hg i)) ^ k • resM 𝒮 F (hij i j) (a i) =
        resO 𝒮 (hij i j) (chartFrac 𝒮 hf (hg i)) ^ k •
          (resO 𝒮 (hij i j) (chartFrac 𝒮 (hg j) (hg i)) ^ N •
            resM 𝒮 F (hji i j) (a j)) := by
    intro i j
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (show kk i j ≤ k from hk (i, j))
    have hm' : k = m + kk i j := by omega
    rw [hm', pow_add, mul_smul, mul_smul, hkk i j]
  have hcompat : ∀ i j : ι,
      resT 𝒮 F (((N + k : ℕ) : ℤ) * d) (hij i j)
          (mulTrivSection 𝒮 (hg i) ((N + k : ℕ) : ℤ) F
            (le_refl (ProjectiveSpectrum.basicOpen 𝒮 (g i)))
            (chartFrac 𝒮 hf (hg i) ^ k • a i)) =
        resT 𝒮 F (((N + k : ℕ) : ℤ) * d) (hji i j)
          (mulTrivSection 𝒮 (hg j) ((N + k : ℕ) : ℤ) F
            (le_refl (ProjectiveSpectrum.basicOpen 𝒮 (g j)))
            (chartFrac 𝒮 hf (hg j) ^ k • a j)) := by
    intro i j
    have hinner : resM 𝒮 F (hij i j) (chartFrac 𝒮 hf (hg i) ^ k • a i) =
        resO 𝒮 (hij i j) (chartFrac 𝒮 (hg j) (hg i)) ^ (N + k) •
          resM 𝒮 F (hji i j) (chartFrac 𝒮 hf (hg j) ^ k • a j) := by
      refine (resM_pow_smul 𝒮 F _ _ _ _).trans (Eq.trans ?_
        (congrArg _ (resM_pow_smul 𝒮 F _ _ _ _)).symm)
      rw [hpk i j, smul_smul, smul_smul]
      refine congrArg (fun r => r • resM 𝒮 F (hji i j) (a j)) ?_
      rw [← resO_chartFrac_mul 𝒮 hf (hg i) (hg j) (hij i j) (hji i j), pow_add, mul_pow]
      ring
    refine Eq.trans (mulTrivSection_restrict 𝒮 F (hg i) ((N + k : ℕ) : ℤ)
      (le_refl (ProjectiveSpectrum.basicOpen 𝒮 (g i))) (hij i j) _) ?_
    refine Eq.trans ?_ (mulTrivSection_restrict 𝒮 F (hg j) ((N + k : ℕ) : ℤ)
      (le_refl (ProjectiveSpectrum.basicOpen 𝒮 (g j))) (hji i j) _).symm
    refine Eq.trans ?_ (mulTrivSection_eq_pow_smul 𝒮 (hg j) (hg i) (N + k) F
      (hji i j) (hij i j) (resO 𝒮 (hij i j) (chartFrac 𝒮 (hg j) (hg i)))
      (val_chartFrac_restrict 𝒮 (hg j) (hg i) (hij i j)) _).symm
    exact congrArg (mulTrivSection 𝒮 (hg i) ((N + k : ℕ) : ℤ) F (hij i j)) hinner
  have hcompat' : TopCat.Presheaf.IsCompatible
      (twistSheafOfModules 𝒮 F (((N + k : ℕ) : ℤ) * d)).val.presheaf
      (fun i => ProjectiveSpectrum.basicOpen 𝒮 (g i))
      (fun i => mulTrivSection 𝒮 (hg i) ((N + k : ℕ) : ℤ) F
        (le_refl (ProjectiveSpectrum.basicOpen 𝒮 (g i)))
        (chartFrac 𝒮 hf (hg i) ^ k • a i)) := by
    intro i j
    exact hcompat i j
  obtain ⟨y, hy⟩ := exists_glue 𝒮 F (fun i => ProjectiveSpectrum.basicOpen 𝒮 (g i)) hsup _ hcompat'
  refine ⟨N + k, DirectSum.of (twistSections 𝒮 F) ((N + k) * d) y, ⟨y, rfl⟩, ?_⟩
  refine (bijective_mulTrivSection 𝒮 hf ((N + k : ℕ) : ℤ) F
    (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f))).1 ?_
  refine Eq.trans (mulTrivSection_numerSection 𝒮 F hf (N + k)
    (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f)) _) ?_
  refine Eq.trans (congrArg (resT 𝒮 F (((N + k : ℕ) : ℤ) * d)
      (le_top : ProjectiveSpectrum.basicOpen 𝒮 f ≤ ⊤))
    (degreeComponent_of 𝒮 F ((N + k) * d) y)) ?_
  refine twistSection_eq_of_cover 𝒮 F (ProjectiveSpectrum.basicOpen 𝒮 f)
    (fun i => (AlgebraicGeometry.Proj 𝒮).basicOpen (chartFrac 𝒮 hf (hg i))) hlef ?_ _ _ ?_
  · intro z hz
    obtain ⟨i, hi⟩ := exists_mem_of_iSup_eq_top 𝒮 hsup z
    refine ⟨i, ?_⟩
    rw [basicOpen_chartFrac 𝒮 hf hd (hg i)]
    exact ⟨hi, hz⟩
  · intro i
    refine Eq.trans (map_map 𝒮 F (le_top : ProjectiveSpectrum.basicOpen 𝒮 f ≤ ⊤)
      (hlef i) y) ?_
    refine Eq.trans (map_map 𝒮 F (le_top : ProjectiveSpectrum.basicOpen 𝒮 (g i) ≤ ⊤)
      (hbo i) y).symm ?_
    refine Eq.trans (congrArg (resT 𝒮 F (((N + k : ℕ) : ℤ) * d) (hbo i)) (hy i)) ?_
    refine Eq.trans (mulTrivSection_restrict 𝒮 F (hg i) ((N + k : ℕ) : ℤ)
      (le_refl (ProjectiveSpectrum.basicOpen 𝒮 (g i))) (hbo i) _) ?_
    refine Eq.trans ?_ (mulTrivSection_restrict 𝒮 F hf ((N + k : ℕ) : ℤ)
      (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f)) (hlef i) t).symm
    refine Eq.trans ?_ (mulTrivSection_eq_pow_smul 𝒮 hf (hg i) (N + k) F (hlef i) (hbo i)
      (resO 𝒮 (hbo i) (chartFrac 𝒮 hf (hg i)))
      (val_chartFrac_restrict 𝒮 hf (hg i) (hbo i)) _).symm
    refine congrArg (mulTrivSection 𝒮 (hg i) ((N + k : ℕ) : ℤ) F (hbo i)) ?_
    exact resM_pow_chartFrac_smul_eq 𝒮 F hf hg N k a t i (hbo i) (hlef i)
      (hS1 i (hbo i) (hlef i) le_rfl)


/-! ### The chart comparison is bijective, and the comparison morphism is an isomorphism -/

/-- **The chart comparison of Tag 03GM is bijective.** For `ℱ` quasi-coherent and a finite family
of homogeneous elements of the same degree `d` as `f` whose standard opens cover `Proj 𝒮`, the
comparison `Γ(D₊(f), M̃) → Γ(D₊(f), ℱ)` is a bijection. -/
theorem bijective_chartHom_of_cover
    (hqc : SheafOfModules.IsQuasicoherent
      (R := (AlgebraicGeometry.Proj 𝒮).ringCatSheaf) F)
    {ι : Type u} [Finite ι] {g : ι → S}
    (hf : f ∈ 𝒮 d) (hd : 0 < d) (hg : ∀ i, g i ∈ 𝒮 d)
    (hsup : (⨆ i, ProjectiveSpectrum.basicOpen 𝒮 (g i)) =
      (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) :
    Function.Bijective (chartHom 𝒮 F hf hd).hom := by
  refine (bijective_chartHom_iff_bijective_chartLift 𝒮 F hf hd).mpr ?_
  refine Stacks.SheafOfModules.bijective_degreeZeroLocalizationLiftOfDegree_of_degree
    𝒮 (moduleGrading 𝒮 F) hf
    (fun n => numerSection 𝒮 F hf n (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f)))
    (fun n k x hx => numerSection_pow_smul 𝒮 F hf n k _ x hx) (fun y => ?_)
    (fun n x hx h0 =>
      exists_pow_smul_eq_zero_of_numerSection_eq_zero 𝒮 F hqc hf hd hg
        (exists_mem_of_iSup_eq_top 𝒮 hsup) n x hx h0)
  obtain ⟨n, x, hx, hxy⟩ := exists_numerSection_eq 𝒮 F hqc hf hd hg hsup y
  exact ⟨n, x, hx, hxy⟩

/-- **The comparison morphism `M̃ ⟶ ℱ` of Tag 03GM (2) is an isomorphism.** For `ℱ`
quasi-coherent on `Proj 𝒮` and finitely many degree-one homogeneous elements whose standard opens
cover, the chart comparison at *every* positive-degree homogeneous element is bijective -- the
cover needed at degree `e` is given by the `e`-th powers of the degree-one elements, whose
standard opens are the same opens -- so the glued morphism is invertible. -/
theorem isIso_comparison_of_degreeOneCover
    (hqc : SheafOfModules.IsQuasicoherent
      (R := (AlgebraicGeometry.Proj 𝒮).ringCatSheaf) F)
    {ι : Type u} [Finite ι] {g : ι → S} (hg : ∀ i, g i ∈ 𝒮 1)
    (hsup : (⨆ i, ProjectiveSpectrum.basicOpen 𝒮 (g i)) =
      (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) :
    IsIso (comparison 𝒮 F) := by
  refine isIso_comparison_of_bijective_chartHom 𝒮 F (fun {h} {e} hh he => ?_)
  have hge : ∀ i, g i ^ e ∈ 𝒮 e := fun i => by
    simpa using SetLike.pow_mem_graded e (hg i)
  have hsup' : (⨆ i, ProjectiveSpectrum.basicOpen 𝒮 (g i ^ e)) =
      (⊤ : Opens (ProjectiveSpectrum.top 𝒮)) := by
    refine Eq.trans ?_ hsup
    exact iSup_congr fun i => ProjectiveSpectrum.basicOpen_pow 𝒮 (g i) e he
  exact bijective_chartHom_of_cover 𝒮 F hqc hh he hge hsup'

end Stacks.AlgebraicGeometry.ProjTwistChartBijective

end
