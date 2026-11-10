module

public import StacksFrontier.AlgebraicGeometry.Variety.Projective.VeryAmpleVanishAtPoint
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartRatioPullback
public import StacksFrontier.RingTheory.GradedAlgebra.HomogeneousAnnihilator

/-!
# A morphism into `Proj` is determined by the ratios of the pulled-back sections

Let `A` and `B` be graded rings, with `B` generated in degree one over `B₀`, let `n ∈ ℤ`, and let
`α : Proj A ⟶ Proj B` be a morphism together with an isomorphism
`e : 𝒪_{Proj A}(n) ≅ α^* 𝒪_{Proj B}(1)`. Every degree-one element `w ∈ B₁` gives a global section
`w / 1` of `𝒪_{Proj B}(1)`, and so, through `e`, a global section `s_w` of `𝒪_{Proj A}(n)`.
On the standard open `D₊(v)` the section `w / 1` is the multiple `(w / v) · (v / 1)`, and this
identity survives the pullback: at a point `x` of `Proj A` with `α(x) ∈ D₊(v)`,

  `α^♯(w / v)(x) · s_v(x) = s_w(x)`

in the fibre of `𝒪(n)` at `x`, which is the localization of `A` at the homogeneous prime `x`.

Since the ratios `w / v` generate the chart ring `B_{(v)}`, and the stalk of `Proj B` at `α(x)` is
a localization of `B_{(v)}`, this pins down the stalk map of `α` at `x` up to what it does on the
ratios `s_w / s_v`. The consequence recorded here is the one an argument against immersions
needs: two morphisms `Spec R ⟶ Proj A` through `x`, given by two homomorphisms out of the stalk at
`x`, have the same composite with `α` as soon as the two homomorphisms agree on every element `r`
of the stalk that solves `r · t(x) = s(x)` for global sections `s`, `t` of `𝒪(n)` with `t` not
vanishing at `x`.

## Main definitions

* `Stacks.ProjMorphismRatios.homogeneousSectionOn`: the section `w / 1` of `𝒪_{Proj B}(1)` over
  an open.
* `Stacks.ProjMorphismRatios.pullbackSection`: the global section `s_w` of `𝒪_{Proj A}(n)`.

## Main results

* `Stacks.ProjMorphismRatios.awayToSection_smul_homogeneousSection`: `w / 1 = (w / v) · (v / 1)`
  on `D₊(v)`.
* `Stacks.ProjMorphismRatios.smul_value_pullbackSection`: the pulled-back ratio identity
  `α^♯(w / v)(x) · s_v(x) = s_w(x)`.
* `Stacks.ProjMorphismRatios.mem_nonvanishingLocus_pullbackSection`: `s_v` does not vanish at
  any point of `α⁻¹ D₊(v)`.
* `Stacks.ProjMorphismRatios.exists_eq_mk_of_mem_degreeOne`: on `D₊(f)`, for `f` of degree one,
  a global section of `𝒪(n)` is a single fraction `a / f ^ N`.
* `Stacks.ProjMorphismRatios.exists_pow_mul_sub_eq_zero`: two such fractions on `D₊(f)` and
  `D₊(g)` agree after a power of `f g`.
* `Stacks.ProjMorphismRatios.notMem_of_mem_nonvanishingLocus`: if a global section of `𝒪(n)` is
  the fraction `a / f ^ N` on `D₊(f)` and does not vanish at a point `x ∈ D₊(f)`, then `a ∉ x`.
* `Stacks.ProjMorphismRatios.stalkMap_comp_eq_of_ratio`: the stalk map of `α` is determined by
  the ratios of the sections `s_w`, and
  `Stacks.ProjMorphismRatios.spec_comp_eq_of_ratio`: **the two composites with `α` agree.**

## Implementation notes

The fibre of `𝒪(n)` at `x` is the ungraded localization `A_x` of the regular module, and a
section is literally a function into these fibres, so the ratio identity is an identity in
`A_x` read off pointwise; the structure sheaf acts on sections through the value map into the
degree-zero localization, and that action is pointwise multiplication there.

## References

* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite HomogeneousLocalization
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

namespace Stacks.ProjMorphismRatios

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {B : Type u} {τ : Type u} [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  (ℬ : ℕ → τ) [GradedRing ℬ]

/-- The homogeneous ideal of a point of `Proj 𝒜` is prime. -/
local instance (x : AlgebraicGeometry.Proj 𝒜) : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime

/-- **The global section `s_w` of `𝒪_{Proj A}(n)` attached to `w ∈ B₁`**: the canonical section
`w / 1` of `𝒪_{Proj B}(1)`, pulled back along `α` and read through `e`. -/
def pullbackSection {n : ℤ} {α : AlgebraicGeometry.Proj 𝒜 ⟶ AlgebraicGeometry.Proj ℬ}
    (e : Stacks.ProjTwistSection.twistingModule 𝒜 n ≅
      (Scheme.Modules.pullback α).obj (Stacks.ProjTwistSection.twistingModule ℬ 1))
    (w : B) (hw : w ∈ ℬ 1) : Γ(Stacks.ProjTwistSection.twistingModule 𝒜 n, ⊤) :=
  e.inv.app ⊤ (Stacks.NonvanishingPullback.pullbackGlobalSection α _
    ((Stacks.ProjTwistSection.homogeneousSection ℬ w hw).eval (op ⊤)))

/-- The canonical section `w / 1` of `𝒪_{Proj B}(1)` attached to `w ∈ B₁`, over an open `U`. -/
def homogeneousSectionOn (w : B) (hw : w ∈ ℬ 1) (U : (AlgebraicGeometry.Proj ℬ).Opens) :
    Γ(Stacks.ProjTwistSection.twistingModule ℬ 1, U) :=
  (Stacks.ProjTwistSection.homogeneousSection ℬ w hw).eval (op U)

/-- The value at a point `y ∈ D₊(f)` of the image of the ratio `a / f ^ m` in `Γ(D₊(f), 𝒪)` is
the fraction `a / f ^ m` in the localization at `y`. -/
private theorem val_awayToSection_mk {f : A} (hf : f ∈ 𝒜 1) (m : ℕ) (a : A)
    (ha : a ∈ 𝒜 (m • 1)) (y : Proj.basicOpen 𝒜 f) :
    HomogeneousLocalization.val
        (((AlgebraicGeometry.Proj.awayToSection 𝒜 f).hom (Away.mk 𝒜 hf m a ha)).1 y) =
      (Localization.mk a ⟨f ^ m, y.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem y.2 m⟩ :
        Localization y.1.asHomogeneousIdeal.toIdeal.primeCompl) := rfl

/-- On `D₊(v)` the canonical section `w / 1` of `𝒪(1)` is `(w / v) · (v / 1)`. -/
theorem awayToSection_smul_homogeneousSection {v w : B} (hv : v ∈ ℬ 1) (hw : w ∈ ℬ 1) :
    (AlgebraicGeometry.Proj.awayToSection ℬ v).hom (Away.mk ℬ hv 1 w (by simpa using hw)) •
        homogeneousSectionOn ℬ v hv (Proj.basicOpen ℬ v) =
      homogeneousSectionOn ℬ w hw (Proj.basicOpen ℬ v) := by
  apply Subtype.ext
  funext x
  have := x.1.isPrime
  have hvx : v ∈ x.1.asHomogeneousIdeal.toIdeal.primeCompl := x.2
  change HomogeneousLocalization.val
      (((AlgebraicGeometry.Proj.awayToSection ℬ v).hom
        (Away.mk ℬ hv 1 w (by simpa using hw))).1 x) *
      Localization.mk v (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl)
    = Localization.mk w (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl)
  rw [val_awayToSection_mk ℬ hv 1 w (by simpa using hw) x, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp [pow_one]; ring⟩

variable {𝒜 ℬ}

/-- The restriction of `s_w` to `α⁻¹ D₊(v)` is the pullback of the restriction of `w / 1` to
`D₊(v)`, read through `e`. -/
theorem map_pullbackSection {n : ℤ} {α : AlgebraicGeometry.Proj 𝒜 ⟶ AlgebraicGeometry.Proj ℬ}
    (e : Stacks.ProjTwistSection.twistingModule 𝒜 n ≅
      (Scheme.Modules.pullback α).obj (Stacks.ProjTwistSection.twistingModule ℬ 1))
    (w : B) (hw : w ∈ ℬ 1) (U : (AlgebraicGeometry.Proj ℬ).Opens) :
    (Stacks.ProjTwistSection.twistingModule 𝒜 n).presheaf.map
        (homOfLE (le_top : α ⁻¹ᵁ U ≤ ⊤)).op (pullbackSection 𝒜 ℬ e w hw) =
      e.inv.app (α ⁻¹ᵁ U) (pullbackSectionHom α (Stacks.ProjTwistSection.twistingModule ℬ 1)
        U (α ⁻¹ᵁ U) le_rfl (homogeneousSectionOn ℬ w hw U)) := by
  refine (Stacks.AlgebraicGeometry.ProjChartRatioPullback.app_map e.inv
    (homOfLE (le_top : α ⁻¹ᵁ U ≤ ⊤)) _).symm.trans (congrArg (fun z => e.inv.app (α ⁻¹ᵁ U) z) ?_)
  have h1 := Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullbackSectionHom_top α
    (Stacks.ProjTwistSection.twistingModule ℬ 1) (homogeneousSectionOn ℬ w hw ⊤)
  have h2 := Stacks.AlgebraicGeometry.ProjChartRatioPullback.map_pullbackSectionHom α
    (Stacks.ProjTwistSection.twistingModule ℬ 1) ⊤ ⊤ (α ⁻¹ᵁ U) (homOfLE le_top)
    (Stacks.AlgebraicGeometry.ProjChartRatioPullback.top_le_preimage_top α)
    (le_top.trans (Stacks.AlgebraicGeometry.ProjChartRatioPullback.top_le_preimage_top α))
    (homogeneousSectionOn ℬ w hw ⊤)
  have h3 := pullbackSectionHom_map α (Stacks.ProjTwistSection.twistingModule ℬ 1) ⊤ U le_top
    (α ⁻¹ᵁ U) le_rfl
    (le_top.trans (Stacks.AlgebraicGeometry.ProjChartRatioPullback.top_le_preimage_top α))
    (homogeneousSectionOn ℬ w hw ⊤)
  have h4 : (Stacks.ProjTwistSection.twistingModule ℬ 1).val.map (homOfLE (le_top : U ≤ ⊤)).op
      (homogeneousSectionOn ℬ w hw ⊤) = homogeneousSectionOn ℬ w hw U :=
    PresheafOfModules.sections_property _ _
  rw [h4] at h3
  rw [show Stacks.NonvanishingPullback.pullbackGlobalSection α
      (Stacks.ProjTwistSection.twistingModule ℬ 1)
      ((Stacks.ProjTwistSection.homogeneousSection ℬ w hw).eval (op ⊤)) = _ from h1.symm]
  exact h2.trans h3.symm

/-- **The pulled-back ratio identity.** At a point `x` of `Proj A` with `α(x) ∈ D₊(v)`, the value
at `x` of the pullback of the function `w / v` on `D₊(v)` carries `s_v(x)` to `s_w(x)`. -/
theorem smul_value_pullbackSection {n : ℤ}
    {α : AlgebraicGeometry.Proj 𝒜 ⟶ AlgebraicGeometry.Proj ℬ}
    (e : Stacks.ProjTwistSection.twistingModule 𝒜 n ≅
      (Scheme.Modules.pullback α).obj (Stacks.ProjTwistSection.twistingModule ℬ 1))
    {v w : B} (hv : v ∈ ℬ 1) (hw : w ∈ ℬ 1) (x : AlgebraicGeometry.Proj 𝒜)
    (hx : x ∈ α ⁻¹ᵁ Proj.basicOpen ℬ v) :
    ((α.appLE (Proj.basicOpen ℬ v) (α ⁻¹ᵁ Proj.basicOpen ℬ v) le_rfl
        ((AlgebraicGeometry.Proj.awayToSection ℬ v).hom
          (Away.mk ℬ hv 1 w (by simpa using hw)))).1 ⟨x, hx⟩).val •
        (pullbackSection 𝒜 ℬ e v hv).1 ⟨x, trivial⟩ =
      (pullbackSection 𝒜 ℬ e w hw).1 ⟨x, trivial⟩ := by
  have hrel := congrArg (fun z => e.inv.app (α ⁻¹ᵁ Proj.basicOpen ℬ v)
      (pullbackSectionHom α (Stacks.ProjTwistSection.twistingModule ℬ 1)
        (Proj.basicOpen ℬ v) (α ⁻¹ᵁ Proj.basicOpen ℬ v) le_rfl z))
    (awayToSection_smul_homogeneousSection ℬ hv hw)
  simp only [pullbackSectionHom_smul, Scheme.Modules.Hom.app_smul] at hrel
  rw [← map_pullbackSection, ← map_pullbackSection] at hrel
  exact congrArg (fun z => z.1 ⟨x, hx⟩) hrel

/-- **`s_v` does not vanish on `α⁻¹ D₊(v)`**: the section `v / 1` does not vanish on `D₊(v)`,
nonvanishing loci pull back to nonvanishing loci (Stacks Tag 0H78), and they are unchanged by an
isomorphism of modules. -/
theorem mem_nonvanishingLocus_pullbackSection
    (hgen : Algebra.adjoin (ℬ 0) ((ℬ 1 : Set B)) = ⊤) {n : ℤ}
    {α : AlgebraicGeometry.Proj 𝒜 ⟶ AlgebraicGeometry.Proj ℬ}
    (e : Stacks.ProjTwistSection.twistingModule 𝒜 n ≅
      (Scheme.Modules.pullback α).obj (Stacks.ProjTwistSection.twistingModule ℬ 1))
    {v : B} (hv : v ∈ ℬ 1) (x : AlgebraicGeometry.Proj 𝒜)
    (hx : x ∈ α ⁻¹ᵁ Proj.basicOpen ℬ v) :
    x ∈ Stacks.Ample.nonvanishingLocus (Stacks.ProjTwistSection.twistingModule 𝒜 n)
      (pullbackSection 𝒜 ℬ e v hv) := by
  let : Stacks.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj ℬ).presheaf
      (structureSheafRing (AlgebraicGeometry.Proj ℬ).toRingedSpace).property
      (Stacks.ProjTwistSection.twistingModule ℬ 1) :=
    Stacks.AlgebraicGeometry.ProjDegreeOne.isInvertible_twistingSheaf ℬ hgen 1
  have hQ : α.base x ∈ Stacks.Ample.nonvanishingLocus
      (Stacks.ProjTwistSection.twistingModule ℬ 1)
      ((Stacks.ProjTwistSection.homogeneousSection ℬ v hv).eval (op ⊤)) :=
    (Set.ext_iff.mp (Stacks.SchemeModulesSpelling.nonvanishingLocus_eq
      (AlgebraicGeometry.Proj ℬ) (Stacks.ProjTwistSection.twistingModule ℬ 1)
      (Stacks.ProjTwistSection.homogeneousSection ℬ v hv)) (α.base x)).mp
      (Stacks.ProjTwistSection.basicOpen_le_nonvanishingOpen_homogeneousSection ℬ v hv hx)
  have h0 := (Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff α
    (Stacks.ProjTwistSection.twistingModule ℬ 1)
    ((Stacks.ProjTwistSection.homogeneousSection ℬ v hv).eval (op ⊤)) x).mpr hQ
  have h1 := Stacks.Ample.nonvanishingLocus_congr e.symm
    (Stacks.NonvanishingPullback.pullbackGlobalSection α
      (Stacks.ProjTwistSection.twistingModule ℬ 1)
      ((Stacks.ProjTwistSection.homogeneousSection ℬ v hv).eval (op ⊤)))
  exact (Set.ext_iff.mp h1 x).mpr h0

omit [AddSubgroupClass τ B] [GradedRing ℬ] in
/-- **A section that is the fraction `a / f ^ N` on `D₊(f)` and does not vanish at `x ∈ D₊(f)`
has `a ∉ x`.** On `D₊(f)` the section is `(a / f ^ m) · (f ^ m / f ^ N)`, and if `a ∈ x` the
function `a / f ^ m` lies in the maximal ideal of the stalk at `x`. -/
theorem notMem_of_mem_nonvanishingLocus {n : ℤ} {f : A} (hf : f ∈ 𝒜 1)
    (t : Γ(Stacks.ProjTwistSection.twistingModule 𝒜 n, ⊤)) {N m : ℕ} (hm : (m : ℤ) = N + n)
    {a : A} (ha : a ∈ 𝒜 m)
    (hval : ∀ (y : AlgebraicGeometry.Proj 𝒜) (hy : f ∉ y.asHomogeneousIdeal),
      t.1 ⟨y, trivial⟩ = LocalizedModule.mk a
        ⟨f ^ N, y.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hy N⟩)
    (x : AlgebraicGeometry.Proj 𝒜) (hx : f ∉ x.asHomogeneousIdeal)
    (hnv : x ∈ Stacks.Ample.nonvanishingLocus (Stacks.ProjTwistSection.twistingModule 𝒜 n) t) :
    a ∉ x.asHomogeneousIdeal := by
  intro hax
  apply hnv
  set U : (AlgebraicGeometry.Proj 𝒜).Opens := Proj.basicOpen 𝒜 f
  have hxU : x ∈ U := hx
  have ha' : a ∈ 𝒜 (m • 1) := by simpa using ha
  set r : Γ(AlgebraicGeometry.Proj 𝒜, U) :=
    (AlgebraicGeometry.Proj.awayToSection 𝒜 f).hom (Away.mk 𝒜 hf m a ha')
  have hfm : f ^ m ∈ twistGrading 𝒜 n (N • ((1 : ℕ) : ℤ)) := by
    have h0 : (0 : ℤ) ≤ N • ((1 : ℕ) : ℤ) + n := by simp; omega
    have h1 : (N • ((1 : ℕ) : ℤ) + n).toNat = m := by simp; omega
    simp only [twistGrading, integerGrading, h0, ite_true, h1]
    simpa using SetLike.pow_mem_graded m hf
  set g : Γ(Stacks.ProjTwistSection.twistingModule 𝒜 n, U) :=
    degreeZeroToSection 𝒜 (twistGrading 𝒜 n) f
      (degreeZeroFraction 𝒜 (twistGrading 𝒜 n) hf N (f ^ m) hfm)
  have hres : (Stacks.ProjTwistSection.twistingModule 𝒜 n).presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op t = r • g := by
    apply Subtype.ext
    funext y
    have := y.1.isPrime
    change t.1 ⟨y.1, trivial⟩ = HomogeneousLocalization.val (r.1 y) • g.1 y
    rw [hval y.1 y.2]
    have hg : g.1 y = (LocalizedModule.mk (f ^ m)
        ⟨f ^ N, y.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem y.2 N⟩ :
          LocalizedModule y.1.asHomogeneousIdeal.toIdeal.primeCompl A) :=
      degreeZeroToSection_fraction 𝒜 (twistGrading 𝒜 n) hf N (f ^ m) hfm y
    rw [show HomogeneousLocalization.val (r.1 y) = _ from val_awayToSection_mk 𝒜 hf m a ha' y,
      hg, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def, smul_eq_mul, Submonoid.coe_mul]
    ring
  have hgerm := Stacks.ModuleStalk.germ_smul (Stacks.ProjTwistSection.twistingModule 𝒜 n) x U
    hxU r g
  rw [← hres] at hgerm
  have hΓ : ((Stacks.ProjTwistSection.twistingModule 𝒜 n).presheaf.Γgerm x).hom t =
      ((Stacks.ProjTwistSection.twistingModule 𝒜 n).presheaf.germ U x hxU).hom
        ((Stacks.ProjTwistSection.twistingModule 𝒜 n).presheaf.map
          (homOfLE (le_top : U ≤ ⊤)).op t) :=
    (TopCat.Presheaf.germ_res_apply _ (homOfLE (le_top : U ≤ ⊤)) x hxU t).symm
  change ((Stacks.ProjTwistSection.twistingModule 𝒜 n).presheaf.Γgerm x).hom t ∈
    Stacks.ModuleStalk.maximalSmul _ x
  rw [hΓ, hgerm]
  refine Stacks.ModuleStalk.smul_mem_maximalSmul_of_mem_maximalIdeal ?_ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hunit
  have hu := hunit.map (Proj.stalkIso' 𝒜 x).toRingHom
  have hval' : (Proj.stalkIso' 𝒜 x).toRingHom
      (((AlgebraicGeometry.Proj 𝒜).presheaf.germ U x hxU).hom r) =
      r.1 ⟨x, hxU⟩ := Proj.stalkIso'_germ 𝒜 U x hxU r
  have hu2 : IsUnit (r.1 ⟨x, hxU⟩) := by
    convert hu using 1
    exact hval'.symm
  have hu' := hu2.map (algebraMap (AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal)
    (Localization x.asHomogeneousIdeal.toIdeal.primeCompl))
  rw [HomogeneousLocalization.algebraMap_apply] at hu'
  change IsUnit (Localization.mk a ⟨f ^ m, _⟩) at hu'
  rw [Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff] at hu'
  exact hu' hax

omit [AddSubgroupClass τ B] [GradedRing ℬ] in
/-- **On a degree-one standard open a global section of `𝒪(n)` is one fraction.** For `f ∈ A₁`
and a global section `t` of `𝒪(n)` there are `N`, `m` with `m = N + n` and `a ∈ A_m` such that
`t(y) = a / f ^ N` at every point `y ∈ D₊(f)`. -/
theorem exists_eq_mk_of_mem_degreeOne {n : ℤ} {f : A} (hf : f ∈ 𝒜 1)
    (t : Γ(Stacks.ProjTwistSection.twistingModule 𝒜 n, ⊤)) :
    ∃ (N m : ℕ) (a : A), (m : ℤ) = N + n ∧ a ∈ 𝒜 m ∧
      ∀ (y : AlgebraicGeometry.Proj 𝒜) (hy : f ∉ y.asHomogeneousIdeal),
        t.1 ⟨y, trivial⟩ = LocalizedModule.mk a
          ⟨f ^ N, y.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hy N⟩ := by
  set U : (AlgebraicGeometry.Proj 𝒜).Opens := Proj.basicOpen 𝒜 f
  obtain ⟨z, hz⟩ := degreeZeroToSection_surjective 𝒜 (twistGrading 𝒜 n) hf one_pos
    ((Stacks.ProjTwistSection.twistingModule 𝒜 n).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t)
  obtain ⟨N, a, ha, hza⟩ :=
    Stacks.SheafOfModules.degreeZeroLocalization_exists_fraction 𝒜 (twistGrading 𝒜 n) hf z
  have hval : ∀ (y : AlgebraicGeometry.Proj 𝒜) (hy : f ∉ y.asHomogeneousIdeal),
      t.1 ⟨y, trivial⟩ = LocalizedModule.mk a
        ⟨f ^ N, y.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hy N⟩ := by
    intro y hy
    have h := congrArg (fun s => s.1 ⟨y, hy⟩) hz
    change moduleToFiber 𝒜 f ⟨y, hy⟩ z.1 = t.1 ⟨y, trivial⟩ at h
    rw [← h, hza, moduleToFiber_mk]
  by_cases hN : 0 ≤ (N : ℤ) + n
  · refine ⟨N, ((N : ℤ) + n).toNat, a, by omega, ?_, hval⟩
    simpa [twistGrading, integerGrading, hN] using ha
  · have ha0 : a = 0 := by
      have : a ∈ (⊥ : Submodule ℤ A) := by simpa [twistGrading, integerGrading, hN] using ha
      simpa using this
    refine ⟨N + (-((N : ℤ) + n)).toNat, 0, 0, by omega, zero_mem _, fun y hy => ?_⟩
    rw [hval y hy, ha0, LocalizedModule.zero_mk, LocalizedModule.zero_mk]

omit [AddSubgroupClass τ B] [GradedRing ℬ] in
/-- **Two fractions representing one section agree after a power of `f g`.** If a global section
of `𝒪(n)` is `a / f ^ N` on `D₊(f)` and `b / g ^ M` on `D₊(g)`, for `f, g ∈ A₁`, then
`(f g) ^ K (g ^ M a - f ^ N b) = 0` for some `K`. -/
theorem exists_pow_mul_sub_eq_zero {n : ℤ} {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (t : Γ(Stacks.ProjTwistSection.twistingModule 𝒜 n, ⊤)) {N M m m' : ℕ}
    (hm : (m : ℤ) = N + n) (hm' : (m' : ℤ) = M + n) {a b : A} (ha : a ∈ 𝒜 m) (hb : b ∈ 𝒜 m')
    (hfa : ∀ (y : AlgebraicGeometry.Proj 𝒜) (hy : f ∉ y.asHomogeneousIdeal),
      t.1 ⟨y, trivial⟩ = LocalizedModule.mk a
        ⟨f ^ N, y.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hy N⟩)
    (hgb : ∀ (y : AlgebraicGeometry.Proj 𝒜) (hy : g ∉ y.asHomogeneousIdeal),
      t.1 ⟨y, trivial⟩ = LocalizedModule.mk b
        ⟨g ^ M, y.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hy M⟩) :
    ∃ K : ℕ, (f * g) ^ K * (g ^ M * a - f ^ N * b) = 0 := by
  have hδ : g ^ M * a - f ^ N * b ∈ 𝒜 (M + m) := by
    refine sub_mem (SetLike.mul_mem_graded (by simpa using SetLike.pow_mem_graded M hg) ha) ?_
    rw [show M + m = N + m' by omega]
    exact SetLike.mul_mem_graded (by simpa using SetLike.pow_mem_graded N hf) hb
  refine ProjectiveSpectrum.exists_pow_mul_eq_zero_of_forall_mem_basicOpen (m := 2)
    two_pos (by simpa [two_mul] using SetLike.mul_mem_graded hf hg) hδ fun y hy => ?_
  have hfy : f ∉ y.asHomogeneousIdeal := fun h => hy (Ideal.mul_mem_right _ _ h)
  have hgy : g ∉ y.asHomogeneousIdeal := fun h => hy (Ideal.mul_mem_left _ _ h)
  obtain ⟨c, hc⟩ := LocalizedModule.mk_eq.mp ((hfa y hfy).symm.trans (hgb y hgy))
  refine ⟨c, c.2, ?_⟩
  simp only [Submonoid.smul_def, smul_eq_mul] at hc
  linear_combination hc

/-- **A ring homomorphism out of a stalk of `Proj B` is determined on a degree-one chart.** Two
ring homomorphisms out of the stalk of `Proj B` at `Q ∈ D₊(v)`, for `v ∈ B₁`, are equal as soon as
they agree on the image of `B_{(v)}`, since that stalk is a localization of `B_{(v)}`. -/
private theorem stalk_hom_ext_of_away {Q : AlgebraicGeometry.Proj ℬ} {v : B} (hv : v ∈ ℬ 1)
    (hQ : Q ∈ Proj.basicOpen ℬ v) {R : CommRingCat.{u}}
    {φ₁ φ₂ : (AlgebraicGeometry.Proj ℬ).presheaf.stalk Q ⟶ R}
    (h : φ₁.hom.comp (((AlgebraicGeometry.Proj ℬ).presheaf.germ (Proj.basicOpen ℬ v) Q hQ).hom.comp
        (AlgebraicGeometry.Proj.awayToSection ℬ v).hom) =
      φ₂.hom.comp (((AlgebraicGeometry.Proj ℬ).presheaf.germ (Proj.basicOpen ℬ v) Q hQ).hom.comp
        (AlgebraicGeometry.Proj.awayToSection ℬ v).hom)) :
    φ₁ = φ₂ := by
  have hvQ : v ∉ Q.asHomogeneousIdeal := hQ
  have hvQ' : v ∈ Q.asHomogeneousIdeal.toIdeal.primeCompl := hvQ
  let _inst : Algebra (Away ℬ v) (AtPrime ℬ Q.asHomogeneousIdeal.toIdeal) :=
    (HomogeneousLocalization.mapId ℬ (Submonoid.powers_le.mpr hvQ')).toAlgebra
  have _hp : ((AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec ℬ v).base
      ⟨Q, hvQ⟩).asIdeal.IsPrime :=
    ((AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec ℬ v).base ⟨Q, hvQ⟩).isPrime
  have _hloc : @IsLocalization (Away ℬ v) _
      ((AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec ℬ v).base ⟨Q, hvQ⟩).asIdeal.primeCompl
      (AtPrime ℬ Q.asHomogeneousIdeal.toIdeal) _ _inst :=
    AlgebraicGeometry.ProjectiveSpectrum.Proj.isLocalization_atPrime ℬ v ⟨Q, hvQ⟩ hv one_pos
  have hj : φ₁.hom.comp (Proj.stalkIso' ℬ Q).symm.toRingHom =
      φ₂.hom.comp (Proj.stalkIso' ℬ Q).symm.toRingHom := by
    refine IsLocalization.ringHom_ext
      ((AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec ℬ v).base ⟨Q, hvQ⟩).asIdeal.primeCompl
      (RingHom.ext fun w => ?_)
    have hgerm := congrArg (fun φ => φ.hom w)
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.awayToSection_germ ℬ v Q hvQ)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hgerm
    simp only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
    change φ₁.hom ((Proj.stalkIso' ℬ Q).symm (HomogeneousLocalization.mapId ℬ _ w)) =
      φ₂.hom ((Proj.stalkIso' ℬ Q).symm (HomogeneousLocalization.mapId ℬ _ w))
    have h2 : (Proj.stalkIso' ℬ Q).symm (HomogeneousLocalization.mapId ℬ _ w) =
        ((AlgebraicGeometry.Proj ℬ).presheaf.germ (Proj.basicOpen ℬ v) Q hQ).hom
          ((AlgebraicGeometry.Proj.awayToSection ℬ v).hom w) := hgerm.symm
    rw [h2]
    exact congrArg (fun φ => φ w) h
  ext z
  obtain ⟨z, rfl⟩ := (Proj.stalkIso' ℬ Q).symm.surjective z
  exact congrArg (fun φ => φ z) hj

/-- **The stalk map of `α` is determined by the ratios of the sections `s_w`.** Let `x` be a point
of `Proj A` and let `χ₁, χ₂` be ring homomorphisms out of the stalk of `Proj A` at `x`. If they
agree on every element `r` of the stalk solving `r · t(x) = s(x)` for global sections `s`, `t` of
`𝒪(n)` with `t` not vanishing at `x`, then `χ₁ ∘ α_x = χ₂ ∘ α_x` on the stalk of `Proj B` at
`α(x)`. -/
theorem stalkMap_comp_eq_of_ratio (hgen : Algebra.adjoin (ℬ 0) ((ℬ 1 : Set B)) = ⊤) {n : ℤ}
    {α : AlgebraicGeometry.Proj 𝒜 ⟶ AlgebraicGeometry.Proj ℬ}
    (e : Stacks.ProjTwistSection.twistingModule 𝒜 n ≅
      (Scheme.Modules.pullback α).obj (Stacks.ProjTwistSection.twistingModule ℬ 1))
    (x : AlgebraicGeometry.Proj 𝒜) {R : CommRingCat.{u}}
    (χ₁ χ₂ : (AlgebraicGeometry.Proj 𝒜).presheaf.stalk x ⟶ R)
    (H : ∀ s t : Γ(Stacks.ProjTwistSection.twistingModule 𝒜 n, ⊤),
      x ∈ Stacks.Ample.nonvanishingLocus (Stacks.ProjTwistSection.twistingModule 𝒜 n) t →
      ∀ r : AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal,
        r.val • t.1 ⟨x, trivial⟩ = s.1 ⟨x, trivial⟩ →
          χ₁ ((Proj.stalkIso' 𝒜 x).symm r) = χ₂ ((Proj.stalkIso' 𝒜 x).symm r)) :
    α.stalkMap x ≫ χ₁ = α.stalkMap x ≫ χ₂ := by
  obtain ⟨v, hv, hvQ⟩ :=
    AlgebraicGeometry.ProjectiveSpectrum.Proj.exists_mem_degreeOne_notMem ℬ hgen
    (α.base x).not_irrelevant_le
  have hxv : x ∈ α ⁻¹ᵁ Proj.basicOpen ℬ v := hvQ
  have hQv : α.base x ∈ Proj.basicOpen ℬ v := hvQ
  let Φ : ((AlgebraicGeometry.Proj 𝒜).presheaf.stalk x ⟶ R) → (Away ℬ v →+* R) := fun χ =>
    (α.stalkMap x ≫ χ).hom.comp (((AlgebraicGeometry.Proj ℬ).presheaf.germ
      (Proj.basicOpen ℬ v) (α.base x) hQv).hom.comp
        (AlgebraicGeometry.Proj.awayToSection ℬ v).hom)
  have hΦ : Φ χ₁ = Φ χ₂ := by
    refine HomogeneousLocalization.Away.ringHom_ext_of_adjoin_degreeOne hv hgen fun w hw' => ?_
    have hw : w ∈ ℬ 1 := by simpa using hw'
    have key : ∀ χ : (AlgebraicGeometry.Proj 𝒜).presheaf.stalk x ⟶ R,
        Φ χ (Away.mk ℬ hv 1 w hw') = χ ((Proj.stalkIso' 𝒜 x).symm
          ((α.appLE (Proj.basicOpen ℬ v) (α ⁻¹ᵁ Proj.basicOpen ℬ v) le_rfl
            ((AlgebraicGeometry.Proj.awayToSection ℬ v).hom
              (Away.mk ℬ hv 1 w (by simpa using hw)))).1 ⟨x, hxv⟩)) := by
      intro χ
      change χ (α.stalkMap x (((AlgebraicGeometry.Proj ℬ).presheaf.germ
        (Proj.basicOpen ℬ v) (α.base x) hQv).hom
          ((AlgebraicGeometry.Proj.awayToSection ℬ v).hom (Away.mk ℬ hv 1 w hw')))) = _
      rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.app_eq_appLE]
      congr 1
      exact ((Proj.stalkIso' 𝒜 x).symm_apply_apply _).symm.trans
        (congrArg (Proj.stalkIso' 𝒜 x).symm (Proj.stalkIso'_germ 𝒜 _ x hxv _))
    rw [key, key]
    exact H _ _ (mem_nonvanishingLocus_pullbackSection hgen e hv x hxv) _
      (smul_value_pullbackSection e hv hw x hxv)
  exact stalk_hom_ext_of_away hv hQv hΦ

/-- **Two morphisms `Spec R ⟶ Proj A` through `x` have the same composite with `α`** as soon as
the two homomorphisms out of the stalk at `x` defining them agree on the ratios `s / t` of global
sections of `𝒪(n)` with `t` not vanishing at `x`. -/
theorem spec_comp_eq_of_ratio (hgen : Algebra.adjoin (ℬ 0) ((ℬ 1 : Set B)) = ⊤) {n : ℤ}
    {α : AlgebraicGeometry.Proj 𝒜 ⟶ AlgebraicGeometry.Proj ℬ}
    (e : Stacks.ProjTwistSection.twistingModule 𝒜 n ≅
      (Scheme.Modules.pullback α).obj (Stacks.ProjTwistSection.twistingModule ℬ 1))
    (x : AlgebraicGeometry.Proj 𝒜) {R : CommRingCat.{u}}
    (χ₁ χ₂ : (AlgebraicGeometry.Proj 𝒜).presheaf.stalk x ⟶ R)
    (H : ∀ s t : Γ(Stacks.ProjTwistSection.twistingModule 𝒜 n, ⊤),
      x ∈ Stacks.Ample.nonvanishingLocus (Stacks.ProjTwistSection.twistingModule 𝒜 n) t →
      ∀ r : AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal,
        r.val • t.1 ⟨x, trivial⟩ = s.1 ⟨x, trivial⟩ →
          χ₁ ((Proj.stalkIso' 𝒜 x).symm r) = χ₂ ((Proj.stalkIso' 𝒜 x).symm r)) :
    (Spec.map χ₁ ≫ (AlgebraicGeometry.Proj 𝒜).fromSpecStalk x) ≫ α =
      (Spec.map χ₂ ≫ (AlgebraicGeometry.Proj 𝒜).fromSpecStalk x) ≫ α := by
  simp only [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk]
  rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp,
    stalkMap_comp_eq_of_ratio hgen e x χ₁ χ₂ H]

end Stacks.ProjMorphismRatios

end
