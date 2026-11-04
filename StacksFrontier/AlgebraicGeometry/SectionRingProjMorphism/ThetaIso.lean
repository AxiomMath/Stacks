module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjMorphism.Theta
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedThetaMoreover
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedTriple
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistTensorPowDegreeOpen
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistMono.Trivialized
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.LocalOnBase
public import StacksFrontier.AlgebraicGeometry.SectionRingProjTwistIso.TensorCancel
public import StacksFrontier.AlgebraicGeometry.VeryAmpleGlue.TwistPullback

/-!
# The twisting maps of Stacks Tag 01NK in a divisible degree are isomorphisms

Let `A` be a graded ring, `X = Proj A`, `T` a scheme, `L` an invertible `𝒪_T`-module and
`ψ : A → Γ_*(T, L)` a graded map, with morphism `r_{L, ψ} : U(ψ) ⟶ X` and map of `ℤ`-graded
algebras `θ : r_{L, ψ}^*(⨁_n 𝒪_X(n)) ⟶ ⨁_n L^{⊗ n}|_{U(ψ)}` as in [Stacks, Tag 01NK]. On an open
`V` where `ψ(A_d)` generates `L^{⊗ d}`, the degree-`d` component of `θ|_V` is an isomorphism; on an
open inside `T_{ψ(f)}` for a homogeneous `f` of degree `d ≥ 1`, so is its degree-`d m` component
for every `m ∈ ℤ`. This gives clause (4) of [Stacks, Tag 01PZ].

## Main definitions

* `Stacks.AlgebraicGeometry.ProjChartGradedDivision.intPowFraction`: the fraction
  `f ^ m⁺ / f ^ m⁻`, a degree-`d m` element of `A_f` for every integer `m`.

## Main results

* `Stacks.AlgebraicGeometry.ProjChartGradedThetaIso.isIso_pullback_theta_app`: the degree-`d`
  component of `θ`, pulled back to an open `V` on which `ψ(A_d)` generates `L^{⊗ d}`, is an
  isomorphism, for every `d ≥ 1`.
* `Stacks.AlgebraicGeometry.ProjChartGradedThetaIso.isIso_pullback_theta_app_mul`: the same in
  every degree `m d` with `m ≥ 1`, on an open inside a single `T_{ψ(f)}` for one homogeneous `f`
  of degree `d`.
* `Stacks.AlgebraicGeometry.ProjChartGradedThetaIso.isIso_pullback_theta_app_intMul`: the same in
  every degree `d m` with `m ∈ ℤ`, on that same open.
* `Stacks.SectionRingProjMorphism.Theta.isIso_pullback_projTheta_app_mul`,
  `Stacks.SectionRingProjMorphism.Theta.exists_isIso_pullback_projTheta_app_mul`,
  `Stacks.SectionRingProjMorphism.Theta.isIso_pullback_projTheta_app_intMul` and
  `Stacks.SectionRingProjMorphism.Theta.exists_isIso_pullback_projTheta_app_intMul`: the same
  statements for the canonical morphism of [Stacks, Tag 01PZ], the `exists_` ones in pointwise
  form.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open Stacks.GradedSections (powSections)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowers (natTensorPow)
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild (theta)
open Stacks.AlgebraicGeometry.ProjChartGradedThetaMoreover (moreover)
open Stacks.MorphismToProj.HomogeneousRatios (pow_mem)
open Stacks.SectionRingGluedComparison (canonicalSections coveringOpen_canonicalSections
  nonvanishingOpen_canonicalSections_of)
open Opposite
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.NonvanishingLocusRestrict (nonvanishingLocusOn)
open Stacks.TensorPowerTrivialize (resTop)
open Stacks.GradedLocalization (gradedPiece)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading)
open Stacks.AlgebraicGeometry.ProjChartGradedTheta (twistM)
open Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild (laurentRestrict)
open Stacks.AlgebraicGeometry.SectionsBaseChange (pullbackUnitSections)
open Stacks.AlgebraicGeometry.ProjTwistAwayPiece (sectionsTwistEquivGradedPiece)
open Stacks.AlgebraicGeometry.ProjChartGradedDivision (intChartSection intChartSection_mk
  intChartSectionOf intValue le_nonvanishingOpen_intValue le_nonvanishingOpen_intValue_pow)

universe u w

/-! ### The non-vanishing locus of a quotient of sections of integer tensor powers -/

namespace Stacks.TensorPowerDivision

section Divide

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-- **A quotient does not vanish exactly where its numerator does not.** The quotient `a / t` of
[Stacks, Tag 01CU]'s division, a section of `L ^⊗ n` over an open `V` inside the non-vanishing
open of `t`, has for non-vanishing locus the non-vanishing locus of `a` inside `V`. -/
theorem nonvanishingLocusOn_intDivTop {X : Scheme.{u}} (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {k : ℤ} (t : Γ(tensorPowerModule X L k, ⊤))
    {V : X.Opens} (hV : V ≤ nonvanishingOpen X (tensorPowerModule X L k) t) (n : ℤ)
    (a : Γ(tensorPowerModule X L (k + n), ⊤)) :
    nonvanishingLocusOn (tensorPowerModule X L n) V (intDivTop L t hV n a)
      = nonvanishingLocusOn (tensorPowerModule X L (k + n)) V
          (resTop (tensorPowerModule X L (k + n)) a V) := by
  have h1 : resTop (tensorPowerModule X L (k + n)) a V
      = localMul L (resTop (tensorPowerModule X L k) t V) (intDivTop L t hV n a) :=
    (mul_intDivTop L t hV n a).symm.trans (intMulMap_app_localMul L t n V _)
  rw [h1, Stacks.InvertibleTensorCancel.nonvanishingLocusOn_localMul L k n V]
  have h2 : nonvanishingLocusOn (tensorPowerModule X L k) V
      (resTop (tensorPowerModule X L k) t V) = (V : Set X) := by
    rw [Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_res (tensorPowerModule X L k)
      (le_top : V ≤ ⊤) t, Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_top]
    exact Set.inter_eq_self_of_subset_left hV
  rw [h2]
  exact (Set.inter_eq_self_of_subset_right
    (Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_subset _ _ _)).symm

end Divide

end Stacks.TensorPowerDivision

/-! ### Non-vanishing on an open subscheme, at an open presented as an image -/

namespace Stacks.NonvanishingLocusRestrict

/-- **Non-vanishing travels into an open subscheme**, for a section over an open of the ambient
scheme presented as the image of an open `W` of the subscheme: a section of `N|_U` over `W` that,
as a section of `N` over `U.ι ''ᵁ W`, does not vanish at `U.ι x`, does not vanish at `x`. -/
theorem mem_nonvanishingLocusOn_restrict_image {X : Scheme.{u}} (U : X.Opens) (N : X.Modules)
    (W : U.toScheme.Opens) (s : Γ(N.restrict U.ι, W)) (x : U.toScheme)
    (hx : U.ι.base x ∈ nonvanishingLocusOn N (U.ι ''ᵁ W) s) :
    x ∈ nonvanishingLocusOn (N.restrict U.ι) W s := by
  have hW : U.ι ⁻¹ᵁ (U.ι ''ᵁ W) ≤ W := (U.ι.preimage_image_eq W).le
  have h := Stacks.VeryAmpleGlue.mem_nonvanishingLocusOn_restrict U N (U.ι ''ᵁ W) s x hx
  have hres : (N.presheaf.map (homOfLE (U.ι.image_preimage_le (U.ι ''ᵁ W))).op).hom s
      = ((N.restrict U.ι).presheaf.map (homOfLE hW).op).hom s := rfl
  rw [hres, nonvanishingLocusOn_res] at h
  exact h.2

end Stacks.NonvanishingLocusRestrict

/-! ### The fraction `f ^ m⁺ / f ^ m⁻` and the non-vanishing of its chart value -/

namespace Stacks.AlgebraicGeometry.ProjChartGradedDivision

section IntPow

open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.MorphismToProj.HomogeneousRatios (pow_mem)

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)
  {d : ℕ} {f : A} {V : T.Opens} (hf : f ∈ 𝒜 d)
  (hV : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨f, hf⟩))

/-- **The chart value of a fraction with non-vanishing numerator does not vanish.** If the
degree-`n` element `y` of `A_f` is represented by `x / f ^ j` with `ψ(x)` non-vanishing on `V`, the
section `ψ(x) / ψ(f ^ j)` of `L ^⊗ n` over `V` does not vanish anywhere on `V`. -/
theorem le_nonvanishingLocusOn_intChartSection (hd : 0 < d) (n : ℤ)
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f n) (j e : ℕ)
    (he : ((j * d : ℕ) : ℤ) + n = (e : ℕ)) {x : A} (hx : x ∈ 𝒜 e)
    (hrep : (y : LocalizedModule.Away f A)
      = LocalizedModule.mk x (⟨f ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers f))
    (hxnv : V ≤ nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨x, hx⟩)) :
    (V : Set T) ⊆ nonvanishingLocusOn (tensorPowerModule T L n) V
      (intChartSection ψ hf hV hd n y) := by
  rw [intChartSection_mk ψ hf hV hd n y j e he x hx hrep]
  unfold intChartSectionOf
  rw [Stacks.TensorPowerDivision.nonvanishingLocusOn_intDivTop L _
      (le_nonvanishingOpen_intValue_pow ψ hf hV j) n,
    Stacks.TensorPowerTrivialize.resTop_app,
    Stacks.SectionPowerOverOpen.nonvanishingLocusOn_congr,
    Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_res (tensorPowerModule T L (e : ℤ))
      (le_top : V ≤ ⊤), Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_top]
  exact Set.subset_inter (fun _ h => h) (le_nonvanishingOpen_intValue ψ hx hxnv)

/-- The degree of the numerator of `f ^ m⁺ / f ^ m⁻`: `m⁻ d + d m = m⁺ d`, for every integer `m`,
where `m⁺ = m.toNat` and `m⁻ = (-m).toNat`. -/
private theorem toNat_mul_add_mul (d : ℕ) (m : ℤ) :
    (((-m).toNat * d : ℕ) : ℤ) + (d : ℤ) * m = ((m.toNat * d : ℕ) : ℤ) := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m <;> simp <;> ring

/-- **The fraction `f ^ m⁺ / f ^ m⁻`**, a degree-`d m` element of `A_f` for every **integer** `m`,
`f` being homogeneous of degree `d`. For `m ≥ 0` it is `f ^ m`, for `m < 0` it is
`1 / f ^ (-m)`. -/
def intPowFraction (hf : f ∈ 𝒜 d) (m : ℤ) :
    gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f ((d : ℤ) * m) :=
  ⟨LocalizedModule.mk (f ^ m.toNat)
      (⟨f ^ (-m).toNat, ⟨(-m).toNat, rfl⟩⟩ : Submonoid.powers f),
    Stacks.GradedLocalization.mk_mem_gradedPiece 𝒜 _ hf (by
      rw [show (d : ℤ) * m + (-m).toNat • (d : ℤ) = ((m.toNat * d : ℕ) : ℤ) from by
        rw [nsmul_eq_mul, ← toNat_mul_add_mul d m]; push_cast; ring]
      rw [AlgebraicGeometry.ProjectiveSpectrum.Proj.integerGrading_natCast,
        AlgebraicGeometry.ProjectiveSpectrum.Proj.mem_homogeneousSubmodule]
      exact pow_mem hf m.toNat)⟩

/-- **The chart value of `f ^ m⁺ / f ^ m⁻` does not vanish anywhere on `T_{ψ(f)}`**, in every
integer degree `d m`. -/
theorem le_nonvanishingLocusOn_intChartSection_intPowFraction (hd : 0 < d) (m : ℤ) :
    ((ψ.chartOpen f : T.Opens) : Set T) ⊆
      nonvanishingLocusOn (tensorPowerModule T L ((d : ℤ) * m)) (ψ.chartOpen f)
        (intChartSection ψ hf (ψ.chartOpen_eq hf hd).le hd ((d : ℤ) * m)
          (intPowFraction hf m)) :=
  le_nonvanishingLocusOn_intChartSection ψ hf (ψ.chartOpen_eq hf hd).le hd ((d : ℤ) * m)
    (intPowFraction hf m) ((-m).toNat) (m.toNat * d) (toNat_mul_add_mul d m)
    (pow_mem hf m.toNat) rfl
    (ψ.le_nonvanishingOpen_pow hf (ψ.chartOpen_eq hf hd).le m.toNat)

end IntPow

end Stacks.AlgebraicGeometry.ProjChartGradedDivision

namespace Stacks.AlgebraicGeometry.ProjChartGradedThetaIso

/-! ### Cancelling the canonical comparisons around a factor of a composite -/

section Cancel

variable {C : Type*} [Category C]

/-- A morphism equal to an isomorphism is an isomorphism. -/
private theorem isIso_of_eq {X Y : C} {f g : X ⟶ Y} (h : f = g) (hg : IsIso g) : IsIso f := h ▸ hg

/-- Cancelling an isomorphism on the left of a composite. -/
private theorem isIso_of_comp_left {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (h : IsIso (f ≫ g))
    (hf : IsIso f) : IsIso g :=
  have := h; have := hf; IsIso.of_isIso_comp_left f g

/-- Cancelling an isomorphism on the right of a composite. -/
private theorem isIso_of_comp_right {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (h : IsIso (f ≫ g))
    (hg : IsIso g) : IsIso f :=
  have := h; have := hg; IsIso.of_isIso_comp_right f g

variable {D : Type*} [Category D]

/-- The image of the forward direction of an isomorphism under a functor is an isomorphism. -/
private theorem isIso_map_hom (F : C ⥤ D) {X Y : C} (e : X ≅ Y) : IsIso (F.map e.hom) :=
  ⟨F.map e.inv, by rw [← F.map_comp, e.hom_inv_id, F.map_id],
    by rw [← F.map_comp, e.inv_hom_id, F.map_id]⟩

/-- The image of the backward direction of an isomorphism under a functor is an isomorphism. -/
private theorem isIso_map_inv (F : C ⥤ D) {X Y : C} (e : X ≅ Y) : IsIso (F.map e.inv) :=
  isIso_map_hom F e.symm

end Cancel

/-! ### `θ` in degree `d` is an isomorphism where `ψ(A_d)` generates -/

section Main

open Stacks.AlgebraicGeometry.ProjChartGradedDivision (intPowFraction
  le_nonvanishingLocusOn_intChartSection_intPowFraction)

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-- **The degree-`d` component of the `θ` of [Stacks, Tag 01NK] is an isomorphism after pullback
to an open on which `ψ(A_d)` generates `L^{⊗ d}`**, for every `d ≥ 1`. -/
theorem isIso_pullback_theta_app {d : ℕ} (hd : 0 < d) {V : T.Opens}
    (hVgen : V ≤ ⨆ g : 𝒜 d, nonvanishingOpen T (natTensorPow L d) (ψ.toFun d g))
    (hVU : V ≤ ψ.coveringOpen) :
    IsIso ((Scheme.Modules.pullback (T.homOfLE hVU)).map ((theta 𝒜 ψ).app (d : ℤ))) := by
  obtain ⟨⟨p, hp, -⟩, hmain⟩ := moreover 𝒜 ψ hd hVgen
  obtain ⟨h, heq⟩ := hmain p hp
  have k0 := isIso_of_eq heq inferInstance
  have k1 := isIso_of_comp_left k0 inferInstance
  have k2 := isIso_of_comp_left k1 inferInstance
  simp only [← Category.assoc] at k2
  have k3 := isIso_of_comp_right k2 inferInstance
  have k4 := isIso_of_comp_right k3 (isIso_map_inv _ _)
  have k5 := isIso_of_comp_right k4 inferInstance
  have k6 := isIso_of_comp_right k5 inferInstance
  exact isIso_of_comp_right k6 (isIso_map_hom _ (Iso.app
    (Scheme.Modules.restrictFunctorIsoPullback ψ.coveringOpen.ι)
    (Stacks.AmpleProjectiveImmersion.tensorPowerModule T L (d : ℤ))))

/-- **One open serves every positive multiple of one degree**: on an open `V` inside the single
nonvanishing open `T_{ψ(f)}` of a homogeneous `f` of degree `d ≥ 1`, the degree-`m d` component of
`θ` is an isomorphism after pullback to `V`, for every `m ≥ 1`. -/
theorem isIso_pullback_theta_app_mul {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d) {V : T.Opens}
    (hV : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨f, hf⟩))
    (hVU : V ≤ ψ.coveringOpen) {m : ℕ} (hm : 0 < m) :
    IsIso ((Scheme.Modules.pullback (T.homOfLE hVU)).map
      ((theta 𝒜 ψ).app ((m * d : ℕ) : ℤ))) :=
  isIso_pullback_theta_app 𝒜 ψ (Nat.mul_pos hm hd)
    ((ψ.le_nonvanishingOpen_pow hf hV m).trans
      (le_iSup (fun g : 𝒜 (m * d) =>
        nonvanishingOpen T (natTensorPow L (m * d)) (ψ.toFun (m * d) g))
        ⟨f ^ m, pow_mem hf m⟩)) hVU

/-! ### `θ` in every integer multiple of one degree, on one chart -/

/-- **`L^{⊗ n}|_{U(ψ)}` is an invertible `𝒪_{U(ψ)}`-module**, for every `n : ℤ` and every graded
map `ψ`. -/
instance isInvertibleModule_laurentPiece (n : ℤ) :
    Stacks.Ample.IsInvertibleModule ψ.coveringOpen.toScheme (ψ.laurentPiece n) := by
  have : Stacks.Ample.IsInvertibleModule ψ.coveringOpen.toScheme
      ((Scheme.Modules.pullback ψ.coveringOpen.ι).obj (tensorPowerModule T L n)) := inferInstance
  exact Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso
    (Stacks.AmplePullbackPart1.restrictIsoPullback ψ.coveringOpen _).symm

/-- **The source of `θ_{d m}` is invertible over an open where `ψ(A_d)` generates**, for every
`m : ℤ`. -/
theorem isInvertibleModule_pullback_theta_source {d : ℕ} (hd : 0 < d) {V : T.Opens}
    (hVgen : V ≤ ⨆ g : 𝒜 d, nonvanishingOpen T (natTensorPow L d) (ψ.toFun d g))
    (hVU : V ≤ ψ.coveringOpen) (m : ℤ) :
    Stacks.Ample.IsInvertibleModule V.toScheme
      ((Scheme.Modules.pullback (T.homOfLE hVU)).obj
        ((Stacks.Conormal.gradedPullback ψ.glued
          (Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜)).piece
            ((d : ℤ) * m))) := by
  obtain ⟨⟨p, hp, -⟩, hmain⟩ := moreover 𝒜 ψ hd hVgen
  obtain ⟨h, -⟩ := hmain p hp
  have : Stacks.Ample.IsInvertibleModule (AlgebraicGeometry.Proj.degreeOpen 𝒜 d).toScheme
      ((Scheme.Modules.pullback (AlgebraicGeometry.Proj.degreeOpen 𝒜 d).ι).obj
        (twistM 𝒜 ((d : ℤ) * m))) :=
    Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.isInvertibleModule_twist 𝒜 d m
  have : Stacks.Ample.IsInvertibleModule V.toScheme
      ((Scheme.Modules.pullback (AlgebraicGeometry.Proj.degreeOpen 𝒜 d).ι ⋙
        Scheme.Modules.pullback p.1).obj (twistM 𝒜 ((d : ℤ) * m))) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback p.1 _
  exact Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso
    ((Scheme.Modules.pullbackComp p.1 (AlgebraicGeometry.Proj.degreeOpen 𝒜 d).ι).app
        (twistM 𝒜 ((d : ℤ) * m)) ≪≫
      (Scheme.Modules.pullbackCongr h.symm).app (twistM 𝒜 ((d : ℤ) * m)) ≪≫
      ((Scheme.Modules.pullbackComp (T.homOfLE hVU) ψ.glued).app
        (twistM 𝒜 ((d : ℤ) * m))).symm)

/-- **The target of `θ_n` pulled back to `V` is invertible**, for every `n : ℤ`. -/
private theorem isInvertibleModule_pullback_laurentRestrict {V : T.Opens} (hVU : V ≤ ψ.coveringOpen)
    (n : ℤ) :
    Stacks.Ample.IsInvertibleModule V.toScheme
      ((Scheme.Modules.pullback (T.homOfLE hVU)).obj ((laurentRestrict 𝒜 ψ).piece n)) :=
  Stacks.InvertiblePullback.isInvertibleModule_pullback (T.homOfLE hVU) (ψ.laurentPiece n)

/-- **`θ_n` pulled back to an open `V` of a chart `T_{ψ(f)}` is an epimorphism as soon as some
degree-`n` element of `A_f` has a non-vanishing chart value there**, for any integer `n`. -/
theorem epi_pullback_theta_app {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d) {V : T.Opens}
    (hVU : V ≤ ψ.coveringOpen) (hVc : V ≤ ψ.chartOpen f) (n : ℤ)
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f n)
    (hy : (ψ.chartOpen f : Set T) ⊆ nonvanishingLocusOn (tensorPowerModule T L n)
      (ψ.chartOpen f) (intChartSection ψ hf (ψ.chartOpen_eq hf hd).le hd n y)) :
    Epi ((Scheme.Modules.pullback (T.homOfLE hVU)).map ((theta 𝒜 ψ).app n)) := by
  have := isInvertibleModule_pullback_laurentRestrict 𝒜 ψ hVU n
  refine Stacks.VeryAmpleGlue.epi_of_forall_mem_nonvanishingLocusOn _ fun z => ?_
  set W := ψ.glued ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f
  set s0 := (AlgebraicGeometry.pullbackSectionHom ψ.glued (twistM 𝒜 n)
      (AlgebraicGeometry.Proj.basicOpen 𝒜 f) W le_rfl
      ((sectionsTwistEquivGradedPiece 𝒜 hf hd n).symm y) :
    Γ((Stacks.Conormal.gradedPullback ψ.glued
      (Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜)).piece n, W))
  refine ⟨T.homOfLE hVU ⁻¹ᵁ W, pullbackUnitSections (T.homOfLE hVU) _ W s0, ?_⟩
  rw [Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackUnitSections_naturality_module
    (T.homOfLE hVU) ((theta 𝒜 ψ).app n) W s0]
  refine (Stacks.NonvanishingLocusRestrict.preimage_nonvanishingLocusOn (T.homOfLE hVU)
    ((laurentRestrict 𝒜 ψ).piece n)
    (Scheme.Modules.Hom.app ((theta 𝒜 ψ).app n) W s0)).le ?_
  have hval : Scheme.Modules.Hom.app ((theta 𝒜 ψ).app n) W s0
      = intChartSection ψ hf (ψ.chartOpen_eq hf hd).le hd n y :=
    (Stacks.AlgebraicGeometry.ProjChartGradedTriple.app_pullbackSection_eq_intChartSection
      (Stacks.AlgebraicGeometry.ProjChartGradedTriple.isClauseTwo_theta ψ) hf hd
      (ψ.chartOpen_eq hf hd).le n _).trans
      (congrArg (intChartSection ψ hf (ψ.chartOpen_eq hf hd).le hd n)
        ((sectionsTwistEquivGradedPiece 𝒜 hf hd n).apply_symm_apply y))
  rw [hval]
  refine Stacks.NonvanishingLocusRestrict.mem_nonvanishingLocusOn_restrict_image
    ψ.coveringOpen (tensorPowerModule T L n) W _ _ ?_
  have hpt : ψ.coveringOpen.ι.base ((T.homOfLE hVU).base z) = V.ι.base z :=
    congrFun (congrArg (fun m : V.toScheme ⟶ T => (ConcreteCategory.hom m.base).toFun)
      (T.homOfLE_ι hVU)) z
  rw [hpt]
  exact hy (hVc z.2)

/-- **One open serves every integer multiple of one degree**: on an open `V` inside the single
non-vanishing open `T_{ψ(f)}` of a homogeneous `f` of degree `d ≥ 1`, the degree-`d m` component
of `θ` is an isomorphism after pullback to `V`, for **every** `m : ℤ`. -/
theorem isIso_pullback_theta_app_intMul {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d) {V : T.Opens}
    (hV : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨f, hf⟩))
    (hVU : V ≤ ψ.coveringOpen) (m : ℤ) :
    IsIso ((Scheme.Modules.pullback (T.homOfLE hVU)).map ((theta 𝒜 ψ).app ((d : ℤ) * m))) := by
  have : Stacks.Ample.IsInvertibleModule V.toScheme
      ((Scheme.Modules.pullback (T.homOfLE hVU)).obj
        ((Stacks.Conormal.gradedPullback ψ.glued
          (Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra 𝒜)).piece
            ((d : ℤ) * m))) :=
    isInvertibleModule_pullback_theta_source 𝒜 ψ hd
      (hV.trans (le_iSup (fun g : 𝒜 d =>
        nonvanishingOpen T (natTensorPow L d) (ψ.toFun d g)) ⟨f, hf⟩)) hVU m
  have := isInvertibleModule_pullback_laurentRestrict 𝒜 ψ hVU ((d : ℤ) * m)
  exact Stacks.AlgebraicGeometry.ProjTwistMono.isIso_of_epi_of_isInvertible _
    (epi_pullback_theta_app 𝒜 ψ hd hf hVU (hV.trans (ψ.chartOpen_eq hf hd).ge) ((d : ℤ) * m)
      (intPowFraction hf m) (le_nonvanishingLocusOn_intChartSection_intPowFraction ψ hf hd m))

end Main

end Stacks.AlgebraicGeometry.ProjChartGradedThetaIso

/-! ### The canonical morphism of Stacks Tag 01PZ -/

namespace Stacks.SectionRingProjMorphism.Theta

section

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

/-- Every point of `⋃_a X_a` lies in some `X_s` for `s` homogeneous of degree `e ≥ 1`, and
`X_s` lies in `⋃_a X_a`. -/
private theorem exists_nvOpen_mem_le_coveringOpen {x : X}
    (hx : x ∈ (canonicalSections L).coveringOpen) :
    ∃ (e : ℕ) (_ : 0 < e) (s : powSections L e), x ∈ nvOpen L s ∧
      nvOpen L s ≤ (canonicalSections L).coveringOpen := by
  rw [coveringOpen_canonicalSections] at hx
  obtain ⟨⟨e, he, s⟩, hxs⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨e, he, s, hxs, (coveringOpen_canonicalSections L).ge.trans'
    (Stacks.SectionRingProjMorphism.nvOpen_le_nvUnion L s he)⟩

/-- **The map `f^*𝒪_Y(m e) ⟶ L^{⊗ m e}` is an isomorphism over `X_s`, for every `m ≥ 1`**, where
`s` is a homogeneous element of `Γ_*(X, L)` of degree `e ≥ 1`. The map is the degree-`m e`
component of `Stacks.SectionRingProjMorphism.Theta.projTheta`, pulled back along the inclusion of
`V` into the open `⋃_a X_a`. -/
theorem isIso_pullback_projTheta_app_mul {e : ℕ} (s : powSections L e) (he : 0 < e)
    (hf : DirectSum.of (powSections L) e s ∈ grading L e) {V : X.Opens} (hV : V ≤ nvOpen L s)
    (hVU : V ≤ (canonicalSections L).coveringOpen) {m : ℕ} (hm : 0 < m) :
    IsIso ((Scheme.Modules.pullback (X.homOfLE hVU)).map
      ((projTheta L).app ((m * e : ℕ) : ℤ))) :=
  Stacks.AlgebraicGeometry.ProjChartGradedThetaIso.isIso_pullback_theta_app_mul (grading L)
    (canonicalSections L) he hf
    (hV.trans (le_of_eq (nonvanishingOpen_canonicalSections_of L e s hf).symm)) hVU hm

/-- **Positive degrees**: every point of `⋃_a X_a` has an integer `e ≥ 1` and an open
neighbourhood `V` on which `f^*𝒪_Y(m e)|_V ⟶ L^{⊗ m e}|_V` is an isomorphism for every `m ≥ 1`. -/
theorem exists_isIso_pullback_projTheta_app_mul {x : X}
    (hx : x ∈ (canonicalSections L).coveringOpen) :
    ∃ (e : ℕ) (_ : 0 < e) (V : X.Opens) (_ : x ∈ V) (hVU : V ≤ (canonicalSections L).coveringOpen),
      ∀ m : ℕ, 0 < m →
        IsIso ((Scheme.Modules.pullback (X.homOfLE hVU)).map
          ((projTheta L).app ((m * e : ℕ) : ℤ))) := by
  obtain ⟨e, he, s, hxs, hVU⟩ := exists_nvOpen_mem_le_coveringOpen L hx
  exact ⟨e, he, nvOpen L s, hxs, hVU, fun m hm =>
    isIso_pullback_projTheta_app_mul L s he (Stacks.ExternalGrading.of_mem_summand e s) le_rfl
      hVU hm⟩

/-- **Every integer multiple of one degree**: the map `f^*𝒪_Y(n e) ⟶ L^{⊗ n e}` is an isomorphism
over `X_s` for **every** `n : ℤ`, where `s` is a homogeneous element of `Γ_*(X, L)` of degree
`e ≥ 1`. The map is the degree-`e n` component of `Stacks.SectionRingProjMorphism.Theta.projTheta`,
pulled back along the inclusion of `V` into the open `⋃_a X_a`. -/
theorem isIso_pullback_projTheta_app_intMul {e : ℕ} (s : powSections L e) (he : 0 < e)
    (hf : DirectSum.of (powSections L) e s ∈ grading L e) {V : X.Opens} (hV : V ≤ nvOpen L s)
    (hVU : V ≤ (canonicalSections L).coveringOpen) (n : ℤ) :
    IsIso ((Scheme.Modules.pullback (X.homOfLE hVU)).map ((projTheta L).app ((e : ℤ) * n))) :=
  Stacks.AlgebraicGeometry.ProjChartGradedThetaIso.isIso_pullback_theta_app_intMul (grading L)
    (canonicalSections L) he hf
    (hV.trans (le_of_eq (nonvanishingOpen_canonicalSections_of L e s hf).symm)) hVU n

/-- Every point of `⋃_a X_a` has an integer `d ≥ 1` and an open neighbourhood `U` on which
`f^*𝒪_Y(d n)|_U ⟶ L^{⊗ d n}|_U` is an isomorphism **for all `n ∈ ℤ`**. -/
@[stacks 01PZ "clause (4): every point of the open where the canonical morphism is defined has an \
integer d >= 1 and an open neighbourhood U of it on which f^*O_Y(dn) -> L^{tensor dn} is an \
isomorphism for all n in Z, positive, zero and negative; d is the degree of a homogeneous element \
of the section ring not vanishing at the point and U is the nonvanishing open of that element"]
theorem exists_isIso_pullback_projTheta_app_intMul {x : X}
    (hx : x ∈ (canonicalSections L).coveringOpen) :
    ∃ (e : ℕ) (_ : 0 < e) (V : X.Opens) (_ : x ∈ V) (hVU : V ≤ (canonicalSections L).coveringOpen),
      ∀ n : ℤ,
        IsIso ((Scheme.Modules.pullback (X.homOfLE hVU)).map
          ((projTheta L).app ((e : ℤ) * n))) := by
  obtain ⟨e, he, s, hxs, hVU⟩ := exists_nvOpen_mem_le_coveringOpen L hx
  exact ⟨e, he, nvOpen L s, hxs, hVU, fun n =>
    isIso_pullback_projTheta_app_intMul L s he (Stacks.ExternalGrading.of_mem_summand e s) le_rfl
      hVU n⟩

end

end Stacks.SectionRingProjMorphism.Theta

end
