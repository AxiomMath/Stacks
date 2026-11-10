module

public import StacksFrontier.AlgebraicGeometry.ProjectiveLineCube.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.Dehomogenization
public import StacksFrontier.AlgebraicGeometry.ProjTwistSection.AwayRatio
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StrictlyHenselianTransport
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ConormalApproximationChartFamily
import StacksFrontier.AlgebraicGeometry.Segre.ChartRing
import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.Preimage

/-!
# The standard charts of a product of three projective lines

The projective line `ℙ¹_ℤ` is covered by the two standard opens `D₊(T₀)` and `D₊(T₁)`, and the
ring of functions on `D₊(Tₐ)` is the polynomial ring `ℤ[t]` in the ratio `t = T_{1-a} / Tₐ` of
the two homogeneous coordinates. Consequently, for a commutative ring `R`, the product
`P = Spec R × ℙ¹ × ℙ¹ × ℙ¹` is covered by the eight affine opens

`V_c = pr₀⁻¹ D₊(T_{c 0}) ∩ pr₁⁻¹ D₊(T_{c 1}) ∩ pr₂⁻¹ D₊(T_{c 2})`,   `c : Fin 3 → Fin 2`,

and `Γ(P, V_c)` is the polynomial ring `R[x₀, x₁, x₂]` in the three pulled-back ratios.

## Main definitions

* `AlgebraicGeometry.projectiveLineBasicOpen a`: the standard open `D₊(Tₐ)` of `ℙ¹_ℤ`.
* `AlgebraicGeometry.projectiveLineBasicOpenEquiv a`: `ℤ[t] ≃ Γ(ℙ¹_ℤ, D₊(Tₐ))`, and
  `AlgebraicGeometry.projectiveLineBasicOpenCoordinate a`, the image of `t`.
* `AlgebraicGeometry.projectiveLineCube.chartOpen c`: the open `V_c`.
* `AlgebraicGeometry.projectiveLineCube.chartCoordinate c i`: the ratio of the `i`-th factor
  pulled back to `V_c`.
* `AlgebraicGeometry.projectiveLineCube.chartRingEquiv c`: `R[x₀, x₁, x₂] ≃ Γ(P, V_c)`.
* `AlgebraicGeometry.projectiveLineCube.rotateChart c`: the chart `ρ⁻¹ V_c`.

## Main results

* `AlgebraicGeometry.projectiveLineBasicOpenCoordinate_eq_divBySection`: the chart coordinate is
  the ratio `T_{1-a} / Tₐ` of the two coordinate sections of `𝒪(1)`.
* `AlgebraicGeometry.projectiveLineCube.isAffineOpen_chartOpen` and
  `AlgebraicGeometry.projectiveLineCube.iSup_chartOpen`: the charts are affine and cover.
* `AlgebraicGeometry.projectiveLineCube.chartRingHom_X`, `chartRingHom_C`: the identification
  sends the variables to the chart coordinates and the scalars to the pullbacks of the functions
  on the base.
* `AlgebraicGeometry.basicOpen_projectiveLineBasicOpenCoordinate` and
  `AlgebraicGeometry.projectiveLineCube.basicOpen_chartCoordinate`: a chart coordinate is a unit
  exactly on the other chart of its factor.
* `AlgebraicGeometry.projectiveLineCube.rotation_preimage_chartOpen` and
  `AlgebraicGeometry.projectiveLineCube.rotation_appLE_chartRingHom`: the cyclic permutation `ρ`
  of the factors maps `ρ⁻¹ V_c` to `V_c` and acts on the chart rings by `xᵢ ↦ x_{i+1}`.

## Implementation notes

Injectivity of `R[x₀, x₁, x₂] → Γ(P, V_c)` is proved by a retraction: the three affine charts
of `ℙ¹` and the base give a morphism `Spec R[x₀, x₁, x₂] ⟶ P` into `V_c`, whose action on
functions sends each chart coordinate back to its variable. Surjectivity is the generation of
the functions on a product of affine opens by the functions on the factors
(`Stacks.AlgebraicGeometry.subring_eq_top_of_pullback_inf`), applied three times along the
iterated fibre product, together with the generation of `Γ(ℙ¹, D₊(Tₐ))` by its coordinate.

## References

* [Stacks Project, Tag 01NG](https://stacks.math.columbia.edu/tag/01NG)
* [Stacks Project, Tag 0DSR](https://stacks.math.columbia.edu/tag/0DSR)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace
open Stacks.ConormalApproximation (appLE_eq_of_eq)

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The standard charts of the projective line -/

/-- The standard open `D₊(Tₐ)` of the projective line `ℙ¹_ℤ`. -/
abbrev projectiveLineBasicOpen (a : Fin 2) : (projectiveSpaceAtUniverse.{u} 1).Opens :=
  Proj.basicOpen (Segre.coordinateGrading.{u} 1) (MvPolynomial.X a)

/-- The standard open `D₊(Tₐ)` of `ℙ¹_ℤ` is affine. -/
theorem isAffineOpen_projectiveLineBasicOpen (a : Fin 2) :
    IsAffineOpen (projectiveLineBasicOpen.{u} a) :=
  Segre.isAffineOpen_basicOpen_X.{u} 1 a

/-- **The ring of functions on a standard chart of `ℙ¹_ℤ` is a polynomial ring in one
variable.** -/
def projectiveLineBasicOpenEquiv (a : Fin 2) :
    MvPolynomial (Fin 1) (ULift.{u} ℤ) ≃+* Γ(projectiveSpaceAtUniverse.{u} 1,
      projectiveLineBasicOpen.{u} a) :=
  Stacks.ProjectiveChart.sectionsChartEquiv (ULift.{u} ℤ) a

/-- The coordinate `T_{1-a} / Tₐ` of the standard chart `D₊(Tₐ)` of `ℙ¹_ℤ`. -/
def projectiveLineBasicOpenCoordinate (a : Fin 2) :
    Γ(projectiveSpaceAtUniverse.{u} 1, projectiveLineBasicOpen.{u} a) :=
  projectiveLineBasicOpenEquiv a (MvPolynomial.X 0)

/-- `projectiveLineBasicOpenEquiv a` sends the variable `t` of `ℤ[t]` to the chart coordinate. -/
theorem projectiveLineBasicOpenEquiv_X (a : Fin 2) (j : Fin 1) :
    projectiveLineBasicOpenEquiv.{u} a (MvPolynomial.X j) =
      projectiveLineBasicOpenCoordinate a := by
  rw [Subsingleton.elim j 0]; rfl

/-- The standard open `D₊(Tₐ)` lies in the nonvanishing locus of the coordinate section `Tₐ`
of `𝒪(1)`. -/
theorem projectiveLineBasicOpen_le_nonvanishingOpen (a : Fin 2) :
    projectiveLineBasicOpen.{u} a ≤ Stacks.SheafOfModules.nonvanishingOpen
      (X := (projectiveSpaceAtUniverse.{u} 1).toRingedSpace)
      (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 1) (Segre.coordinateSection.{u} 1 a) :=
  Stacks.ProjTwistSection.basicOpen_le_nonvanishingOpen_homogeneousSection _ _ _

/-- **The chart coordinate is the ratio of the two homogeneous coordinates**: on `D₊(Tₐ)` it is
`T_{1-a} / Tₐ`, the quotient of the coordinate sections of `𝒪(1)`. -/
theorem projectiveLineBasicOpenCoordinate_eq_divBySection (a : Fin 2) :
    projectiveLineBasicOpenCoordinate.{u} a =
      Stacks.SheafOfModules.divBySection (X := (projectiveSpaceAtUniverse.{u} 1).toRingedSpace)
        (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 1) (Segre.coordinateSection.{u} 1 a)
        (projectiveLineBasicOpen_le_nonvanishingOpen a)
        ((Segre.coordinateSection.{u} 1 a.rev).eval (op (projectiveLineBasicOpen.{u} a))) := by
  refine Eq.trans ?_ (Stacks.ProjTwistSection.divBySection_homogeneousSection
    (Segre.coordinateGrading.{u} 1) (MvPolynomial.X a) (MvPolynomial.X a.rev)
    (Stacks.ProjectiveChart.X_mem_degree_one _ _)
    (Stacks.ProjectiveChart.X_mem_degree_one _ _)).symm
  have h := Stacks.ProjectiveChart.sectionsChartEquiv_dehomCoeff (ULift.{u} ℤ) a 1
    (MvPolynomial.X a.rev) (Stacks.ProjectiveChart.X_mem_degree_one _ _)
  have h2 : Stacks.ProjectiveChart.dehomCoeff (ULift.{u} ℤ) a (MvPolynomial.X a.rev) =
      MvPolynomial.X 0 := by
    rw [Stacks.ProjectiveChart.dehomCoeff_eq_aeval]
    fin_cases a <;> simp [finSuccEquiv']
    rfl
  rw [h2] at h
  refine h.trans ?_
  unfold AlgebraicGeometry.ProjectiveSpectrum.Proj.chartFraction
  congr 1
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.Away.val_mk]

/-- **The chart coordinate is a unit exactly on the other chart**: the basic open of
`T_{1-a} / Tₐ` in `D₊(Tₐ)` is `D₊(Tₐ) ∩ D₊(T_{1-a})`. -/
theorem basicOpen_projectiveLineBasicOpenCoordinate (a : Fin 2) :
    (projectiveSpaceAtUniverse.{u} 1).basicOpen (projectiveLineBasicOpenCoordinate a) =
      projectiveLineBasicOpen.{u} a ⊓ projectiveLineBasicOpen.{u} a.rev := by
  have hNV : ∀ b : Fin 2, Stacks.ProjectiveSpaceSections.nonvanishingChart
      (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 1) (Segre.coordinateSection.{u} 1 b) =
      projectiveLineBasicOpen.{u} b :=
    fun b => Segre.nonvanishingOpen_coordinateSection_eq_basicOpen.{u} 1 b
  have h := Stacks.ProjectiveSpaceSections.basicOpen_divBySection
    (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 1) (Segre.coordinateSection.{u} 1) a a.rev
  have hle := projectiveLineBasicOpen_le_nonvanishingOpen.{u} a
  have hres := Stacks.SheafOfModules.map_divBySection
    (X := (projectiveSpaceAtUniverse.{u} 1).toRingedSpace)
    (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 1) (Segre.coordinateSection.{u} 1 a) hle le_rfl
    ((Segre.coordinateSection.{u} 1 a.rev).eval (op (Stacks.SheafOfModules.nonvanishingOpen
      (X := (projectiveSpaceAtUniverse.{u} 1).toRingedSpace)
      (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 1) (Segre.coordinateSection.{u} 1 a))))
  have h2 := Stacks.SheafOfModules.secRestr_sections_eval
    (X := (projectiveSpaceAtUniverse.{u} 1).toRingedSpace)
    (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 1) (Segre.coordinateSection.{u} 1 a.rev) hle
  have hres' := hres.trans (congrArg _ h2)
  rw [projectiveLineBasicOpenCoordinate_eq_divBySection, ← hres', Scheme.basicOpen_res]
  change _ ⊓ (projectiveSpaceAtUniverse.{u} 1).basicOpen (Stacks.SheafOfModules.divBySection
    (X := (projectiveSpaceAtUniverse.{u} 1).toRingedSpace)
    (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 1) (Segre.coordinateSection.{u} 1 a) le_rfl
    ((Segre.coordinateSection.{u} 1 a.rev).eval
      (op (Stacks.ProjectiveSpaceSections.nonvanishingChart
        (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 1) (Segre.coordinateSection.{u} 1 a))))) = _
  rw [h, hNV, hNV, inf_comm (projectiveLineBasicOpen.{u} a.rev), ← inf_assoc, inf_idem]

/-- On `D₊(Tₐ)` the ratio of `Tₐ` to itself is `1`. -/
theorem divBySection_coordinateSection_self (a : Fin 2) :
    Stacks.SheafOfModules.divBySection (X := (projectiveSpaceAtUniverse.{u} 1).toRingedSpace)
        (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 1) (Segre.coordinateSection.{u} 1 a)
        (projectiveLineBasicOpen_le_nonvanishingOpen a)
        ((Segre.coordinateSection.{u} 1 a).eval (op (projectiveLineBasicOpen.{u} a))) = 1 :=
  Stacks.SheafOfModules.divBySection_self _ _ _

/-- A ring homomorphism out of `Γ(ℙ¹_ℤ, D₊(Tₐ))` is determined by its value on the chart
coordinate. -/
theorem ringHom_ext_projectiveLineBasicOpen {A : Type*} [CommRing A] (a : Fin 2)
    {f g : Γ(projectiveSpaceAtUniverse.{u} 1, projectiveLineBasicOpen.{u} a) →+* A}
    (h : f (projectiveLineBasicOpenCoordinate a) = g (projectiveLineBasicOpenCoordinate a)) :
    f = g := by
  have : f.comp (projectiveLineBasicOpenEquiv a).toRingHom =
      g.comp (projectiveLineBasicOpenEquiv a).toRingHom :=
    MvPolynomial.ringHom_ext (fun r => DFunLike.congr_fun ((MvPolynomial.eq_uliftIntCast
      ((f.comp (projectiveLineBasicOpenEquiv a).toRingHom).comp MvPolynomial.C)).trans
      (MvPolynomial.eq_uliftIntCast
        ((g.comp (projectiveLineBasicOpenEquiv a).toRingHom).comp MvPolynomial.C)).symm) r)
      (fun j => by simpa [projectiveLineBasicOpenEquiv_X] using h)
  ext x
  obtain ⟨p, rfl⟩ := (projectiveLineBasicOpenEquiv a).surjective x
  exact congrArg (fun φ => φ p) this

/-- The ring homomorphism out of `Γ(ℙ¹_ℤ, D₊(Tₐ))` sending the chart coordinate to `t`. -/
def projectiveLineBasicOpenLift {A : Type*} [CommRing A] (a : Fin 2) (t : A) :
    Γ(projectiveSpaceAtUniverse.{u} 1, projectiveLineBasicOpen.{u} a) →+* A :=
  (MvPolynomial.eval₂Hom (MvPolynomial.uliftIntCast A) fun _ => t).comp
    (projectiveLineBasicOpenEquiv a).symm.toRingHom

/-- `projectiveLineBasicOpenLift a t` sends the chart coordinate to `t`. -/
@[simp]
theorem projectiveLineBasicOpenLift_coordinate {A : Type*} [CommRing A] (a : Fin 2) (t : A) :
    projectiveLineBasicOpenLift.{u} a t (projectiveLineBasicOpenCoordinate a) = t := by
  simp [projectiveLineBasicOpenLift, projectiveLineBasicOpenCoordinate]

/-! ### Functions on affine opens and morphisms from spectra -/

/-- `Scheme.Hom.appLE_comp_appLE` on elements. -/
theorem Scheme.Hom.appLE_appLE_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {U : Z.Opens} {V : Y.Opens} {W : X.Opens} (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V)
    (e : W ≤ (f ≫ g) ⁻¹ᵁ U) (x : Γ(Z, U)) :
    f.appLE V W e₂ (g.appLE U V e₁ x) = (f ≫ g).appLE U W e x := by
  rw [← Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂]
  rfl

/-- `Scheme.Hom.appLE_comp_appLE` for a composite given only up to equality. -/
private theorem appLE_comp_appLE_of_comp_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {k : X ⟶ Z} (hk : f ≫ g = k) {U : Z.Opens} {V : Y.Opens} {W : X.Opens} (e₁ : V ≤ g ⁻¹ᵁ U)
    (e₂ : W ≤ f ⁻¹ᵁ V) (e : W ≤ k ⁻¹ᵁ U) :
    g.appLE U V e₁ ≫ f.appLE V W e₂ = k.appLE U W e := by
  subst hk
  exact Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂

/-- `Scheme.Hom.appLE_appLE_apply` for a composite given only up to equality. -/
private theorem appLE_appLE_apply_of_comp_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {k : X ⟶ Z} (hk : f ≫ g = k) {U : Z.Opens} {V : Y.Opens} {W : X.Opens} (e₁ : V ≤ g ⁻¹ᵁ U)
    (e₂ : W ≤ f ⁻¹ᵁ V) (e : W ≤ k ⁻¹ᵁ U) (x : Γ(Z, U)) :
    f.appLE V W e₂ (g.appLE U V e₁ x) = k.appLE U W e x := by
  subst hk
  exact Scheme.Hom.appLE_appLE_apply f g e₁ e₂ e x

/-- On global functions, `Spec.map φ` is `φ`. -/
@[reassoc]
theorem Spec_map_appLE_top_comp_ΓSpecIso_hom {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (e : ⊤ ≤ Spec.map φ ⁻¹ᵁ ⊤) :
    (Spec.map φ).appLE ⊤ ⊤ e ≫ (Scheme.ΓSpecIso B).hom = (Scheme.ΓSpecIso A).hom ≫ φ := by
  have h := Scheme.ΓSpecIso_inv_naturality φ
  rw [Scheme.Hom.appLE_top_top, ← cancel_epi (Scheme.ΓSpecIso A).inv, ← Scheme.Hom.appTop,
    ← Category.assoc, ← h]
  simp

/-- For an affine open `U`, the map `Γ(X, U) → Γ(Spec Γ(X, U), ⊤)` induced by `hU.fromSpec`
is the inverse of `Scheme.ΓSpecIso`. -/
theorem IsAffineOpen.fromSpec_appLE_self {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (e : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ e = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  convert Category.comp_id _
  exact CategoryTheory.Functor.map_id _ _

/-- The preimage of an affine open `U` under `Spec B ⟶ Spec Γ(X, U) ⟶ X` is everything. -/
theorem IsAffineOpen.top_le_preimage_Spec_map_comp_fromSpec {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {B : CommRingCat.{u}} (φ : Γ(X, U) ⟶ B) :
    ⊤ ≤ (Spec.map φ ≫ hU.fromSpec) ⁻¹ᵁ U := by
  rw [Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self, Scheme.Hom.preimage_top]

/-- The functions on an affine open `U` pulled back along `Spec B ⟶ Spec Γ(U) ⟶ X` are their
images under the ring map. -/
theorem IsAffineOpen.Spec_map_comp_fromSpec_appLE {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {B : CommRingCat.{u}} (φ : Γ(X, U) ⟶ B)
    (e : ⊤ ≤ (Spec.map φ ≫ hU.fromSpec) ⁻¹ᵁ U) :
    (Spec.map φ ≫ hU.fromSpec).appLE U ⊤ e ≫ (Scheme.ΓSpecIso B).hom = φ := by
  have e₁ : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by simp
  have e₂ : ⊤ ≤ Spec.map φ ⁻¹ᵁ ⊤ := by simp
  rw [← Scheme.Hom.appLE_comp_appLE _ _ _ _ _ e₁ e₂, Category.assoc,
    Spec_map_appLE_top_comp_ΓSpecIso_hom, IsAffineOpen.fromSpec_appLE_self, Iso.inv_hom_id_assoc]

/-! ### The charts of `S × ℙ¹ × ℙ¹ × ℙ¹` -/

namespace cubeProduct

variable (S X : Scheme.{u})

/-- The projection to the first `ℙ¹` factor is `pullback.snd ≫ pullback.fst`. -/
theorem proj_zero : proj S X 0 = pullback.snd _ _ ≫ pullback.fst _ _ := rfl

/-- The projection to the second `ℙ¹` factor is `pullback.snd ≫ pullback.snd ≫ pullback.fst`. -/
theorem proj_one : proj S X 1 = pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.fst _ _ := rfl

/-- The projection to the third `ℙ¹` factor is `pullback.snd ≫ pullback.snd ≫ pullback.snd`. -/
theorem proj_two : proj S X 2 = pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.snd _ _ := rfl

end cubeProduct

namespace projectiveLineCube

open cubeProduct

variable (S : Scheme.{u})

/-- The chart `V_c = pr₀⁻¹ D₊(T_{c 0}) ∩ pr₁⁻¹ D₊(T_{c 1}) ∩ pr₂⁻¹ D₊(T_{c 2})` of
`S × ℙ¹ × ℙ¹ × ℙ¹`. -/
def chartOpen (c : Fin 3 → Fin 2) : (projectiveLineCube S).Opens :=
  proj S _ 0 ⁻¹ᵁ projectiveLineBasicOpen.{u} (c 0) ⊓
    proj S _ 1 ⁻¹ᵁ projectiveLineBasicOpen.{u} (c 1) ⊓
    proj S _ 2 ⁻¹ᵁ projectiveLineBasicOpen.{u} (c 2)

/-- The chart `V_c` lies in the preimage of `D₊(T_{c i})` under the `i`-th projection. -/
theorem chartOpen_le (c : Fin 3 → Fin 2) (i : Fin 3) :
    chartOpen S c ≤ proj S _ i ⁻¹ᵁ projectiveLineBasicOpen.{u} (c i) := by
  fin_cases i
  · exact inf_le_left.trans inf_le_left
  · exact inf_le_left.trans inf_le_right
  · exact inf_le_right

/-- A point lies in `V_c` if and only if its `i`-th projection lies in `D₊(T_{c i})` for
every `i`. -/
theorem mem_chartOpen_iff (c : Fin 3 → Fin 2) (x : projectiveLineCube S) :
    x ∈ chartOpen S c ↔ ∀ i, proj S _ i x ∈ projectiveLineBasicOpen.{u} (c i) := by
  refine ⟨fun h i => chartOpen_le S c i h, fun h => ⟨⟨h 0, h 1⟩, h 2⟩⟩

/-- The charts are affine over an affine base. -/
theorem isAffineOpen_chartOpen [IsAffine S] (c : Fin 3 → Fin 2) :
    IsAffineOpen (chartOpen S c) :=
  isAffineOpen_proj_preimage_inf S _ (U := fun i => projectiveLineBasicOpen.{u} (c i))
    fun i => isAffineOpen_projectiveLineBasicOpen (c i)

/-- **The eight charts cover `S × ℙ¹ × ℙ¹ × ℙ¹`.** -/
theorem iSup_chartOpen : ⨆ c, chartOpen S c = ⊤ := by
  refine top_unique fun x _ => ?_
  have hcov : ∀ i : Fin 3, ∃ a : Fin 2, proj S _ i x ∈ projectiveLineBasicOpen.{u} a := by
    intro i
    have h := (Segre.iSup_nonvanishingOpen_coordinateSection_eq_top.{u} 1).ge
      (Set.mem_univ (proj S _ i x))
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp h
    refine ⟨a, ?_⟩
    change _ ∈ Proj.basicOpen _ _
    exact (Segre.nonvanishingOpen_coordinateSection_eq_basicOpen.{u} 1 a) ▸ ha
  choose c hc using hcov
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨c, (mem_chartOpen_iff S c x).mpr hc⟩

/-- The coordinate of the `i`-th factor on the chart `V_c`: the pullback of the chart
coordinate of `D₊(T_{c i})` along the `i`-th projection. -/
def chartCoordinate (c : Fin 3 → Fin 2) (i : Fin 3) : Γ(projectiveLineCube S, chartOpen S c) :=
  (proj S _ i).appLE (projectiveLineBasicOpen.{u} (c i)) (chartOpen S c) (chartOpen_le S c i)
    (projectiveLineBasicOpenCoordinate (c i))

/-- **A chart coordinate is a unit exactly on the other chart of its factor.** -/
theorem basicOpen_chartCoordinate (c : Fin 3 → Fin 2) (i : Fin 3) :
    (projectiveLineCube S).basicOpen (chartCoordinate S c i) =
      chartOpen S c ⊓ proj S _ i ⁻¹ᵁ projectiveLineBasicOpen.{u} (c i).rev := by
  rw [chartCoordinate, Scheme.basicOpen_appLE, basicOpen_projectiveLineBasicOpenCoordinate]
  exact le_antisymm (fun x hx => ⟨hx.1, hx.2.2⟩)
    (fun x hx => ⟨hx.1, chartOpen_le S c i hx.1, hx.2⟩)

/-! ### The cyclic permutation of the factors on the charts -/

/-- The chart `c ∘ (· - 1)`: the preimage of `V_c` under the cyclic permutation `ρ` of the
factors. -/
def rotateChart (c : Fin 3 → Fin 2) : Fin 3 → Fin 2 := fun j => c (j - 1)

/-- **The cyclic permutation moves the charts**: `ρ⁻¹ V_c = V_{c ∘ (· - 1)}`. -/
theorem rotation_preimage_chartOpen (c : Fin 3 → Fin 2) :
    (rotation S (projectiveSpaceAtUniverse.{u} 1)).hom ⁻¹ᵁ chartOpen S c =
      chartOpen S (rotateChart c) := by
  have key : ∀ (x : projectiveLineCube S) (i : Fin 3),
      proj S _ i ((rotation S (projectiveSpaceAtUniverse.{u} 1)).hom x) = proj S _ (i + 1) x :=
    fun x i => by
      rw [← rotation_hom_proj S _ i]
      rfl
  ext x
  change (rotation S (projectiveSpaceAtUniverse.{u} 1)).hom x ∈ chartOpen S c ↔
    x ∈ chartOpen S (rotateChart c)
  rw [mem_chartOpen_iff, mem_chartOpen_iff]
  refine ⟨fun h j => ?_, fun h i => ?_⟩
  · have := h (j - 1)
    rw [key, sub_add_cancel] at this
    exact this
  · rw [key]
    have := h (i + 1)
    simpa [rotateChart] using this

/-- `rotateChart c` at `i + 1` is `c i`. -/
theorem rotateChart_add_one (c : Fin 3 → Fin 2) (i : Fin 3) : rotateChart c (i + 1) = c i := by
  simp [rotateChart]

/-- A pulled-back chart coordinate only depends on the chart through the index. -/
theorem proj_appLE_projectiveLineBasicOpenCoordinate_congr {V : (projectiveLineCube S).Opens}
    (j : Fin 3) {a b : Fin 2} (h : a = b) (ha : V ≤ proj S _ j ⁻¹ᵁ projectiveLineBasicOpen.{u} a)
    (hb : V ≤ proj S _ j ⁻¹ᵁ projectiveLineBasicOpen.{u} b) :
    (proj S _ j).appLE (projectiveLineBasicOpen.{u} a) V ha (projectiveLineBasicOpenCoordinate a) =
      (proj S _ j).appLE (projectiveLineBasicOpen.{u} b) V hb
        (projectiveLineBasicOpenCoordinate b) := by
  subst h; rfl

/-- **The cyclic permutation sends the `i`-th chart coordinate of `V_c` to the `(i + 1)`-th
chart coordinate of `ρ⁻¹ V_c`.** -/
theorem rotation_appLE_chartCoordinate (c : Fin 3 → Fin 2) (i : Fin 3)
    (e : chartOpen S (rotateChart c) ≤
      (rotation S (projectiveSpaceAtUniverse.{u} 1)).hom ⁻¹ᵁ chartOpen S c) :
    (rotation S (projectiveSpaceAtUniverse.{u} 1)).hom.appLE (chartOpen S c)
        (chartOpen S (rotateChart c)) e (chartCoordinate S c i) =
      chartCoordinate S (rotateChart c) (i + 1) := by
  have e₂ : chartOpen S (rotateChart c) ≤
      proj S _ (i + 1) ⁻¹ᵁ projectiveLineBasicOpen.{u} (c i) := by
    rw [← rotation_hom_proj S _ i, Scheme.Hom.comp_preimage]
    exact e.trans fun x hx => chartOpen_le S c i hx
  refine (appLE_appLE_apply_of_comp_eq _ _ (rotation_hom_proj S _ i) (chartOpen_le S c i) e
    e₂ _).trans ?_
  exact proj_appLE_projectiveLineBasicOpenCoordinate_congr S (i + 1) (rotateChart_add_one c i).symm
    e₂ _

section Affine

variable (R : Type u) [CommRing R]

/-- The scalars of the base `Spec R`, as functions on the chart `V_c`. -/
def chartScalar (c : Fin 3 → Fin 2) :
    R →+* Γ(projectiveLineCube (Spec (.of R)), chartOpen _ c) :=
  ((toBase (Spec (.of R)) _).appLE ⊤ (chartOpen _ c)
    le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

/-- The ring homomorphism `R[x₀, x₁, x₂] → Γ(P, V_c)` sending `xᵢ` to the `i`-th chart
coordinate. -/
def chartRingHom (c : Fin 3 → Fin 2) :
    MvPolynomial (Fin 3) R →+* Γ(projectiveLineCube (Spec (.of R)), chartOpen _ c) :=
  MvPolynomial.eval₂Hom (chartScalar R c) (chartCoordinate _ c)

/-- `chartRingHom R c` sends the variable `xᵢ` to the `i`-th chart coordinate. -/
@[simp]
theorem chartRingHom_X (c : Fin 3 → Fin 2) (i : Fin 3) :
    chartRingHom R c (MvPolynomial.X i) = chartCoordinate _ c i :=
  MvPolynomial.eval₂Hom_X' _ _ _

/-- `chartRingHom R c` sends a constant `r` to the scalar `chartScalar R c r`. -/
@[simp]
theorem chartRingHom_C (c : Fin 3 → Fin 2) (r : R) :
    chartRingHom R c (MvPolynomial.C r) = chartScalar R c r :=
  MvPolynomial.eval₂Hom_C _ _ _

/-- The functions on `D₊(T_{c i})` pulled back to `V_c` along the `i`-th projection: the
polynomial in the chart coordinate becomes the same polynomial in `xᵢ`. -/
theorem proj_appLE_eq_chartRingHom (c : Fin 3 → Fin 2) (i : Fin 3)
    (p : Γ(projectiveSpaceAtUniverse.{u} 1, projectiveLineBasicOpen.{u} (c i))) :
    (proj (Spec (.of R)) _ i).appLE (projectiveLineBasicOpen.{u} (c i)) (chartOpen _ c)
        (chartOpen_le _ c i) p =
      chartRingHom R c (projectiveLineBasicOpenLift (c i) (MvPolynomial.X i) p) := by
  have h := ringHom_ext_projectiveLineBasicOpen (c i)
    (f := ((proj (Spec (.of R)) _ i).appLE (projectiveLineBasicOpen.{u} (c i)) (chartOpen _ c)
        (chartOpen_le _ c i)).hom)
    (g := (chartRingHom R c).comp (projectiveLineBasicOpenLift (c i) (MvPolynomial.X i)))
    (by simp [chartCoordinate])
  exact DFunLike.congr_fun h p

/-- The morphism `Spec R[x₀, x₁, x₂] ⟶ S × ℙ¹ × ℙ¹ × ℙ¹` into the chart `V_c`, whose `i`-th
component is the chart `Spec ℤ[t] ≅ D₊(T_{c i})` composed with `t ↦ xᵢ`. -/
def chartMorphism (c : Fin 3 → Fin 2) :
    Spec (.of (MvPolynomial (Fin 3) R)) ⟶ projectiveLineCube (Spec (.of R)) :=
  lift (Spec.map (CommRingCat.ofHom MvPolynomial.C)) fun i =>
    Spec.map (CommRingCat.ofHom (projectiveLineBasicOpenLift (c i) (MvPolynomial.X i))) ≫
      (isAffineOpen_projectiveLineBasicOpen (c i)).fromSpec

/-- `chartMorphism R c` followed by the structure morphism to `Spec R` is `Spec` of the
inclusion of constants `R → R[x₀, x₁, x₂]`. -/
@[reassoc (attr := simp)]
theorem chartMorphism_toBase (c : Fin 3 → Fin 2) :
    chartMorphism R c ≫ toBase _ _ = Spec.map (CommRingCat.ofHom MvPolynomial.C) :=
  lift_toBase _ _

/-- The `i`-th component of `chartMorphism R c` is `Spec` of
`projectiveLineBasicOpenLift (c i) xᵢ` followed by `Spec Γ(ℙ¹_ℤ, D₊(T_{c i})) ⟶ ℙ¹_ℤ`. -/
@[reassoc (attr := simp)]
theorem chartMorphism_proj (c : Fin 3 → Fin 2) (i : Fin 3) :
    chartMorphism R c ≫ proj _ _ i =
      Spec.map (CommRingCat.ofHom (projectiveLineBasicOpenLift (c i) (MvPolynomial.X i))) ≫
        (isAffineOpen_projectiveLineBasicOpen (c i)).fromSpec :=
  lift_proj _ _ i

/-- `chartMorphism R c` lands in the chart `V_c`. -/
theorem chartMorphism_preimage (c : Fin 3 → Fin 2) :
    ⊤ ≤ chartMorphism R c ⁻¹ᵁ chartOpen _ c := by
  intro x _
  refine (mem_chartOpen_iff _ c _).mpr fun i => ?_
  change (chartMorphism R c ≫ proj _ _ i) x ∈ _
  rw [chartMorphism, lift_proj]
  change _ ∈ ((projectiveLineBasicOpen.{u} (c i) : (projectiveSpaceAtUniverse.{u} 1).Opens) :
    Set (projectiveSpaceAtUniverse.{u} 1))
  rw [← (isAffineOpen_projectiveLineBasicOpen (c i)).range_fromSpec]
  exact ⟨_, rfl⟩

/-- The retraction `Γ(P, V_c) → R[x₀, x₁, x₂]`: pull back along `chartMorphism`. -/
def chartRetraction (c : Fin 3 → Fin 2) :
    Γ(projectiveLineCube (Spec (.of R)), chartOpen _ c) →+* MvPolynomial (Fin 3) R :=
  ((chartMorphism R c).appLE (chartOpen _ c) ⊤ (chartMorphism_preimage R c) ≫
    (Scheme.ΓSpecIso _).hom).hom

/-- `chartRetraction R c` is a left inverse of `chartRingHom R c`. -/
theorem chartRetraction_comp_chartRingHom (c : Fin 3 → Fin 2) :
    (chartRetraction R c).comp (chartRingHom R c) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    have key : (toBase (Spec (.of R)) _).appLE ⊤ (chartOpen _ c)
          le_top ≫
        (chartMorphism R c).appLE (chartOpen _ c) ⊤ (chartMorphism_preimage R c) ≫
          (Scheme.ΓSpecIso _).hom =
        (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom MvPolynomial.C := by
      rw [← Category.assoc]
      exact (congrArg (· ≫ _) (appLE_comp_appLE_of_comp_eq _ _ (chartMorphism_toBase R c) le_top _
        le_top)).trans (Spec_map_appLE_top_comp_ΓSpecIso_hom _ le_top)
    have := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) key
    simpa [chartRetraction, chartScalar] using this
  · intro i
    have key : (proj (Spec (.of R)) _ i).appLE (projectiveLineBasicOpen.{u} (c i)) (chartOpen _ c)
          (chartOpen_le _ c i) ≫
        (chartMorphism R c).appLE (chartOpen _ c) ⊤ (chartMorphism_preimage R c) ≫
          (Scheme.ΓSpecIso _).hom =
        CommRingCat.ofHom (projectiveLineBasicOpenLift (c i) (MvPolynomial.X i)) := by
      rw [← Category.assoc, appLE_comp_appLE_of_comp_eq _ _ (chartMorphism_proj R c i) _ _
        (IsAffineOpen.top_le_preimage_Spec_map_comp_fromSpec _ _),
        IsAffineOpen.Spec_map_comp_fromSpec_appLE]
    have := congrArg (fun φ => φ.hom (projectiveLineBasicOpenCoordinate (c i))) key
    simpa [chartRetraction, chartCoordinate] using this

/-- `chartRingHom R c : R[x₀, x₁, x₂] → Γ(P, V_c)` is injective. -/
theorem chartRingHom_injective (c : Fin 3 → Fin 2) : Function.Injective (chartRingHom R c) :=
  Function.LeftInverse.injective (g := chartRetraction R c)
    fun p => DFunLike.congr_fun (chartRetraction_comp_chartRingHom R c) p

/-- **The functions on a chart are polynomials in the chart coordinates.** -/
theorem chartRingHom_surjective (c : Fin 3 → Fin 2) : Function.Surjective (chartRingHom R c) := by
  let L := projectiveSpaceAtUniverse.{u} 1
  let Q' := pullback (terminal.from L) (terminal.from L)
  let W' : Q'.Opens := pullback.fst (terminal.from L) (terminal.from L) ⁻¹ᵁ
    projectiveLineBasicOpen.{u} (c 1) ⊓
    pullback.snd (terminal.from L) (terminal.from L) ⁻¹ᵁ projectiveLineBasicOpen.{u} (c 2)
  let Q := pullback (terminal.from L) (terminal.from Q')
  let W : Q.Opens := pullback.fst (terminal.from L) (terminal.from Q') ⁻¹ᵁ
    projectiveLineBasicOpen.{u} (c 0) ⊓ pullback.snd (terminal.from L) (terminal.from Q') ⁻¹ᵁ W'
  have hW' : IsAffineOpen W' := Stacks.AlgebraicGeometry.isAffineOpen_pullback_inf _ _
    (isAffineOpen_projectiveLineBasicOpen (c 1)) (isAffineOpen_projectiveLineBasicOpen (c 2))
  have hW : IsAffineOpen W := Stacks.AlgebraicGeometry.isAffineOpen_pullback_inf _ _
    (isAffineOpen_projectiveLineBasicOpen (c 0)) hW'
  let T := (chartRingHom R c).range
  have leV0 : chartOpen (Spec (.of R)) c ≤
      pullback.fst (terminal.from (Spec (.of R))) (terminal.from Q) ⁻¹ᵁ ⊤ :=
    le_top
  have leVW : chartOpen (Spec (.of R)) c ≤
      pullback.snd (terminal.from (Spec (.of R))) (terminal.from Q) ⁻¹ᵁ W :=
    fun x hx => ⟨hx.1.1, hx.1.2, hx.2⟩
  have hWo : chartOpen (Spec (.of R)) c =
      pullback.fst (terminal.from (Spec (.of R))) (terminal.from Q) ⁻¹ᵁ ⊤ ⊓
        pullback.snd (terminal.from (Spec (.of R))) (terminal.from Q) ⁻¹ᵁ W :=
    le_antisymm (le_inf leV0 leVW) fun x hx => ⟨⟨hx.2.1, hx.2.2.1⟩, hx.2.2.2⟩
  have htop := Stacks.AlgebraicGeometry.subring_eq_top_of_pullback_inf
    (terminal.from (Spec (.of R))) (terminal.from Q) (isAffineOpen_top _) hW hWo leV0 leVW T
    (fun a => ⟨MvPolynomial.C ((Scheme.ΓSpecIso (CommRingCat.of R)).hom a), by
      simp only [chartRingHom_C, chartScalar, RingHom.comp_apply, Iso.hom_inv_id_apply]
      rfl⟩) ?_
  · intro x
    have hx : x ∈ (⊤ : Subring _) := trivial
    rw [← htop] at hx
    exact hx
  intro b
  have htop₂ := Stacks.AlgebraicGeometry.subring_eq_top_of_pullback_inf
    (terminal.from L) (terminal.from Q') (isAffineOpen_projectiveLineBasicOpen (c 0)) hW' (Wo := W)
    rfl inf_le_left inf_le_right
    (T.comap ((pullback.snd (terminal.from (Spec (.of R))) (terminal.from Q)).appLE W
      (chartOpen _ c) leVW).hom)
    (fun a => ⟨_, (proj_appLE_eq_chartRingHom R c 0 a).symm.trans
      (appLE_appLE_apply_of_comp_eq _ _ (proj_zero (Spec (.of R)) L).symm _ _ _ a).symm⟩) ?_
  · have hb : b ∈ (⊤ : Subring _) := trivial
    rw [← htop₂] at hb
    exact hb
  intro b'
  have htop₃ := Stacks.AlgebraicGeometry.subring_eq_top_of_pullback_inf
    (terminal.from L) (terminal.from L) (isAffineOpen_projectiveLineBasicOpen (c 1))
    (isAffineOpen_projectiveLineBasicOpen (c 2)) (Wo := W') rfl inf_le_left inf_le_right
    ((T.comap ((pullback.snd (terminal.from (Spec (.of R))) (terminal.from Q)).appLE W
      (chartOpen _ c) leVW).hom).comap
        ((pullback.snd (terminal.from L) (terminal.from Q')).appLE W' W inf_le_right).hom)
    (fun a => ⟨_, (proj_appLE_eq_chartRingHom R c 1 a).symm.trans (by
      rw [Scheme.Hom.appLE_appLE_apply _ _ _ _ (by
          rw [Scheme.Hom.comp_preimage]; exact leVW.trans fun x hx => hx.2),
        Scheme.Hom.appLE_appLE_apply _ _ _ _ (by
          rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
          exact leVW.trans fun x hx => hx.2.1)]
      exact DFunLike.congr_fun (congrArg (fun φ => ConcreteCategory.hom φ)
        (appLE_eq_of_eq ((proj_one (Spec (.of R)) L).trans (Category.assoc _ _ _).symm)
          _ _ _ _)) a)⟩)
    (fun a => ⟨_, (proj_appLE_eq_chartRingHom R c 2 a).symm.trans (by
      rw [Scheme.Hom.appLE_appLE_apply _ _ _ _ (by
          rw [Scheme.Hom.comp_preimage]; exact leVW.trans fun x hx => hx.2),
        Scheme.Hom.appLE_appLE_apply _ _ _ _ (by
          rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
          exact leVW.trans fun x hx => hx.2.2)]
      exact DFunLike.congr_fun (congrArg (fun φ => ConcreteCategory.hom φ)
        (appLE_eq_of_eq ((proj_two (Spec (.of R)) L).trans (Category.assoc _ _ _).symm)
          _ _ _ _)) a)⟩)
  have hb : b' ∈ (⊤ : Subring _) := trivial
  rw [← htop₃] at hb
  exact hb

/-- **The ring of functions on the chart `V_c` of `Spec R × ℙ¹ × ℙ¹ × ℙ¹` is the polynomial ring
`R[x₀, x₁, x₂]`**, the variable `xᵢ` being the pulled-back coordinate of the `i`-th factor. -/
def chartRingEquiv (c : Fin 3 → Fin 2) :
    MvPolynomial (Fin 3) R ≃+* Γ(projectiveLineCube (Spec (.of R)), chartOpen _ c) :=
  RingEquiv.ofBijective (chartRingHom R c) ⟨chartRingHom_injective R c, chartRingHom_surjective R c⟩

/-- `chartRingEquiv R c` is `chartRingHom R c` as a function. -/
@[simp]
theorem chartRingEquiv_apply (c : Fin 3 → Fin 2) (p : MvPolynomial (Fin 3) R) :
    chartRingEquiv R c p = chartRingHom R c p := rfl

/-- Over `Spec R`, the cyclic permutation pulls back the scalars of the base to themselves. -/
theorem rotation_appLE_chartScalar (c : Fin 3 → Fin 2)
    (e : chartOpen _ (rotateChart c) ≤
      (rotation (Spec (.of R)) (projectiveSpaceAtUniverse.{u} 1)).hom ⁻¹ᵁ chartOpen _ c)
    (r : R) :
    (rotation (Spec (.of R)) (projectiveSpaceAtUniverse.{u} 1)).hom.appLE (chartOpen _ c)
        (chartOpen _ (rotateChart c)) e (chartScalar R c r) = chartScalar R (rotateChart c) r := by
  exact appLE_appLE_apply_of_comp_eq _ _ (permutation_toBase _ _ _) le_top e le_top _

/-- **The cyclic permutation on the chart rings**: pulling back along `ρ` from `V_c` to
`ρ⁻¹ V_c` is the substitution `xᵢ ↦ x_{i+1}`. -/
theorem rotation_appLE_chartRingHom (c : Fin 3 → Fin 2)
    (e : chartOpen _ (rotateChart c) ≤
      (rotation (Spec (.of R)) (projectiveSpaceAtUniverse.{u} 1)).hom ⁻¹ᵁ chartOpen _ c)
    (p : MvPolynomial (Fin 3) R) :
    (rotation (Spec (.of R)) (projectiveSpaceAtUniverse.{u} 1)).hom.appLE (chartOpen _ c)
        (chartOpen _ (rotateChart c)) e (chartRingHom R c p) =
      chartRingHom R (rotateChart c) (MvPolynomial.rename (· + 1) p) := by
  have h : ((rotation (Spec (.of R)) (projectiveSpaceAtUniverse.{u} 1)).hom.appLE (chartOpen _ c)
      (chartOpen _ (rotateChart c)) e).hom.comp (chartRingHom R c) =
      (chartRingHom R (rotateChart c)).comp (MvPolynomial.rename (R := R) (· + 1)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · change ((rotation (Spec (.of R)) (projectiveSpaceAtUniverse.{u} 1)).hom.appLE
          (chartOpen _ c) (chartOpen _ (rotateChart c)) e).hom (chartRingHom R c
            (MvPolynomial.C r)) = chartRingHom R (rotateChart c)
              (MvPolynomial.rename (· + 1) (MvPolynomial.C r))
      rw [chartRingHom_C, rotation_appLE_chartScalar, MvPolynomial.rename_C, chartRingHom_C]
    · change ((rotation (Spec (.of R)) (projectiveSpaceAtUniverse.{u} 1)).hom.appLE
          (chartOpen _ c) (chartOpen _ (rotateChart c)) e).hom (chartRingHom R c
            (MvPolynomial.X i)) = chartRingHom R (rotateChart c)
              (MvPolynomial.rename (· + 1) (MvPolynomial.X i))
      rw [chartRingHom_X, rotation_appLE_chartCoordinate, MvPolynomial.rename_X, chartRingHom_X]
  exact DFunLike.congr_fun h p

/-- The chart ring homomorphism applied to an integer polynomial is its evaluation at the chart
coordinates. -/
theorem chartRingHom_map_intCast (c : Fin 3 → Fin 2) (p : MvPolynomial (Fin 3) ℤ) :
    chartRingHom R c (MvPolynomial.map (Int.castRingHom R) p) =
      MvPolynomial.eval₂ (Int.castRingHom _) (chartCoordinate _ c) p := by
  rw [chartRingHom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map]
  congr 1
  exact RingHom.ext_int _ _

end Affine

end projectiveLineCube

end AlgebraicGeometry
