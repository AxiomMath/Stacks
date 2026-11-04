module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjTheta.TwistRemarkSections
public import StacksFrontier.AlgebraicGeometry.ProjShifted.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseTensorCompatibility
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjModuleDegreeZeroFlat

/-!
# Stacks Tag 01QK: the twist square, at the constructed comparison of Tag 01QJ

In the situation of Stacks Tag 01QH — `X` a scheme, `𝓛` an ample invertible `𝒪_X`-module,
`S = Γ_*(X, 𝓛)`, `Y = Proj S` and `f : X ⟶ Y` the canonical morphism of Stacks Tag 01PZ — let
`θ_𝓕 : f^*M̃ ⟶ 𝓕`, `M = Γ_*(X, 𝓛, 𝓕)`, be the comparison of Stacks Tag 01QJ,
`Stacks.SectionRingProjQuasicoherent.pullbackTildeComparison`.

This file sets up the objects of the square of Stacks Tag 01QK and the chart-level facts its proof
uses:

* on a good chart `X_s`, `θ_𝓕` sends the pullback of a section over `D₊(s)` to the division of its
  representative by the powers of `s` (`pullbackTildeComparison_app_pullbackSection`), and every
  section of `f^*A` over `X_s` is pulled back from `D₊(s)` (`pullbackSection_surjective`);
* the division by the powers of `s` is multiplicative for the tensor product
  (`tensorSection_localDivision`);
* the obvious identifications `M(n)~ ≅ (Γ_*(X, 𝓛, 𝓕 ⊗ N))~` and `𝒪_Y(n) ≅ (Γ_*(X, 𝓛, N))~`
  attached to an isomorphism `𝓛^{⊗ e} ≅ N ⊙ k`, `n = e - k` (`twistIdent`, `unitTwistIdent`);
* the top arrow of the square, the pullback of the multiplication of Equation 01MQ (`twistTop`),
  and both paths of the square on pulled-back sections.

The square itself is `Stacks.SectionRingProjTheta.twistSquareInt`, and assertion (i) is
`Stacks.SectionRingProjTheta.projTheta_app_eq_twistThetaInt`.

## Main definitions

* `Stacks.SectionRingProjTheta.twistIdent`, `Stacks.SectionRingProjTheta.unitTwistIdent`.
* `Stacks.SectionRingProjTheta.twistTop`.

## References

* [Stacks Project, Tag 01QK](https://stacks.math.columbia.edu/tag/01QK)
* [Stacks Project, Tag 01QJ](https://stacks.math.columbia.edu/tag/01QJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace Opposite
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections sectionRing mul)
open Stacks.TwistedSections (twistPow twistSections twistModule moduleGrading)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)
open Stacks.SectionRingProjQuasicoherent (tildeFunctor pullbackTildeFunctor
  pullbackTildeComparison gluedComparison GoodChart localDivision unitSec powMul tildeModule)
open scoped TensorProduct

universe u

namespace Stacks.SectionRingProjTheta

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local instance] ProjectiveSpectrum.isPrime

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (hL : Stacks.Ample.IsAmple X L)

section Chart

variable [IsOpenImmersion (projHomOfIsAmple L hL)]

/-! ### Tag 01QJ's comparison on a pulled-back fraction -/

/-- The standard open `D₊(s)` of a good chart. -/
abbrev chartOpen (c : GoodChart L hL) : (AlgebraicGeometry.Proj (grading L)).Opens :=
  AlgebraicGeometry.Proj.basicOpen (grading L) (DirectSum.of (powSections L) c.1.deg c.1.val)

/-- The chart `X_s` lies in the preimage of `D₊(s)` under `f`. -/
theorem nvOpen_le_preimage (c : GoodChart L hL) :
    nvOpen L c.1.val ≤ projHomOfIsAmple L hL ⁻¹ᵁ chartOpen L hL c :=
  (Stacks.SectionRingProjMorphism.projHomOfIsAmple_preimage_projBasicOpen L hL c.1.val
    c.1.deg_pos).ge

/-- **The comparison `M̃|_X ⟶ 𝓕` on a chart**, unfolded. -/
theorem gluedComparison_app_eq (F : X.Modules) (c : GoodChart L hL)
    (x : Γ((tildeModule L F).restrict (projHomOfIsAmple L hL), nvOpen L c.1.val)) :
    (gluedComparison L hL F).app (nvOpen L c.1.val) x =
      localDivision L F c.1.val le_rfl
        (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (grading L)
          (moduleGrading F L) (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val)
          c.1.deg_pos
          ((ProjectiveSpectrum.Proj.imageSectionsIso (projHomOfIsAmple L hL)
            (tildeModule L F) (nvOpen L c.1.val) _
            (Stacks.SectionRingProjQuasicoherent.image_nvOpen L hL c)).hom x)) := by
  have hg := Stacks.SectionRingProjQuasicoherent.gluedComparison_app L hL F c
  exact congrArg (fun ψ : ((tildeModule L F).restrict (projHomOfIsAmple L hL)).val.obj
      (op (nvOpen L c.1.val)) ⟶ F.val.obj (op (nvOpen L c.1.val)) =>
    ConcreteCategory.hom ψ x) hg

/-- Restricting a section of a module to a smaller open and back returns it. -/
private theorem presheaf_map_map_self {Y : Scheme.{u}} (M : Y.Modules) {U V : Y.Opens}
    (a : op U ⟶ op V) (b : op V ⟶ op U) (y : Γ(M, U)) :
    M.presheaf.map b (M.presheaf.map a y) = y :=
  (Stacks.SectionRingProjQuasicoherent.presheaf_map_map M a b (𝟙 _) y).trans (by simp)

/-- `imageSectionsIso` undoes the restriction from `D₊(s)` to the image of `X_s`. -/
theorem imageSectionsIso_hom_map (F : X.Modules) (c : GoodChart L hL)
    (y : Γ(tildeModule L F, chartOpen L hL c)) :
    (ProjectiveSpectrum.Proj.imageSectionsIso (projHomOfIsAmple L hL)
        (tildeModule L F) (nvOpen L c.1.val) _
        (Stacks.SectionRingProjQuasicoherent.image_nvOpen L hL c)).hom
      ((tildeModule L F).val.map (homOfLE
        (le_of_eq (Stacks.SectionRingProjQuasicoherent.image_nvOpen L hL c))).op y) = y := by
  refine (Stacks.SectionRingProjQuasicoherent.imageSectionsIso_hom_apply _ _ _ _ _ _).trans ?_
  exact presheaf_map_map_self (tildeModule L F) _ _ y

/-- **Tag 01QJ's comparison on the pullback of a section over `D₊(s)`** is the division by the
powers of `s` of the fraction the section names. -/
theorem pullbackTildeComparison_app_pullbackSection (F : X.Modules) (c : GoodChart L hL)
    (y : Γ((tildeFunctor L).obj F, chartOpen L hL c)) :
    ((pullbackTildeComparison L hL).app F).app (nvOpen L c.1.val)
        (Scheme.Modules.pullbackSection (projHomOfIsAmple L hL) ((tildeFunctor L).obj F)
          (chartOpen L hL c) (nvOpen L c.1.val) (nvOpen_le_preimage L hL c) y) =
      localDivision L F c.1.val le_rfl
        (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (grading L)
          (moduleGrading F L) (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val)
          c.1.deg_pos y) := by
  have h := Stacks.SectionRingProjQuasicoherent.pullbackTildeComparison_app L hL F
  have h2 := Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection
    (projHomOfIsAmple L hL) ((tildeFunctor L).obj F) (chartOpen L hL c) (nvOpen L c.1.val)
    (nvOpen_le_preimage L hL c)
    (le_of_eq (Stacks.SectionRingProjQuasicoherent.image_nvOpen L hL c)) y
  refine (congrArg (fun φ : (pullbackTildeFunctor L hL).obj F ⟶ F => φ.app (nvOpen L c.1.val)
    (Scheme.Modules.pullbackSection (projHomOfIsAmple L hL) ((tildeFunctor L).obj F)
      (chartOpen L hL c) (nvOpen L c.1.val) (nvOpen_le_preimage L hL c) y)) h).trans ?_
  refine (congrArg ((gluedComparison L hL F).app (nvOpen L c.1.val)) h2).trans ?_
  refine (gluedComparison_app_eq L hL F c _).trans ?_
  exact congrArg (fun w => localDivision L F c.1.val le_rfl
    (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (grading L)
      (moduleGrading F L) (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val)
      c.1.deg_pos w)) (imageSectionsIso_hom_map L hL F c y)

/-- **Every section of `f^*A` over `X_s` is pulled back from `D₊(s)`.** -/
theorem pullbackSection_surjective (A : (AlgebraicGeometry.Proj (grading L)).Modules)
    (c : GoodChart L hL) :
    Function.Surjective (Scheme.Modules.pullbackSection (projHomOfIsAmple L hL) A
      (chartOpen L hL c) (nvOpen L c.1.val) (nvOpen_le_preimage L hL c)) := by
  intro y
  have him := Stacks.SectionRingProjQuasicoherent.image_nvOpen L hL c
  refine ⟨A.val.map (homOfLE (le_of_eq him.symm)).op
    (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback
      (projHomOfIsAmple L hL)).inv.app A) (nvOpen L c.1.val) y), ?_⟩
  have h2 := Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection
    (projHomOfIsAmple L hL) A (chartOpen L hL c) (nvOpen L c.1.val)
    (nvOpen_le_preimage L hL c) (le_of_eq him)
    (A.val.map (homOfLE (le_of_eq him.symm)).op
      (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback
        (projHomOfIsAmple L hL)).inv.app A) (nvOpen L c.1.val) y))
  have h3 : A.val.map (homOfLE (le_of_eq him)).op (A.val.map (homOfLE (le_of_eq him.symm)).op
      (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback
        (projHomOfIsAmple L hL)).inv.app A) (nvOpen L c.1.val) y)) =
      Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback
        (projHomOfIsAmple L hL)).inv.app A) (nvOpen L c.1.val) y := by
    exact presheaf_map_map_self A _ _ _
  have hinj : Function.Injective (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback
      (projHomOfIsAmple L hL)).inv.app A) (nvOpen L c.1.val)) :=
    (ConcreteCategory.bijective_of_isIso _).1
  exact hinj (h2.trans h3)

end Chart

/-! ### Multiplication by the powers of a section, through the external product -/

section Powers

open Stacks.SectionExtension (powSec)

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow
  Stacks.TwistedSections.twistPow

/-- **Multiplication by `aᵏ` is multiplication by the section `aᵏ`**, in the grouped form. -/
theorem powMul_eq_smulRight (F : X.Modules) {d : ℕ} (a : powSections L d) (k : ℕ) :
    powMul L F a k = smulRight F (powSec L a k) := by
  rw [Stacks.SectionRingProjQuasicoherent.powMul_eq_twistMul, ← twistMul_zero_eq]
  simp

omit [Ample.IsInvertibleModule X L] in
/-- Transporting a section along an equality of degrees transports the multiplication. -/
theorem smulRight_comp_eqToHom (A : X.Modules) {i j : ℕ} (h : i = j)
    (a : 𝟙_ X.Modules ⟶ natTensorPow L i) :
    smulRight A a ≫ eqToHom (congrArg (twistPow A L) h) =
      smulRight A (a ≫ eqToHom (congrArg (natTensorPow L) h)) := by
  subst h
  simp

omit [Ample.IsInvertibleModule X L] in
/-- **`aˡ aᵏ = a^{k + l}`** in the section ring, up to the transport of degrees. -/
theorem mul_powSec_powSec {d : ℕ} (a : powSections L d) (k l : ℕ) :
    mul (powSec L a l) (powSec L a k) ≫
        eqToHom (congrArg (natTensorPow L)
          ((Nat.add_comm (d * l) (d * k)).trans (Nat.mul_add d k l).symm)) =
      powSec L a (k + l) := by
  apply DirectSum.of_injective (β := powSections L) (d * (k + l))
  rw [Stacks.SectionRingProjQuasicoherent.of_comp_eqToHom,
    Stacks.SectionRingChartMap.of_mul_eq, Stacks.SectionRingChartMap.of_powSec_eq_pow,
    Stacks.SectionRingChartMap.of_powSec_eq_pow, Stacks.SectionRingChartMap.of_powSec_eq_pow,
    ← pow_add, add_comm]
  all_goals ring

/-- **Division by powers of a section is multiplicative for the external product**: multiplying
`F` by `aᵏ` and `G` by `aˡ` and taking the external product is multiplying `F ⊗ G` by
`a^{k + l}`. -/
theorem powMul_tensorHom_extProd (F G : X.Modules) {d : ℕ} (a : powSections L d) (k l : ℕ) :
    (powMul L F a k ⊗ₘ powMul L G a l) ≫ extProd F G (d * k) (d * l) ≫
        eqToHom (congrArg (twistPow (F ⊗ G) L)
          ((Nat.add_comm (d * l) (d * k)).trans (Nat.mul_add d k l).symm)) =
      powMul L (F ⊗ G) a (k + l) := by
  rw [powMul_eq_smulRight, powMul_eq_smulRight, powMul_eq_smulRight,
    ← Category.assoc, smulRight_tensorHom_extProd, smulRight_comp_eqToHom, mul_powSec_powSec]
  all_goals ring

open Stacks.TwistedSections (twistCongr) in
/-- **The division by powers of a section is multiplicative**: the product of `t / sᵖ` and
`t' / s^q` is `z / s^{p + q}` whenever `z` is the external product of `t` and `t'`. -/
theorem tensorSection_localDivision (F G : X.Modules) {d : ℕ} (a : powSections L d) {U : X.Opens}
    (hU : U ≤ nvOpen L a) (p q : ℕ)
    (u : GradedModuleDegreeZeroLocalization (grading L) (moduleGrading F L)
      (DirectSum.of (powSections L) d a))
    (v : GradedModuleDegreeZeroLocalization (grading L) (moduleGrading G L)
      (DirectSum.of (powSections L) d a))
    (w : GradedModuleDegreeZeroLocalization (grading L) (moduleGrading (F ⊗ G) L)
      (DirectSum.of (powSections L) d a))
    (t : twistSections F L (p * d)) (t' : twistSections G L (q * d))
    (z : twistSections (F ⊗ G) L ((p + q) * d))
    (hu : (u : LocalizedModule.Away (DirectSum.of (powSections L) d a) (twistModule F L)) =
      LocalizedModule.mk (S := Submonoid.powers (DirectSum.of (powSections L) d a))
        (DirectSum.of (twistSections F L) (p * d) t)
        ⟨DirectSum.of (powSections L) d a ^ p, ⟨p, rfl⟩⟩)
    (hv : (v : LocalizedModule.Away (DirectSum.of (powSections L) d a) (twistModule G L)) =
      LocalizedModule.mk (S := Submonoid.powers (DirectSum.of (powSections L) d a))
        (DirectSum.of (twistSections G L) (q * d) t')
        ⟨DirectSum.of (powSections L) d a ^ q, ⟨q, rfl⟩⟩)
    (hw : (w : LocalizedModule.Away (DirectSum.of (powSections L) d a) (twistModule (F ⊗ G) L)) =
      LocalizedModule.mk (S := Submonoid.powers (DirectSum.of (powSections L) d a))
        (DirectSum.of (twistSections (F ⊗ G) L) ((p + q) * d) z)
        ⟨DirectSum.of (powSections L) d a ^ (p + q), ⟨p + q, rfl⟩⟩)
    (hz : twistCongr (Nat.mul_comm (p + q) d) z =
      (λ_ (𝟙_ X.Modules)).inv ≫ (twistCongr (Nat.mul_comm p d) t ⊗ₘ
        twistCongr (Nat.mul_comm q d) t') ≫ extProd F G (d * p) (d * q) ≫
          eqToHom (congrArg (twistPow (F ⊗ G) L)
            ((Nat.add_comm (d * q) (d * p)).trans (Nat.mul_add d p q).symm))) :
    Stacks.SectionTensorFormula.tensorSection F G (localDivision L F a hU u)
        (localDivision L G a hU v) = localDivision L (F ⊗ G) a hU w := by
  apply (Stacks.SectionRingProjQuasicoherent.bijective_powMul_app L (F ⊗ G) a hU (p + q)).1
  rw [Stacks.SectionRingProjQuasicoherent.powMul_app_localDivision L (F ⊗ G) a hU w (p + q) z hw,
    ← powMul_tensorHom_extProd L F G a p q]
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [tensorSection_tensorHom,
    Stacks.SectionRingProjQuasicoherent.powMul_app_localDivision L F a hU u p t hu,
    Stacks.SectionRingProjQuasicoherent.powMul_app_localDivision L G a hU v q t' hv,
    tensorSection_unitSec, ← Stacks.SectionRingProjQuasicoherent.unitSec_comp,
    ← Stacks.SectionRingProjQuasicoherent.unitSec_comp, hz]
  simp only [Category.assoc]

end Powers

/-! ### The obvious identifications, on the associated sheaves -/

section Ident

open Stacks.AlgebraicGeometry.ProjSheafFunctoriality (associatedModuleSheafMap
  associatedModuleSheafMap_standardOpen)
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections
  (isIso_associatedModuleSheafMap_of_eventually_bijective)
open Stacks.GradedModule (shiftedGrading)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (associatedModuleSheaf twistingSheaf)

variable (F N : X.Modules) {e k : ℕ} (β : natTensorPow L e ≅ twistPow N L k) {n : ℤ}
  (he : (e : ℤ) = n + k)

/-- The left leg of `M(n)~ ≅ (Γ_*(X, 𝓛, 𝓕 ⊗ N))~`, on the associated sheaves. -/
def identSheafLeft :
    (associatedModuleSheaf (grading L)
        (shiftedGrading (moduleGrading (twistPow (F ⊗ N) L k) L) (-(k : ℤ))) :
          (AlgebraicGeometry.Proj (grading L)).Modules) ⟶
      (associatedModuleSheaf (grading L) (shiftedGrading (moduleGrading F L) n) :
          (AlgebraicGeometry.Proj (grading L)).Modules) :=
  associatedModuleSheafMap (grading L) _ _ (identLeft F N β) (identLeft_mem F N β he)

/-- `identSheafLeft` is an isomorphism. -/
theorem isIso_identSheafLeft : IsIso (identSheafLeft L F N β he) :=
  isIso_associatedModuleSheafMap_of_eventually_bijective (grading L) _ _ _ _ (N₀ := k)
    (fun j _ x hx h => identLeft_injective F N β j x hx h)
    (fun j hj y hy => identLeft_surjective F N β he j hj y hy)

/-- The right leg of the identifications, on the associated sheaves: the shift by `k`. -/
def identSheafRight (G : X.Modules) (k : ℕ) :
    (associatedModuleSheaf (grading L)
        (shiftedGrading (moduleGrading (twistPow G L k) L) (-(k : ℤ))) :
          (AlgebraicGeometry.Proj (grading L)).Modules) ⟶ (tildeFunctor L).obj G :=
  associatedModuleSheafMap (grading L) _ _ (twistShiftLinearMap G L k) (identRight_mem G k)

/-- `identSheafRight` is an isomorphism. -/
theorem isIso_identSheafRight (G : X.Modules) (k : ℕ) : IsIso (identSheafRight L G k) :=
  isIso_associatedModuleSheafMap_of_eventually_bijective (grading L) _ _ _ _ (N₀ := k)
    (fun j _ x hx h => identRight_injective G k j x hx h)
    (fun j hj y hy => identRight_surjective G k j hj y hy)

/-- **The obvious identification `M(n)~ ≅ (Γ_*(X, 𝓛, 𝓕 ⊗ N))~`** of Stacks Tag 01QK, for
`β : 𝓛^{⊗ e} ≅ N ⊙ k` with `e = n + k`. -/
def twistIdent :
    (associatedModuleSheaf (grading L) (shiftedGrading (moduleGrading F L) n) :
        (AlgebraicGeometry.Proj (grading L)).Modules) ≅ (tildeFunctor L).obj (F ⊗ N) :=
  haveI := isIso_identSheafLeft L F N β he
  haveI := isIso_identSheafRight L (F ⊗ N) k
  (asIso (identSheafLeft L F N β he)).symm ≪≫ asIso (identSheafRight L (F ⊗ N) k)

/-- The left leg of `𝒪_Y(n) ≅ (Γ_*(X, 𝓛, N))~`, on the associated sheaves. -/
def unitSheafLeft :
    (associatedModuleSheaf (grading L)
        (shiftedGrading (moduleGrading (twistPow N L k) L) (-(k : ℤ))) :
          (AlgebraicGeometry.Proj (grading L)).Modules) ⟶
      (twistingSheaf (grading L) n : (AlgebraicGeometry.Proj (grading L)).Modules) :=
  associatedModuleSheafMap (grading L) _ _ (unitIdent N β) (unitIdent_mem N β he)

/-- `unitSheafLeft` is an isomorphism. -/
theorem isIso_unitSheafLeft : IsIso (unitSheafLeft L N β he) :=
  isIso_associatedModuleSheafMap_of_eventually_bijective (grading L) _ _ _ _ (N₀ := k)
    (fun j _ x hx h => unitIdent_injective N β j x hx h)
    (fun j hj y hy => unitIdent_surjective N β he j hj y hy)

/-- **The identification `𝒪_Y(n) ≅ (Γ_*(X, 𝓛, N))~`** that Stacks Tag 01QK uses to read Tag
01QI's map as `θ_N`, for `β : 𝓛^{⊗ e} ≅ N ⊙ k` with `e = n + k`. -/
def unitTwistIdent :
    (twistingSheaf (grading L) n : (AlgebraicGeometry.Proj (grading L)).Modules) ≅
      (tildeFunctor L).obj N :=
  haveI := isIso_unitSheafLeft L N β he
  haveI := isIso_identSheafRight L N k
  (asIso (unitSheafLeft L N β he)).symm ≪≫ asIso (identSheafRight L N k)

/-- **The obvious identification `(Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ n}))~ ⟶ M(n)~`** of Stacks Tag 01QK, for
`n ≥ 0`. It is an isomorphism (`isIso_identSheafNat`). -/
def identSheafNat (F : X.Modules) (n : ℕ) :
    (tildeFunctor L).obj (F ⊗ natTensorPow L n) ⟶
      (associatedModuleSheaf (grading L) (shiftedGrading (moduleGrading F L) n) :
          (AlgebraicGeometry.Proj (grading L)).Modules) :=
  associatedModuleSheafMap (grading L) _ _ (identNat F n) (identNat_mem F n)

/-- `identSheafNat` is an isomorphism. -/
instance isIso_identSheafNat (F : X.Modules) (n : ℕ) : IsIso (identSheafNat L F n) :=
  isIso_associatedModuleSheafMap_of_eventually_bijective (grading L) _ _ _ _ (N₀ := 0)
    (fun j _ x hx h => identNat_injective F n j x hx h)
    (fun j hj y hy => identNat_surjective F n j hj y hy)

/-- **The identification `(Γ_*(X, 𝓛, 𝓛^{⊗ n}))~ ⟶ 𝒪_Y(n)`** that Stacks Tag 01QK uses to read
Tag 01QI's map as `θ_{𝓛^{⊗ n}}`, for `n ≥ 0`. It is an isomorphism (`isIso_unitSheafNat`). -/
def unitSheafNat (n : ℕ) :
    (tildeFunctor L).obj (natTensorPow L n) ⟶
      (twistingSheaf (grading L) n : (AlgebraicGeometry.Proj (grading L)).Modules) :=
  associatedModuleSheafMap (grading L) _ _ (unitShiftLinearMap L n) (unitShiftLinearMap_mem n)

/-- `unitSheafNat` is an isomorphism. -/
instance isIso_unitSheafNat (n : ℕ) : IsIso (unitSheafNat L n) :=
  isIso_associatedModuleSheafMap_of_eventually_bijective (grading L) _ _ _ _ (N₀ := 0)
    (fun j _ x hx h => unitShiftLinearMap_injective n j x hx h)
    (fun j hj y hy => unitShiftLinearMap_surjective n j hj y hy)

end Ident

/-! ### The identifications on fractions -/

section Fraction

open Stacks.AlgebraicGeometry.ProjSheafFunctoriality (associatedModuleSheafMap
  associatedModuleSheafMap_standardOpen)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (associatedModuleSheaf
  associatedModuleSheafStandardOpenEquiv degreeZeroFraction)

variable {S M N : Type u} {σ τ υ : Type*} [CommRing S] [AddCommGroup M] [Module S M]
  [AddCommGroup N] [Module S N] [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]
  [SetLike υ N] [AddSubgroupClass υ N] (𝒩 : ℤ → υ) [DirectSum.Decomposition 𝒩]
  [SetLike.GradedSMul 𝒮 𝒩]

/-- **The map of associated sheaves on a homogeneous fraction** over `D₊(f)` is the fraction of
the image of the numerator. -/
theorem associatedModuleSheafMap_fraction (φ : M →ₗ[S] N) (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i)
    {f : S} {d : ℕ} (hf : f ∈ 𝒮 d) (hd : 0 < d) (p : ℕ) (m : M) (hm : m ∈ 𝒨 (p • (d : ℤ))) :
    (associatedModuleSheafMap 𝒮 𝒨 𝒩 φ hφ).val.app (op (ProjectiveSpectrum.basicOpen 𝒮 f))
        ((associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf hd).symm
          (degreeZeroFraction 𝒮 𝒨 hf p m hm)) =
      (associatedModuleSheafStandardOpenEquiv 𝒮 𝒩 hf hd).symm
        (degreeZeroFraction 𝒮 𝒩 hf p (φ m) (hφ _ m hm)) := by
  apply (associatedModuleSheafStandardOpenEquiv 𝒮 𝒩 hf hd).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [associatedModuleSheafMap_standardOpen, LinearEquiv.apply_symm_apply]
  simp [degreeZeroFraction, LocalizedModule.map_mk]

open Stacks.AlgebraicGeometry.ProjShifted (moduleTwistMap) in
open Stacks.GradedModule (shiftedGrading) in
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistGrading twistingSheaf) in
/-- **Equation 01MQ's multiplication on a pure tensor of homogeneous fractions** over `D₊(f)`:
`m / fᵖ ⊗ r / f^q ↦ r m / f^{p + q}`. -/
theorem moduleTwistMap_fraction (n : ℤ) {f : S} {d : ℕ} (hf : f ∈ 𝒮 d) (hd : 0 < d) (p q : ℕ)
    (m : M) (hm : m ∈ 𝒨 (p • (d : ℤ))) (r : S) (hr : r ∈ twistGrading 𝒮 n (q • (d : ℤ)))
    (hrm : r • m ∈ shiftedGrading 𝒨 n ((p + q) • (d : ℤ))) :
    (moduleTwistMap 𝒮 𝒨 n).val.app (op (ProjectiveSpectrum.basicOpen 𝒮 f))
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
          (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace _ _
          (op (ProjectiveSpectrum.basicOpen 𝒮 f))
          ((associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf hd).symm
              (degreeZeroFraction 𝒮 𝒨 hf p m hm) ⊗ₜ
            (associatedModuleSheafStandardOpenEquiv 𝒮 (twistGrading 𝒮 n) hf hd).symm
              (degreeZeroFraction 𝒮 (twistGrading 𝒮 n) hf q r hr))) =
      (associatedModuleSheafStandardOpenEquiv 𝒮 (shiftedGrading 𝒨 n) hf hd).symm
        (degreeZeroFraction 𝒮 (shiftedGrading 𝒨 n) hf (p + q) (r • m) hrm) := by
  let := Stacks.AlgebraicGeometry.ProjSheafFunctoriality.tensorGrading_decomposition (S := S) 𝒮 𝒨
    (twistGrading (S := S) 𝒮 n)
  let := Stacks.AlgebraicGeometry.ProjSheafFunctoriality.tensorGrading_gradedSMul (S := S) 𝒮 𝒨
    (twistGrading (S := S) 𝒮 n)
  have ht :=
    Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafTensorMap_standardOpen
      𝒮 𝒨 (twistGrading (S := S) 𝒮 n) hf hd p q m hm r hr
  have hr' := associatedModuleSheafMap_fraction 𝒮
    (Stacks.GradedModule.tensorGrading 𝒨 (twistGrading (S := S) 𝒮 n)) (shiftedGrading 𝒨 n)
    (TensorProduct.rid S M).toLinearMap (Stacks.GradedModule.rid_mem_shiftedGrading 𝒮 𝒨 n) hf hd
    (p + q) (m ⊗ₜ[S] r) (by
      apply AddSubgroup.subset_closure
      refine ⟨p • (d : ℤ), q • (d : ℤ), ?_, m, hm, r, hr, rfl⟩
      simp [add_mul])
  exact (congrArg (ConcreteCategory.hom
    ((Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafMap
    𝒮 (Stacks.GradedModule.tensorGrading 𝒨 (twistGrading (S := S) 𝒮 n)) (shiftedGrading 𝒨 n)
    (TensorProduct.rid S M).toLinearMap (Stacks.GradedModule.rid_mem_shiftedGrading 𝒮 𝒨 n)).val.app
      (op (ProjectiveSpectrum.basicOpen 𝒮 f)))) ht).trans hr'

end Fraction

/-! ### The sheaves on `Proj Γ_*(X, 𝓛)` the square involves -/

/-- `𝒪_Y(n)`, as a module on the scheme `Y = Proj Γ_*(X, 𝓛)`. -/
abbrev twistY (n : ℤ) : (AlgebraicGeometry.Proj (grading L)).Modules :=
  AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf (grading L) n

/-- `M(n)~` for `M = Γ_*(X, 𝓛, 𝓕)`, as a module on the scheme `Y = Proj Γ_*(X, 𝓛)`. -/
abbrev shiftY (F : X.Modules) (n : ℤ) : (AlgebraicGeometry.Proj (grading L)).Modules :=
  AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf (grading L)
    (Stacks.GradedModule.shiftedGrading (moduleGrading F L) n)

/-! ### The top arrow of the Remark's square -/

section Top

open Stacks.GradedModule (shiftedGrading)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (associatedModuleSheaf twistingSheaf)
open Stacks.SectionTensorFormula (tensorSheafIsoTensorObj schemeSheafCondition)

/-- **The top arrow of Stacks Tag 01QK's square**: `f^*M̃ ⊗ f^*𝒪_Y(n) ⟶ f^*(M(n)~)`, the
pullback along `f` of Equation 01MQ's multiplication `M̃ ⊗ 𝒪_Y(n) ⟶ M(n)~`
(`Stacks.AlgebraicGeometry.ProjShifted.moduleTwistMap`), read through the identification
`f^*A ⊗ f^*B ≅ f^*(A ⊗ B)` of Stacks Tag 01CD and the identification of the sheafified tensor
product with the monoidal one. -/
def twistTop (F : X.Modules) (n : ℤ) :
    (pullbackTildeFunctor L hL).obj F ⊗
        (Scheme.Modules.pullback (projHomOfIsAmple L hL)).obj (twistingSheaf (grading L) n) ⟶
      (Scheme.Modules.pullback (projHomOfIsAmple L hL)).obj
        (associatedModuleSheaf (grading L) (shiftedGrading (moduleGrading F L) n)) :=
  (tensorSheafIsoTensorObj X.presheaf (schemeSheafCondition X) _ _).inv ≫
    (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso (projHomOfIsAmple L hL)
      ((tildeFunctor L).obj F) (twistingSheaf (grading L) n)).inv ≫
    (Scheme.Modules.pullback (projHomOfIsAmple L hL)).map
      (Stacks.AlgebraicGeometry.ProjShifted.moduleTwistMap (grading L) (moduleGrading F L) n)

end Top

/-! ### The identifications on fractions -/

section IdentFraction

open Stacks.AlgebraicGeometry.ProjSheafFunctoriality (associatedModuleSheafMap)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (associatedModuleSheaf
  associatedModuleSheafStandardOpenEquiv degreeZeroFraction twistGrading)
open Stacks.GradedModule (shiftedGrading)

variable {F N : X.Modules} {e k : ℕ} (β : natTensorPow L e ≅ twistPow N L k) {n : ℤ}
  (he : (e : ℤ) = n + k)

/-- The inverse of an isomorphism of associated sheaves on the fraction of an image. -/
theorem inv_app_fraction {M₁ M₂ : Type u} {τ₁ τ₂ : Type*} [AddCommGroup M₁]
    [Module (sectionRing L) M₁]
    [AddCommGroup M₂] [Module (sectionRing L) M₂] [SetLike τ₁ M₁] [AddSubgroupClass τ₁ M₁]
    [SetLike τ₂ M₂] [AddSubgroupClass τ₂ M₂] (𝒨₁ : ℤ → τ₁) [DirectSum.Decomposition 𝒨₁]
    [SetLike.GradedSMul (grading L) 𝒨₁] (𝒨₂ : ℤ → τ₂) [DirectSum.Decomposition 𝒨₂]
    [SetLike.GradedSMul (grading L) 𝒨₂] (φ : M₁ →ₗ[sectionRing L] M₂)
    (hφ : ∀ i (m : M₁), m ∈ 𝒨₁ i → φ m ∈ 𝒨₂ i)
    [IsIso (associatedModuleSheafMap (grading L) 𝒨₁ 𝒨₂ φ hφ)]
    {f : sectionRing L} {d : ℕ} (hf : f ∈ grading L d) (hd : 0 < d) (p : ℕ) (m : M₁)
    (hm : m ∈ 𝒨₁ (p • (d : ℤ))) :
    (inv (associatedModuleSheafMap (grading L) 𝒨₁ 𝒨₂ φ hφ)).val.app
        (op (ProjectiveSpectrum.basicOpen (grading L) f))
        ((associatedModuleSheafStandardOpenEquiv (grading L) 𝒨₂ hf hd).symm
          (degreeZeroFraction (grading L) 𝒨₂ hf p (φ m) (hφ _ m hm))) =
      (associatedModuleSheafStandardOpenEquiv (grading L) 𝒨₁ hf hd).symm
        (degreeZeroFraction (grading L) 𝒨₁ hf p m hm) := by
  refine (congrArg (ConcreteCategory.hom ((inv (associatedModuleSheafMap (grading L) 𝒨₁ 𝒨₂ φ
    hφ)).val.app (op (ProjectiveSpectrum.basicOpen (grading L) f))))
      (associatedModuleSheafMap_fraction (grading L) 𝒨₁ 𝒨₂ φ hφ hf hd p m hm).symm).trans ?_
  exact congrArg (fun ψ : associatedModuleSheaf (grading L) 𝒨₁ ⟶
      associatedModuleSheaf (grading L) 𝒨₁ => (ψ.val.app
      (op (ProjectiveSpectrum.basicOpen (grading L) f))).hom
      ((associatedModuleSheafStandardOpenEquiv (grading L) 𝒨₁ hf hd).symm
        (degreeZeroFraction (grading L) 𝒨₁ hf p m hm)))
    (IsIso.hom_inv_id (associatedModuleSheafMap (grading L) 𝒨₁ 𝒨₂ φ hφ))

end IdentFraction

/-! ### Pulled-back sections -/

section PullbackSection

/-- **Stacks Tag 01CD on pulled-back sections**: the inverse of the identification
`f^*(A ⊗ B) ≅ f^*A ⊗ f^*B` sends the section of the pure tensor of two pulled-back sections to
the pullback of the section of the pure tensor. -/
theorem schemePullbackTensorIso_inv_pullbackSection {Y : Scheme.{u}} (g : X ⟶ Y)
    (A B : Y.Modules) (U : Y.Opens) (V : X.Opens) (h : V ≤ g ⁻¹ᵁ U) (a : Γ(A, U))
    (b : Γ(B, U)) :
    Scheme.Modules.Hom.app (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso g A B).inv V
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace
          ((Scheme.Modules.pullback g).obj A) ((Scheme.Modules.pullback g).obj B) (op V)
          (Scheme.Modules.pullbackSection g A U V h a ⊗ₜ
            Scheme.Modules.pullbackSection g B U V h b)) =
      Scheme.Modules.pullbackSection g _ U V h
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection Y.toRingedSpace A B
          (op U) (a ⊗ₜ b)) := by
  have hv := Stacks.Veronese.schemePullbackTensorIso_inv_toTensorSheafSection g A B U a b
  have hr := Stacks.Tag01VSPullbackTensor.homApp_presheaf_map
    (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso g A B).inv (homOfLE h)
    (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace
      ((Scheme.Modules.pullback g).obj A) ((Scheme.Modules.pullback g).obj B) (op (g ⁻¹ᵁ U))
      (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g A U a ⊗ₜ
        Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g B U b))
  rw [hv, Stacks.Tag01VSPullbackTensor.toTensorSheafSection_presheaf_map] at hr
  exact hr

end PullbackSection

/-! ### Stacks Tag 01QK -/

section Remark

open Stacks.GradedModule (shiftedGrading)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (associatedModuleSheaf twistingSheaf)

variable [IsOpenImmersion (projHomOfIsAmple L hL)]

/-- **The lower-left path of the square on the section of a pure tensor of pulled-back
sections.** -/
theorem tensorHom_app_pullbackSection (F N : X.Modules) (c : GoodChart L hL)
    {B : (AlgebraicGeometry.Proj (grading L)).Modules} (κ : B ⟶ (tildeFunctor L).obj N)
    (a : Γ((tildeFunctor L).obj F, chartOpen L hL c)) (b : Γ(B, chartOpen L hL c)) :
    Scheme.Modules.Hom.app ((pullbackTildeComparison L hL).app F ⊗ₘ
          ((Scheme.Modules.pullback (projHomOfIsAmple L hL)).map κ ≫
            (pullbackTildeComparison L hL).app N)) (nvOpen L c.1.val)
      (Stacks.SectionTensorFormula.tensorSection ((pullbackTildeFunctor L hL).obj F)
        ((Scheme.Modules.pullback (projHomOfIsAmple L hL)).obj B)
        (Scheme.Modules.pullbackSection (projHomOfIsAmple L hL) ((tildeFunctor L).obj F)
            (chartOpen L hL c) (nvOpen L c.1.val) (nvOpen_le_preimage L hL c) a)
        (Scheme.Modules.pullbackSection (projHomOfIsAmple L hL) B (chartOpen L hL c)
            (nvOpen L c.1.val) (nvOpen_le_preimage L hL c) b)) =
      Stacks.SectionTensorFormula.tensorSection F N
        (localDivision L F c.1.val le_rfl
          (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (grading L)
            (moduleGrading F L) (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val)
            c.1.deg_pos a))
        (localDivision L N c.1.val le_rfl
          (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (grading L)
            (moduleGrading N L) (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val)
            c.1.deg_pos (κ.app (chartOpen L hL c) b))) := by
  refine (tensorSection_tensorHom _ _ _ _).trans ?_
  congr 1
  · exact pullbackTildeComparison_app_pullbackSection L hL F c a
  · have hn := Scheme.Modules.pullbackSection_naturality (projHomOfIsAmple L hL) κ
      (chartOpen L hL c) (nvOpen L c.1.val) (nvOpen_le_preimage L hL c) b
    exact (congrArg (Scheme.Modules.Hom.app ((pullbackTildeComparison L hL).app N)
      (nvOpen L c.1.val)) hn).trans (pullbackTildeComparison_app_pullbackSection L hL N c _)

omit [IsOpenImmersion (projHomOfIsAmple L hL)] in
open Stacks.SectionTensorFormula (tensorSheafIsoTensorObj schemeSheafCondition) in
/-- Precomposed with the identification of the sheafified tensor product with the monoidal one,
`twistTop` is the inverse of the identification `f^*(A ⊗ B) ≅ f^*A ⊗ f^*B` followed by the
pullback of Equation 01MQ's multiplication. -/
theorem tensorSheafIsoTensorObj_hom_twistTop (F : X.Modules) (n : ℤ) :
    (tensorSheafIsoTensorObj X.presheaf (schemeSheafCondition X) _ _).hom ≫ twistTop L hL F n =
      (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso (projHomOfIsAmple L hL)
        ((tildeFunctor L).obj F) (twistingSheaf (grading L) n)).inv ≫
      (Scheme.Modules.pullback (projHomOfIsAmple L hL)).map
        (Stacks.AlgebraicGeometry.ProjShifted.moduleTwistMap (grading L) (moduleGrading F L) n) :=
  Iso.hom_inv_id_assoc _ _

/-- **The upper-right path of the square on the product of two pulled-back sections.** -/
theorem twistTop_comp_app_pullbackSection (F G : X.Modules) (n : ℤ) (c : GoodChart L hL)
    (κ : shiftY L F n ⟶ (tildeFunctor L).obj G)
    (a : Γ((tildeFunctor L).obj F, chartOpen L hL c)) (b : Γ(twistY L n, chartOpen L hL c)) :
    Scheme.Modules.Hom.app (twistTop L hL F n ≫
        (Scheme.Modules.pullback (projHomOfIsAmple L hL)).map κ ≫
          (pullbackTildeComparison L hL).app G) (nvOpen L c.1.val)
      (Stacks.SectionTensorFormula.tensorSection ((pullbackTildeFunctor L hL).obj F)
        ((Scheme.Modules.pullback (projHomOfIsAmple L hL)).obj (twistingSheaf (grading L) n))
        (Scheme.Modules.pullbackSection (projHomOfIsAmple L hL) ((tildeFunctor L).obj F)
            (chartOpen L hL c) (nvOpen L c.1.val) (nvOpen_le_preimage L hL c) a)
        (Scheme.Modules.pullbackSection (projHomOfIsAmple L hL) _ (chartOpen L hL c)
            (nvOpen L c.1.val) (nvOpen_le_preimage L hL c) b)) =
      localDivision L G c.1.val le_rfl
        (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (grading L)
          (moduleGrading G L) (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val)
          c.1.deg_pos (Scheme.Modules.Hom.app κ (chartOpen L hL c)
            (Scheme.Modules.Hom.app (Stacks.AlgebraicGeometry.ProjShifted.moduleTwistMap
              (grading L) (moduleGrading F L) n) (chartOpen L hL c)
              (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
                (AlgebraicGeometry.Proj (grading L)).toRingedSpace _ _
                (op (chartOpen L hL c)) (a ⊗ₜ b))))) := by
  have h1 := congrArg (fun (φ : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
        ((Scheme.Modules.pullback (projHomOfIsAmple L hL)).obj ((tildeFunctor L).obj F))).obj
          ((Scheme.Modules.pullback (projHomOfIsAmple L hL)).obj (twistY L n))) ⟶
      (Scheme.Modules.pullback (projHomOfIsAmple L hL)).obj (shiftY L F n)) =>
      Scheme.Modules.Hom.app (φ ≫
      (Scheme.Modules.pullback (projHomOfIsAmple L hL)).map κ ≫
        (pullbackTildeComparison L hL).app G) (nvOpen L c.1.val)
      (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace _ _
        (op (nvOpen L c.1.val))
        (Scheme.Modules.pullbackSection (projHomOfIsAmple L hL) ((tildeFunctor L).obj F)
            (chartOpen L hL c) (nvOpen L c.1.val) (nvOpen_le_preimage L hL c) a ⊗ₜ
          Scheme.Modules.pullbackSection (projHomOfIsAmple L hL) _ (chartOpen L hL c)
            (nvOpen L c.1.val) (nvOpen_le_preimage L hL c) b)))
    (tensorSheafIsoTensorObj_hom_twistTop L hL F n)
  simp only at h1
  refine h1.trans ?_
  simp only
  have e1 := schemePullbackTensorIso_inv_pullbackSection (projHomOfIsAmple L hL)
    ((tildeFunctor L).obj F) (twistY L n) (chartOpen L hL c) (nvOpen L c.1.val)
    (nvOpen_le_preimage L hL c) a b
  have e2 := Scheme.Modules.pullbackSection_naturality (projHomOfIsAmple L hL)
    (Stacks.AlgebraicGeometry.ProjShifted.moduleTwistMap (grading L) (moduleGrading F L) n)
    (chartOpen L hL c) (nvOpen L c.1.val) (nvOpen_le_preimage L hL c)
    (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
      (AlgebraicGeometry.Proj (grading L)).toRingedSpace _ _ (op (chartOpen L hL c)) (a ⊗ₜ b))
  have e3 := Scheme.Modules.pullbackSection_naturality (projHomOfIsAmple L hL) κ
    (chartOpen L hL c) (nvOpen L c.1.val) (nvOpen_le_preimage L hL c)
    (Scheme.Modules.Hom.app (Stacks.AlgebraicGeometry.ProjShifted.moduleTwistMap
      (grading L) (moduleGrading F L) n) (chartOpen L hL c)
      (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
        (AlgebraicGeometry.Proj (grading L)).toRingedSpace _ _ (op (chartOpen L hL c)) (a ⊗ₜ b)))
  refine (congrArg (fun z => Scheme.Modules.Hom.app ((pullbackTildeComparison L hL).app G)
    (nvOpen L c.1.val) (Scheme.Modules.Hom.app ((Scheme.Modules.pullback
      (projHomOfIsAmple L hL)).map κ) (nvOpen L c.1.val) (Scheme.Modules.Hom.app
        ((Scheme.Modules.pullback (projHomOfIsAmple L hL)).map
          (Stacks.AlgebraicGeometry.ProjShifted.moduleTwistMap (grading L) (moduleGrading F L) n))
        (nvOpen L c.1.val) z))) e1).trans ?_
  refine (congrArg (fun z => Scheme.Modules.Hom.app ((pullbackTildeComparison L hL).app G)
    (nvOpen L c.1.val) (Scheme.Modules.Hom.app ((Scheme.Modules.pullback
      (projHomOfIsAmple L hL)).map κ) (nvOpen L c.1.val) z)) e2).trans ?_
  refine (congrArg (fun z => Scheme.Modules.Hom.app ((pullbackTildeComparison L hL).app G)
    (nvOpen L c.1.val) z) e3).trans ?_
  exact pullbackTildeComparison_app_pullbackSection L hL G c _


end Remark

end Stacks.SectionRingProjTheta

end
