module

public import StacksFrontier.AlgebraicGeometry.DeRham.ProjConeChartForms
public import StacksFrontier.RingTheory.Cech.WeightedVariablesFormsCharts
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.OrderedCechCoordinates
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateConeFormsDerivedHomology
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBundleCover

/-!
# Clause (3) of Stacks 0FUR: the positive-weight part of the forms on the cone is acyclic

In the standard situation of Section 50.16 of the source let `r : Ω^a_{L/S} ⟶ 0_*Ω^a_{P/S}` be the
restriction of forms to the zero section of the cone `π : L ⟶ P` and `K` the kernel of `π_*r`.
Over a standard open `D₊(g)` of `P`, `g = ∏_{j ∈ t} yⱼ`, the sections of `K` are the forms on the
trivial line bundle `Spec A₍g₎[X]` vanishing on the zero section, which are exactly the forms of
positive weight on `A_g`; so the ordered Čech complex of `K` for the cover by the `D₊(yⱼ)` is the
positive part of the Čech complex `C^•(y₁, …, y_n; Ω^a_{A/R})`, which is exact
(`Cech.WeightedVariables.forms_exists_eq_cechD_of_posPart`). Hence `K` has no higher cohomology,
`π_*r` is an epimorphism, and the comparison `Rb_*Ω^a_{L/S} ⟶ i_*Rp_*Ω^a_{P/S}` is an isomorphism
on cohomology sheaves in degrees `≥ 1`: **clause (3) of [Stacks, Tag 0FUR]**.

## References

* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite KaehlerDifferential

universe u

/-! ### The identification of the localized forms is natural -/

namespace Cech.WeightedVariables

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]

/-- **The identification `M_g ≃ Ω_{A_g/R}` commutes with the transition maps of the Čech
complex**: `M_{g_s} → M_{g_t}` becomes the restriction of forms along `A_{g_s} → A_{g_t}`. -/
theorem locFormsEquiv_cechι {r : ℕ} (f : Fin r → A) (a : ℕ) {s t : Finset (Fin r)} (h : s ⊆ t)
    (z : Cech.cechMod f (⋀[A]^a (Ω[A⁄R])) s) :
    locFormsEquiv a (∏ i ∈ t, f i) (Cech.cechι f _ h z) =
      formsₛₗ (Stacks.ProjConeChartForms.locMap (R := R) (Finset.prod_dvd_prod_of_subset s t f h))
        a (locFormsEquiv a (∏ i ∈ s, f i) z) := by
  set S := ∏ i ∈ s, f i
  set T := ∏ i ∈ t, f i
  have hdiv : S ∣ T := Finset.prod_dvd_prod_of_subset s t f h
  -- the forms map along `A_S → A_T` on forms pulled back from `A`
  have hcomp : ∀ x : ⋀[A]^a (Ω[A⁄R]),
      formsₛₗ (Stacks.ProjConeChartForms.locMap (R := R) hdiv) a
        (mapExteriorPower R A (Localization.Away S) a x) =
        mapExteriorPower R A (Localization.Away T) a x := by
    intro x
    have hc : (Stacks.ProjConeChartForms.locMap (R := R) hdiv).comp
        (IsScalarTower.toAlgHom R A (Localization.Away S)) =
        IsScalarTower.toAlgHom R A (Localization.Away T) :=
      AlgHom.ext fun b => Stacks.ProjConeChartForms.locMap_algebraMap (R := R) hdiv b
    rw [← formsₛₗ_toAlgHom, formsₛₗ_comp, ← formsₛₗ_toAlgHom, hc]
  induction z using LocalizedModule.induction_on with
  | h m u =>
    have hu : IsUnit (algebraMap A (Localization.Away T) (u : A)) := by
      obtain ⟨_, k, rfl⟩ := u
      rw [map_pow]
      exact (isUnit_of_dvd_unit (map_dvd (algebraMap A (Localization.Away T)) hdiv)
        (IsLocalization.Away.algebraMap_isUnit T)).pow k
    have hinj : Function.Injective fun y : ⋀[Localization.Away T]^a (Ω[Localization.Away T⁄R]) =>
        algebraMap A (Localization.Away T) (u : A) • y := by
      intro y y' hyy'
      simpa only [smul_smul, IsUnit.val_inv_mul, one_smul] using
        congrArg (fun w => (hu.unit⁻¹ : (Localization.Away T)ˣ).val • w) hyy'
    refine hinj ?_
    simp only
    have h1 : (u : A) • LocalizedModule.mk m u =
        LocalizedModule.mk m (1 : Submonoid.powers S) := by
      rw [LocalizedModule.smul'_mk]
      exact LocalizedModule.mk_cancel u m
    have h2 : Cech.cechι f _ h ((u : A) • LocalizedModule.mk m u) =
        LocalizedModule.mk m (1 : Submonoid.powers T) := by
      rw [h1]
      exact Cech.cechι_mk f _ h m
    rw [algebraMap_smul, ← LinearEquiv.map_smul, ← LinearMap.map_smul, h2, locFormsEquiv_mk,
      locFormsEquiv_mk, map_smulₛₗ, hcomp, smul_smul]
    congr 1
    rw [← Stacks.ProjConeChartForms.locMap_algebraMap (R := R) hdiv]
    have e : ((Stacks.ProjConeChartForms.locMap (R := R) hdiv :
        Localization.Away S →ₐ[R] Localization.Away T) :
          Localization.Away S →+* Localization.Away T) (Localization.mk 1 u) =
        Stacks.ProjConeChartForms.locMap (R := R) hdiv (Localization.mk 1 u) :=
      rfl
    rw [e, ← map_mul, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, one_mul, mul_one,
      Localization.mk_self, map_one, Localization.mk_one]

end Cech.WeightedVariables

/-! ### Sections of modules on a scheme -/

namespace Stacks.ConeKernelSections

variable {X : Scheme.{u}}

/-- Two successive restrictions are one restriction. -/
theorem map_map_eq (M : X.Modules) {A B C : X.Opens} (g₁ : B ⟶ A) (g₂ : C ⟶ B) (g₃ : C ⟶ A)
    (x : Γ(M, A)) : M.presheaf.map g₂.op (M.presheaf.map g₁.op x) = M.presheaf.map g₃.op x := by
  rw [Subsingleton.elim g₃ (g₂ ≫ g₁), op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- Restriction along an equality of opens is injective. -/
theorem injective_map_eqToHom (M : X.Modules) {U V : X.Opens} (h : U = V) :
    Function.Injective (M.presheaf.map (eqToHom h).op) := by
  subst h
  rw [eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  exact fun _ _ hxy => hxy

/-- Restriction along an equality of opens is surjective. -/
theorem surjective_map_eqToHom (M : X.Modules) {U V : X.Opens} (h : U = V) :
    Function.Surjective (M.presheaf.map (eqToHom h).op) := by
  subst h
  rw [eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  exact fun y => ⟨y, rfl⟩

/-- A morphism of modules commutes with restriction of sections. -/
theorem app_naturality {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : U ⟶ V)
    (x : Γ(M, V)) :
    Scheme.Modules.Hom.app φ U (M.presheaf.map i.op x) =
      N.presheaf.map i.op (Scheme.Modules.Hom.app φ V x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) x

/-- An isomorphism of modules is injective on sections over every open. -/
theorem injective_app_of_isIso {M N : X.Modules} (φ : M ⟶ N) [IsIso φ] (U : X.Opens) :
    Function.Injective (Scheme.Modules.Hom.app φ U) :=
  (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app φ U)).1

/-- `f` kills the image in `M` of a section of the kernel of `f : M ⟶ N`. -/
theorem app_kernel_ι_eq_zero {M N : X.Modules} (f : M ⟶ N) (U : X.Opens) (x : Γ(kernel f, U)) :
    Scheme.Modules.Hom.app f U (Scheme.Modules.Hom.app (kernel.ι f) U x) = 0 := by
  have h := congrArg (fun φ => Scheme.Modules.Hom.app φ U x) (kernel.condition f)
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.zero_app] at h
  exact h

/-- A section sent to zero by an isomorphism of modules is zero. -/
theorem eq_zero_of_app_isIso {M N : X.Modules} (φ : M ⟶ N) [IsIso φ] (U : X.Opens)
    (x : Γ(M, U)) (h : Scheme.Modules.Hom.app φ U x = 0) : x = 0 :=
  injective_app_of_isIso φ U (h.trans (map_zero _).symm)

/-- If `φ ≫ ψ` kills `x`, with `ψ` an isomorphism, then `φ` kills `x`. -/
theorem app_eq_zero_of_comp_isIso {M N N' : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ N') [IsIso ψ]
    (U : X.Opens) (x : Γ(M, U)) (h : Scheme.Modules.Hom.app (φ ≫ ψ) U x = 0) :
    Scheme.Modules.Hom.app φ U x = 0 := by
  rw [Scheme.Modules.Hom.comp_app] at h
  exact eq_zero_of_app_isIso ψ U _ h

/-- `φ` kills the section of `M` over `f⁻¹U` underlying a section of the kernel of `f_*φ` over
`U`. -/
theorem app_pushforward_kernel_ι_eq_zero {Y : Scheme.{u}} (f : X ⟶ Y) {M N : X.Modules}
    (φ : M ⟶ N) (U : Y.Opens) (x : Γ(kernel ((Scheme.Modules.pushforward f).map φ), U)) :
    Scheme.Modules.Hom.app φ (f ⁻¹ᵁ U)
      (Scheme.Modules.Hom.app (kernel.ι ((Scheme.Modules.pushforward f).map φ)) U x) = 0 :=
  app_kernel_ι_eq_zero ((Scheme.Modules.pushforward f).map φ) U x

/-- If `φ ≫ ψ` kills `x`, with `ψ` an isomorphism, then `φ` kills every restriction of `x`. -/
theorem app_map_eq_zero_of_comp_isIso {M N N' : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ N') [IsIso ψ]
    {U V : X.Opens} (i : V ⟶ U) (x : Γ(M, U)) (h : Scheme.Modules.Hom.app (φ ≫ ψ) U x = 0) :
    Scheme.Modules.Hom.app φ V (M.presheaf.map i.op x) = 0 := by
  rw [app_naturality, app_eq_zero_of_comp_isIso φ ψ U x h, map_zero]

/-- If `ρ = φ ≫ ψ` kills `x`, with `ψ` an isomorphism, then `φ` kills every restriction of `x`. -/
theorem app_map_eq_zero_of_eq_comp {M N N' : X.Modules} (ρ : M ⟶ N') (φ : M ⟶ N) (ψ : N ⟶ N')
    [IsIso ψ] (hρ : ρ = φ ≫ ψ) {U V : X.Opens} (i : V ⟶ U) (x : Γ(M, U))
    (h : Scheme.Modules.Hom.app ρ U x = 0) :
    Scheme.Modules.Hom.app φ V (M.presheaf.map i.op x) = 0 := by
  subst hρ
  exact app_map_eq_zero_of_comp_isIso φ ψ i x h

/-- The section of `M` underlying a section of the kernel of `f : M ⟶ N`. -/
def kernelSection {M N : X.Modules} (f : M ⟶ N) (U : X.Opens) (x : Γ(kernel f, U)) : Γ(M, U) :=
  Scheme.Modules.Hom.app (kernel.ι f) U x

/-- The restriction of a section of `f_*M` over `U` to an open `V ⊆ f⁻¹U`, as a section of `M`. -/
def restrictPushforwardSection {Y : Scheme.{u}} (f : X ⟶ Y) {M : X.Modules} {U : Y.Opens}
    {V : X.Opens} (i : V ⟶ f ⁻¹ᵁ U) (y : Γ((Scheme.Modules.pushforward f).obj M, U)) : Γ(M, V) :=
  M.presheaf.map i.op y

/-- **A section of the kernel of `f_*ρ`, with `ρ = φ ≫ ψ` and `ψ` an isomorphism, is killed by `φ`
on every open inside its preimage.** -/
theorem app_map_pushforward_kernel_eq_zero {Y : Scheme.{u}} (f : X ⟶ Y) {M N N' : X.Modules}
    (ρ : M ⟶ N') (φ : M ⟶ N) (ψ : N ⟶ N') [IsIso ψ] (hρ : ρ = φ ≫ ψ) (U : Y.Opens)
    {V : X.Opens} (i : V ⟶ f ⁻¹ᵁ U)
    (x : Γ(kernel ((Scheme.Modules.pushforward f).map ρ), U)) :
    Scheme.Modules.Hom.app φ V (restrictPushforwardSection f i
      (kernelSection ((Scheme.Modules.pushforward f).map ρ) U x)) = 0 :=
  app_map_eq_zero_of_eq_comp ρ φ ψ hρ i _ (app_pushforward_kernel_ι_eq_zero f ρ U x)

/-- The inclusion of the kernel of `f` is injective on sections over every open. -/
theorem injective_app_kernel_ι {M N : X.Modules} (f : M ⟶ N) (U : X.Opens) :
    Function.Injective (Scheme.Modules.Hom.app (kernel.ι f) U) := by
  let T : X.Modules ⥤ ModuleCat Γ(X, U) := _root_.SheafOfModules.evaluation X.ringCatSheaf (op U)
  have : Mono (T.map (kernel.ι f)) :=
    @Functor.map_mono _ _ _ _ T
      (inferInstanceAs
        ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op U)).PreservesMonomorphisms))
      _ _ _ inferInstance
  exact (ModuleCat.mono_iff_injective _).mp this

/-! ### Sections of a kernel of a direct image, restricted to an open of the source -/

/-- **Sections of the kernel of `f` are the sections of the source killed by `f`.** -/
theorem exists_kernel_section {M N : X.Modules} (f : M ⟶ N) (U : X.Opens) (x : Γ(M, U))
    (hx : Scheme.Modules.Hom.app f U x = 0) :
    ∃ y : Γ(kernel f, U), Scheme.Modules.Hom.app (kernel.ι f) U y = x := by
  let T : X.Modules ⥤ ModuleCat Γ(X, U) := _root_.SheafOfModules.evaluation X.ringCatSheaf (op U)
  let _ : T.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  let _ : PreservesFiniteLimits T :=
    _root_.SheafOfModules.Finite.evaluationPreservesFiniteLimits X.ringCatSheaf (op U)
  exact (ShortComplex.moduleCat_exact_iff _).mp
    ((ShortComplex.exact_kernel f).map_of_mono_of_preservesKernel T inferInstance inferInstance)
    x hx

section Restricted

variable {Y : Scheme.{u}} (f : X ⟶ Y) {M N' : X.Modules} (ρ : M ⟶ N') (U : Y.Opens)
  {V : X.Opens} (i : V ⟶ f ⁻¹ᵁ U)

/-- A section of the kernel of `f_*ρ` over `U`, as a section of `M` over an open `V ⊆ f⁻¹U`. -/
def restrictedKernelHom : Γ(kernel ((Scheme.Modules.pushforward f).map ρ), U) →+ Γ(M, V) :=
  (show Γ((Scheme.Modules.pushforward f).obj M, U) →+ Γ(M, V) from
    (ConcreteCategory.hom (M.presheaf.map i.op))).comp
    (ConcreteCategory.hom (Scheme.Modules.Hom.app
      (kernel.ι ((Scheme.Modules.pushforward f).map ρ)) U))

/-- `restrictedKernelHom` is the restriction of the underlying section of `M`. -/
theorem restrictedKernelHom_apply (x : Γ(kernel ((Scheme.Modules.pushforward f).map ρ), U)) :
    restrictedKernelHom f ρ U i x =
      restrictPushforwardSection f i (kernelSection ((Scheme.Modules.pushforward f).map ρ) U x) :=
  rfl

/-- On an open equal to the preimage the restricted kernel section is injective. -/
theorem restrictedKernelHom_injective (hV : V = f ⁻¹ᵁ U) :
    Function.Injective (restrictedKernelHom f ρ U i) := by
  intro x y hxy
  obtain rfl : i = eqToHom hV := Subsingleton.elim _ _
  exact injective_app_kernel_ι ((Scheme.Modules.pushforward f).map ρ) U
    (injective_map_eqToHom M hV (show M.presheaf.map (eqToHom hV).op
      (Scheme.Modules.Hom.app (kernel.ι ((Scheme.Modules.pushforward f).map ρ)) U x) =
      M.presheaf.map (eqToHom hV).op
      (Scheme.Modules.Hom.app (kernel.ι ((Scheme.Modules.pushforward f).map ρ)) U y) from hxy))

/-- **The restricted kernel sections commute with restriction.** -/
theorem restrictedKernelHom_restr {U' : Y.Opens} (h : U' ≤ U) {V' : X.Opens} (i' : V' ⟶ f ⁻¹ᵁ U')
    (hVV : V' ≤ V) (x : Γ(kernel ((Scheme.Modules.pushforward f).map ρ), U)) :
    restrictedKernelHom f ρ U' i'
        ((kernel ((Scheme.Modules.pushforward f).map ρ)).presheaf.map (homOfLE h).op x) =
      M.presheaf.map (homOfLE hVV).op (restrictedKernelHom f ρ U i x) := by
  have hn := app_naturality (kernel.ι ((Scheme.Modules.pushforward f).map ρ)) (homOfLE h) x
  show M.presheaf.map i'.op (Scheme.Modules.Hom.app (kernel.ι _) U'
      ((kernel ((Scheme.Modules.pushforward f).map ρ)).presheaf.map (homOfLE h).op x)) =
    M.presheaf.map (homOfLE hVV).op (M.presheaf.map i.op
      (Scheme.Modules.Hom.app (kernel.ι ((Scheme.Modules.pushforward f).map ρ)) U x))
  rw [hn, Scheme.Modules.pushforward_obj_presheaf_map]
  exact (map_map_eq M ((TopologicalSpace.Opens.map f.base).map (homOfLE h)) i'
    (homOfLE hVV ≫ i) _).trans
    (map_map_eq M i (homOfLE hVV) (homOfLE hVV ≫ i) _).symm

/-- **A form on `V = f⁻¹U` killed by `φ`, where `ρ = φ ≫ ψ` with `ψ` an isomorphism, is the
restriction of a section of the kernel of `f_*ρ`.** -/
theorem exists_restrictedKernelHom_eq {N : X.Modules} {φ : M ⟶ N} (hV : V = f ⁻¹ᵁ U)
    (ω : Γ(M, V)) (hω : Scheme.Modules.Hom.app φ V ω = 0) {ψ : N ⟶ N'} [IsIso ψ]
    (hρ : ρ = φ ≫ ψ) :
    ∃ x, restrictedKernelHom f ρ U i x = ω := by
  obtain rfl : i = eqToHom hV := Subsingleton.elim _ _
  obtain ⟨ω', rfl⟩ := surjective_map_eqToHom M hV ω
  have hφ : Scheme.Modules.Hom.app φ (f ⁻¹ᵁ U) ω' = 0 := by
    have hn := app_naturality φ (eqToHom hV) ω'
    rw [hω] at hn
    exact injective_map_eqToHom N hV (hn.symm.trans (map_zero _).symm)
  have h0 : Scheme.Modules.Hom.app ((Scheme.Modules.pushforward f).map ρ) U ω' = 0 := by
    subst hρ
    show Scheme.Modules.Hom.app ψ (f ⁻¹ᵁ U) (Scheme.Modules.Hom.app φ (f ⁻¹ᵁ U) ω') = 0
    rw [hφ, map_zero]
  obtain ⟨x, hx⟩ := exists_kernel_section ((Scheme.Modules.pushforward f).map ρ) U ω' h0
  exact ⟨x, congrArg (M.presheaf.map (eqToHom hV).op) hx⟩

end Restricted

end Stacks.ConeKernelSections

namespace Stacks.DeRham.CoordinateCone

open Cech.WeightedVariables Stacks.ProjConeChartForms Stacks.Truncation Stacks.Truncation.Chart
open Stacks.AlgebraicGeometry.ProjAndSpec Stacks.AlgebraicGeometry.ProjAndSpecTruncation

variable (R : Type u) [CommRing R] (m n : ℕ) (a : ℕ)

/-! ### The charts of the kernel

The terms below are written out as in `Stacks.DeRham.CoordinateCone.coneFormsRestriction` and in
the statement of `isIso_homology_coneFormsDerivedComparison_of_vanishing`, rather than abbreviated:
the kernel checks a large concrete morphism against an abbreviation of it only by unfolding both
completely. -/

variable {R m n}

/-- For `j ∈ t`, the product `∏_{k ∈ t} yₖ` is homogeneous of degree `|t \ {j}| + 1`. -/
theorem prodY_mem {t : Finset (Fin n)} {j : Fin n} (hj : j ∈ t) :
    (∏ k ∈ t, yVar R m n k) ∈ yGrading R m n ((∑ _i ∈ t.erase j, 1) + 1) :=
  prod_yVar_mem_succ hj

/-- The variable `yⱼ` is homogeneous of degree `1`. -/
theorem yVar_mem_yGrading (j : Fin n) : yVar R m n j ∈ yGrading R m n 1 :=
  yVar_mem R m n j

/-- The product `∏_{k ∈ s} yₖ` is homogeneous of degree `|s|`. -/
theorem prod_yVar_mem_yGrading (s : Finset (Fin n)) :
    (∏ k ∈ s, yVar R m n k) ∈ yGrading R m n (∑ _i ∈ s, 1) :=
  prod_yVar_mem_natGrading s

/-- The Laurent chart of the punctured cone over `D₊(∏_{j ∈ t} yⱼ)` is the one of
`Cech.WeightedVariables.chartLaurent`: the forms of positive weight agree. -/
theorem posForms_eq {t : Finset (Fin n)} {j : Fin n} (hj : j ∈ t) :
    PolynomialDeRham.Chart.posForms (laurentAlgEquiv (𝒜 := yGrading R m n) (yVar_mem_yGrading j)
      (prod_yVar_mem_yGrading (t.erase j)) (yVar_mul_prod_erase hj)) a =
    PolynomialDeRham.Chart.posForms (chartLaurent R m hj) a :=
  rfl

/-- **The coordinates of a form on `L` over `D₊(∏_{j ∈ t} yⱼ)`**: the localized form of
`Ω^a_{A/R}` it restricts to on the punctured cone. -/
def formChart {t : Finset (Fin n)} {j : Fin n} (hj : j ∈ t)
    (ω : Γ(Scheme.Hom.relativeDifferentialForms (coneToBase R m n) (a : ℤ),
      chartOpen (yGrading R m n) (∏ k ∈ t, yVar R m n k))) :
    Cech.cechMod (yVar R m n) (Forms R m n a) t :=
  (locFormsEquiv a (∏ k ∈ t, yVar R m n k)).symm
    (KaehlerDifferential.formsₛₗ (restrictAlg (𝒜 := yGrading R m n) (prodY_mem hj)) a
      (chartForms (𝒜 := yGrading R m n) (coneToBase R m n) rfl (prodY_mem hj) (Nat.add_one_pos _) a
        ω))

/-- `formChart` of a form with given image under `chartForms`. -/
private theorem formChart_eq_of_chartForms_eq {t : Finset (Fin n)} {j : Fin n} (hj : j ∈ t)
    {ω : Γ(Scheme.Hom.relativeDifferentialForms (coneToBase R m n) (a : ℤ),
      chartOpen (yGrading R m n) (∏ k ∈ t, yVar R m n k))}
    {η : _}
    (h : chartForms (𝒜 := yGrading R m n) (coneToBase R m n) rfl (prodY_mem hj)
      (Nat.add_one_pos _) a ω = η) :
    formChart a hj ω = (locFormsEquiv a (∏ k ∈ t, yVar R m n k)).symm
      (KaehlerDifferential.formsₛₗ (restrictAlg (𝒜 := yGrading R m n) (prodY_mem hj)) a η) := by
  subst h
  rfl

/-- `formChart` is additive. -/
theorem formChart_add {t : Finset (Fin n)} {j : Fin n} (hj : j ∈ t)
    (ω ω' : Γ(Scheme.Hom.relativeDifferentialForms (coneToBase R m n) (a : ℤ),
      chartOpen (yGrading R m n) (∏ k ∈ t, yVar R m n k))) :
    formChart a hj (ω + ω') = formChart a hj ω + formChart a hj ω' := by
  refine (formChart_eq_of_chartForms_eq a hj (chartForms_add (𝒜 := yGrading R m n)
    (coneToBase R m n) rfl (prodY_mem hj) (Nat.add_one_pos _) a ω ω')).trans ?_
  unfold formChart
  exact (congrArg (locFormsEquiv a (∏ k ∈ t, yVar R m n k)).symm (LinearMap.map_add _ _ _)).trans
    (LinearEquiv.map_add _ _ _)

/-- `formChart` as an additive map. -/
def formChartHom {t : Finset (Fin n)} {j : Fin n} (hj : j ∈ t) :
    Γ(Scheme.Hom.relativeDifferentialForms (coneToBase R m n) (a : ℤ),
      chartOpen (yGrading R m n) (∏ k ∈ t, yVar R m n k)) →+
    Cech.cechMod (yVar R m n) (Forms R m n a) t :=
  AddMonoidHom.mk' (formChart a hj) (formChart_add a hj)

/-- `formChartHom` is `formChart`. -/
theorem formChartHom_apply {t : Finset (Fin n)} {j : Fin n} (hj : j ∈ t)
    (ω : Γ(Scheme.Hom.relativeDifferentialForms (coneToBase R m n) (a : ℤ),
      chartOpen (yGrading R m n) (∏ k ∈ t, yVar R m n k))) :
    formChartHom a hj ω = formChart a hj ω :=
  rfl

/-- **The coordinates of a form on `L` determine it.** -/
theorem formChart_injective {t : Finset (Fin n)} {j : Fin n} (hj : j ∈ t) :
    Function.Injective (formChart (R := R) (m := m) a hj) := by
  intro ω ω' h
  unfold formChart at h
  exact chartForms_injective (𝒜 := yGrading R m n) (coneToBase R m n) rfl (prodY_mem hj)
    (Nat.add_one_pos _) a (PolynomialDeRham.Chart.injective_formsₛₗ_restrict
      (restrictAlg_comp_polyAlgEquiv (𝒜 := yGrading R m n) (yVar_mem_yGrading j)
        (prod_yVar_mem_yGrading (t.erase j)) (yVar_mul_prod_erase hj)) a
      ((locFormsEquiv a _).symm.injective h))

open Stacks.ConeKernelSections in
/-- **A section of `K` restricts to zero on the zero section**, in the chart. -/
theorem formChart_kernel_zeroAlg {t : Finset (Fin n)} {j : Fin n} (hj : j ∈ t)
    (U : (coneBundle R m n).Opens)
    (i : chartOpen (yGrading R m n) (∏ k ∈ t, yVar R m n k) ⟶
      coneProjection R m n ⁻¹ᵁ U)
    (x : Γ(kernel ((Scheme.Modules.pushforward (coneProjection R m n)).map
      (coneFormsRestriction R m n (a : ℤ))), U)) :
    KaehlerDifferential.formsₛₗ (zeroAlg (𝒜 := yGrading R m n) (prodY_mem hj)) a
      (chartForms (𝒜 := yGrading R m n) (coneToBase R m n) rfl (prodY_mem hj) (Nat.add_one_pos _) a
        (restrictedKernelHom (coneProjection R m n) (coneFormsRestriction R m n (a : ℤ)) U i x)) =
      0 :=
  (formsDirectImageComparison_zeroSection_app_eq_zero_iff (coneToBase R m n) rfl
    (prodY_mem hj) a _).1 <| app_map_pushforward_kernel_eq_zero (coneProjection R m n)
      (coneFormsRestriction R m n (a : ℤ)) _ _ (coneFormsRestriction.eq_1 R m n (a : ℤ)) U i x

/-- **The coordinates of a section of `K` are forms of positive weight.** -/
theorem formChart_kernel_mem {t : Finset (Fin n)} {j : Fin n} (hj : j ∈ t)
    (U : (coneBundle R m n).Opens)
    (i : chartOpen (yGrading R m n) (∏ k ∈ t, yVar R m n k) ⟶
      coneProjection R m n ⁻¹ᵁ U)
    (x : Γ(kernel ((Scheme.Modules.pushforward (coneProjection R m n)).map
      (coneFormsRestriction R m n (a : ℤ))), U)) :
    formChart a hj (Stacks.ConeKernelSections.restrictedKernelHom (coneProjection R m n)
      (coneFormsRestriction R m n (a : ℤ)) U i x) ∈ posPart R m n a t := by
  rw [mem_posPart_iff a hj, formChart, LinearEquiv.apply_symm_apply]
  exact (posForms_eq a hj).le <| PolynomialDeRham.Chart.mem_posForms
    (restrictAlg_comp_polyAlgEquiv (𝒜 := yGrading R m n) (yVar_mem_yGrading j)
      (prod_yVar_mem_yGrading (t.erase j)) (yVar_mul_prod_erase hj))
    (zeroAlg_comp_polyAlgEquiv (𝒜 := yGrading R m n) (yVar_mem_yGrading j)
      (prod_yVar_mem_yGrading (t.erase j)) (yVar_mul_prod_erase hj))
    (formChart_kernel_zeroAlg a hj U i x)

/-- **A form on a chart of the cone restricts to zero on the zero section exactly when its chart
form does.** -/
theorem comparison_app_eq_zero_iff {t : Finset (Fin n)} {j : Fin n} (hj : j ∈ t)
    (ω : Γ(Scheme.Hom.relativeDifferentialForms (coneToBase R m n) (a : ℤ),
      chartOpen (yGrading R m n) (∏ k ∈ t, yVar R m n k))) :
    Scheme.Modules.Hom.app (Scheme.Hom.formsDirectImageComparison
        (zeroSection (truncationConeData (yGrading R m n))) (coneToBase R m n) (a : ℤ))
        (chartOpen (yGrading R m n) (∏ k ∈ t, yVar R m n k)) ω = 0 ↔
      KaehlerDifferential.formsₛₗ (zeroAlg (𝒜 := yGrading R m n) (prodY_mem hj)) a
        (chartForms (𝒜 := yGrading R m n) (coneToBase R m n) rfl (prodY_mem hj)
          (Nat.add_one_pos _) a ω) = 0 :=
  formsDirectImageComparison_zeroSection_app_eq_zero_iff (coneToBase R m n) rfl (prodY_mem hj) a ω

/-- A Čech cochain in the positive part corresponds to a form of positive weight on the Laurent
chart. -/
theorem mem_posForms_of_mem_posPart {t : Finset (Fin n)} {j : Fin n} (hj : j ∈ t)
    {z : Cech.cechMod (yVar R m n) (Forms R m n a) t} (hz : z ∈ posPart R m n a t) :
    locFormsEquiv a (∏ k ∈ t, yVar R m n k) z ∈
      PolynomialDeRham.Chart.posForms (laurentAlgEquiv (𝒜 := yGrading R m n) (yVar_mem_yGrading j)
        (prod_yVar_mem_yGrading (t.erase j)) (yVar_mul_prod_erase hj)) a :=
  (posForms_eq a hj).ge ((mem_posPart_iff a hj z).1 hz)

/-- **A form of positive weight on the punctured chart extends over the chart of the cone,
vanishing on the zero section.** -/
theorem exists_chart_form_of_mem_posPart {t : Finset (Fin n)} {j : Fin n} (hj : j ∈ t)
    {z : Cech.cechMod (yVar R m n) (Forms R m n a) t} (hz : z ∈ posPart R m n a t) :
    ∃ ω₀, KaehlerDifferential.formsₛₗ (zeroAlg (𝒜 := yGrading R m n) (prodY_mem hj)) a ω₀ = 0 ∧
      KaehlerDifferential.formsₛₗ (restrictAlg (𝒜 := yGrading R m n) (prodY_mem hj)) a ω₀ =
        locFormsEquiv a (∏ k ∈ t, yVar R m n k) z :=
  PolynomialDeRham.Chart.exists_of_mem_posForms
    (restrictAlg_comp_polyAlgEquiv (𝒜 := yGrading R m n) (yVar_mem_yGrading j)
      (prod_yVar_mem_yGrading (t.erase j)) (yVar_mul_prod_erase hj))
    (zeroAlg_comp_polyAlgEquiv (𝒜 := yGrading R m n) (yVar_mem_yGrading j)
      (prod_yVar_mem_yGrading (t.erase j)) (yVar_mul_prod_erase hj))
    (mem_posForms_of_mem_posPart a hj hz)

/-- **Every form of positive weight is the coordinate of a form on the chart which vanishes on the
zero section.** -/
theorem exists_formChart_eq {t : Finset (Fin n)} {j : Fin n} (hj : j ∈ t)
    (z : Cech.cechMod (yVar R m n) (Forms R m n a) t) (hz : z ∈ posPart R m n a t) :
    ∃ ω : Γ(Scheme.Hom.relativeDifferentialForms (coneToBase R m n) (a : ℤ),
        chartOpen (yGrading R m n) (∏ k ∈ t, yVar R m n k)),
      KaehlerDifferential.formsₛₗ (zeroAlg (𝒜 := yGrading R m n) (prodY_mem hj)) a
        (chartForms (𝒜 := yGrading R m n) (coneToBase R m n) rfl (prodY_mem hj)
          (Nat.add_one_pos _) a ω) = 0 ∧ formChart a hj ω = z := by
  have e := exists_chart_form_of_mem_posPart a hj hz
  have e2 := chartForms_surjective (𝒜 := yGrading R m n) (coneToBase R m n) rfl
    (prodY_mem hj) (Nat.add_one_pos _) a e.choose
  refine ⟨e2.choose, (congrArg (KaehlerDifferential.formsₛₗ
    (zeroAlg (𝒜 := yGrading R m n) (prodY_mem hj)) a) e2.choose_spec).trans e.choose_spec.1, ?_⟩
  exact (formChart_eq_of_chartForms_eq a hj e2.choose_spec).trans
    ((congrArg (locFormsEquiv a (∏ k ∈ t, yVar R m n k)).symm e.choose_spec.2).trans
      (LinearEquiv.symm_apply_apply _ _))

/-- **A form on the chart vanishing on the zero section is the restriction of a section of `K`**,
when the chart is the whole preimage of the open. -/
theorem exists_restrictedKernelHom_eq_of_zeroAlg {t : Finset (Fin n)} {j : Fin n} (hj : j ∈ t)
    (U : (coneBundle R m n).Opens)
    (i : chartOpen (yGrading R m n) (∏ k ∈ t, yVar R m n k) ⟶ coneProjection R m n ⁻¹ᵁ U)
    (hV : chartOpen (yGrading R m n) (∏ k ∈ t, yVar R m n k) = coneProjection R m n ⁻¹ᵁ U)
    (ω : Γ(Scheme.Hom.relativeDifferentialForms (coneToBase R m n) (a : ℤ),
        chartOpen (yGrading R m n) (∏ k ∈ t, yVar R m n k)))
    (h0 : KaehlerDifferential.formsₛₗ (zeroAlg (𝒜 := yGrading R m n) (prodY_mem hj)) a
        (chartForms (𝒜 := yGrading R m n) (coneToBase R m n) rfl (prodY_mem hj)
          (Nat.add_one_pos _) a ω) = 0) :
    ∃ x, Stacks.ConeKernelSections.restrictedKernelHom (coneProjection R m n)
      (coneFormsRestriction R m n (a : ℤ)) U i x = ω :=
  Stacks.ConeKernelSections.exists_restrictedKernelHom_eq (coneProjection R m n)
    (coneFormsRestriction R m n (a : ℤ)) U i hV ω ((comparison_app_eq_zero_iff a hj ω).2 h0)
    (coneFormsRestriction.eq_1 R m n (a : ℤ))

/-- **Every form of positive weight is the coordinate of a section of `K`**, on a chart which is
the whole preimage of the open. -/
theorem exists_formChart_kernel_eq {t : Finset (Fin n)} {j : Fin n} (hj : j ∈ t)
    (U : (coneBundle R m n).Opens)
    (i : chartOpen (yGrading R m n) (∏ k ∈ t, yVar R m n k) ⟶ coneProjection R m n ⁻¹ᵁ U)
    (hV : chartOpen (yGrading R m n) (∏ k ∈ t, yVar R m n k) = coneProjection R m n ⁻¹ᵁ U)
    (z : Cech.cechMod (yVar R m n) (Forms R m n a) t) (hz : z ∈ posPart R m n a t) :
    ∃ x, formChart a hj (Stacks.ConeKernelSections.restrictedKernelHom (coneProjection R m n)
      (coneFormsRestriction R m n (a : ℤ)) U i x) = z := by
  obtain ⟨ω, h0, rfl⟩ := exists_formChart_eq a hj z hz
  obtain ⟨x, rfl⟩ := exists_restrictedKernelHom_eq_of_zeroAlg a hj U i hV ω h0
  exact ⟨x, rfl⟩

/-- **The coordinates commute with restriction**: restricting a form from the chart of `t'` to
the chart of `t ⊇ t'` is the transition map of the Čech complex on coordinates. -/
theorem formChart_restrict {t' t : Finset (Fin n)} (hst : t' ⊆ t) {j' j : Fin n} (hj' : j' ∈ t')
    (hj : j ∈ t)
    (hle : chartOpen (yGrading R m n) (∏ k ∈ t, yVar R m n k) ≤
      chartOpen (yGrading R m n) (∏ k ∈ t', yVar R m n k))
    (ω : Γ(Scheme.Hom.relativeDifferentialForms (coneToBase R m n) (a : ℤ),
      chartOpen (yGrading R m n) (∏ k ∈ t', yVar R m n k))) :
    formChart a hj ((Scheme.Hom.relativeDifferentialForms (coneToBase R m n) (a : ℤ)).presheaf.map
        (homOfLE hle).op ω) =
      Cech.cechι (yVar R m n) (Forms R m n a) hst (formChart a hj' ω) := by
  have hx : (∏ k ∈ t, yVar R m n k) = (∏ k ∈ t', yVar R m n k) * ∏ k ∈ t \ t', yVar R m n k := by
    rw [← Finset.prod_sdiff hst, mul_comm]
  have key := chartForms_restrict (𝒜 := yGrading R m n) (coneToBase R m n) rfl (prodY_mem hj')
    (Nat.add_one_pos _) (prod_yVar_mem_yGrading (t \ t')) (prodY_mem hj) (Nat.add_one_pos _) hx
    hle a ω
  refine (locFormsEquiv a (∏ k ∈ t, yVar R m n k)).injective ?_
  rw [locFormsEquiv_cechι]
  unfold formChart
  exact (LinearEquiv.apply_symm_apply _ _).trans ((congrArg
    (KaehlerDifferential.formsₛₗ (restrictAlg (𝒜 := yGrading R m n) (prodY_mem hj)) a) key).trans
    ((formsₛₗ_restrictAlg_chartAwayMap (prodY_mem hj') (prod_yVar_mem_yGrading (t \ t'))
      (prodY_mem hj) hx a _).trans
      (congrArg _ (LinearEquiv.apply_symm_apply _ _).symm)))

end Stacks.DeRham.CoordinateCone

end
