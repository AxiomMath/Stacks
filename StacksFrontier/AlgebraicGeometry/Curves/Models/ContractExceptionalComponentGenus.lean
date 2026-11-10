module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ContractExceptionalComponentCohomology
public import StacksFrontier.AlgebraicGeometry.Curves.Models.GenusFormulaModel
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ExceptionalComponentsMeet
public import StacksFrontier.AlgebraicGeometry.Curves.Models.InseparableModel.ComponentGenus

/-!
# The genus of a component after contracting an exceptional curve

In the situation of [Stacks, Tag 0C6C] let `C_n` be an exceptional curve of the first kind on the
regular proper model `X`, `f : X ⟶ X'` its contraction and `C'_i = f(C_i)`. [Stacks, Remark 0CA8]
relates the genus `g'_i` of `C'_i` to the genus `g_i` of `C_i`:

`g'_i = (w_i/w'_i)(g_i - 1) + 1 + ((C_i · C_n)² - w_n(C_i · C_n)) / (2 w'_i w_n)`,

where `w_i = [κ_i : k]`, `w_n = [κ_n : k]` and `w'_i = [κ'_i : k]`.

## The argument

The inverse image `f⁻¹C'_i` is the effective Cartier divisor `C_i + e_i C_n`
(`Stacks.Models.RegularProperModelSituation.exists_comap_contractedComponent_eq`).
Its structure sheaf and that of `C'_i` have the same cohomology: the higher direct images of the
pullback of an invertible module along the contraction vanish, so the sequence
`0 ⟶ 𝒪_X(-f⁻¹C'_i) ⟶ 𝒪_X ⟶ 𝒪_{f⁻¹C'_i} ⟶ 0` gives `Rf_*𝒪_{f⁻¹C'_i} = 𝒪_{C'_i}`
(`AlgebraicGeometry.IsContractionOfExceptionalCurve.nonempty_cohomology_subscheme_iso`). Adding
the components one at a time ([Stacks, Tag 0CA2]),

`χ(𝒪_{C_i + e_i C_n}) = χ(𝒪_{C_i}) - (e_i(e_i + 1)/2)(C_n · C_n) - e_i(C_i · C_n)`,

using `χ(𝒪_{C_n}) = -(C_n · C_n) = w_n` for the exceptional curve. Finally
`0 = deg_{C_n} f^*𝒪_{X'}(C'_i) = (C_i · C_n) + e_i (C_n · C_n)`, and
`χ(𝒪_{C'_i}) = w'_i(1 - g'_i)`, `χ(𝒪_{C_i}) = w_i(1 - g_i)`.

## Main results

All in the namespace `Stacks.Models.RegularProperModelSituation`:

* `cast_specialFiberComponentGenus_contractedComponentEquiv`: the formula for `g'_i` above
  ([Stacks, Remark 0CA8]).
* `eulerCharacteristic_comap_contractedComponent_eq`: `χ(𝒪_{f⁻¹C'_i}) = χ(𝒪_{C'_i})`.

## References

* [Stacks Project, Remark 0CA8](https://stacks.math.columbia.edu/tag/0CA8)
* [Stacks Project, Tag 0C6C](https://stacks.math.columbia.edu/tag/0C6C)
* [Stacks Project, Tag 0CA2](https://stacks.math.columbia.edu/tag/0CA2)
* [Stacks Project, Tag 0CA3](https://stacks.math.columbia.edu/tag/0CA3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/-- **Dimensions over a field agree across a semilinear comparison.** Let `π : R ⟶ k` be a
surjection onto a field, and let `M₁`, `M₂` be modules over rings `B₁`, `B₂` which are
`k`-algebras through `κ₁`, `κ₂`. If `M₁` and `M₂` are isomorphic as modules over a ring `A`
through ring maps whose composites with some `r : R ⟶ A` are `κ₁ ∘ π` and `κ₂ ∘ π`, then
`M₁` and `M₂` have the same dimension over `k`. -/
theorem Module.finrank_restrictScalars_eq_of_iso {R A A' B₁ B₂ k : Type u} [CommRing R]
    [CommRing A] [CommRing A'] [CommRing B₁] [CommRing B₂] [Field k] {π : R →+* k}
    (hπ : Function.Surjective π) (r : R →+* A) (a₀ : A →+* A') (a₁ : A' →+* B₁) (b : A →+* B₂)
    (κ₁ : k →+* B₁) (κ₂ : k →+* B₂) (h₁ : ∀ x, a₁ (a₀ (r x)) = κ₁ (π x))
    (h₂ : ∀ x, b (r x) = κ₂ (π x)) (M₁ : ModuleCat.{u} B₁) (M₂ : ModuleCat.{u} B₂)
    (e : (ModuleCat.restrictScalars a₀).obj ((ModuleCat.restrictScalars a₁).obj M₁) ≅
      (ModuleCat.restrictScalars b).obj M₂) :
    Module.finrank k ((ModuleCat.restrictScalars κ₁).obj M₁) =
      Module.finrank k ((ModuleCat.restrictScalars κ₂).obj M₂) := by
  let φ : (ModuleCat.restrictScalars κ₁).obj M₁ ≃ₗ[k] (ModuleCat.restrictScalars κ₂).obj M₂ :=
    { toFun := fun m => e.hom.hom m
      invFun := fun m => e.inv.hom m
      left_inv := fun m => Iso.hom_inv_id_apply e m
      right_inv := fun m => Iso.inv_hom_id_apply e m
      map_add' := fun m m' => map_add e.hom.hom m m'
      map_smul' := fun c m => by
        obtain ⟨x, rfl⟩ := hπ c
        change e.hom.hom (κ₁ (π x) • m) = κ₂ (π x) • e.hom.hom m
        rw [← h₁, ← h₂]
        exact e.hom.hom.map_smul (r x) m }
  exact φ.finrank_eq

/-- On global sections, a morphism over `Spec R` that factors through `Spec k ⟶ Spec R` induces
the composite of the structure maps. -/
theorem AlgebraicGeometry.Scheme.ΓSpecIso_inv_comp_appTop_of_eq {Y : Scheme.{u}}
    {R k : CommRingCat.{u}} (p : Y ⟶ Spec R) (q : Y ⟶ Spec k) (φ : R ⟶ k)
    (h : p = q ≫ Spec.map φ) (x : R) :
    ((Scheme.ΓSpecIso R).inv ≫ p.appTop) x = ((Scheme.ΓSpecIso k).inv ≫ q.appTop) (φ x) := by
  subst h
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

namespace Stacks.Models

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u}) {N : irreducibleComponents S.specialFiber}
  {X' : Scheme.{u}} {f : S.X ⟶ X'}

/-! ### The inverse image of a contracted component -/

/-- The inverse image `f⁻¹C'_i` of a contracted component lies in the special fibre `X_k`. -/
theorem specialFiberIdeal_le_comap_contractedComponent
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) :
    S.specialFiberIdeal ≤ ((S.contractedSituation hf).specialFiberComponentIdeal
      (S.contractedComponentEquiv hf Z)).comap f := by
  rw [S.specialFiberIdeal_eq_comap_contraction hf]
  let hc := (S.contractedSituation hf).toRegularModelSituation
  exact Scheme.IdealSheafData.comap_mono f
    (hc.specialFiberIdeal_le_specialFiberComponentIdeal _)

/-- **The morphism `f⁻¹C'_i ⟶ C'_i`** induced by the contraction. -/
def comapContractedComponentMap
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) :
    (((S.contractedSituation hf).specialFiberComponentIdeal
        (S.contractedComponentEquiv hf Z)).comap f).subscheme ⟶
      ((S.contractedSituation hf).specialFiberComponentIdeal
        (S.contractedComponentEquiv hf Z)).subscheme :=
  IsClosedImmersion.lift ((S.contractedSituation hf).specialFiberComponentIdeal
      (S.contractedComponentEquiv hf Z)).subschemeι
    ((((S.contractedSituation hf).specialFiberComponentIdeal
      (S.contractedComponentEquiv hf Z)).comap f).subschemeι ≫ f) (by
    rw [Scheme.IdealSheafData.ker_subschemeι, ← Scheme.IdealSheafData.map_ker,
      Scheme.IdealSheafData.ker_subschemeι]
    exact Scheme.IdealSheafData.le_map_comap _ f)

/-- The morphism `f⁻¹C'_i ⟶ C'_i` followed by the closed immersion `C'_i ⟶ X'` is the closed
immersion `f⁻¹C'_i ⟶ X` followed by `f`. -/
@[reassoc]
theorem comapContractedComponentMap_subschemeι
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) :
    S.comapContractedComponentMap hf Z ≫ ((S.contractedSituation hf).specialFiberComponentIdeal
        (S.contractedComponentEquiv hf Z)).subschemeι =
      (((S.contractedSituation hf).specialFiberComponentIdeal
        (S.contractedComponentEquiv hf Z)).comap f).subschemeι ≫ f :=
  IsClosedImmersion.lift_fac _ _ _

/-- The morphism `f⁻¹C'_i ⟶ C'_i` hits the generic point of `C'_i`: the generic point of
`C_i ⊆ f⁻¹C'_i` maps to it. -/
theorem exists_comapContractedComponentMap_eq_genericPoint
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) :
    ∃ y, S.comapContractedComponentMap hf Z y =
      genericPoint ((S.contractedSituation hf).specialFiberComponentIdeal
        (S.contractedComponentEquiv hf Z)).subscheme := by
  obtain ⟨-, e, he⟩ := S.exists_comap_contractedComponent_eq hf Z
  have hle : ((S.contractedSituation hf).specialFiberComponentIdeal
      (S.contractedComponentEquiv hf Z)).comap f ≤ S.specialFiberComponentIdeal Z.1 := by
    rw [he]
    exact Scheme.IdealSheafData.mul_le_left _ _
  refine ⟨Scheme.IdealSheafData.inclusion hle
    (genericPoint (S.specialFiberComponentIdeal Z.1).subscheme), ?_⟩
  apply ((S.contractedSituation hf).specialFiberComponentIdeal
    (S.contractedComponentEquiv hf Z)).subschemeι.isClosedEmbedding.injective
  rw [← S.contractedComponentMap_genericPoint hf Z]
  have h1 := congrArg (fun φ => φ (genericPoint (S.specialFiberComponentIdeal Z.1).subscheme))
    (S.contractedComponentMap_subschemeι hf Z)
  have h2 := congrArg (fun φ => φ (genericPoint (S.specialFiberComponentIdeal Z.1).subscheme))
    (Scheme.IdealSheafData.inclusion hle ≫=
      S.comapContractedComponentMap_subschemeι hf Z)
  have h3 := congrArg (fun φ => φ (genericPoint (S.specialFiberComponentIdeal Z.1).subscheme))
    (Scheme.IdealSheafData.inclusion_subschemeι hle =≫ f)
  simp only [Scheme.Hom.comp_apply] at h1 h2 h3
  rw [h2, h3, h1]

/-- The inverse image `f⁻¹C'_i` lies over `Spec k`, compatibly with `X' ⟶ Spec R`. -/
theorem comap_contractedComponent_subschemeι_comp
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) :
    (((S.contractedSituation hf).specialFiberComponentIdeal
        (S.contractedComponentEquiv hf Z)).comap f).subschemeι ≫ f ≫ S.contractionToBase hf =
      S.fibreSubschemeToSpec _ (S.specialFiberIdeal_le_comap_contractedComponent hf Z) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)) := by
  rw [S.contraction_comp_contractionToBase hf, fibreSubschemeToSpec, Category.assoc,
    ← pullback.condition, ← Category.assoc, S.fibreSubschemeι_comp]

/-- The component `C'_i` lies over `Spec k`, compatibly with `X' ⟶ Spec R`. -/
theorem contractedComponent_subschemeι_comp
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) :
    ((S.contractedSituation hf).specialFiberComponentIdeal
        (S.contractedComponentEquiv hf Z)).subschemeι ≫ S.contractionToBase hf =
      (S.contractedSituation hf).specialFiberComponentToSpec (S.contractedComponentEquiv hf Z) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)) := by
  change _ = ((S.contractedSituation hf).specialFiberComponentι _ ≫
    (S.contractedSituation hf).specialFiberToSpec) ≫ _
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    (S.contractedSituation hf).specialFiberComponentι_specialFiberι]

/-- **`Hⁿ(f⁻¹C'_i, 𝒪)` and `Hⁿ(C'_i, 𝒪)` have the same dimension over `k`**, in every degree
(`AlgebraicGeometry.IsContractionOfExceptionalCurve.nonempty_cohomology_subscheme_iso`). -/
theorem finrank_cohomologyOverField_comap_contractedComponent_eq
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) (n : ℕ) :
    Module.finrank S.k (cohomologyOverField S.k
        (S.fibreSubschemeToSpec _ (S.specialFiberIdeal_le_comap_contractedComponent hf Z))
        (SheafOfModules.unit (((S.contractedSituation hf).specialFiberComponentIdeal
          (S.contractedComponentEquiv hf Z)).comap f).subscheme.ringCatSheaf) n) =
      Module.finrank S.k (cohomologyOverField S.k
        ((S.contractedSituation hf).specialFiberComponentToSpec (S.contractedComponentEquiv hf Z))
        (SheafOfModules.unit ((S.contractedSituation hf).specialFiberComponentIdeal
          (S.contractedComponentEquiv hf Z)).subscheme.ringCatSheaf) n) := by
  have := (S.contractedSituation hf).isEffectiveCartierDivisor_specialFiberComponent
    (S.contractedComponentEquiv hf Z)
  have hD := (S.exists_comap_contractedComponent_eq hf Z).1
  obtain ⟨y, hy⟩ := S.exists_comapContractedComponentMap_eq_genericPoint hf Z
  have hD' := S.comap_contractedComponent_subschemeι_comp hf Z
  have hC' := S.contractedComponent_subschemeι_comp hf Z
  have happ : ∀ {Y : Scheme.{u}} (g : Y ⟶ Spec (.of S.k)) (h : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ ⊤),
      g.appLE ⊤ ⊤ h = g.appTop := fun g _ => Scheme.Hom.appLE_eq_app g
  obtain ⟨e⟩ := hf.nonempty_cohomology_subscheme_iso _ hD (S.comapContractedComponentMap hf Z)
    (S.comapContractedComponentMap_subschemeι hf Z) hy n
  refine Module.finrank_restrictScalars_eq_of_iso S.surjective_algebraMap_residueField
    ((Scheme.ΓSpecIso (.of S.R)).inv ≫ (S.contractionToBase hf).appTop).hom _ _ _ _ _
    (fun x => ?_) (fun x => ?_) _ _ e
  · have h := Scheme.ΓSpecIso_inv_comp_appTop_of_eq _ _ _ hD' x
    simp only [Scheme.Hom.comp_appTop] at h
    rw [happ]
    exact h
  · have h := Scheme.ΓSpecIso_inv_comp_appTop_of_eq _ _ _ hC' x
    rw [happ]
    exact h

/-- **`χ(𝒪_{f⁻¹C'_i}) = χ(𝒪_{C'_i})`**: the structure sheaves of the inverse image of a
contracted component and of the component itself have the same Euler characteristic over `k`. -/
theorem eulerCharacteristic_comap_contractedComponent_eq
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) :
    @eulerCharacteristic S.k _ _
        (S.fibreSubschemeToSpec _ (S.specialFiberIdeal_le_comap_contractedComponent hf Z)) _
        (SheafOfModules.unit (((S.contractedSituation hf).specialFiberComponentIdeal
          (S.contractedComponentEquiv hf Z)).comap f).subscheme.ringCatSheaf)
        (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.k
          (S.fibreSubschemeToSpec _ (S.specialFiberIdeal_le_comap_contractedComponent hf Z))) =
      @eulerCharacteristic S.k _ _
        ((S.contractedSituation hf).specialFiberComponentToSpec (S.contractedComponentEquiv hf Z))
        ((S.contractedSituation hf).isProper_specialFiberComponentToSpec _)
        (SheafOfModules.unit ((S.contractedSituation hf).specialFiberComponentIdeal
          (S.contractedComponentEquiv hf Z)).subscheme.ringCatSheaf)
        ((S.contractedSituation hf).isCoherent_unit_specialFiberComponent _) := by
  have := (S.contractedSituation hf).isProper_specialFiberComponentToSpec
    (S.contractedComponentEquiv hf Z)
  have := (S.contractedSituation hf).isCoherent_unit_specialFiberComponent
    (S.contractedComponentEquiv hf Z)
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.k
    (S.fibreSubschemeToSpec _ (S.specialFiberIdeal_le_comap_contractedComponent hf Z))
  exact eulerCharacteristic_eq_of_finrank_cohomologyOverField_eq S.k S.k _ _ _ _
    fun n => S.finrank_cohomologyOverField_comap_contractedComponent_eq hf Z n

/-! ### The Euler characteristics of `C_i + j C_n` -/

section Chain

variable [DecidableEq (irreducibleComponents S.specialFiber)]

/-- `Σ_Y Cᵧ^{cᵧ} = C_Z + j C_N` for the coefficients `c = 1·[Z] + j·[N]`, `Z ≠ N`. -/
theorem prod_specialFiberComponentIdeal_pow_single_add {Z N : irreducibleComponents S.specialFiber}
    (hZN : Z ≠ N) (j : ℕ) :
    ∏ Y, S.specialFiberComponentIdeal Y ^
        (Pi.single Z 1 + Pi.single N j : irreducibleComponents S.specialFiber → ℕ) Y =
      S.specialFiberComponentIdeal Z * S.specialFiberComponentIdeal N ^ j := by
  rw [Finset.prod_eq_mul Z N hZN (fun Y _ hY => by
      simp [hY.1, hY.2])
    (fun h => (h (Finset.mem_univ _)).elim) (fun h => (h (Finset.mem_univ _)).elim)]
  simp [hZN, Ne.symm hZN]

omit [DecidableEq (irreducibleComponents S.specialFiber)] in
/-- `Σ_Y cᵧ aᵧ = a_Z + j a_N` for the coefficients `c = 1·[Z] + j·[N]`, `Z ≠ N`. -/
theorem sum_single_add_mul {Z N : irreducibleComponents S.specialFiber} (_hZN : Z ≠ N) (j : ℕ)
    (a : irreducibleComponents S.specialFiber → ℤ)
    [DecidableEq (irreducibleComponents S.specialFiber)] :
    ∑ Y, ((Pi.single Z 1 + Pi.single N j : irreducibleComponents S.specialFiber → ℕ) Y : ℤ) * a Y =
      a Z + j * a N := by
  simp [Pi.single_apply, add_mul, Finset.sum_add_distrib]

omit [DecidableEq (irreducibleComponents S.specialFiber)] in
/-- The divisor `C_Z + j C_N` is an effective Cartier divisor. -/
theorem isEffectiveCartierDivisor_mul_pow (Z N : irreducibleComponents S.specialFiber) (j : ℕ) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (S.specialFiberComponentIdeal Z * S.specialFiberComponentIdeal N ^ j) := by
  have := S.isEffectiveCartierDivisor_specialFiberComponent Z
  have := S.isEffectiveCartierDivisor_specialFiberComponent N
  induction j with
  | zero =>
    rw [pow_zero, mul_one]
    infer_instance
  | succ j ih =>
    rw [pow_succ, ← mul_assoc]
    exact AlgebraicGeometry.isEffectiveCartierDivisor_mul _ _ ih inferInstance

omit [DecidableEq (irreducibleComponents S.specialFiber)] in
/-- The Euler characteristic on `X_k` of the structure sheaf of a closed subscheme of `X_k`
depends only on the subscheme. -/
theorem eulerCharacteristic_pushforward_fibreSubschemeι_congr {I I' : S.X.IdealSheafData}
    (hI : I = I') (h : S.specialFiberIdeal ≤ I) (h' : S.specialFiberIdeal ≤ I') :
    eulerCharacteristic S.k S.specialFiberToSpec
        ((Scheme.Modules.pushforward (S.fibreSubschemeι I h)).obj
          (SheafOfModules.unit I.subscheme.ringCatSheaf)) =
      eulerCharacteristic S.k S.specialFiberToSpec
        ((Scheme.Modules.pushforward (S.fibreSubschemeι I' h')).obj
          (SheafOfModules.unit I'.subscheme.ringCatSheaf)) := by
  subst hI
  rfl

/-- **The Euler characteristic of `C_Z + j C_N`**, added one copy of `C_N` at a time
([Stacks, Tag 0CA2]):
`2χ(𝒪_{C_Z + jC_N}) = 2χ(𝒪_{C_Z}) + 2jχ(𝒪_{C_N}) - 2j(C_Z · C_N) - j(j - 1)(C_N · C_N)`. -/
theorem two_mul_eulerCharacteristic_mul_pow {Z N : irreducibleComponents S.specialFiber}
    (hZN : Z ≠ N) (j : ℕ)
    (h : S.specialFiberIdeal ≤
      S.specialFiberComponentIdeal Z * S.specialFiberComponentIdeal N ^ j) :
    2 * eulerCharacteristic S.k S.specialFiberToSpec
        ((Scheme.Modules.pushforward (S.fibreSubschemeι _ h)).obj
          (SheafOfModules.unit (S.specialFiberComponentIdeal Z *
            S.specialFiberComponentIdeal N ^ j).subscheme.ringCatSheaf)) =
      2 * eulerCharacteristic S.k (S.specialFiberComponentToSpec Z)
          (SheafOfModules.unit (S.specialFiberComponentIdeal Z).subscheme.ringCatSheaf) +
        2 * j * eulerCharacteristic S.k (S.specialFiberComponentToSpec N)
          (SheafOfModules.unit (S.specialFiberComponentIdeal N).subscheme.ringCatSheaf) -
        2 * j * S.specialFiberIntersectionMatrix Z N -
        j * ((j : ℤ) - 1) * S.specialFiberIntersectionMatrix N N := by
  induction j with
  | zero =>
    have hZ := S.specialFiberIdeal_le_specialFiberComponentIdeal Z
    have e1 : eulerCharacteristic S.k S.specialFiberToSpec
        ((Scheme.Modules.pushforward (S.fibreSubschemeι _ hZ)).obj
          (SheafOfModules.unit (S.specialFiberComponentIdeal Z).subscheme.ringCatSheaf)) =
        eulerCharacteristic S.k (S.specialFiberComponentToSpec Z)
          (SheafOfModules.unit (S.specialFiberComponentIdeal Z).subscheme.ringCatSheaf) :=
      (eulerCharacteristic_pushforward_of_isClosedImmersion S.k (S.fibreSubschemeι _ hZ)
        S.specialFiberToSpec _ inferInstance inferInstance).trans
        (eulerCharacteristic_congr_morphism _ _ _ _
          (S.fibreSubschemeToSpec_specialFiberComponentIdeal Z))
    rw [S.eulerCharacteristic_pushforward_fibreSubschemeι_congr (by rw [pow_zero, mul_one]) h hZ,
      e1]
    push_cast
    ring
  | succ j ih =>
    have hsum : S.specialFiberComponentIdeal Z * S.specialFiberComponentIdeal N ^ (j + 1) =
        (S.specialFiberComponentIdeal Z * S.specialFiberComponentIdeal N ^ j) *
          S.specialFiberComponentIdeal N := by
      rw [pow_succ, mul_assoc]
    have hj : S.specialFiberIdeal ≤
        S.specialFiberComponentIdeal Z * S.specialFiberComponentIdeal N ^ j :=
      h.trans (hsum ▸ Scheme.IdealSheafData.mul_le_left _ _)
    have := S.isEffectiveCartierDivisor_mul_pow Z N j
    obtain ⟨h1, h2⟩ := S.eulerCharacteristic_addComponent N _ _ hsum h
    have hcoeff : ∀ Y, S.specialFiberDivisorCoeff
        (S.specialFiberComponentIdeal Z * S.specialFiberComponentIdeal N ^ j) Y =
        (Pi.single Z 1 + Pi.single N j : irreducibleComponents S.specialFiber → ℕ) Y := fun Y => by
      rw [← S.prod_specialFiberComponentIdeal_pow_single_add hZN j,
        S.specialFiberDivisorCoeff_prod]
    rw [S.intersectionProduct_single_right] at h2
    simp only [hcoeff] at h2
    rw [S.sum_single_add_mul hZN j] at h2
    have hZN' : S.specialFiberComponentDegree Z
        (Stacks.Divisors.invertibleSheaf' (S.specialFiberComponentIdeal N))
        (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ _
          (S.isEffectiveCartierDivisor_specialFiberComponent N)) =
        S.specialFiberIntersectionMatrix Z N :=
      (S.specialFiberIntersectionMatrix_eq_componentDegree Z N).symm
    have hNN' : S.specialFiberComponentDegree N
        (Stacks.Divisors.invertibleSheaf' (S.specialFiberComponentIdeal N))
        (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ _
          (S.isEffectiveCartierDivisor_specialFiberComponent N)) =
        S.specialFiberIntersectionMatrix N N :=
      (S.specialFiberIntersectionMatrix_eq_componentDegree N N).symm
    rw [hZN', hNN'] at h2
    have ih' := ih hj
    push_cast
    linarith

end Chain

/-! ### The genus formula -/

/-- **`(C_i · C_n) + e_i (C_n · C_n) = 0`** for `f⁻¹C'_i = C_i + e_i C_n`: the invertible module
`𝒪_X(f⁻¹C'_i) = f^*𝒪_{X'}(C'_i)` is pulled back along the contraction, so it has degree zero on
the contracted curve `C_n`. -/
theorem specialFiberIntersectionMatrix_add_mul_eq_zero
    [DecidableEq (irreducibleComponents S.specialFiber)]
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) (e : ℕ)
    (he : ((S.contractedSituation hf).specialFiberComponentIdeal
        (S.contractedComponentEquiv hf Z)).comap f =
      S.specialFiberComponentIdeal Z.1 * S.specialFiberComponentIdeal N ^ e) :
    S.specialFiberIntersectionMatrix Z.1 N + e * S.specialFiberIntersectionMatrix N N = 0 := by
  classical
  have hD := (S.exists_comap_contractedComponent_eq hf Z).1
  have : Stacks.Divisors.IsEffectiveCartierDivisor
      (((S.contractedSituation hf).specialFiberComponentIdeal
        (S.contractedComponentEquiv hf Z)).comap f) := hD
  have := (S.contractedSituation hf).isEffectiveCartierDivisor_specialFiberComponent
    (S.contractedComponentEquiv hf Z)
  have : Stacks.Divisors.IsPullbackDefined f ((S.contractedSituation hf).specialFiberComponentIdeal
      (S.contractedComponentEquiv hf Z)) := hD
  have hk := S.specialFiberIdeal_le_comap_contractedComponent hf Z
  let L := Stacks.Divisors.invertibleSheaf' ((S.contractedSituation hf).specialFiberComponentIdeal
    (S.contractedComponentEquiv hf Z))
  have hL : Stacks.SheafOfModules.IsInvertible X'.presheaf
      (structureSheafRing X'.toRingedSpace).property L :=
    Stacks.Divisors.isTensorInvertible_invertibleSheaf _
  have := hL
  have hL' : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property ((Scheme.Modules.pullback f).obj L) :=
    Stacks.Modules.isInvertible_pullback f L
  have h0 := S.componentDegree_pullback_contraction_exceptional hf L hL hL'
  rw [componentDegree_eq_of_iso _ _ _ _ _ _ _ hL'
    (Stacks.Divisors.isTensorInvertible_invertibleSheaf _)
    (Stacks.Divisors.invertibleSheafPullbackIso f _)] at h0
  have hsum := S.specialFiberComponentDegree_invertibleSheaf_eq_sum N _ hk
  unfold specialFiberComponentDegree at hsum
  rw [h0] at hsum
  have hcoeff : ∀ Y, S.specialFiberDivisorCoeff
      (((S.contractedSituation hf).specialFiberComponentIdeal
        (S.contractedComponentEquiv hf Z)).comap f) Y =
      (Pi.single Z.1 1 + Pi.single N e : irreducibleComponents S.specialFiber → ℕ) Y := fun Y => by
    rw [he, ← S.prod_specialFiberComponentIdeal_pow_single_add Z.2 e,
      S.specialFiberDivisorCoeff_prod]
  simp only [hcoeff] at hsum
  rw [S.sum_single_add_mul Z.2 e] at hsum
  have h1 := (S.specialFiberIntersectionMatrix_eq_componentDegree N Z.1).symm
  have h2 := (S.specialFiberIntersectionMatrix_eq_componentDegree N N).symm
  rw [h1, h2, S.specialFiberIntersectionMatrix_comm N Z.1] at hsum
  linarith

/-- **The genus of a component after contracting an exceptional curve** ([Stacks, Remark 0CA8]).
In the situation of [Stacks, Tag 0C6C] — `X` a regular proper model of `C` over a discrete
valuation ring with residue field `k`, `C_n` a component of the special fibre which is an
exceptional curve of the first kind, `f : X ⟶ X'` its contraction, and `C'_i = f(C_i)` for
`i ≠ n` — the genus `g'_i` of `C'_i` is

`g'_i = (w_i/w'_i)(g_i - 1) + 1 + ((C_i · C_n)² - w_n(C_i · C_n)) / (2 w'_i w_n)`,

where `w_i = [κ_i : k]`, `w_n = [κ_n : k]`, `w'_i = [κ'_i : k]` and `g_i` is the genus of `C_i`.
Here `X'` is the regular proper model
`Stacks.Models.RegularProperModelSituation.contractedSituation` and `C'_i` its component
`Stacks.Models.RegularProperModelSituation.contractedComponentEquiv`. The components are indexed
by `irreducibleComponents X_k`, the exceptional curve being presented as `𝐏¹_κ` by `ε`. -/
@[stacks 0CA8 "g'_i = (w_i/w'_i)(g_i - 1) + 1 + ((C_i · C_n)^2 - w_n(C_i · C_n))/(2 w'_i w_n)"]
theorem cast_specialFiberComponentGenus_contractedComponentEquiv
    [DecidableEq (irreducibleComponents S.specialFiber)]
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (κ : Type u) [Field κ] {ε : projectiveLineProj κ ≅ (S.specialFiberComponentIdeal N).subscheme}
    (hE : (S.specialFiberComponentIdeal N).IsExceptionalCurveOfFirstKind κ ε)
    (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) :
    ((S.contractedSituation hf).specialFiberComponentGenus (S.contractedComponentEquiv hf Z) : ℚ) =
      (S.specialFiberComponentWeight Z.1 : ℚ) /
          ((S.contractedSituation hf).specialFiberComponentWeight
            (S.contractedComponentEquiv hf Z) : ℚ) *
          ((S.specialFiberComponentGenus Z.1 : ℚ) - 1) + 1 +
        ((S.specialFiberIntersectionMatrix Z.1 N : ℚ) ^ 2 -
            (S.specialFiberComponentWeight N : ℚ) * S.specialFiberIntersectionMatrix Z.1 N) /
          (2 * ((S.contractedSituation hf).specialFiberComponentWeight
            (S.contractedComponentEquiv hf Z) : ℚ) * (S.specialFiberComponentWeight N : ℚ)) := by
  classical
  obtain ⟨hD, e, he⟩ := S.exists_comap_contractedComponent_eq hf Z
  have hk := S.specialFiberIdeal_le_comap_contractedComponent hf Z
  have hgN : S.specialFiberComponentGenus N = 0 := by
    let := (S.isField_and_finite_globalSections_specialFiberComponent N).1.toField
    exact Stacks.Curves.genus_eq_zero_of_iso_projectiveLine ε.symm _
  have hNN : S.specialFiberIntersectionMatrix N N = -(S.specialFiberComponentWeight N : ℤ) := by
    rw [S.specialFiberIntersectionMatrix_self_eq_neg_weight_add_genus N κ hE,
      Stacks.Curves.genus_eq_zero_of_iso_projectiveLine ε.symm _]
    simp
  have hχN := S.eulerCharacteristic_specialFiberComponent_eq N
  rw [hgN] at hχN
  have hχZ := S.eulerCharacteristic_specialFiberComponent_eq Z.1
  have hχW := (S.contractedSituation hf).eulerCharacteristic_specialFiberComponent_eq
    (S.contractedComponentEquiv hf Z)
  have hrel := S.specialFiberIntersectionMatrix_add_mul_eq_zero hf Z e he
  -- `χ(𝒪_{f⁻¹C'_i})` on `X_k`, by the chain of [Stacks, Tag 0CA2]
  have hke : S.specialFiberIdeal ≤
      S.specialFiberComponentIdeal Z.1 * S.specialFiberComponentIdeal N ^ e := he ▸ hk
  have hchain := S.two_mul_eulerCharacteristic_mul_pow Z.2 e hke
  have e1 : eulerCharacteristic S.k S.specialFiberToSpec
      ((Scheme.Modules.pushforward (S.fibreSubschemeι _ hk)).obj
        (SheafOfModules.unit (((S.contractedSituation hf).specialFiberComponentIdeal
          (S.contractedComponentEquiv hf Z)).comap f).subscheme.ringCatSheaf)) =
      @eulerCharacteristic S.k _ _ (S.fibreSubschemeToSpec _ hk) _
        (SheafOfModules.unit (((S.contractedSituation hf).specialFiberComponentIdeal
          (S.contractedComponentEquiv hf Z)).comap f).subscheme.ringCatSheaf)
        (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.k
          (S.fibreSubschemeToSpec _ hk)) :=
    eulerCharacteristic_pushforward_of_isClosedImmersion S.k (S.fibreSubschemeι _ hk)
      S.specialFiberToSpec _ (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.k
        (S.fibreSubschemeToSpec _ hk)) inferInstance
  rw [← S.eulerCharacteristic_pushforward_fibreSubschemeι_congr he hk hke, e1,
    S.eulerCharacteristic_comap_contractedComponent_eq hf Z, hχW, hχZ, hχN] at hchain
  have hw := S.specialFiberComponentWeight_pos N
  have hw' := (S.contractedSituation hf).specialFiberComponentWeight_pos
    (S.contractedComponentEquiv hf Z)
  have hwQ : (0 : ℚ) < S.specialFiberComponentWeight N := by exact_mod_cast hw
  have hwQ' : (0 : ℚ) < (S.contractedSituation hf).specialFiberComponentWeight
      (S.contractedComponentEquiv hf Z) := by exact_mod_cast hw'
  have hchainQ : (2 : ℚ) * ((S.contractedSituation hf).specialFiberComponentWeight
        (S.contractedComponentEquiv hf Z) *
        (1 - ((S.contractedSituation hf).specialFiberComponentGenus
          (S.contractedComponentEquiv hf Z) : ℚ))) =
      2 * (S.specialFiberComponentWeight Z.1 * (1 - (S.specialFiberComponentGenus Z.1 : ℚ))) +
        2 * e * (S.specialFiberComponentWeight N * (1 - 0)) -
        2 * e * S.specialFiberIntersectionMatrix Z.1 N -
        e * ((e : ℚ) - 1) * S.specialFiberIntersectionMatrix N N := by
    exact_mod_cast hchain
  have hrelQ : (S.specialFiberIntersectionMatrix Z.1 N : ℚ) +
      e * S.specialFiberIntersectionMatrix N N = 0 := by exact_mod_cast hrel
  have hNNQ : (S.specialFiberIntersectionMatrix N N : ℚ) =
      -(S.specialFiberComponentWeight N : ℚ) := by exact_mod_cast hNN
  rw [hNNQ] at hchainQ hrelQ
  have ha : (S.specialFiberIntersectionMatrix Z.1 N : ℚ) = e * S.specialFiberComponentWeight N := by
    linarith
  rw [ha]
  rw [ha] at hchainQ
  set w := (S.specialFiberComponentWeight N : ℚ)
  set w' := ((S.contractedSituation hf).specialFiberComponentWeight
    (S.contractedComponentEquiv hf Z) : ℚ)
  set g' := ((S.contractedSituation hf).specialFiberComponentGenus
    (S.contractedComponentEquiv hf Z) : ℚ)
  set wZ := (S.specialFiberComponentWeight Z.1 : ℚ)
  set gZ := (S.specialFiberComponentGenus Z.1 : ℚ)
  have h1 : g' = 1 - (2 * (wZ * (1 - gZ)) + e * w - e ^ 2 * w) / (2 * w') := by
    field_simp
    linarith [hchainQ]
  rw [h1]
  field_simp
  ring

end RegularProperModelSituation

end Stacks.Models

end
