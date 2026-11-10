module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperCohomologyAdicBounds
public import StacksFrontier.AlgebraicGeometry.Spaces.AdicSectionsOfSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.BaseIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartwiseIsomorphismDetection

/-!
# The theorem on formal functions in degree zero, for the ideal sheaf `I 𝒪_X`

Let `A` be a Noetherian ring complete with respect to an ideal `I`, let `X` be a proper algebraic
space over `Spec A` and let `K` be a coherent `𝒪_X`-module.  Then

`Γ(X, K) ⟶ limₙ Γ(X, K / (I 𝒪_X)ⁿ⁺¹ K)`

is bijective: this is [Stacks, Tag 08B0] in degree zero, in the vocabulary in which the category
`Coh(X, 𝓘)` of coherent adic systems and the completion functor of [Stacks, Tag 08B4] are
built — the ideal sheaf is `AlgebraicGeometry.Space.baseIdealSheaf`, the quotients are
`AlgebraicGeometry.Space.idealPowerQuotient`, and the limit is
`AlgebraicGeometry.Space.adicSections`, as in [Stacks, Tag 08B6].

It is deduced from `AlgebraicGeometry.Space.bijective_adicCohomologyLimitMap_of_isAdicComplete`,
which is stated for the cohomology modules `H⁰` and for the multiples `Iⁿ K` of
`AlgebraicGeometry.Space.idealMultiple`, by three identifications:

* the two spellings of `Iⁿ K` agree for quasi-coherent `K`
  (`AlgebraicGeometry.Space.idealQuotientIsoIdealPowerQuotient`), which is checked on affine étale
  charts, where both are `Iⁿ · K(U)`;
* `H⁰` is the functor of global sections (`AlgebraicGeometry.Space.cohomologyResZeroIso`);
* a compatible family over all pairs `m ≤ n` is the same as a compatible family for the successive
  transition maps, with the index shifted by one
  (`AlgebraicGeometry.Space.bijective_of_bijective_towerLimit`).

## Main results

* `AlgebraicGeometry.Space.bijective_adicSectionsOfSections_of_isProper` — the bijection above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules
open scoped IsMulCommutative

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] hasInjectiveResolutions_modules

/-! ### From all pairs to successive transition maps -/

section Tower

variable {M : Type*} {P : ℕ → Type*} {R : ℕ → Type*}
  [AddCommGroup M] [∀ n, AddCommGroup (P n)] {A : Type*} [CommRing A] [Module A M]
  [∀ n, Module A (P n)]
  (T : ∀ m n : ℕ, m ≤ n → P n →ₗ[A] P m) (π : ∀ n, M →ₗ[A] P n)
  (hTid : ∀ n (x : P n), T n n le_rfl x = x)
  (hTcomp : ∀ m n k (h₁ : m ≤ n) (h₂ : n ≤ k) (x : P k),
    T m n h₁ (T n k h₂ x) = T m k (h₁.trans h₂) x)
  (r : ∀ n, R (n + 1) → R n) (e : ∀ n, P (n + 1) ≃ R n)
  (he : ∀ n (x : P (n + 2)), e n (T (n + 1) (n + 2) (Nat.le_succ _) x) = r n (e (n + 1) x))

include hTid hTcomp he in
/-- **A compatible family for all pairs `m ≤ n` is a compatible family for the successive
transition maps, shifted by one.**  If `x ↦ (π n x)ₙ` is a bijection from `M` onto the limit of
a tower `(P n, T)`, and `P (n + 1) ≃ R n` carries the transition maps to the maps `r n`, then
`x ↦ (e n (π (n + 1) x))ₙ` is a bijection from `M` onto the compatible families of `(R n, r)`. -/
theorem bijective_of_bijective_towerLimit
    (hπ : ∀ (m n : ℕ) (h : m ≤ n) (x : M), T m n h (π n x) = π m x)
    (hbij : Function.Bijective (fun x : M =>
      (⟨fun n => π n x, fun m n h => hπ m n h x⟩ :
        Stacks.IntertwinedFiltration.towerLimit P T)))
    (g : M → { s : ∀ n, R n // ∀ n, r n (s (n + 1)) = s n })
    (hg : ∀ x n, (g x).1 n = e n (π (n + 1) x)) :
    Function.Bijective g := by
  refine ⟨fun x y hxy => ?_, fun s => ?_⟩
  · refine hbij.1 (Subtype.ext (funext fun n => ?_))
    have hs : ∀ n, π (n + 1) x = π (n + 1) y := fun n =>
      (e n).injective (by simpa only [hg] using congrArg (fun z => z.1 n) hxy)
    rcases n with _ | n
    · change π 0 x = π 0 y
      rw [← hπ 0 1 (Nat.zero_le 1) x, ← hπ 0 1 (Nat.zero_le 1) y, hs 0]
    · exact hs n
  · let y : ∀ n, P n := fun n => match n with
      | 0 => T 0 1 (Nat.zero_le 1) ((e 0).symm (s.1 0))
      | n + 1 => (e n).symm (s.1 n)
    have hsucc : ∀ n, T n (n + 1) (Nat.le_succ n) (y (n + 1)) = y n := by
      rintro (_ | n)
      · rfl
      · change T (n + 1) (n + 2) _ ((e (n + 1)).symm (s.1 (n + 1))) = (e n).symm (s.1 n)
        apply (e n).injective
        rw [Equiv.apply_symm_apply, he, Equiv.apply_symm_apply, s.2 n]
    have hall : ∀ m n (h : m ≤ n), T m n h (y n) = y m := by
      intro m n h
      induction n, h using Nat.le_induction with
      | base => exact hTid m (y m)
      | succ k hk ih =>
        rw [← hTcomp m k (k + 1) hk (Nat.le_succ k), hsucc k, ih]
    obtain ⟨x, hx⟩ := hbij.2 ⟨y, hall⟩
    refine ⟨x, Subtype.ext (funext fun n => ?_)⟩
    rw [hg, show π (n + 1) x = y (n + 1) from congrArg (fun z => z.1 (n + 1)) hx]
    exact (e n).apply_symm_apply (s.1 n)

end Tower

/-! ### The two spellings of `Iⁿ K` -/

section Spellings

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  (X : AlgebraicSpaces B (Spec (.of A)) hA) (I : Ideal A)
  (K : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2)

/-- A function `a ∈ Iⁿ` of the base, read on an étale chart, lies in `(I 𝒪_X)(U)ⁿ`. -/
theorem chartBaseRingHom_mem_pow_baseIdealSheaf {n : ℕ} {a : A} (ha : a ∈ I ^ n)
    (U : SmallEtale B (Spec (.of A)) hA X.1) :
    chartBaseRingHom A X U a ∈
      chartIdeal B (Spec (.of A)) hA X (baseIdealSheaf A X I) U ^ n := by
  have h1 : Ideal.map (chartBaseRingHom A X U) I ≤
      chartIdeal B (Spec (.of A)) hA X (baseIdealSheaf A X I) U :=
    le_baseIdealSheaf A X I U
  have h2 := Ideal.mem_map_of_mem (chartBaseRingHom A X U) ha
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 n h2

/-- Multiplication by a function of the base in `Iⁿ` kills `K / (I 𝒪_X)ⁿ K`. -/
theorem globalSmul_idealPowerQuotient_eq_zero {n : ℕ} {a : A} (ha : a ∈ I ^ n) :
    globalSmul _ (baseRingHom A B hA X.1 X.2 a)
      (idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) n K) = 0 := by
  ext U y
  rw [globalSmul_app]
  exact isPowAnnihilated_idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) n K
    U.unop _ (chartBaseRingHom_mem_pow_baseIdealSheaf X I ha U.unop) y

/-- The submodule `Iⁿ K` of `AlgebraicGeometry.Space.idealMultiple` lies in the submodule
`(I 𝒪_X)ⁿ K` of `AlgebraicGeometry.Space.idealPowerMultiple`. -/
def idealMultipleToIdealPowerMultiple (n : ℕ) :
    idealMultiple (baseRingHom A B hA X.1 X.2) K (I ^ n) ⟶
      (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) n
        K).toSheafOfModules :=
  Abelian.monoLift
    (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) n K).ι
    (idealMultipleι (baseRingHom A B hA X.1 X.2) K (I ^ n)) (by
    refine idealMultiple_hom_ext _ K (I ^ n) fun a ha => ?_
    rw [idealMultipleFactor_ι_assoc, comp_zero, ← comp_globalSmul,
      globalSmul_idealPowerQuotient_eq_zero X I K ha, comp_zero])

/-- The inclusion `Iⁿ K → K` factors as `idealMultipleToIdealPowerMultiple` followed by the
inclusion `(I 𝒪_X)ⁿ K → K`. -/
@[reassoc (attr := simp)]
theorem idealMultipleToIdealPowerMultiple_ι (n : ℕ) :
    idealMultipleToIdealPowerMultiple X I K n ≫
        (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) n K).ι =
      idealMultipleι (baseRingHom A B hA X.1 X.2) K (I ^ n) :=
  Abelian.monoLift_comp _ _ _

/-- **The two spellings of `Iⁿ K` agree**, for a quasi-coherent `K`: on an affine étale chart `U`
both are `Iⁿ · K(U)`. -/
theorem isIso_idealMultipleToIdealPowerMultiple (hK : K.IsQuasicoherentOnSite) (n : ℕ) :
    IsIso (idealMultipleToIdealPowerMultiple X I K n) := by
  refine isIso_of_forall_bijective_val_app_affine_chart B (Spec (.of A)) hA X _ fun V hV => ?_
  let P := idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) n K
  let ι := idealMultipleι (baseRingHom A B hA X.1 X.2) K (I ^ n)
  have hι : ∀ x, P.ι.val.app (op V) ((idealMultipleToIdealPowerMultiple X I K n).val.app (op V) x) =
      ι.val.app (op V) x := fun x =>
    congrArg (fun g => g.val.app (op V) x) (idealMultipleToIdealPowerMultiple_ι X I K n)
  have hPinj := Stacks.SheafOfModules.injective_app_of_mono P.ι (op V)
  have hιinj := Stacks.SheafOfModules.injective_app_of_mono ι (op V)
  refine ⟨fun x x' hxx' => hιinj ?_, fun y => ?_⟩
  · rw [← hι, ← hι, hxx']
  · have hKc := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B (Spec (.of A)) hA X.1 X.2 K hK
    have hmem : P.ι.val.app (op V) y ∈
        chartSubmodule B (Spec (.of A)) hA X.1 X.2
          (idealPowSubmodule (baseIdealSheaf A X I) n K) V := by
      change _ ∈ (idealPowSubmodule (baseIdealSheaf A X I) n K).obj (op V)
      rw [← idealPowerMultiple_eq_idealPowSubmodule]
      exact y.2
    rw [chartSubmodule_idealPowSubmodule_eq_of_isAffine B (Spec (.of A)) hA X.1 X.2 _ K hKc
        (isCartesianOnAffineCharts_baseIdealSheaf A X I) n hV] at hmem
    let J : Ideal (chartRing B (Spec (.of A)) hA X.1 X.2 V) := Ideal.map (chartBaseRingHom A X V) I
    let Jn : Ideal (chartRing B (Spec (.of A)) hA X.1 X.2 V) :=
      Ideal.map (chartBaseRingHom A X V) (I ^ n)
    have hideal : chartSectionIdeal B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) V = J :=
      baseIdealSheaf_obj_of_isAffine A X I V hV
    have hpow : J ^ n = Jn := (Ideal.map_pow _ _ _).symm
    rw [hideal, hpow] at hmem
    have hle : Jn • (⊤ : Submodule (chartRing B (Spec (.of A)) hA X.1 X.2 V) (K.val.obj (op V))) ≤
        LinearMap.range (ι.val.app (op V)).hom := by
      refine Submodule.smul_le.2 fun r hr z _ => ?_
      refine Submodule.span_induction (p := fun r _ => r • z ∈
        LinearMap.range (ι.val.app (op V)).hom) ?_ ?_ ?_ ?_ hr
      · rintro _ ⟨a, ha, rfl⟩
        exact ⟨(idealMultipleFactor (baseRingHom A B hA X.1 X.2) K (I ^ n) ha).val.app (op V) z,
          congrArg (fun g => g.val.app (op V) z)
            (idealMultipleFactor_ι (baseRingHom A B hA X.1 X.2) K (I ^ n) ha)⟩
      · rw [zero_smul]
        exact Submodule.zero_mem _
      · intro r r' _ _ h h'
        rw [add_smul]
        exact Submodule.add_mem _ h h'
      · intro c r _ h
        rw [smul_eq_mul, mul_smul]
        exact Submodule.smul_mem _ c h
    obtain ⟨x, hx⟩ := hle hmem
    exact ⟨x, hPinj ((hι x).trans hx)⟩

/-- `K / Iⁿ K` of `AlgebraicGeometry.Space.idealQuotient` maps to `K / (I 𝒪_X)ⁿ K` of
`AlgebraicGeometry.Space.idealPowerQuotient`. -/
def idealQuotientToIdealPowerQuotient (n : ℕ) :
    idealQuotient (baseRingHom A B hA X.1 X.2) K (I ^ n) ⟶
      idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) n K :=
  cokernel.desc _ (cokernel.π _) (by
    rw [← idealMultipleToIdealPowerMultiple_ι X I K n, Category.assoc, cokernel.condition,
      comp_zero])

/-- The projection `K → K / Iⁿ K` followed by `idealQuotientToIdealPowerQuotient` is the
projection `K → K / (I 𝒪_X)ⁿ K`. -/
@[reassoc (attr := simp)]
theorem idealQuotientπ_comp_idealQuotientToIdealPowerQuotient (n : ℕ) :
    idealQuotientπ (baseRingHom A B hA X.1 X.2) K (I ^ n) ≫
        idealQuotientToIdealPowerQuotient X I K n =
      cokernel.π (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) n K).ι :=
  cokernel.π_desc _ _ _

/-- **The two spellings of `K / Iⁿ K` agree** for a quasi-coherent `K`. -/
theorem isIso_idealQuotientToIdealPowerQuotient (hK : K.IsQuasicoherentOnSite) (n : ℕ) :
    IsIso (idealQuotientToIdealPowerQuotient X I K n) := by
  have := isIso_idealMultipleToIdealPowerMultiple X I K hK n
  refine ⟨cokernel.desc _ (idealQuotientπ (baseRingHom A B hA X.1 X.2) K (I ^ n)) ?_, ?_, ?_⟩
  · have h : inv (idealMultipleToIdealPowerMultiple X I K n) ≫
        idealMultipleι (baseRingHom A B hA X.1 X.2) K (I ^ n) =
        (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) n K).ι :=
      (IsIso.inv_comp_eq _).2 (idealMultipleToIdealPowerMultiple_ι X I K n).symm
    rw [← h, Category.assoc, idealMultipleι_idealQuotientπ, comp_zero]
  · refine (cancel_epi (idealQuotientπ (baseRingHom A B hA X.1 X.2) K (I ^ n))).1 ?_
    rw [idealQuotientπ_comp_idealQuotientToIdealPowerQuotient_assoc, cokernel.π_desc,
      Category.comp_id]
  · refine (cancel_epi (cokernel.π
      (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) n K).ι)).1 ?_
    rw [cokernel.π_desc_assoc, idealQuotientπ_comp_idealQuotientToIdealPowerQuotient,
      Category.comp_id]

/-- The comparison commutes with the transition maps. -/
theorem idealQuotientMap_comp_idealQuotientToIdealPowerQuotient {m n : ℕ} (h : m ≤ n) :
    idealQuotientMap (baseRingHom A B hA X.1 X.2) K (Ideal.pow_le_pow_right h) ≫
        idealQuotientToIdealPowerQuotient X I K m =
      idealQuotientToIdealPowerQuotient X I K n ≫
        idealPowerQuotientMapOfLE B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) h K := by
  refine (cancel_epi (idealQuotientπ (baseRingHom A B hA X.1 X.2) K (I ^ n))).1 ?_
  rw [idealQuotientπ_idealQuotientMap_assoc, idealQuotientπ_comp_idealQuotientToIdealPowerQuotient,
    idealQuotientπ_comp_idealQuotientToIdealPowerQuotient_assoc, π_comp_idealPowerQuotientMapOfLE]

end Spellings

/-! ### `H⁰` is the functor of global sections -/

section DegreeZero

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  (X : AlgebraicSpaces B (Spec (.of A)) hA)

/-- `H⁰(X, M)`, as an `A`-module, is the module of global sections of `M`. -/
def cohomologyResZeroIso (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) :
    cohomologyRes (baseRingHom A B hA X.1 X.2) 0 M ≅ (sectionsOverBase A B hA X.1 X.2).obj M :=
  have := preservesFiniteLimits_globalSectionsFunctor_ringUniverse
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)
  (ModuleCat.restrictScalars (baseRingHom A B hA X.1 X.2)).mapIso
    ((globalSectionsFunctor.{u + 1, u, u, u} _).rightDerivedZeroIsoSelf.app M)

/-- The isomorphism `cohomologyResZeroIso` is natural in the module: for `g : M ⟶ N` it
intertwines `H⁰(g)` with the map of global sections induced by `g`. -/
theorem cohomologyResZeroIso_naturality {M N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (g : M ⟶ N) (x : cohomologyRes (baseRingHom A B hA X.1 X.2) 0 M) :
    (cohomologyResZeroIso X N).hom (cohomologyResMap (baseRingHom A B hA X.1 X.2) 0 g x) =
      ((sectionsOverBase A B hA X.1 X.2).map g).hom ((cohomologyResZeroIso X M).hom x) := by
  have := preservesFiniteLimits_globalSectionsFunctor_ringUniverse
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)
  have h := ((globalSectionsFunctor.{u + 1, u, u, u} _).rightDerivedZeroIsoSelf.hom.naturality g)
  have h2 := congrArg
    (fun k => ((ModuleCat.restrictScalars (baseRingHom A B hA X.1 X.2)).map k).hom x) h
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2

end DegreeZero

/-! ### The theorem on formal functions in degree zero -/

section Comparison

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  (X : AlgebraicSpaces B (Spec (.of A)) hA) (I : Ideal A)
  (K : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (hK : K.IsQuasicoherentOnSite)

/-- Applying `sectionsMap f` after `cohomologyResZeroIso` and `H⁰(g)` is `sectionsMap (g ≫ f)`
after `cohomologyResZeroIso`. -/
private theorem sectionsMap_cohomologyResZeroIso_cohomologyResMap
    {M N P : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2} (g : M ⟶ N) (f : N ⟶ P)
    (x : cohomologyRes (baseRingHom A B hA X.1 X.2) 0 M) :
    SheafOfModules.sectionsMap f
        ((cohomologyResZeroIso X N).hom (cohomologyResMap (baseRingHom A B hA X.1 X.2) 0 g x)) =
      SheafOfModules.sectionsMap (g ≫ f) ((cohomologyResZeroIso X M).hom x) :=
  (congrArg (SheafOfModules.sectionsMap f) (cohomologyResZeroIso_naturality X g x)).trans
    (SheafOfModules.sectionsMap_comp _ _ _).symm

/-- `K / Iⁿ K ≅ K / (I 𝒪_X)ⁿ K` for a quasi-coherent `K`. -/
def idealQuotientIsoIdealPowerQuotient (n : ℕ) :
    idealQuotient (baseRingHom A B hA X.1 X.2) K (I ^ n) ≅
      idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) n K :=
  haveI := isIso_idealQuotientToIdealPowerQuotient X I K hK n
  asIso (idealQuotientToIdealPowerQuotient X I K n)

/-- The global sections of `K / Iⁿ K` are those of `K / (I 𝒪_X)ⁿ K`. -/
def idealQuotientSectionsEquiv (n : ℕ) :
    (idealQuotient (baseRingHom A B hA X.1 X.2) K (I ^ n)).sections ≃
      (idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) n K).sections where
  toFun := SheafOfModules.sectionsMap (idealQuotientIsoIdealPowerQuotient X I K hK n).hom
  invFun := SheafOfModules.sectionsMap (idealQuotientIsoIdealPowerQuotient X I K hK n).inv
  left_inv := fun s => by
    rw [← SheafOfModules.sectionsMap_comp, Iso.hom_inv_id, SheafOfModules.sectionsMap_id]
  right_inv := fun s => by
    rw [← SheafOfModules.sectionsMap_comp, Iso.inv_hom_id, SheafOfModules.sectionsMap_id]

/-- `H⁰(X, K / Iⁿ K)` is the module of global sections of `K / (I 𝒪_X)ⁿ K`. -/
def adicCohomologyZeroEquiv (n : ℕ) :
    adicCohomology (baseRingHom A B hA X.1 X.2) K I 0 n ≃
      (idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) n K).sections :=
  ((cohomologyResZeroIso X
      (idealQuotient (baseRingHom A B hA X.1 X.2) K (I ^ n))).toLinearEquiv.toEquiv).trans
    (idealQuotientSectionsEquiv X I K hK n)

/-- Under `adicCohomologyZeroEquiv`, the transition map `H⁰(X, K / Iⁿ⁺² K) → H⁰(X, K / Iⁿ⁺¹ K)`
corresponds to the map of global sections induced by `K / (I 𝒪_X)ⁿ⁺² K → K / (I 𝒪_X)ⁿ⁺¹ K`. -/
theorem adicCohomologyZeroEquiv_map (n : ℕ)
    (x : adicCohomology (baseRingHom A B hA X.1 X.2) K I 0 (n + 2)) :
    adicCohomologyZeroEquiv X I K hK (n + 1)
        (adicCohomologyMap (baseRingHom A B hA X.1 X.2) K I 0 (n + 1) (n + 2) (Nat.le_succ _) x) =
      SheafOfModules.sectionsMap
        (idealPowerQuotientMapOfLE B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I)
          (Nat.le_succ (n + 1)) K)
        (adicCohomologyZeroEquiv X I K hK (n + 2) x) := by
  refine (sectionsMap_cohomologyResZeroIso_cohomologyResMap X _ _ x).trans ?_
  exact (congrArg (fun k => SheafOfModules.sectionsMap k _)
    (idealQuotientMap_comp_idealQuotientToIdealPowerQuotient X I K (Nat.le_succ (n + 1)))).trans
    (SheafOfModules.sectionsMap_comp _ _ _)

/-- Under `cohomologyResZeroIso` and `adicCohomologyZeroEquiv`, the projection
`H⁰(X, K) → H⁰(X, K / Iⁿ K)` corresponds to the map of global sections induced by the projection
`K → K / (I 𝒪_X)ⁿ K`. -/
theorem adicCohomologyZeroEquiv_proj (n : ℕ)
    (x : cohomologyRes (baseRingHom A B hA X.1 X.2) 0 K) :
    adicCohomologyZeroEquiv X I K hK n (adicCohomologyProj (baseRingHom A B hA X.1 X.2) K I 0 n x) =
      SheafOfModules.sectionsMap
        (cokernel.π (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) n K).ι)
        ((cohomologyResZeroIso X K).hom x) := by
  refine (sectionsMap_cohomologyResZeroIso_cohomologyResMap X _ _ x).trans ?_
  exact congrArg (fun k => SheafOfModules.sectionsMap k _)
    (idealQuotientπ_comp_idealQuotientToIdealPowerQuotient X I K n)

end Comparison

section Proper

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] [IsNoetherianRing A]
  {hA : B.Contains (Spec (.of A))} (X : AlgebraicSpaces B (Spec (.of A)) hA)
  (hX : IsProper B (Spec (.of A)) hA ((isTerminal_yoneda_obj_base B _ hA).from X.1))
  (I : Ideal A) [IsAdicComplete I A]

include hX in
/-- **The theorem on formal functions in degree zero over a complete base** ([Stacks, Tag 08B0]
for `p = 0`): for a coherent `K` on a proper algebraic space `X` over `Spec A`, with `A` Noetherian
and `I`-adically complete, `Γ(X, K) ⟶ limₙ Γ(X, K / (I 𝒪_X)ⁿ⁺¹ K)` is bijective. -/
theorem bijective_adicSectionsOfSections_of_isProper
    (K : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) [IsCoherent B (Spec (.of A)) hA X.1 X.2 K] :
    Function.Bijective
      (adicSectionsOfSections B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) K) := by
  have hK : K.IsQuasicoherentOnSite :=
    (inferInstance : IsCoherent _ _ _ _ _ K).toIsQuasicoherentOnSite
  let η := cohomologyResZeroIso X K
  let g : cohomologyRes (baseRingHom A B hA X.1 X.2) 0 K → adicSections B (Spec (.of A)) hA X.1 X.2
      (fun n => smallEtaleAdicQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) (n + 1) K)
      (fun n => smallEtaleAdicQuotientTransition B (Spec (.of A)) hA X.1 X.2
        (baseIdealSheaf A X I) (n + 1) K) :=
    fun x => adicSectionsOfSections B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) K (η.hom x)
  have hg : Function.Bijective g := by
    refine bijective_of_bijective_towerLimit
      (adicCohomologyMap (baseRingHom A B hA X.1 X.2) K I 0)
      (adicCohomologyProj (baseRingHom A B hA X.1 X.2) K I 0) ?_ ?_ _
      (fun n => adicCohomologyZeroEquiv X I K hK (n + 1))
      (fun n x => adicCohomologyZeroEquiv_map X I K hK n x)
      (fun m n h x => by rw [← LinearMap.comp_apply, adicCohomologyMap_comp_proj])
      (bijective_adicCohomologyLimitMap_of_isAdicComplete X hX K I 0) g
      (fun x n => (adicCohomologyZeroEquiv_proj X I K hK (n + 1) x).symm)
    · intro n x
      change cohomologyResMap (baseRingHom A B hA X.1 X.2) 0
        (idealQuotientMap (baseRingHom A B hA X.1 X.2) K (le_refl (I ^ n))) x = x
      rw [idealQuotientMap_refl, cohomologyResMap_id_apply]
    · intro m n k h₁ h₂ x
      rw [cohomologyResMap_comp_apply, idealQuotientMap_comp]
  have hfac : adicSectionsOfSections B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) K =
      g ∘ η.inv := by
    funext σ
    change _ = adicSectionsOfSections B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) K
      (η.hom (η.inv σ))
    exact congrArg _ (Iso.inv_hom_id_apply η σ).symm
  rw [hfac]
  exact hg.comp η.toLinearEquiv.symm.bijective

end Proper

end AlgebraicGeometry.Space

end
