module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.FlatLocalBaseShifts
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.PrincipalNonzerodivisor
public import StacksFrontier.RingTheory.Noetherian.CommutingShifts
public import StacksFrontier.Topology.Algebra.AdicLimitTopologyModuleCat
public import StacksFrontier.Topology.Sheaves.Cohomology.InverseSystems.MittagLefflerIdealBoundaries

/-!
# Stacks 0EJU: algebraization of a coherent formal module flat over a Noetherian local base

Fix an algebraization situation (Stacks 0EHC): a Noetherian ring `A` with ideals `I ⊆ 𝔞`,
`X = Spec(A)`, `Y = V(I)`, `Z = V(𝔞)` and `U = X \ Z`. Let `(F_n)` be a coherent `I`-adic system
on `U`, and suppose there is a Noetherian local ring `(R, 𝔪)` with a ring map `R → A` such that

1. `I = 𝔪 A`,
2. the formal stalk `F_y^∧` is `R`-flat for every `y ∈ U ∩ Y`,
3. `H⁰(U, F_1)` and `H¹(U, F_1)` are finite `A`-modules.

Stacks 0EJU concludes that `(F_n)` extends canonically to `X`, and that it is the completion of a
coherent `𝒪_U`-module when `A` is complete. The proof is that of Stacks 0EJS: verify the three
conditions of the Mittag-Leffler criterion Stacks 0EHH, using the decomposition of `Iⁿ F_(n+1)`
into copies of `F_1`.

* Condition (c), finiteness of the sections, is
  `Stacks.Algebraization.finite_idealPowerSections_of_flatLocalBase` together with the induction
  of Stacks 0EJS.
* Condition (a), Mittag-Leffler for `H⁰(U, F_n)`, is Cohomology 0GYK in its general-ideal form
  `Stacks.Cohomology.IdealBoundaries.isMittagLefflerCategorical_of_idealBoundaries`, whose last
  hypothesis — the boundary classes are eventually generated in degree one — is the graded chain
  condition on `⨁ₙ H¹(U, Iⁿ F_(n+1))`: `Stacks.CommutingShifts.exists_eventual_sum_shift` applied
  to the shifts of `StacksFrontier/AlgebraicGeometry/FormalGeometry/AlgebraizationCoherentFormal/
  FlatLocalBaseShifts.lean`, with `H¹(U, I F_2)` finite by hypothesis (3).
* Condition (b), the limit topology on `M = lim H⁰(U, F_n)` is `I`-adic, is Cohomology 0GYM: the
  same chain condition on `⨁ₙ H⁰(U, Iⁿ F_(n+1))` gives a successive approximation of the elements
  of `M` dying in `F_(n+1)`, which `Stacks.AdicLimit.iInf_induced_limit_eq_adicModuleTopology`
  turns into the equality of topologies.

## Main results

* `Stacks.Algebraization.isMittagLeffler_globalSectionsSystem_of_flatLocalBase` — condition (a).
* `Stacks.Algebraization.limitTopology_eq_adicModuleTopology_of_flatLocalBase` — condition (b).
* `Stacks.Algebraization.canonicallyExtends_of_flatLocalBase` — **Stacks 0EJU**.
* `Stacks.Algebraization.essImage_completionFunctor_of_flatLocalBase` — its concluding sentence,
  over an `I`-adically complete `A`.

## Implementation notes

The terms of the system are indexed from zero: the term of index `n` is the source's `F_(n+1)`.
Hypotheses (1) and (2) are the structure `Stacks.Algebraization.FlatLocalBase`, and hypothesis (3)
is `Stacks.Algebraization.HasFiniteLowDegreeCohomology`.

The boundary maps `H⁰(U, F_n) ⟶ H¹(U, Iⁿ⁺¹ F_(n+1))` are those of the universal `δ`-functor of
Stacks 071H, through `Stacks.Cohomology.InverseSystems.exists_connecting_maps`, with sections
identified with their zeroth right derived functor. Everything is then read over `A` by
restriction of scalars along `A → Γ(U, 𝒪_U)`, because the chain condition is a Noetherian argument
and needs the Noetherian ring `A`.

## References

* [Stacks Project, Tag 0EJU](https://stacks.math.columbia.edu/tag/0EJU)
* [Stacks Project, Tag 0EJS](https://stacks.math.columbia.edu/tag/0EJS)
* [Stacks Project, Tag 0EHH](https://stacks.math.columbia.edu/tag/0EHH)
* [Stacks Project, Tag 0GYK](https://stacks.math.columbia.edu/tag/0GYK)
* [Stacks Project, Tag 0GYM](https://stacks.math.columbia.edu/tag/0GYM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

variable (S : AlgebraizationSituation.{u})
  (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) (B : FlatLocalBase S F)

/-- Sections over `U`, as a functor to `A`-modules, are additive. -/
instance openSectionsFunctor_additive' : (openSectionsFunctor S).Additive where
  map_add := by
    intros
    ext x
    rfl

/-- Multiplication by an element of `A` acts on sections over `U` as the scalar action. -/
theorem openSectionsFunctor_map_sectionSmul (a : S.A) (M : S.U.toScheme.Modules)
    (x : (openSectionsFunctor S).obj M) :
    ((openSectionsFunctor S).map (sectionSmul (scalarMap S a) M)).hom x = a • x := by
  have hid : (S.U.toScheme.presheaf.map (⊤ : S.U.toScheme.Opens).leTop.op) (scalarMap S a) =
      scalarMap S a := by
    rw [show (⊤ : S.U.toScheme.Opens).leTop.op = 𝟙 _ from
      Quiver.Hom.unop_inj (Subsingleton.elim _ _), S.U.toScheme.presheaf.map_id]
    rfl
  have h2 : ∀ y : Γ(M, ⊤),
      (S.U.toScheme.presheaf.map (⊤ : S.U.toScheme.Opens).leTop.op) (scalarMap S a) • y =
        Scheme.Modules.Hom.app (sectionSmul (scalarMap S a) M) (⊤ : S.U.toScheme.Opens) y :=
    fun y => rfl
  have h3 : ∀ y : Γ(M, ⊤), Scheme.Modules.Hom.app (sectionSmul (scalarMap S a) M)
      (⊤ : S.U.toScheme.Opens) y = scalarMap S a • y := by
    intro y
    rw [← h2 y, hid]
  exact h3 x

/-- The structure map of `U` over `Spec A` used by `Stacks.LocalCohomology.cohomologyOverBase` is
`Stacks.Algebraization.scalarMap`. -/
theorem baseScalars_eq_scalarMap :
    Stacks.LocalCohomology.baseScalars S.A S.U.ι = scalarMap S := by
  change ((Scheme.ΓSpecIso (.of S.A)).inv ≫ S.U.ι.appLE ⊤ ⊤ _).hom =
    ((Scheme.ΓSpecIso (.of S.A)).inv ≫ S.U.ι.app ⊤).hom
  rw [← Scheme.Hom.appLE_eq_app]
  rfl

/-- Cohomology over the base and `H^p(U, -)` with scalars restricted along
`Stacks.Algebraization.scalarMap` are the same `A`-module. -/
theorem finite_openCohomology_of_finite_cohomologyOverBase (p : ℕ) (M : S.U.toScheme.Modules)
    (h : Module.Finite S.A (Stacks.LocalCohomology.cohomologyOverBase.{u, u} S.A S.U.ι M p)) :
    Module.Finite S.A ((openCohomologyFunctor S p).obj M) := by
  have e : Stacks.LocalCohomology.cohomologyOverBase.{u, u} S.A S.U.ι M p =
      (openCohomologyFunctor S p).obj M := by
    change (ModuleCat.restrictScalars (Stacks.LocalCohomology.baseScalars S.A S.U.ι)).obj _ = _
    rw [baseScalars_eq_scalarMap]
    rfl
  rwa [← e]

/-! ### Two abstract computations with boundary maps

They are stated for arbitrary categories and functors because the concrete objects, sheaves of
modules over `S.U.toScheme.ringCatSheaf`, are not type-correct at the transparency `rw` uses: the
structure sheaf is a `TopCat.Sheaf` where `SheafOfModules` asks for a `Sheaf` on the site, and the
two types agree only after unfolding. -/

section Abstract

variable {C : Type*} [Category C] {Γ' : Type*} [Ring Γ']

/-- The kernel of `δ ∘ R⁰(e⁻¹) ∘ α⁻¹`, for `α : R⁰ ≅ E`, a boundary `δ` with kernel the image of
`R⁰(g)`, and `e : X₃ ≅ Y` with `g ≫ e = t`, is the image of `E(t)`. -/
theorem abstract_boundary_eq_zero_iff (R0 E : C ⥤ ModuleCat.{u} Γ') (α : R0 ≅ E)
    {X₂ X₃ Y : C} (g : X₂ ⟶ X₃) (e : X₃ ≅ Y) (t : X₂ ⟶ Y) (ht : g ≫ e.hom = t)
    {N : ModuleCat.{u} Γ'} (δ : R0.obj X₃ ⟶ N)
    (hδ : LinearMap.range (R0.map g).hom = LinearMap.ker δ.hom) (y : E.obj Y) :
    (α.inv.app Y ≫ R0.map e.inv ≫ δ).hom y = 0 ↔ y ∈ LinearMap.range (E.map t).hom := by
  have hcomp : R0.map t ≫ R0.map e.inv = R0.map g := by
    rw [← ht, ← R0.map_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  constructor
  · intro hy
    have hmem : (R0.map e.inv).hom ((α.inv.app Y).hom y) ∈ LinearMap.range (R0.map g).hom := by
      rw [hδ]
      exact hy
    obtain ⟨z, hz⟩ := hmem
    refine ⟨(α.hom.app X₂).hom z, ?_⟩
    have hz' : (R0.map t).hom z = (α.inv.app Y).hom y := by
      have h := congrArg (R0.map e.hom).hom hz
      rw [← hcomp] at h
      change (R0.map t ≫ R0.map e.inv ≫ R0.map e.hom).hom z =
        (R0.map e.inv ≫ R0.map e.hom).hom _ at h
      rwa [← R0.map_comp, ← R0.map_comp, Iso.inv_hom_id, R0.map_id, Category.comp_id] at h
    have hnat := congrArg (fun φ => φ.hom z) (α.hom.naturality t)
    change (α.hom.app Y).hom ((R0.map t).hom z) = (E.map t).hom ((α.hom.app X₂).hom z) at hnat
    rw [← hnat, hz']
    change (α.inv.app Y ≫ α.hom.app Y).hom y = y
    rw [Iso.inv_hom_id_app]
    rfl
  · rintro ⟨w, rfl⟩
    have hnat := congrArg (fun φ => φ.hom w) (α.inv.naturality t)
    change (α.inv.app Y).hom ((E.map t).hom w) = (R0.map t).hom ((α.inv.app X₂).hom w) at hnat
    change δ.hom ((R0.map e.inv).hom ((α.inv.app Y).hom ((E.map t).hom w))) = 0
    rw [hnat]
    change δ.hom ((R0.map t ≫ R0.map e.inv).hom ((α.inv.app X₂).hom w)) = 0
    rw [hcomp, ← LinearMap.mem_ker, ← hδ]
    exact LinearMap.mem_range_self _ _

/-- The naturality of `δ ∘ R⁰(e⁻¹) ∘ α⁻¹` in a morphism of short sequences whose third component
is `e ≫ u ≫ e'⁻¹`. -/
theorem abstract_boundary_naturality (R0 E R1 : C ⥤ ModuleCat.{u} Γ') (α : R0 ≅ E)
    {X₃ X₃' Y Y' K K' : C} (e : X₃ ≅ Y) (e' : X₃' ≅ Y') (u : Y ⟶ Y') (μ : K ⟶ K')
    (δ : R0.obj X₃ ⟶ R1.obj K) (δ' : R0.obj X₃' ⟶ R1.obj K')
    (hnat : R0.map (e.hom ≫ u ≫ e'.inv) ≫ δ' = δ ≫ R1.map μ) :
    E.map u ≫ α.inv.app Y' ≫ R0.map e'.inv ≫ δ' =
      (α.inv.app Y ≫ R0.map e.inv ≫ δ) ≫ R1.map μ := by
  rw [← Category.assoc, α.inv.naturality, Category.assoc, ← Category.assoc (R0.map u),
    ← R0.map_comp, show u ≫ e'.inv = e.inv ≫ e.hom ≫ u ≫ e'.inv by
      rw [Iso.inv_hom_id_assoc], R0.map_comp, Category.assoc, hnat]
  simp only [Category.assoc]

/-- A square of up maps and cokernel projections. -/
theorem abstract_up_comp_π {P₀ P₁ T₀ T₁ T₂ : C} (π₀ : T₁ ⟶ P₀) (π₁ : T₂ ⟶ P₁) (eh₀ : P₀ ⟶ T₀)
    (ei₁ : T₁ ⟶ P₁) (t₀ : T₁ ⟶ T₀) (t₁ : T₂ ⟶ T₁) (u₀ : T₀ ⟶ T₁) (u₁ : T₁ ⟶ T₂) (m : T₁ ⟶ T₁)
    (h₀ : π₀ ≫ eh₀ = t₀) (h₁ : π₁ = t₁ ≫ ei₁) (hu₀ : t₀ ≫ u₀ = m) (hu₁ : u₁ ≫ t₁ = m) :
    u₁ ≫ π₁ = π₀ ≫ eh₀ ≫ u₀ ≫ ei₁ := by
  rw [h₁, ← Category.assoc, hu₁, ← Category.assoc, ← Category.assoc, h₀, hu₀]

/-- A functor carries two equal composites to equal composites of linear maps. -/
theorem abstract_map_comm {A' : Type*} [Ring A'] (G : C ⥤ ModuleCat.{u} A') {K₀ K₁ K₁' K₂ : C}
    (a : K₀ ⟶ K₁) (b : K₁ ⟶ K₂) (a' : K₀ ⟶ K₁') (b' : K₁' ⟶ K₂) (h : a ≫ b = a' ≫ b')
    (x : G.obj K₀) : (G.map b).hom ((G.map a).hom x) = (G.map b').hom ((G.map a').hom x) := by
  change (G.map a ≫ G.map b).hom x = (G.map a' ≫ G.map b').hom x
  rw [← G.map_comp, ← G.map_comp, h]

end Abstract

/-! ### The boundary maps and their naturality -/

/-- Sections over `U` with values in `Γ(U, 𝒪_U)`-modules. -/
abbrev topSections : _root_.SheafOfModules.{u} S.U.toScheme.ringCatSheaf ⥤
    ModuleCat.{u} (S.U.toScheme.ringCatSheaf.obj.obj (op (⊤ : S.U.toScheme.Opens))) :=
  _root_.SheafOfModules.evaluation S.U.toScheme.ringCatSheaf (op (⊤ : S.U.toScheme.Opens))

/-- The boundary maps `H⁰(U, X₃) ⟶ H¹(U, X₁)` of short exact sequences of `𝒪_U`-modules, those of
the universal `δ`-functor of Stacks 071H. -/
def boundary {T : ShortComplex (_root_.SheafOfModules.{u} S.U.toScheme.ringCatSheaf)}
    (hT : T.ShortExact) :
    ((topSections S).rightDerived 0).obj T.X₃ ⟶ ((topSections S).rightDerived 1).obj T.X₁ :=
  (Stacks.Cohomology.InverseSystems.exists_connecting_maps S.U.toScheme.ringCatSheaf 0).2.choose hT

/-- For a short exact sequence `0 → X₁ → X₂ → X₃ → 0` of `𝒪_U`-modules, the image of
`H⁰(U, X₂) ⟶ H⁰(U, X₃)` is the kernel of the boundary map `boundary`. -/
theorem range_eq_ker_boundary
    {T : ShortComplex (_root_.SheafOfModules.{u} S.U.toScheme.ringCatSheaf)}
    (hT : T.ShortExact) :
    LinearMap.range (((topSections S).rightDerived 0).map T.g).hom =
      LinearMap.ker (boundary S hT).hom :=
  (Stacks.Cohomology.InverseSystems.exists_connecting_maps S.U.toScheme.ringCatSheaf
    0).2.choose_spec.1 hT

/-- The boundary maps `H⁰(U, X₃) ⟶ H¹(U, X₁)` are natural with respect to morphisms of short
exact sequences. -/
theorem boundary_naturality
    {T T' : ShortComplex (_root_.SheafOfModules.{u} S.U.toScheme.ringCatSheaf)}
    (hT : T.ShortExact) (hT' : T'.ShortExact) (φ : T ⟶ T') :
    ((topSections S).rightDerived 0).map φ.τ₃ ≫ boundary S hT' =
      boundary S hT ≫ ((topSections S).rightDerived 1).map φ.τ₁ :=
  (Stacks.Cohomology.InverseSystems.exists_connecting_maps S.U.toScheme.ringCatSheaf
    0).2.choose_spec.2 hT hT' φ

/-- The identification of the cokernel of `Iⁿ⁺¹ F_(n+1) ⟶ F_(n+1)` with `F_n`. -/
def cokernelIso (n : ℕ) : (idealPowerShortComplex S F n).X₃ ≅ F.obj.obj (op n) :=
  (F.property.2.2 n).choose

/-- The projection `F_(n+1) ⟶ F_(n+1)/Iⁿ⁺¹ F_(n+1)` followed by `cokernelIso` is the
transition map `F_(n+1) ⟶ F_n`. -/
theorem π_cokernelIso_hom (n : ℕ) :
    (idealPowerShortComplex S F n).g ≫ (cokernelIso S F n).hom = succTrans S F n :=
  (F.property.2.2 n).choose_spec

/-- **The boundary map of the ideal-power sequence**, `H⁰(U, F_n) ⟶ H¹(U, Iⁿ⁺¹ F_(n+1))`. -/
def sectionsBoundary (n : ℕ) :
    (topSections S).obj (F.obj.obj (op n)) ⟶
      ((topSections S).rightDerived 1).obj (idealPowerSub S F n).toSheafOfModules :=
  (topSections S).rightDerivedZeroIsoSelf.inv.app _ ≫
    ((topSections S).rightDerived 0).map (cokernelIso S F n).inv ≫
      boundary S (idealPowerShortComplex_shortExact S F n)

/-- The kernel of the boundary map is the image of the transition. -/
theorem sectionsBoundary_eq_zero_iff (n : ℕ) (y : (topSections S).obj (F.obj.obj (op n))) :
    (sectionsBoundary S F n).hom y = 0 ↔
      y ∈ LinearMap.range ((topSections S).map (succTrans S F n)).hom :=
  abstract_boundary_eq_zero_iff _ _ (topSections S).rightDerivedZeroIsoSelf _ _ _
    (π_cokernelIso_hom S F n) _ (range_eq_ker_boundary S (idealPowerShortComplex_shortExact S F n))
    y

/-- The morphism of ideal-power sequences given by the up maps of a generator. -/
def shiftShortComplex (l : maxGens S F B) (n : ℕ) :
    idealPowerShortComplex S F n ⟶ idealPowerShortComplex S F (n + 1) where
  τ₁ := shiftSub S F B l n
  τ₂ := upMap S F B l (n + 1)
  τ₃ := (cokernelIso S F n).hom ≫ upMap S F B l n ≫ (cokernelIso S F (n + 1)).inv
  comm₁₂ := shiftSub_ι S F B l n
  comm₂₃ := abstract_up_comp_π _ _ _ _ _ _ _ _ _ (π_cokernelIso_hom S F n)
    ((Iso.eq_comp_inv _).mpr (π_cokernelIso_hom S F (n + 1))) (trans_upMap S F B l n)
    (upMap_trans S F B l (n + 1))

/-- **The boundary maps commute with the shifts**: `δ_(n+1) ∘ H⁰(uₗ) = H¹(μₗ) ∘ δₙ`. -/
theorem upMap_comp_sectionsBoundary (l : maxGens S F B) (n : ℕ) :
    (topSections S).map (upMap S F B l n) ≫ sectionsBoundary S F (n + 1) =
      sectionsBoundary S F n ≫ ((topSections S).rightDerived 1).map (shiftSub S F B l n) :=
  abstract_boundary_naturality _ _ _ (topSections S).rightDerivedZeroIsoSelf _ _ _ _ _ _
    (boundary_naturality S (idealPowerShortComplex_shortExact S F n)
      (idealPowerShortComplex_shortExact S F (n + 1)) (shiftShortComplex S F B l n))

/-! ### Condition (a) of Stacks 0EHH: Mittag-Leffler -/

/-- The boundary map `H⁰(U, F_n) ⟶ H¹(U, Iⁿ⁺¹ F_(n+1))`, as a map of `A`-modules. -/
def sectionsBoundaryA (n : ℕ) :
    (openSectionsFunctor S).obj (F.obj.obj (op n)) →ₗ[S.A]
      (openCohomologyFunctor S 1).obj (idealPowerSub S F n).toSheafOfModules :=
  ((ModuleCat.restrictScalars (scalarMap S)).map (sectionsBoundary S F n)).hom

/-- The shift `H¹(U, Iⁿ⁺¹ F_(n+1)) ⟶ H¹(U, Iⁿ⁺² F_(n+2))` of a generator, over `A`. -/
def cohomologyShift (p : ℕ) (l : maxGens S F B) (n : ℕ) :
    (openCohomologyFunctor S p).obj (idealPowerSub S F n).toSheafOfModules →ₗ[S.A]
      (openCohomologyFunctor S p).obj (idealPowerSub S F (n + 1)).toSheafOfModules :=
  ((openCohomologyFunctor S p).map (shiftSub S F B l n)).hom

/-- The functor `H^p(U, -)` to `A`-modules is additive. -/
instance openCohomologyFunctor_additive (p : ℕ) : (openCohomologyFunctor S p).Additive where
  map_add {_ _ f g} :=
    congrArg (ModuleCat.restrictScalars (scalarMap S)).map
      ((Stacks.Cohomology.InverseSystems.exists_connecting_maps
        S.U.toScheme.ringCatSheaf p).1.map_add (f := f) (g := g))

/-- The inverse system of sections over `U` is the sequence of transition maps of `(F_n)`
followed by sections over `U`. -/
private theorem globalSectionsSystem_eq_ofOpSequence :
    globalSectionsSystem S F =
      Functor.ofOpSequence (X := fun n => F.obj.obj (op n))
        (fun n => F.obj.map (homOfLE (Nat.le_succ n)).op) ⋙ openSectionsFunctor S :=
  congrArg (fun G => G ⋙ openSectionsFunctor S) (eq_ofOpSequence F.obj)

/-- **Condition (a) of Stacks 0EHH in the situation of Stacks 0EJU.** Under hypotheses (1) and
(2) of Stacks 0EJU, and finiteness of `H¹(U, F_1)` — the degree-one half of hypothesis (3) — the
inverse system `H⁰(U, F_n)` has the Mittag-Leffler property.

This is Cohomology 0GYK in its general-ideal form
`Stacks.Cohomology.IdealBoundaries.isMittagLefflerCategorical_of_idealBoundaries`, for the up maps
of a finite generating family of `𝔪`; its hypothesis that the boundaries are eventually generated
in degree one is the chain condition `Stacks.CommutingShifts.exists_eventual_sum_shift` on the
graded module `⨁ₙ H¹(U, Iⁿ⁺¹ F_(n+1))`, which is generated in degree zero by the decomposition
of `Iⁿ⁺¹ F_(n+1)` into copies of `F_1`. -/
theorem isMittagLeffler_globalSectionsSystem_of_flatLocalBase (B : FlatLocalBase S F)
    (h1 : Module.Finite S.A
      (Stacks.LocalCohomology.cohomologyOverBase.{u, u} S.A S.U.ι (F.obj.obj (op 0)) 1)) :
    IsMittagLefflerCategorical (globalSectionsSystem S F) := by
  classical
  have hfin0 : Module.Finite S.A
      ((openCohomologyFunctor S 1).obj (idealPowerSub S F 0).toSheafOfModules) :=
    finite_openCohomology_of_finite_cohomologyOverBase S 1 _
      (finite_cohomologyOverBase_idealPowerSub_of_flatLocalBase S F B 1 h1 0)
  have hd : ∀ n, LinearMap.range ((openSectionsFunctor S).map (succTrans S F n)).hom =
      LinearMap.ker (sectionsBoundaryA S F n) := by
    intro n
    ext y
    exact (sectionsBoundary_eq_zero_iff S F n y).symm
  have hdu : ∀ (l : maxGens S F B) (n : ℕ), (sectionsBoundaryA S F (n + 1)).comp
      ((openSectionsFunctor S).map (upMap S F B l n)).hom =
        (cohomologyShift S F B 1 l n).comp (sectionsBoundaryA S F n) := fun l n =>
    LinearMap.ext fun x =>
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (upMap_comp_sectionsBoundary S F B l n)) x
  have hup : ∀ (l : maxGens S F B) (n : ℕ),
      ((openSectionsFunctor S).map (upMap S F B l n) ≫
        (openSectionsFunctor S).map (succTrans S F n)).hom =
        B.φ l • (LinearMap.id : (openSectionsFunctor S).obj (F.obj.obj (op n)) →ₗ[S.A] _) := by
    intro l n
    rw [← Functor.map_comp, upMap_trans]
    exact LinearMap.ext fun x => openSectionsFunctor_map_sectionSmul S (B.φ l) _ x
  obtain ⟨c, hc⟩ := Stacks.CommutingShifts.exists_eventual_sum_shift
    (N := fun n => (openCohomologyFunctor S 1).obj (idealPowerSub S F n).toSheafOfModules)
    (cohomologyShift S F B 1)
    (fun l l' n x => abstract_map_comm _ _ _ _ _ (shiftSub_comm S F B l l' n) x)
    (fun n x => exists_sum_shiftSub S F B (openCohomologyFunctor S 1) n x)
    (fun n => LinearMap.range (sectionsBoundaryA S F n))
    (fun l n x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact ⟨_, LinearMap.congr_fun (hdu l n) y⟩)
  have hboundary : ∀ n, c ≤ n → ∀ x : (openSectionsFunctor S).obj (F.obj.obj (op (n + 1))),
      ∃ y : maxGens S F B → (openSectionsFunctor S).obj (F.obj.obj (op n)),
        sectionsBoundaryA S F (n + 1) x =
          ∑ l, cohomologyShift S F B 1 l n (sectionsBoundaryA S F n (y l)) := by
    intro n hn x
    obtain ⟨z, hz, hsum⟩ := hc n hn _ ⟨x, rfl⟩
    choose y hy using hz
    refine ⟨y, ?_⟩
    rw [hsum]
    simp only [hy]
  rw [globalSectionsSystem_eq_ofOpSequence]
  exact Stacks.Cohomology.IdealBoundaries.isMittagLefflerCategorical_of_idealBoundaries
    (openSectionsFunctor S) (fun n => F.obj.obj (op n)) (succTrans S F)
    (fun l : maxGens S F B => B.φ l) S.I (I_eq_span_gens S F B) (upMap S F B) hup
    (fun i => idealPow_smul_globalSections_eq_bot S F i) (sectionsBoundaryA S F) hd
    (cohomologyShift S F B 1) hdu c hboundary

/-! ### Condition (b) of Stacks 0EHH: the limit topology -/

/-- The shift `H⁰(U, Iⁿ⁺¹ F_(n+1)) ⟶ H⁰(U, Iⁿ⁺² F_(n+2))` of a generator, over `A`. -/
abbrev sectionsShift (l : maxGens S F B) (n : ℕ) :
    idealPowerSections S F n →ₗ[S.A] idealPowerSections S F (n + 1) :=
  ((openSectionsFunctor S).map (shiftSub S F B l n)).hom

/-- `fₗ` kills the sections of `Iⁿ⁺¹ F_(n+1)` inside those of `F_(n+1)`. -/
theorem gen_smul_idealPowerSectionsι (l : maxGens S F B) (n : ℕ) (k : idealPowerSections S F n) :
    B.φ l • (idealPowerSectionsι S F n).hom k = 0 := by
  have : (F.obj.obj (op (n + 1))).IsQuasicoherent := F.property.isQuasicoherent (n + 1)
  have hzero := idealPowerMultiple_ι_comp_sectionSmul (F.obj.obj (op (n + 1))) (k := 1)
    (d := n + 1) (r := n + 1 + 1) (by omega) (F.property.idealPowerMultiple_eq_bot (n + 1))
    (restrictMemIdealPow_genSection S F B l)
  rw [← openSectionsFunctor_map_sectionSmul]
  exact (congrArg (fun φ => ((openSectionsFunctor S).map φ).hom k) hzero).trans rfl

/-- The transition map of the sections system sends the `(n+1)`-st term of a compatible family to
its `n`-th term. -/
private theorem map_limit_π_succ (n : ℕ) (x : limitGlobalSections S F) :
    ((globalSectionsSystem S F).map (homOfLE (Nat.le_succ n)).op).hom
      ((limit.π (globalSectionsSystem S F) (op (n + 1))).hom x) =
        (limit.π (globalSectionsSystem S F) (op n)).hom x :=
  congrArg (fun g => ModuleCat.Hom.hom g x)
    (limit.w (globalSectionsSystem S F) (homOfLE (Nat.le_succ n)).op)

/-- On a compatible family whose `(n+1)`-st term is a section `k` of `Iⁿ⁺¹ F_(n+1)`,
multiplication by `fₗ` in degree `n + 2` is the shift of `k`. -/
theorem gen_smul_π_eq_shift (l : maxGens S F B) (n : ℕ) (x : limitGlobalSections S F)
    (k : idealPowerSections S F n)
    (hk : (limit.π (globalSectionsSystem S F) (op (n + 1))).hom x =
      (idealPowerSectionsι S F n).hom k) :
    B.φ l • (limit.π (globalSectionsSystem S F) (op (n + 2))).hom x =
      (idealPowerSectionsι S F (n + 1)).hom (sectionsShift S F B l n k) := by
  rw [← openSectionsFunctor_map_sectionSmul, ← trans_upMap]
  rw [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
    show ((openSectionsFunctor S).map (succTrans S F (n + 1))).hom _ = _ from
      map_limit_π_succ S F (n + 1) x, hk]
  exact abstract_map_comm _ _ _ _ _ (shiftSub_ι S F B l n).symm k

/-- The sections of `Iⁿ⁺¹ F_(n+1)` that are the `(n+1)`-st term of a compatible family dying in
degree `n`: the graded submodule `⨁ Eₙ` of the proof of Cohomology 0GYM. -/
def liftingSections (n : ℕ) : Submodule S.A (idealPowerSections S F n) :=
  (LinearMap.ker (limit.π (globalSectionsSystem S F) (op n)).hom).map
      (limit.π (globalSectionsSystem S F) (op (n + 1))).hom |>.comap
    (idealPowerSectionsι S F n).hom

/-- A section `k` of `Iⁿ⁺¹ F_(n+1)` lies in `liftingSections` if and only if its image in
`F_(n+1)` is the `(n+1)`-st term of a compatible family whose `n`-th term vanishes. -/
theorem mem_liftingSections_iff (n : ℕ) (k : idealPowerSections S F n) :
    k ∈ liftingSections S F n ↔ ∃ x : limitGlobalSections S F,
      (limit.π (globalSectionsSystem S F) (op n)).hom x = 0 ∧
        (limit.π (globalSectionsSystem S F) (op (n + 1))).hom x =
          (idealPowerSectionsι S F n).hom k := Iff.rfl

/-- The shift `sectionsShift` of a generator maps `liftingSections` in degree `n` into
`liftingSections` in degree `n + 1`. -/
theorem sectionsShift_mem_liftingSections (l : maxGens S F B) (n : ℕ)
    (k : idealPowerSections S F n) (hk : k ∈ liftingSections S F n) :
    sectionsShift S F B l n k ∈ liftingSections S F (n + 1) := by
  obtain ⟨x, hx0, hx1⟩ := (mem_liftingSections_iff S F n k).mp hk
  refine (mem_liftingSections_iff S F (n + 1) _).mpr ⟨B.φ l • x, ?_, ?_⟩
  · rw [map_smul, hx1]
    exact gen_smul_idealPowerSectionsι S F B l n k
  · rw [map_smul]
    exact gen_smul_π_eq_shift S F B l n x k hx1

/-- **Condition (b) of Stacks 0EHH in the situation of Stacks 0EJU.** Under hypotheses (1) and
(2) of Stacks 0EJU, and finiteness of `H⁰(U, F_1)`, the limit topology on
`M = lim H⁰(U, F_n)` is the `I`-adic topology.

This is Cohomology 0GYM: the chain condition `Stacks.CommutingShifts.exists_eventual_sum_shift` on
the graded module `⨁ₙ H⁰(U, Iⁿ⁺¹ F_(n+1))`, applied to the graded submodule
`Stacks.Algebraization.liftingSections`, gives a successive approximation of the elements of `M`
dying in degree `n + 1` by `fₗ`-multiples of elements dying in degree `n`. -/
theorem limitTopology_eq_adicModuleTopology_of_flatLocalBase (B : FlatLocalBase S F)
    (h0 : Module.Finite S.A ((globalSectionsSystem S F).obj (op 0))) :
    (⨅ n : ℕ, TopologicalSpace.induced
      (fun x : limitGlobalSections S F =>
        (limit.π (globalSectionsSystem S F) (op n)).hom x) ⊥) =
        S.I.adicModuleTopology (limitGlobalSections S F) := by
  classical
  have : Module.Finite S.A (idealPowerSections S F 0) :=
    finite_idealPowerSections_of_flatLocalBase S F B h0 0
  obtain ⟨c, hc⟩ := Stacks.CommutingShifts.exists_eventual_sum_shift
    (N := fun n => idealPowerSections S F n) (sectionsShift S F B)
    (fun l l' n x => abstract_map_comm _ _ _ _ _ (shiftSub_comm S F B l l' n) x)
    (fun n x => exists_sum_shiftSub S F B (openSectionsFunctor S) n x)
    (liftingSections S F) (sectionsShift_mem_liftingSections S F B)
  refine Stacks.AdicLimit.iInf_induced_limit_eq_adicModuleTopology (globalSectionsSystem S F)
    S.I (idealPow_smul_globalSections_eq_bot S F) (fun l : maxGens S F B => B.φ l)
    (gen_mem_I S F B) c fun n hn x hx => ?_
  have hker : (limit.π (globalSectionsSystem S F) (op (n + 2))).hom x ∈ LinearMap.ker
      ((globalSectionsSystem S F).map (homOfLE (Nat.le_succ (n + 1))).op).hom := by
    rw [LinearMap.mem_ker]
    exact (map_limit_π_succ S F (n + 1) x).trans hx
  obtain ⟨k, hk⟩ := ker_globalSectionsSystem_map_le_range S F (n + 1) hker
  obtain ⟨z, hz, hsum⟩ := hc n hn k ((mem_liftingSections_iff S F (n + 1) k).mpr ⟨x, hx, hk.symm⟩)
  choose y hy0 hy1 using fun l => (mem_liftingSections_iff S F n (z l)).mp (hz l)
  refine ⟨y, hy0, ?_⟩
  rw [map_sub, map_sum, ← hk, hsum, map_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [map_smul, gen_smul_π_eq_shift S F B l n (y l) (z l) (hy1 l), sub_self]

/-! ### Stacks 0EJU -/

/-- **Stacks Project, Tag 0EJU.** In Situation 0EHC let `(F_n)` be a coherent `I`-adic system on
`U`, and let `(R, 𝔪)` be a Noetherian local ring with a ring map `R → A` such that `I = 𝔪 A` and
the formal stalks `F_y^∧`, `y ∈ U ∩ Y`, are `R`-flat (both recorded by `B`), and suppose that
`H⁰(U, F_1)` and `H¹(U, F_1)` are finite `A`-modules. Then `(F_n)` extends canonically to `X`.

The proof verifies the three conditions of Stacks 0EHH: (a) is
`Stacks.Algebraization.isMittagLeffler_globalSectionsSystem_of_flatLocalBase`, (b) is
`Stacks.Algebraization.limitTopology_eq_adicModuleTopology_of_flatLocalBase`, and (c) comes from
the finiteness of every `H⁰(U, Iⁿ F_(n+1))`, which the direct-sum decomposition
`Stacks.Algebraization.exists_isoDirectSum_idealPowerSub` gives. -/
@[stacks 0EJU]
theorem canonicallyExtends_of_flatLocalBase (B : FlatLocalBase S F)
    (h3 : HasFiniteLowDegreeCohomology S F) : CanonicallyExtends S F :=
  canonicallyExtends_of_isoDirectSum S F
    (isMittagLeffler_globalSectionsSystem_of_flatLocalBase S F B h3.2)
    (limitTopology_eq_adicModuleTopology_of_flatLocalBase S F B h3.1) h3.1
    (fun m => exists_isoDirectSum_idealPowerSub S F B m)

/-- **Stacks Project, Tag 0EJU, the concluding sentence.** Under the hypotheses of Stacks 0EJU, if
`A` is moreover `I`-adically complete, then `(F_n)` is the completion of a coherent
`𝒪_U`-module. -/
@[stacks 0EJU "in particular, over an I-adically complete A the system is the completion of a \
coherent 𝒪_U-module"]
theorem essImage_completionFunctor_of_flatLocalBase [IsAdicComplete S.I S.A]
    (B : FlatLocalBase S F) (h3 : HasFiniteLowDegreeCohomology S F) :
    (completionFunctor S.U.toScheme (idealOnOpen S)).essImage F :=
  essImage_completionFunctor_of_isoDirectSum S F
    (isMittagLeffler_globalSectionsSystem_of_flatLocalBase S F B h3.2)
    (limitTopology_eq_adicModuleTopology_of_flatLocalBase S F B h3.1) h3.1
    (fun m => exists_isoDirectSum_idealPowerSub S F B m)

end Stacks.Algebraization

end
