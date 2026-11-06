module

public import Mathlib.CategoryTheory.Center.Linear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseRingLinear
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.IdealPowers
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.MilnorSurjection
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.Reduction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.GradedSplittingCharts
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.IdealPowerSplitting
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerived.DerivedDeltaFunctor
public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections

/-!
# The limit topology on the cohomology of an adic inverse system is `I`-adic

Let `I` be an ideal of a Noetherian ring `A`, let `X` be a Noetherian scheme over `Spec A` and
let `(F_n)` be an inverse system of coherent `𝒪_X`-modules with `F_n = F_{n+1} / I ^ n F_{n+1}`,
that is, a `Stacks.Algebraization.AdicInverseSystem` along `I · 𝒪_X`. [Stacks, Tag 0EH7] states
that when `cd(A, I) = 1` the limit topology on `lim_n H^p(X, F_n)` is the `I`-adic topology, for
every integer `p`. This file proves it.

Cohomology is `moduleCohomologyFunctorInt X p`, the `p`-th right derived functor of global
sections taken in `Γ(X, 𝒪_X)`-modules, for an integer degree `p`; the ideal `I` acts on it through
the structure morphism.

## Main definitions

* `Stacks.Algebraization.AdicInverseSystem.moduleCohomologyFunctorInt`: `H^p(X, -)` in
  `Γ(X, 𝒪_X)`-modules for an integer degree `p`.

## Main results

* `Stacks.Algebraization.AdicInverseSystem.limitIntCohomologyTopology_eq_adicModuleTopology`:
  [Stacks, Tag 0EH7], the limit topology on `lim_n H^p(X, F_n)` is the `I`-adic topology.

## References

* [Stacks Project, Tag 0EH7](https://stacks.math.columbia.edu/tag/0EH7)
* [Stacks Project, Tag 0EH6](https://stacks.math.columbia.edu/tag/0EH6)
* [Stacks Project, Tag 0EI8](https://stacks.math.columbia.edu/tag/0EI8)
* [Stacks Project, Tag 0EIA](https://stacks.math.columbia.edu/tag/0EIA)
* [Stacks Project, Tag 05TE](https://stacks.math.columbia.edu/tag/05TE)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry TopologicalSpace
open Stacks.Cohomology.FormalFunctions Stacks.Coherent Stacks.ReesAlgebra
open AlgebraicGeometry.SheafOfModules.Submodule (asModules ιModules)
open scoped AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Algebraization.AdicInverseSystem

/-- **A right derived functor of an `R`-linear functor is `R`-linear.** If `G`, with unit
`α : F ⟶ L ⋙ G`, is a right derived functor of an `R`-linear `F` along an `R`-linear
localization functor `L`, then `G` is `R`-linear. -/
private theorem rightDerived_linear_of_linear_unit
    {R : Type u} [CommRing R]
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
    [CategoryTheory.Linear R E]
    {W : MorphismProperty C} {L : C ⥤ D} [L.IsLocalization W]
    {F : C ⥤ E} {G : D ⥤ E} (α : F ⟶ L ⋙ G)
    [G.IsRightDerivedFunctor α W] (hF : Functor.Linear R F)
    (hL : Functor.Linear R L) : Functor.Linear R G := by
  let : Functor.Linear R F := hF
  let : Functor.Linear R L := hL
  rw [Functor.linear_iff]
  intro Z a
  let τ : F ⟶ F :=
    { app Y := a • (𝟙 (F.obj Y))
      naturality := by intro Y Y' g; simp [Linear.comp_smul, Linear.smul_comp] }
  let γ : G ⟶ G :=
    { app Y := G.map (a • (𝟙 Y))
      naturality := by
        intro Y Y' g
        rw [← G.map_comp, ← G.map_comp]
        congr 1
        simp [Linear.comp_smul, Linear.smul_comp] }
  let ε : G ⟶ G :=
    { app Y := a • (𝟙 (G.obj Y))
      naturality := by intro Y Y' g; simp [Linear.comp_smul, Linear.smul_comp] }
  have hγ : α ≫ Functor.whiskerLeft L γ = τ ≫ α := by
    ext Y
    dsimp [γ, τ, Functor.whiskerLeft]
    simpa [Functor.comp_map, Functor.map_smul] using
      (α.naturality (a • (𝟙 Y : Y ⟶ Y))).symm
  have hε : α ≫ Functor.whiskerLeft L ε = τ ≫ α := by
    ext Y
    dsimp [ε, τ, Functor.whiskerLeft]
    simp [Linear.comp_smul, Linear.smul_comp]
  simpa [γ, ε] using congrArg (fun η : G ⟶ G => η.app Z)
    (G.rightDerived_ext α W G γ ε (hγ.trans hε.symm))

/-- **The localization `K⁺(𝒜) ⥤ D⁺(𝒜)` is `R`-linear** when `𝒜` is. -/
private theorem derivedCategoryPlus_Qh_linear
    {R : Type*} [CommRing R] {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] [Linear R C] :
    Functor.Linear R (DerivedCategory.Plus.Qh (C := C)) := by
  apply (Functor.linear_iff (R := R) _).2
  intro Z a
  apply DerivedCategory.Plus.ι.map_injective
  show DerivedCategory.Qh.map (a • 𝟙 ((HomotopyCategory.Plus.ι C).obj Z)) =
    a • 𝟙 (DerivedCategory.Qh.obj ((HomotopyCategory.Plus.ι C).obj Z))
  exact (Functor.linear_iff (R := R) DerivedCategory.Qh).mp inferInstance _ a

/-- **The right derived functor `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` of an `R`-linear `F` is `R`-linear.** -/
private theorem rightDerivedFunctorPlus_linear_of_linear
    {R : Type u} [CommRing R]
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    [Linear R C] [Linear R D]
    (F : C ⥤ D) [F.Additive] (hF : Functor.Linear R F) :
    Functor.Linear R F.rightDerivedFunctorPlus := by
  let : Functor.Linear R F := hF
  let W : MorphismProperty (HomotopyCategory.Plus C) := HomotopyCategory.Plus.quasiIso C
  let α : F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus := F.rightDerivedFunctorPlusUnith
  let F₀ := F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh
  have hFm : Functor.Linear R F.mapHomotopyCategoryPlus := by
    apply (Functor.linear_iff (R := R) F.mapHomotopyCategoryPlus).2
    intro Z a
    apply (HomotopyCategory.Plus.ι D).map_injective
    show (F.mapHomotopyCategory (ComplexShape.up ℤ)).map
        (a • 𝟙 ((HomotopyCategory.Plus.ι C).obj Z)) =
      a • 𝟙 ((F.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.Plus.ι C).obj Z))
    exact (Functor.linear_iff (R := R) (F.mapHomotopyCategory (.up ℤ))).mp inferInstance _ a
  let : Functor.Linear R F.mapHomotopyCategoryPlus := hFm
  let : Functor.Linear R (DerivedCategory.Plus.Qh (C := C)) := derivedCategoryPlus_Qh_linear
  let : Functor.Linear R (DerivedCategory.Plus.Qh (C := D)) := derivedCategoryPlus_Qh_linear
  have hF₀ : Functor.Linear R F₀ := by
    dsimp [F₀]
    infer_instance
  let : F.rightDerivedFunctorPlus.IsRightDerivedFunctor α W := inferInstance
  exact rightDerived_linear_of_linear_unit (R := R)
    (L := DerivedCategory.Plus.Qh) (W := W) (F := F₀)
    (G := F.rightDerivedFunctorPlus) α hF₀ (by infer_instance)

/-- **The homology functors of `D(𝒜)` are `R`-linear** when `𝒜` is. -/
private theorem derivedCategory_homologyFunctor_linear
    {R : Type*} [CommRing R] {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] [Linear R C] (i : ℤ) :
    Functor.Linear R (DerivedCategory.homologyFunctor C i) := by
  let : Functor.Linear R (HomologicalComplex.shortComplexFunctor C (.up ℤ) i) :=
    { map_smul := by intros; ext <;> rfl }
  let : Functor.Linear R (HomologicalComplex.homologyFunctor C (.up ℤ) i) :=
    Functor.linear_of_iso R (HomologicalComplex.homologyFunctorIso C (.up ℤ) i).symm
  let : Localization.Lifting DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
      (HomologicalComplex.homologyFunctor C (.up ℤ) i)
      (DerivedCategory.homologyFunctor C i) :=
    ⟨DerivedCategory.homologyFunctorFactors C i⟩
  exact (Localization.functor_linear_iff DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) R
    (HomologicalComplex.homologyFunctor C (.up ℤ) i)
    (DerivedCategory.homologyFunctor C i)).mp inferInstance

/-- **The higher right derived functors `R ⁱ F` of an `R`-linear `F` are `R`-linear.** -/
private theorem rightDerivedPlus_linear_of_linear
    {R : Type u} [CommRing R]
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    [Linear R C] [Linear R D]
    (F : C ⥤ D) [F.Additive] (hF : Functor.Linear R F) (i : ℤ) :
    Functor.Linear R (F.rightDerivedPlus i) := by
  let : Functor.Linear R F := hF
  let : Functor.Linear R F.rightDerivedFunctorPlus :=
    rightDerivedFunctorPlus_linear_of_linear F hF
  let : Functor.Linear R (DerivedCategory.homologyFunctor D i) :=
    derivedCategory_homologyFunctor_linear i
  let : Functor.Linear R (DerivedCategory.Plus.homologyFunctor D i) :=
    inferInstanceAs (Functor.Linear R
      (DerivedCategory.Plus.ι ⋙ DerivedCategory.homologyFunctor D i))
  let : Functor.Linear R (DerivedCategory.Plus.singleFunctor C 0 ⋙ DerivedCategory.Plus.ι) :=
    Functor.linear_of_iso R (DerivedCategory.Plus.singleFunctorιIso C 0).symm
  let : Functor.Linear R (DerivedCategory.Plus.singleFunctor C 0) := by
    constructor
    intro Z Y φ a
    apply DerivedCategory.Plus.ι.map_injective
    exact (DerivedCategory.Plus.singleFunctor C 0 ⋙ DerivedCategory.Plus.ι).map_smul a φ
  show Functor.Linear R
    (DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor D i)
  infer_instance

/-- **The higher right derived functors `R ⁱ F` of an additive `F` are additive.** -/
private theorem rightDerivedPlus_additive
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] (p : ℤ) : (F.rightDerivedPlus p).Additive := by
  let : F.rightDerivedFunctorPlus.CommShift ℤ :=
    Functor.IsRightDerivedFunctor.commShift _ F.rightDerivedFunctorPlusUnith
      (HomotopyCategory.Plus.quasiIso C) ℤ
  let : NatTrans.CommShift F.rightDerivedFunctorPlusUnith ℤ :=
    Functor.IsRightDerivedFunctor.natTrans_commShift F.rightDerivedFunctorPlus
      F.rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso C) ℤ
  let : F.rightDerivedFunctorPlus.IsTriangulated :=
    Functor.isTriangulated_of_isRightDerivedFunctor_mapHomotopyCategoryPlus F _
      F.rightDerivedFunctorPlusUnith
  show (DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor D p).Additive
  infer_instance

variable (A : Type u) [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **The structure map `A ⟶ Γ(X, 𝒪_X)` of a scheme over `Spec A`**: the inverse of the
`Γ`–`Spec` adjunction isomorphism followed by `f` on global sections. -/
private def baseRingHom : A →+* Γ(X, ⊤) :=
  f.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom

/-- **Sheaves of `𝒪_X`-modules form an `A`-linear category** for a scheme `X` over `Spec A`:
the scalar `a : A` acts on a morphism by composing it with multiplication by the image of `a`. -/
@[instance_reducible]
private def baseLinear : Linear A X.Modules :=
  Scheme.linearOfRingHom.{u, u} X A (baseRingHom A f)

/-- **A base scalar acts on a morphism of `𝒪_X`-modules by its image in the sections.** In the
`A`-linear structure `baseLinear`, the morphism `a • g` acts on sections over `U` as
multiplication by the restriction to `U` of the image of `a` in `Γ(X, 𝒪_X)`. -/
private theorem smul_hom_app (a : A) {M N : X.Modules} (g : M ⟶ N) (U : X.Opens) (x : Γ(M, U)) :
    letI := baseLinear A f
    Scheme.Modules.Hom.app (a • g) U x =
      Stacks.Coherent.baseSectionHom A f U a • Scheme.Modules.Hom.app g U x :=
  Stacks.SheafOfModules.smul_val_app X.ringCatSheaf A ⊤ isTerminalTop (baseRingHom A f) a g (op U) x

/-- **The base scalar endomorphism acts on sections by the image of the scalar.** This is
`smul_hom_app` at `g = 𝟙`. -/
private theorem smul_id_app (a : A) (M : X.Modules) (U : X.Opens) (x : Γ(M, U)) :
    letI := baseLinear A f
    Scheme.Modules.Hom.app (a • 𝟙 M) U x = Stacks.Coherent.baseSectionHom A f U a • x :=
  Stacks.SheafOfModules.smul_val_app X.ringCatSheaf A ⊤ isTerminalTop (baseRingHom A f)
    a (𝟙 M) (op U) x

/-- **`Γ(X, 𝒪_X)`-modules form an `A`-linear category** for a scheme `X` over `Spec A`, by
restriction of scalars along the structure map. -/
@[instance_reducible]
private def baseModuleCatLinear : Linear A (ModuleCat.{u} Γ(X, ⊤)) :=
  Linear.ofRingMorphism
    ((Linear.toCatCenter Γ(X, ⊤) (ModuleCat.{u} Γ(X, ⊤))).comp (baseRingHom A f))

/-- **Global sections is an `A`-linear functor** for a scheme `X` over `Spec A`. -/
private theorem globalSections_linear :
    letI := baseLinear A f
    letI := baseModuleCatLinear A f
    Functor.Linear A (moduleGlobalSections X) := by
  let := baseLinear A f
  let := baseModuleCatLinear A f
  apply (Functor.linear_iff (R := A) (moduleGlobalSections X)).2
  intro M a
  apply ModuleCat.hom_ext
  ext x
  exact Scheme.smul_val_app_top.{u, u} X A (baseRingHom A f) a (𝟙 M) x

/-- A base scalar acts on a morphism of `Γ(X, 𝒪_X)`-modules through its image in
`Γ(X, 𝒪_X)`. -/
private theorem smul_moduleCat_hom (a : A) {M N : ModuleCat.{u} Γ(X, ⊤)} (g : M ⟶ N) (z : M) :
    letI := baseModuleCatLinear A f
    (a • g).hom z = baseRingHom A f a • g.hom z := by
  let := baseModuleCatLinear A f
  show g.hom (baseRingHom A f a • z) = _
  exact g.hom.map_smul _ z

/-- **`H^p(X, -)` carries the base scalar endomorphism to multiplication by its image.** For
`a : A`, the image under `R ᵖ Γ(X, -)` of the endomorphism `a • 𝟙` of an `𝒪_X`-module is
multiplication by the image of `a` in `Γ(X, 𝒪_X)`. -/
private theorem rightDerivedPlus_map_smul_id (p : ℤ) (M : X.Modules) (a : A) :
    letI := baseLinear A f
    ((moduleGlobalSections X).rightDerivedPlus p).map (a • 𝟙 M) =
      ModuleCat.ofHom (baseRingHom A f a • LinearMap.id) := by
  let := baseLinear A f
  let := baseModuleCatLinear A f
  rw [(Functor.linear_iff (R := A) ((moduleGlobalSections X).rightDerivedPlus p)).mp
    (rightDerivedPlus_linear_of_linear (moduleGlobalSections X) (globalSections_linear A f) p) M a]
  rfl

/-- **`I ^ (n+1)` annihilates the `n`-th term of an adic inverse system.** For `a ∈ I ^ (n+1)`
the endomorphism `a • 𝟙` of `F_n` is zero. -/
private theorem smul_id_system_eq_zero (I : Ideal A)
    (S : AdicInverseSystem.{u}) (fX : S.X ⟶ Spec (.of A))
    (hSI : S.I = baseIdealSheaf A I fX)
    (n : ℕ) (a : A) (ha : a ∈ I ^ (n + 1)) :
    letI := baseLinear A fX
    (a • 𝟙 (S.system.obj (op n)) : S.system.obj (op n) ⟶ S.system.obj (op n)) = 0 := by
  let := baseLinear A fX
  ext U x
  have key : ∀ (V : S.X.affineOpens) (i : V.1 ⟶ U),
      (S.system.obj (op n)).val.map i.op
          (Scheme.Modules.Hom.app (a • 𝟙 (S.system.obj (op n))) U x) ∈
        (⊥ : (S.system.obj (op n)).Submodule).toSubmodule.obj (op V.1) := by
    intro V i
    have hmem : baseSectionHom A fX V.1 a ∈ (S.I.ideal V) ^ (n + 1) := by
      rw [hSI, baseIdealSheaf_ideal_pow_eq_map]
      exact Ideal.mem_map_of_mem _ ha
    have hres := Stacks.Coherent.app_presheaf_map (a • 𝟙 (S.system.obj (op n)))
      (leOfHom i) x
    rw [smul_id_app A fX a _ V.1 _] at hres
    have hzero : (S.system.obj (op n)).val.map i.op
        (Scheme.Modules.Hom.app (a • 𝟙 (S.system.obj (op n))) U x) = 0 :=
      hres.symm.trans ((Submodule.mem_bot _).1
        ((S.pow_smul_sections_eq_bot V n) ▸
          Submodule.smul_mem_smul hmem (Submodule.mem_top)))
    exact (SheafOfModules.Submodule.bot_obj _ (op V.1)).ge
      ((Submodule.mem_bot _).2 hzero)
  have hx := mem_submodule_of_affine (⊥ : (S.system.obj (op n)).Submodule) U _ key
  have hx' : Scheme.Modules.Hom.app (a • 𝟙 (S.system.obj (op n))) U x ∈
      (⊥ : Submodule Γ(S.X, U) Γ(S.system.obj (op n), U)) :=
    (SheafOfModules.Submodule.bot_obj _ (op U)).le hx
  simpa using (Submodule.mem_bot _).1 hx'

/-- **The Milnor surjection in a non-negative degree.** For `p : ℕ` the comparison map
`H^p(X, lim F_n) ⟶ lim_n H^p(X, F_n)` of [Stacks, Tag 0EI8] is surjective in the `ℤ`-indexed
model. -/
private theorem surjective_limitComparison_rightDerivedPlus
    (S : AdicInverseSystem.{u}) (p : ℕ) :
    Function.Surjective
      (AdicInverseSystem.limitComparison S
        ((moduleGlobalSections S.X).rightDerivedPlus (p : ℤ))).hom := by
  have hsurj := AdicInverseSystem.surjective_limitComparison_moduleCohomologyFunctor S p
  have hepi : Epi (AdicInverseSystem.limitComparison S
      (AdicInverseSystem.moduleCohomologyFunctor S.X p)) := by
    rw [ModuleCat.epi_iff_surjective]
    exact hsurj
  have h := AdicInverseSystem.epi_limitComparison_of_natIso S
    (Stacks.DerivedIndexing.rightDerivedIso (moduleGlobalSections S.X) p) hepi
  rw [← LinearMap.range_eq_top]
  exact ModuleCat.range_eq_top_of_epi _

/-- **The negative right derived functors vanish.** For `p < 0` the object `R ᵖ F(Y)` is zero. -/
private theorem isZero_rightDerivedPlus_obj_of_neg
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] {p : ℤ} (hp : p < 0) (Y : C) :
    IsZero ((F.rightDerivedPlus p).obj Y) :=
  ((Functor.isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits
    F F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnith).1 p hp).obj Y

/-- **The higher right derived functors are exact in the middle.** For a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` the sequence `R ᵖ F(X₁) ⟶ R ᵖ F(X₂) ⟶ R ᵖ F(X₃)` is exact, for every
integer `p`. -/
private theorem rightDerivedPlus_exact_middle
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] {T : ShortComplex C} (hT : T.ShortExact) (p : ℤ) :
    ∃ hz : (F.rightDerivedPlus p).map T.f ≫ (F.rightDerivedPlus p).map T.g = 0,
      (ShortComplex.mk ((F.rightDerivedPlus p).map T.f)
        ((F.rightDerivedPlus p).map T.g) hz).Exact := by
  by_cases hp : 0 ≤ p
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    exact (Stacks.Cohomology.CechDelta.rightDerivedPlus_deltaAxioms F).2.2.1 hT n
  · have h₂ := isZero_rightDerivedPlus_obj_of_neg F (lt_of_not_ge hp) T.X₂
    refine ⟨?_, ShortComplex.exact_of_isZero_X₂ _ h₂⟩
    rw [h₂.eq_of_src ((F.rightDerivedPlus p).map T.g) 0, comp_zero]

/-- **The Milnor surjection in every integer degree.** For `p : ℤ` the comparison map
`H^p(X, lim F_n) ⟶ lim_n H^p(X, F_n)` is surjective. -/
private theorem surjective_limitComparison_rightDerivedPlus_int
    (S : AdicInverseSystem.{u}) (p : ℤ) :
    Function.Surjective
      (AdicInverseSystem.limitComparison S
        ((moduleGlobalSections S.X).rightDerivedPlus p)).hom := by
  by_cases hp : 0 ≤ p
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    exact surjective_limitComparison_rightDerivedPlus S n
  · have hzero := isZero_rightDerivedPlus_obj_of_neg (moduleGlobalSections S.X) (lt_of_not_ge hp)
    have hlim : IsZero (AdicInverseSystem.cohomologyLimit S
        ((moduleGlobalSections S.X).rightDerivedPlus p)) := by
      rw [IsZero.iff_id_eq_zero]
      refine limit.hom_ext fun n => ?_
      rw [Category.id_comp, zero_comp]
      exact (hzero _).eq_of_tgt _ _
    intro y
    refine ⟨0, ?_⟩
    have hid : (𝟙 (AdicInverseSystem.cohomologyLimit S
        ((moduleGlobalSections S.X).rightDerivedPlus p)) : _ ⟶ _) = 0 :=
      hlim.eq_of_src _ _
    have hy : y = 0 := by
      simpa using congrArg (fun g : AdicInverseSystem.cohomologyLimit S
        ((moduleGlobalSections S.X).rightDerivedPlus p) ⟶ _ => g.hom y) hid
    rw [hy, map_zero]

/-- **Cohomology as a functor into `Γ(X, 𝒪_X)`-modules, in an integer degree.** This is
`R ᵖ Γ(X, -)` for `p : ℤ`, the `p`-th right derived functor of global sections taken in
`Γ(X, 𝒪_X)`-modules on the bounded below derived category. -/
public abbrev moduleCohomologyFunctorInt (X : Scheme.{u}) (p : ℤ) :
    X.Modules ⥤ ModuleCat.{u} Γ(X, ⊤) :=
  (moduleGlobalSections X).rightDerivedPlus p

/-- **A finite sum of morphisms of `𝒪_X`-modules acts on sections by the sum of the actions.**
This is the additivity of `AlgebraicGeometry.Scheme.Modules.Hom.app` over a `Finset`. -/
private theorem app_sum {Y : Scheme.{u}} {M N : Y.Modules} {ι : Type*} (s : Finset ι)
    (q : ι → (M ⟶ N)) (U : Y.Opens) (t : Γ(M, U)) :
    Scheme.Modules.Hom.app (∑ i ∈ s, q i) U t =
      ∑ i ∈ s, Scheme.Modules.Hom.app (q i) U t := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih,
      Scheme.Modules.Hom.add_app]
    rfl

/-- **A monomorphism and a cokernel of it form a short exact sequence.** If `g` is a
monomorphism and `e` identifies its cokernel with `D`, then `0 ⟶ M ⟶ N ⟶ D ⟶ 0` is short
exact. -/
private theorem shortExact_of_cokernelIso
    {C : Type*} [Category C] [Abelian C]
    {M N D : C} {g : M ⟶ N} [Mono g] (e : cokernel g ≅ D) :
    (ShortComplex.mk g (cokernel.π g ≫ e.hom) (by simp)).ShortExact := by
  have hdesc : cokernel.desc g (cokernel.π g ≫ e.hom) (by simp) = e.hom := by
    apply (cancel_epi (cokernel.π g)).1
    simp
  have hmono : Mono (cokernel.desc g (cokernel.π g ≫ e.hom) (by simp)) := by
    rw [hdesc]
    infer_instance
  exact ShortComplex.ShortExact.mk'
    ((ShortComplex.mk g (cokernel.π g ≫ e.hom) (by simp)).exact_iff_mono_cokernel_desc.mpr hmono)
    inferInstance inferInstance

/-- **An adic inverse system of coherent modules along `I · 𝒪_X` is a coherent adic system.** -/
private theorem isCoherentAdicSystem_of_adicInverseSystem (I : Ideal A)
    (S : AdicInverseSystem.{u}) (fX : S.X ⟶ Spec (.of A))
    (hSI : S.I = baseIdealSheaf A I fX)
    (hcoh : ∀ n : ℕ, _root_.SheafOfModules.IsCoherent.{u} (S.system.obj (op n))) :
    IsCoherentAdicSystem (baseIdealSheaf A I fX) S.system := by
  rw [← hSI]
  exact ⟨hcoh, fun n => S.idealPowerMultiple_eq_bot n,
    fun n => ⟨S.quotientIso n, S.quotientIso_hom_comp n⟩⟩

/-- **`I · 𝒪_X` is of finite type** when `I` is an ideal of a Noetherian ring. -/
private theorem isFiniteType_of_baseIdealSheaf [IsNoetherianRing A] (I : Ideal A)
    (S : AdicInverseSystem.{u}) (fX : S.X ⟶ Spec (.of A))
    (hSI : S.I = baseIdealSheaf A I fX) :
    Scheme.IdealSheafData.IsFiniteType S.I := by
  intro U
  rw [hSI, baseIdealSheaf_ideal_eq_map]
  exact Ideal.FG.map (IsNoetherian.noetherian I) _

/-- **`I ^ (n+1)` annihilates `H^p(X, F_n)`.** For `a ∈ I ^ (n+1)`, multiplication by the image
of `a` in `Γ(X, 𝒪_X)` is zero on `H^p(X, F_n)`. -/
private theorem smul_cohomology_eq_zero (I : Ideal A)
    (S : AdicInverseSystem.{u}) (fX : S.X ⟶ Spec (.of A))
    (hSI : S.I = baseIdealSheaf A I fX) (p : ℤ) (n : ℕ) (a : A) (ha : a ∈ I ^ (n + 1))
    (x : ((moduleGlobalSections S.X).rightDerivedPlus p).obj (S.system.obj (op n))) :
    baseRingHom A fX a • x = 0 := by
  let := baseLinear A fX
  let : ((moduleGlobalSections S.X).rightDerivedPlus p).Additive :=
    rightDerivedPlus_additive (moduleGlobalSections S.X) p
  have h0 : ((moduleGlobalSections S.X).rightDerivedPlus p).map
      (a • 𝟙 (S.system.obj (op n))) = 0 := by
    rw [smul_id_system_eq_zero A I S fX hSI n a ha]
    exact Functor.map_zero _ _ _
  rw [rightDerivedPlus_map_smul_id A fX p (S.system.obj (op n)) a] at h0
  exact congrArg (fun g : ((moduleGlobalSections S.X).rightDerivedPlus p).obj
    (S.system.obj (op n)) ⟶ ((moduleGlobalSections S.X).rightDerivedPlus p).obj
      (S.system.obj (op n)) => g.hom x) h0

/-- **Exactness of `H^p(X, -)` in the middle of `0 ⟶ I^(m+1) F ⟶ F ⟶ F_m ⟶ 0`.** The kernel of
`H^p(X, lim F_n) ⟶ H^p(X, F_m)` is contained in the image of
`H^p(X, I^(m+1) lim F_n) ⟶ H^p(X, lim F_n)`. -/
private theorem ker_map_limitProjection_le (I : Ideal A)
    (S : AdicInverseSystem.{u}) (fX : S.X ⟶ Spec (.of A))
    (hSI : S.I = baseIdealSheaf A I fX)
    (hIft : Scheme.IdealSheafData.IsFiniteType S.I) (p : ℤ) (m : ℕ) :
    LinearMap.ker (((moduleGlobalSections S.X).rightDerivedPlus p).map
        (limit.π S.system (op m))).hom ≤
      LinearMap.range (((moduleGlobalSections S.X).rightDerivedPlus p).map
        (AlgebraicGeometry.SheafOfModules.Submodule.ιModules
          (idealPowerMultiple (baseIdealSheaf A I fX) (m + 1) S.limitModule))).hom := by
  have hq : ∃ e : cokernel (AlgebraicGeometry.SheafOfModules.Submodule.ιModules
        (idealPowerMultiple (baseIdealSheaf A I fX) (m + 1) S.limitModule)) ≅
      S.system.obj (op m),
      cokernel.π (AlgebraicGeometry.SheafOfModules.Submodule.ιModules
          (idealPowerMultiple (baseIdealSheaf A I fX) (m + 1) S.limitModule)) ≫
          e.hom = limit.π S.system (op m) := by
    rw [← hSI]
    exact S.exists_idealPowerQuotientIso hIft m
  obtain ⟨e, he⟩ := hq
  have hse := shortExact_of_cokernelIso (C := S.X.Modules)
    (g := AlgebraicGeometry.SheafOfModules.Submodule.ιModules
      (idealPowerMultiple (baseIdealSheaf A I fX) (m + 1) S.limitModule)) e
  obtain ⟨_hz, hex⟩ := rightDerivedPlus_exact_middle (moduleGlobalSections S.X) hse p
  intro x hx
  rw [hex.moduleCat_range_eq_ker]
  show x ∈ LinearMap.ker (((moduleGlobalSections S.X).rightDerivedPlus p).map
    (cokernel.π _ ≫ e.hom)).hom
  rw [he]
  exact hx

/-- **The graded splitting, as an identity of morphisms of `𝒪_X`-modules.** The weighted sum
`∑_{|σ| = k} f^σ · Ψ_σ` of the components of the graded map of [Stacks, Tag 0EH6] is the
inclusion `I ^ (k d) F ⟶ F`. -/
private theorem sum_smul_gradedSplittingComponentAt (I : Ideal A) {r : ℕ} (gen : Fin r → A)
    (hgenmem : ∀ j, gen j ∈ I) {F : X.Modules} {d : ℕ}
    {ψ : Fin r → (I ^ d : Ideal A) →ₗ[A] A}
    (hψ : ∀ x : (I ^ d : Ideal A), (∑ j, gen j * ψ j x) = (x : A))
    {Ψ : GradedSplittingComponents A I f F r d}
    (hΨ : IsGradedSplitting A I f F d ψ Ψ) (k : ℕ) :
    letI := baseLinear A f
    (∑ σ ∈ (degreeMonomials r k).attach,
        (∏ j, gen j ^ (σ.1 : Fin r →₀ ℕ) j) •
          gradedSplittingComponentAt Ψ (mem_degreeMonomials.1 σ.2)) =
      ιModules (idealPowerMultiple (baseIdealSheaf A I f) (k * d) F) := by
  let := baseLinear A f
  let : Preadditive X.Modules := inferInstance
  ext U t
  rw [app_sum]
  simp only [smul_hom_app A f]
  exact sum_pow_smul_gradedSplitting gen hgenmem hψ hΨ k U t

/-- **The graded splitting, transported through `H^p(X, -)`.** The map
`H^p(X, I ^ (k d) F) ⟶ H^p(X, F)` is the sum, over the monomials `f^σ` of degree `k` in the
generators, of the maps induced by the components `Ψ_σ` multiplied by the image of `f^σ`. -/
private theorem map_ι_eq_sum_smul (I : Ideal A) {r : ℕ} (gen : Fin r → A)
    (hgenmem : ∀ j, gen j ∈ I) {F : X.Modules} {d : ℕ}
    {ψ : Fin r → (I ^ d : Ideal A) →ₗ[A] A}
    (hψ : ∀ x : (I ^ d : Ideal A), (∑ j, gen j * ψ j x) = (x : A))
    {Ψ : GradedSplittingComponents A I f F r d}
    (hΨ : IsGradedSplitting A I f F d ψ Ψ) (p : ℤ) (k : ℕ)
    (z : ((moduleGlobalSections X).rightDerivedPlus p).obj
      (asModules (idealPowerMultiple (baseIdealSheaf A I f) (k * d) F))) :
    (((moduleGlobalSections X).rightDerivedPlus p).map
        (ιModules (idealPowerMultiple (baseIdealSheaf A I f) (k * d) F))).hom z =
      ∑ σ ∈ (degreeMonomials r k).attach,
        baseRingHom A f (∏ j, gen j ^ (σ.1 : Fin r →₀ ℕ) j) •
          (((moduleGlobalSections X).rightDerivedPlus p).map
            (gradedSplittingComponentAt Ψ (mem_degreeMonomials.1 σ.2))).hom z := by
  let := baseLinear A f
  let := baseModuleCatLinear A f
  let : Preadditive X.Modules := inferInstance
  let : ((moduleGlobalSections X).rightDerivedPlus p).Additive :=
    rightDerivedPlus_additive (moduleGlobalSections X) p
  let : Functor.Linear A ((moduleGlobalSections X).rightDerivedPlus p) :=
    rightDerivedPlus_linear_of_linear (moduleGlobalSections X) (globalSections_linear A f) p
  rw [← sum_smul_gradedSplittingComponentAt A f I gen hgenmem hψ hΨ k,
    Functor.map_sum, ModuleCat.hom_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun σ _ => by
    rw [Functor.map_smul]
    exact smul_moduleCat_hom A f _ _ z

/-- **A monomial of degree `n` in the generators of `I` lands in `J ^ n`**, where `J` is the
ideal of `Γ(X, 𝒪_X)` generated by the image of `I`. -/
private theorem baseRingHom_monomial_mem (I : Ideal A) {r : ℕ} (gen : Fin r → A)
    (hgenmem : ∀ j, gen j ∈ I) (n : ℕ) (σ : {x // x ∈ degreeMonomials r n}) :
    baseRingHom A f (∏ j, gen j ^ (σ.1 : Fin r →₀ ℕ) j) ∈ (I.map (baseRingHom A f)) ^ n := by
  rw [show (I.map (baseRingHom A f)) ^ n = (I ^ n).map (baseRingHom A f) from
    (Ideal.map_pow (baseRingHom A f) I n).symm]
  refine Ideal.mem_map_of_mem _ ?_
  have hprod : (∏ j, gen j ^ (σ.1 : Fin r →₀ ℕ) j) ∈ ∏ j, I ^ (σ.1 : Fin r →₀ ℕ) j :=
    Ideal.prod_mem_prod fun j _ => Ideal.pow_mem_pow (hgenmem j) _
  simpa only [Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_eq_sum,
    mem_degreeMonomials.1 σ.2] using hprod

/-- **The easy half of the comparison of the two topologies**: `J ^ (n+1)` kills
`lim_m H^p(X, F_m)` modulo the kernel of the `n`-th projection, where `J` is the ideal of
`Γ(X, 𝒪_X)` generated by `I`. -/
private theorem pow_smul_top_le_ker (I : Ideal A)
    (S : AdicInverseSystem.{u}) (fX : S.X ⟶ Spec (.of A))
    (hSI : S.I = baseIdealSheaf A I fX) (p : ℤ) (n : ℕ) :
    (I.map (baseRingHom A fX)) ^ (n + 1) •
        (⊤ : Submodule Γ(S.X, ⊤) (AdicInverseSystem.cohomologyLimit S
          ((moduleGlobalSections S.X).rightDerivedPlus p))) ≤
      LinearMap.ker (limit.π (AdicInverseSystem.cohomologySystem S
        ((moduleGlobalSections S.X).rightDerivedPlus p)) (op n)).hom := by
  have hle : ((I ^ (n + 1)).map (baseRingHom A fX)) ≤ Module.annihilator Γ(S.X, ⊤)
      ((AdicInverseSystem.cohomologySystem S
        ((moduleGlobalSections S.X).rightDerivedPlus p)).obj (op n)) := by
    rw [Ideal.map_le_iff_le_comap]
    exact fun a ha => Module.mem_annihilator.mpr fun y =>
      smul_cohomology_eq_zero A I S fX hSI p n a ha y
  rw [show (I.map (baseRingHom A fX)) ^ (n + 1) = (I ^ (n + 1)).map (baseRingHom A fX) from
    (Ideal.map_pow (baseRingHom A fX) I (n + 1)).symm]
  refine Submodule.smul_le.mpr fun a ha x _ => LinearMap.mem_ker.mpr ?_
  rw [map_smul]
  exact Module.mem_annihilator.mp (hle ha) _

/-- **The substantial half of the comparison of the two topologies**: for every `k` the kernel
of some projection out of `lim_n H^p(X, F_n)` is contained in `J ^ k` times the whole module. -/
private theorem exists_ker_le_pow_smul_top (I : Ideal A) {r : ℕ} (gen : Fin r → A)
    (hgenmem : ∀ j, gen j ∈ I)
    (S : AdicInverseSystem.{u}) (fX : S.X ⟶ Spec (.of A))
    (hSI : S.I = baseIdealSheaf A I fX)
    (hIft : Scheme.IdealSheafData.IsFiniteType S.I)
    {d : ℕ} (hd : 1 ≤ d) {ψ : Fin r → (I ^ d : Ideal A) →ₗ[A] A}
    (hψ : ∀ x : (I ^ d : Ideal A), (∑ j, gen j * ψ j x) = (x : A))
    {Ψ : GradedSplittingComponents A I fX S.limitModule r d}
    (hΨ : IsGradedSplitting A I fX S.limitModule d ψ Ψ) (p : ℤ) (k : ℕ) :
    ∃ n : ℕ, LinearMap.ker (limit.π (AdicInverseSystem.cohomologySystem S
        ((moduleGlobalSections S.X).rightDerivedPlus p)) (op n)).hom ≤
      (I.map (baseRingHom A fX)) ^ k •
        (⊤ : Submodule Γ(S.X, ⊤) (AdicInverseSystem.cohomologyLimit S
          ((moduleGlobalSections S.X).rightDerivedPlus p))) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · exact ⟨0, by simp [hk]⟩
  have hkd : 1 ≤ k * d := by simpa using Nat.mul_le_mul hk hd
  have hmd : k * d - 1 + 1 = k * d := Nat.sub_add_cancel hkd
  refine ⟨k * d - 1, ?_⟩
  refine AdicInverseSystem.ker_le_pow_smul_of_surjective (I.map (baseRingHom A fX)) k
    (AdicInverseSystem.limitComparison S
      ((moduleGlobalSections S.X).rightDerivedPlus p)).hom
    (surjective_limitComparison_rightDerivedPlus_int S p)
    (limit.π (AdicInverseSystem.cohomologySystem S
      ((moduleGlobalSections S.X).rightDerivedPlus p)) (op (k * d - 1))).hom
    (((moduleGlobalSections S.X).rightDerivedPlus p).map
      (limit.π S.system (op (k * d - 1)))).hom
    (AdicInverseSystem.limitComparison_π_apply S
      ((moduleGlobalSections S.X).rightDerivedPlus p) (op (k * d - 1))) ?_
  intro w hw
  have hrange : w ∈ LinearMap.range
      (((moduleGlobalSections S.X).rightDerivedPlus p).map
        (ιModules (idealPowerMultiple (baseIdealSheaf A I fX) (k * d) S.limitModule))).hom := by
    have h := ker_map_limitProjection_le A I S fX hSI hIft p (k * d - 1) hw
    rwa [hmd] at h
  obtain ⟨z, rfl⟩ := hrange
  rw [map_ι_eq_sum_smul A fX I gen hgenmem hψ hΨ p k z]
  exact Submodule.sum_mem _ fun σ _ =>
    Submodule.smul_mem_smul (baseRingHom_monomial_mem A fX I gen hgenmem k σ) Submodule.mem_top

/-- **Stacks Project, Tag 0EH7.** Let `I` be an ideal of a Noetherian ring `A`, let `X` be a
Noetherian scheme over `Spec A` and let `… ⟶ F_3 ⟶ F_2 ⟶ F_1` be an inverse system of coherent
`𝒪_X`-modules with `F_n = F_{n+1} / I ^ n F_{n+1}`. If `cd(A, I) = 1` then for every `p ∈ ℤ` the
limit topology on `lim_n H^p(X, F_n)` — the infimum of the topologies induced from the discrete
modules `H^p(X, F_n)` — is the `I`-adic topology.

Cohomology is `moduleCohomologyFunctorInt X p`, the `p`-th right derived functor of global
sections taken in `Γ(X, 𝒪_X)`-modules, so that `lim_n H^p(X, F_n)` carries the module structure
the `I`-adic topology needs, and `I` acts through the ideal of `Γ(X, 𝒪_X)` generated by its
image. The system is zero-indexed, so its object at `n` is the source's `F_{n+1}` and the
source's exponent `n` appears as `n + 1`; quasi-coherence of the terms is a field of
`Stacks.Algebraization.AdicInverseSystem` rather than a hypothesis here, and it follows from the
coherence `hcoh` the source assumes. -/
@[stacks 0EH7]
public theorem limitIntCohomologyTopology_eq_adicModuleTopology [IsNoetherianRing A] (I : Ideal A)
    (S : AdicInverseSystem.{u}) [AlgebraicGeometry.IsNoetherian S.X]
    (fX : S.X ⟶ Spec (.of A))
    (hSI : S.I = baseIdealSheaf A I fX)
    (hcoh : ∀ n : ℕ, _root_.SheafOfModules.IsCoherent.{u} (S.system.obj (op n)))
    (hcd : Stacks.LocalCohomology.cohomologicalDimension A I (IsNoetherian.noetherian I) = 1)
    (p : ℤ) :
    (⨅ n : ℕ, TopologicalSpace.induced
        (fun x : AdicInverseSystem.cohomologyLimit S (moduleCohomologyFunctorInt S.X p) =>
          (limit.π (AdicInverseSystem.cohomologySystem S
            (moduleCohomologyFunctorInt S.X p)) (op n)).hom x) ⊥) =
      (I.map (fX.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom)).adicModuleTopology
        (AdicInverseSystem.cohomologyLimit S (moduleCohomologyFunctorInt S.X p)) := by
  obtain ⟨r, gen, hgen⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  have hgen' : I = Ideal.span (Set.range gen) := hgen.symm
  have hgenmem : ∀ j, gen j ∈ I := fun j => hgen' ▸ Ideal.subset_span ⟨j, rfl⟩
  obtain ⟨c, hc, φ, hφ⟩ :=
    Stacks.LocalCohomology.exists_pow_linearMaps_sum_eq_self A I gen hgen' hcd
  obtain ⟨d, hcd', ψ, -, hψsum, Ψ, ⟨hΨ1, -⟩, -⟩ :=
    existsUnique_gradedSplitting A I gen hgen' hcd hc φ hφ fX S.system
      (isCoherentAdicSystem_of_adicInverseSystem A I S fX hSI hcoh)
  exact Stacks.AdicLimit.iInf_induced_eq_adicModuleTopology (I.map (baseRingHom A fX))
    (fun n => (limit.π (AdicInverseSystem.cohomologySystem S
      ((moduleGlobalSections S.X).rightDerivedPlus p)) (op n)).hom)
    (fun i j hij => AdicInverseSystem.ker_limitProjection_antitone
      (AdicInverseSystem.cohomologySystem S
        ((moduleGlobalSections S.X).rightDerivedPlus p)) hij)
    (fun n => ⟨n + 1, pow_smul_top_le_ker A I S fX hSI p n⟩)
    (fun k => exists_ker_le_pow_smul_top A I gen hgenmem S fX hSI
      (isFiniteType_of_baseIdealSheaf A I S fX hSI) (hc.trans hcd') hψsum hΨ1 p k)

end Stacks.Algebraization.AdicInverseSystem

end

end
