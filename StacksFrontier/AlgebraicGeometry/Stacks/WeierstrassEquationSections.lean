module

public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Perfect.CohomologyAndBaseChangeVanishing
public import StacksFrontier.AlgebraicGeometry.SheafRankOne.Basic
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliEllipticCurvesZeroSections
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassEquationFieldSections
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassMonomials
public import StacksFrontier.RingTheory.TensorProduct.IsBaseChangeDet

/-!
# A Weierstrass equation from sections of the powers of `O(0)`

Let `E` be a proper pointed family over `Spec A`, `A` Noetherian, smooth of relative dimension
one, whose fibre at a prime `p` is a curve of genus one with `H⁰ = κ(p)`, and let `O(0)` be the
invertible sheaf of the zero section, with canonical section `s`. By cohomology and base change the
sections of `O(0)^{⊗ n}` commute with base change near `p` and are free; sections `x`, `y` of
`O(0)^{⊗ 2}`, `O(0)^{⊗ 3}` with poles of exact orders `2` and `3` on the fibre make the monomials
`s⁶, s⁴x, s³y, s²x², sxy, x³` a basis of the sections of `O(0)^{⊗ 6}` near `p`, and the expansion
of `y²` in this basis is, after rescaling, a Weierstrass equation.

## Main results

* `PointedFamily.exists_isBaseChange_restrictSection_of_isUnit`:
  cohomology and base change for the powers of `O(0)`.
* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.exists_weierstrassEquation_of_expansion`:
  the Weierstrass equation from an expansion of `y²` with a unit coefficient of `x³`.
* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.exists_weierstrassEquation_sections`:
  a Weierstrass equation in sections of `O(0)^{⊗ 2}`, `O(0)^{⊗ 3}` over every base change
  inverting some `h ∉ p`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Divisors
open Stacks.TensorPowers (natTensorPow)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullSection pullbackNatTensorPowIso)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (mulSections)
open Stacks.Cech (sectionsModule baseRingHom)

universe u

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

namespace AlgebraicGeometry.ModuliEllipticCurves.PointedFamily

/-- An isomorphism of modules on a scheme over `Spec B`, read on sections over an open as a
`B`-linear equivalence for the module structures through the structure morphism. -/
def sectionsBaseLinearEquiv {B : Type u} [CommRing B] {X : Scheme.{u}} (f : X ⟶ Spec (.of B))
    {M N : X.Modules} (e : M ≅ N) (V : X.Opens) :
    letI := sectionsModule f M V
    letI := sectionsModule f N V
    Γ(M, V) ≃ₗ[B] Γ(N, V) :=
  letI := sectionsModule f M V
  letI := sectionsModule f N V
  { toFun a := Scheme.Modules.Hom.app e.hom V a
    invFun a := Scheme.Modules.Hom.app e.inv V a
    map_add' a b := map_add _ a b
    map_smul' r a := Scheme.Modules.Hom.app_smul e.hom ((baseRingHom f V).hom r) a
    left_inv := (sectionsLinearEquivOfIso e V).left_inv
    right_inv := (sectionsLinearEquivOfIso e V).right_inv }

/-- Restriction along an equality of opens, as a `B`-linear equivalence of sections for the
module structures through a structure morphism to `Spec B`. -/
def sectionsBaseRestrictEquiv {B : Type u} [CommRing B] {X : Scheme.{u}} (f : X ⟶ Spec (.of B))
    (M : X.Modules) {V W : X.Opens} (h : V = W) :
    letI := sectionsModule f M V
    letI := sectionsModule f M W
    Γ(M, V) ≃ₗ[B] Γ(M, W) :=
  letI := sectionsModule f M V
  letI := sectionsModule f M W
  { toFun a := M.presheaf.map (eqToHom h.symm).op a
    invFun a := M.presheaf.map (eqToHom h).op a
    map_add' a b := map_add _ a b
    map_smul' r a := by
      change M.presheaf.map (eqToHom h.symm).op ((baseRingHom f V).hom r • a) =
        (baseRingHom f W).hom r • M.presheaf.map (eqToHom h.symm).op a
      rw [Scheme.Modules.map_smul, Stacks.Cech.map_baseRingHom_apply]
    left_inv a := by
      subst h
      simp only [eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
      rfl
    right_inv a := by
      subst h
      simp only [eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
      rfl }

variable {A B : Type u} [CommRing A] [CommRing B] (E : PointedFamily (Spec (.of A)))
  [IsSeparated E.map] [SmoothOfRelativeDimension 1 E.map] (φ : A →+* B)

/-- The base change of `E` along `Spec B ⟶ Spec A`. -/
abbrev baseChange : PointedFamily (Spec (.of B)) :=
  E.pullback (Spec.map (CommRingCat.ofHom φ))

/-- The identification of the pullback of a power of `O(0)` with the power of `O(0)` of the
base-changed family, through which `restrictSection` is read. -/
def powPullbackIso (n : ℕ) :
    (Scheme.Modules.pullback (Limits.pullback.fst E.map (Spec.map (CommRingCat.ofHom φ)))).obj
        (natTensorPow E.zeroSheaf n) ≅ natTensorPow (E.baseChange φ).zeroSheaf n :=
  (pullbackNatTensorPowIso _ E.zeroSheaf n).symm ≪≫
    Stacks.AmplePullbackPart1.natTensorPowCongr (E.zeroSheafPullbackIso _) n

/-- The restriction of a section `x` of `O(0)^{⊗ n}` to the base change along `φ` is the pullback
of `x`, read through `powPullbackIso`. -/
theorem restrictSection_eq (n : ℕ) (x : Γ(natTensorPow E.zeroSheaf n, ⊤)) :
    E.restrictSection (Spec.map (CommRingCat.ofHom φ)) n x =
      Scheme.Modules.Hom.app (E.powPullbackIso φ n).hom ⊤
        (pullbackSectionHom (Limits.pullback.fst E.map (Spec.map (CommRingCat.ofHom φ)))
          (natTensorPow E.zeroSheaf n) ⊤ ⊤
          (Stacks.AlgebraicGeometry.ProjChartRatioPullback.top_le_preimage_top _) x) :=
  rfl


/-- The sections of the pullback of `O(0)^{⊗ n}` over the preimage of `⊤`, identified
`B`-linearly with the sections of `O(0)^{⊗ n}` of the base-changed family. -/
def sectionsEquiv (n : ℕ) :
    letI := sectionsModule (E.baseChange φ).map
      ((Scheme.Modules.pullback (Limits.pullback.fst E.map (Spec.map (CommRingCat.ofHom φ)))).obj
        (natTensorPow E.zeroSheaf n))
      ((Limits.pullback.fst E.map (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ ⊤)
    letI := sectionsModule (E.baseChange φ).map (natTensorPow (E.baseChange φ).zeroSheaf n) ⊤
    Γ((Scheme.Modules.pullback (Limits.pullback.fst E.map (Spec.map (CommRingCat.ofHom φ)))).obj
        (natTensorPow E.zeroSheaf n),
      (Limits.pullback.fst E.map (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ ⊤) ≃ₗ[B]
      Γ(natTensorPow (E.baseChange φ).zeroSheaf n, ⊤) :=
  (sectionsBaseRestrictEquiv (E.baseChange φ).map _ (Scheme.Hom.preimage_top _)).trans
    (sectionsBaseLinearEquiv (E.baseChange φ).map (E.powPullbackIso φ n) ⊤)

/-- **The restriction of sections to a base change, as a base change of modules.** Given that the
canonical pullback of sections of `O(0)^{⊗ n}` to `E ×_{Spec A} Spec B` exhibits its sections as
the base change of those of `E` (which is what cohomology and base change provides), the
restriction `restrictSection` is an `A`-linear map exhibiting the same base change. -/
theorem exists_isBaseChange_restrictSection (n : ℕ)
    (hbc :
      letI : Algebra A B := φ.toAlgebra
      letI := sectionsModule E.map (natTensorPow E.zeroSheaf n) ⊤
      letI := sectionsModule (E.baseChange φ).map
        ((Scheme.Modules.pullback (Limits.pullback.fst E.map (Spec.map (CommRingCat.ofHom φ)))).obj
          (natTensorPow E.zeroSheaf n))
        ((Limits.pullback.fst E.map (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ ⊤)
      letI := Stacks.Cech.baseSectionsModule (Limits.pullback.fst E.map
        (Spec.map (CommRingCat.ofHom φ))) (natTensorPow E.zeroSheaf n) φ (E.baseChange φ).map
        ((Limits.pullback.fst E.map (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ ⊤)
      letI := Stacks.Cech.isScalarTowerBaseSections (Limits.pullback.fst E.map
        (Spec.map (CommRingCat.ofHom φ))) (natTensorPow E.zeroSheaf n) φ (E.baseChange φ).map
        ((Limits.pullback.fst E.map (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ ⊤)
      IsBaseChange B (Stacks.Cech.pullbackSectionsBaseₗ
        (Limits.pullback.fst E.map (Spec.map (CommRingCat.ofHom φ))) (natTensorPow E.zeroSheaf n) φ
        E.map (E.baseChange φ).map
        (fun W => Stacks.Cech.baseRingHom_comp_app _ E.map (E.baseChange φ).map _
          (IsPullback.of_hasPullback E.map (Spec.map (CommRingCat.ofHom φ))) W) ⊤)) :
    letI : Algebra A B := φ.toAlgebra
    letI := sectionsModule E.map (natTensorPow E.zeroSheaf n) ⊤
    letI := sectionsModule (E.baseChange φ).map (natTensorPow (E.baseChange φ).zeroSheaf n) ⊤
    letI : Module A Γ(natTensorPow (E.baseChange φ).zeroSheaf n, ⊤) := Module.compHom _ φ
    letI : IsScalarTower A B Γ(natTensorPow (E.baseChange φ).zeroSheaf n, ⊤) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    ∃ ρ : Γ(natTensorPow E.zeroSheaf n, ⊤) →ₗ[A] Γ(natTensorPow (E.baseChange φ).zeroSheaf n, ⊤),
      ⇑ρ = E.restrictSection (Spec.map (CommRingCat.ofHom φ)) n ∧ IsBaseChange B ρ := by
  let : Algebra A B := φ.toAlgebra
  set g := Limits.pullback.fst E.map (Spec.map (CommRingCat.ofHom φ))
  set F := natTensorPow E.zeroSheaf n
  let := sectionsModule E.map F ⊤
  let := sectionsModule (E.baseChange φ).map ((Scheme.Modules.pullback g).obj F) (g ⁻¹ᵁ ⊤)
  let := Stacks.Cech.baseSectionsModule g F φ (E.baseChange φ).map (g ⁻¹ᵁ ⊤)
  let := Stacks.Cech.isScalarTowerBaseSections g F φ (E.baseChange φ).map (g ⁻¹ᵁ ⊤)
  let := sectionsModule (E.baseChange φ).map ((Scheme.Modules.pullback g).obj F) ⊤
  let := sectionsModule (E.baseChange φ).map (natTensorPow (E.baseChange φ).zeroSheaf n) ⊤
  let : Module A Γ(natTensorPow (E.baseChange φ).zeroSheaf n, ⊤) := Module.compHom _ φ
  let : IsScalarTower A B Γ(natTensorPow (E.baseChange φ).zeroSheaf n, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let e := E.sectionsEquiv φ n
  refine ⟨(e.toLinearMap.restrictScalars A).comp (Stacks.Cech.pullbackSectionsBaseₗ g F φ E.map
    (E.baseChange φ).map (fun W => Stacks.Cech.baseRingHom_comp_app _ E.map (E.baseChange φ).map _
      (IsPullback.of_hasPullback E.map (Spec.map (CommRingCat.ofHom φ))) W) ⊤), ?_,
    hbc.comp (IsBaseChange.ofEquiv e)⟩
  funext x
  show e (Stacks.Cech.pullbackSectionsBaseₗ g F φ E.map _ _ ⊤ x) = _
  rw [Stacks.AlgebraicGeometry.ProperFlatGlobalSections.pullbackSectionsBaseₗ_top_apply,
    restrictSection_eq]
  show Scheme.Modules.Hom.app (E.powPullbackIso φ n).hom ⊤
      (((Scheme.Modules.pullback g).obj F).presheaf.map _ _) = _
  congr 1
  exact Stacks.AlgebraicGeometry.ProjChartRatioPullback.map_pullbackSectionHom g F ⊤ _ ⊤ _ _ _ x


/-- The base change of `E` to the residue field at a prime `p`: the fibre of `E` at `p`. -/
abbrev fibreFamily (p : Ideal A) [p.IsPrime] : PointedFamily (Spec (.of p.ResidueField)) :=
  E.baseChange (algebraMap A p.ResidueField)

/-- **Cohomology and base change for the powers of `O(0)`.** If the higher cohomology of
`O(0)^{⊗ n}` vanishes on the fibre at `p`, then over some basic open `D(g) ∋ p` the restriction of
sections to every base change `Spec B ⟶ D(g)` is a base change of modules, and the sections over
`B` are free of a fixed rank. -/
theorem exists_away_isBaseChange_restrictSection [IsNoetherianRing A] [IsProper E.map]
    (p : Ideal A) [p.IsPrime] (n : ℕ)
    (hvan : ∀ i : ℕ, 0 < i → Subsingleton (cohomologyOverField p.ResidueField
      (E.fibreFamily p).map (natTensorPow (E.fibreFamily p).zeroSheaf n) i)) :
    ∃ g : A, g ∉ p ∧ ∃ m : ℕ, ∀ {B : Type u} [CommRing B] (ψ : Localization.Away g →+* B),
      letI : Algebra A B := (ψ.comp (algebraMap A (Localization.Away g))).toAlgebra
      letI := sectionsModule E.map (natTensorPow E.zeroSheaf n) ⊤
      letI := sectionsModule (E.baseChange (ψ.comp (algebraMap A (Localization.Away g)))).map
        (natTensorPow (E.baseChange (ψ.comp (algebraMap A (Localization.Away g)))).zeroSheaf n) ⊤
      letI : Module A Γ(natTensorPow (E.baseChange
        (ψ.comp (algebraMap A (Localization.Away g)))).zeroSheaf n, ⊤) :=
        Module.compHom _ (ψ.comp (algebraMap A (Localization.Away g)))
      letI : IsScalarTower A B Γ(natTensorPow (E.baseChange
        (ψ.comp (algebraMap A (Localization.Away g)))).zeroSheaf n, ⊤) :=
        IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
      (∃ ρ : Γ(natTensorPow E.zeroSheaf n, ⊤) →ₗ[A]
          Γ(natTensorPow (E.baseChange (ψ.comp (algebraMap A (Localization.Away g)))).zeroSheaf n,
            ⊤),
        ⇑ρ = E.restrictSection
          (Spec.map (CommRingCat.ofHom (ψ.comp (algebraMap A (Localization.Away g))))) n ∧
          IsBaseChange B ρ) ∧
      Nonempty (Module.Basis (Fin m) B Γ(natTensorPow
        (E.baseChange (ψ.comp (algebraMap A (Localization.Away g)))).zeroSheaf n, ⊤)) := by
  have : Smooth E.map := SmoothOfRelativeDimension.smooth 1 E.map
  let F := natTensorPow E.zeroSheaf n
  have hinv : Stacks.Ample.IsInvertibleModule E.total F :=
    Stacks.SectionProduct.isInvertibleModule_natTensorPow E.zeroSheaf n
  have hinv' : AlgebraicGeometry.SheafOfModules.IsInvertible E.total.presheaf
      E.total.ringCatSheaf.2 F := hinv
  have : IsLocallyNoetherian E.total := LocallyOfFiniteType.isLocallyNoetherian E.map
  have hcoh : F.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible (X := E.total) F
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (R := E.total.ringCatSheaf)
      F 1 := Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme E.total F
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := E.total.ringCatSheaf) F :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F 1
  have hflat : IsFlatOver E.map.toLRSHom.toShHom F :=
    AlgebraicGeometry.VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree E.map F
  have hvan' : ∀ i : ℕ, 0 < i → Subsingleton
      (((moduleGlobalSections (E.fibreFamily p).total).rightDerived i).obj
        ((Scheme.Modules.pullback (Limits.pullback.fst E.map
          (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))).obj F)) := fun i hi => by
    have h := open Stacks.AlgebraicGeometry.ProperFlatGlobalSections in
      subsingleton_rightDerived_of_cohomologyOverField _ _ i (hvan i hi)
    exact (((moduleGlobalSections (E.fibreFamily p).total).rightDerived i).mapIso
      (E.powPullbackIso (algebraMap A p.ResidueField) n)).toLinearEquiv.injective.subsingleton
  obtain ⟨g, hg, m, H⟩ :=
    Stacks.AlgebraicGeometry.ProperFlatGlobalSections.exists_away_cohomologyBaseChange
      E.map F hflat p (IsPullback.of_hasPullback _ _) hvan'
  refine ⟨g, hg, m, fun {B} _ ψ => ?_⟩
  obtain ⟨-, hbc, hb⟩ := H ψ (IsPullback.of_hasPullback E.map
    (Spec.map (CommRingCat.ofHom (ψ.comp (algebraMap A (Localization.Away g))))))
  let := sectionsModule (E.baseChange (ψ.comp (algebraMap A (Localization.Away g)))).map
    ((Scheme.Modules.pullback (Limits.pullback.fst E.map (Spec.map (CommRingCat.ofHom
      (ψ.comp (algebraMap A (Localization.Away g))))))).obj F)
    ((Limits.pullback.fst E.map (Spec.map (CommRingCat.ofHom
      (ψ.comp (algebraMap A (Localization.Away g)))))) ⁻¹ᵁ ⊤)
  let := sectionsModule (E.baseChange (ψ.comp (algebraMap A (Localization.Away g)))).map
    (natTensorPow (E.baseChange (ψ.comp (algebraMap A (Localization.Away g)))).zeroSheaf n) ⊤
  obtain ⟨b⟩ := hb
  exact ⟨E.exists_isBaseChange_restrictSection _ n hbc,
    ⟨b.map (E.sectionsEquiv (ψ.comp (algebraMap A (Localization.Away g))) n)⟩⟩


/-- **Cohomology and base change for the powers of `O(0)`**, in the form used below: over every
`A`-algebra `B` in which a fixed `g ∉ p` becomes a unit, the restriction of sections is a base
change of modules and the sections are free of a fixed rank. -/
theorem exists_isBaseChange_restrictSection_of_isUnit [IsNoetherianRing A] [IsProper E.map]
    (p : Ideal A) [p.IsPrime] (n : ℕ)
    (hvan : ∀ i : ℕ, 0 < i → Subsingleton (cohomologyOverField p.ResidueField
      (E.fibreFamily p).map (natTensorPow (E.fibreFamily p).zeroSheaf n) i)) :
    ∃ g : A, g ∉ p ∧ ∃ m : ℕ, ∀ {B : Type u} [CommRing B] (φ : A →+* B), IsUnit (φ g) →
      letI : Algebra A B := φ.toAlgebra
      letI := sectionsModule E.map (natTensorPow E.zeroSheaf n) ⊤
      letI := sectionsModule (E.baseChange φ).map (natTensorPow (E.baseChange φ).zeroSheaf n) ⊤
      letI : Module A Γ(natTensorPow (E.baseChange φ).zeroSheaf n, ⊤) := Module.compHom _ φ
      letI : IsScalarTower A B Γ(natTensorPow (E.baseChange φ).zeroSheaf n, ⊤) :=
        IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
      (∃ ρ : Γ(natTensorPow E.zeroSheaf n, ⊤) →ₗ[A]
          Γ(natTensorPow (E.baseChange φ).zeroSheaf n, ⊤),
        ⇑ρ = E.restrictSection (Spec.map (CommRingCat.ofHom φ)) n ∧ IsBaseChange B ρ) ∧
      Nonempty (Module.Basis (Fin m) B Γ(natTensorPow (E.baseChange φ).zeroSheaf n, ⊤)) := by
  obtain ⟨g, hg, m, H⟩ := E.exists_away_isBaseChange_restrictSection p n hvan
  refine ⟨g, hg, m, fun {B} _ φ hφ => ?_⟩
  have h := H (IsLocalization.Away.lift g hφ)
  rwa [IsLocalization.Away.lift_comp] at h


/-- Multiplication by a fixed section, as a linear map over the base for the module structures
through a structure morphism. -/
def mulSectionsLinear {B : Type u} [CommRing B] {X : Scheme.{u}} (f : X ⟶ Spec (.of B))
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {n : ℕ} (a : Γ(natTensorPow L n, ⊤))
    (m : ℕ) :
    letI := sectionsModule f (natTensorPow L m) ⊤
    letI := sectionsModule f (natTensorPow L (n + m)) ⊤
    Γ(natTensorPow L m, ⊤) →ₗ[B] Γ(natTensorPow L (n + m), ⊤) :=
  letI := sectionsModule f (natTensorPow L m) ⊤
  letI := sectionsModule f (natTensorPow L (n + m)) ⊤
  { toFun := mulSections L a
    map_add' := map_add _
    map_smul' b t := Scheme.Modules.Hom.app_smul
      (Stacks.GradedSections.mulMap (Stacks.AlgebraicGeometry.ProjChartFromRatios.secOf L a) m)
      ((baseRingHom f ⊤).hom b) t }

/-- A base change of modules has a source element whose image avoids any proper submodule. -/
theorem exists_not_mem_of_isBaseChange {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] {f : M →ₗ[R] N} (hf : IsBaseChange S f) {W : Submodule S N}
    (hW : W ≠ ⊤) : ∃ m, f m ∉ W := by
  by_contra h
  push Not at h
  refine hW (eq_top_iff.2 ?_)
  rw [← hf.span_range_eq_top, Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  exact h m

/-- A proper image: multiplication by a section, from a space of dimension `n` into one of
dimension `n + 1`, is not onto. -/
theorem range_mulSectionsLinear_ne_top {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (a : Γ(natTensorPow L 1, ⊤)) (m : ℕ) (hm0 : 0 < m)
    (hm :
      letI := sectionsModule f (natTensorPow L m) ⊤
      Module.finrank k Γ(natTensorPow L m, ⊤) = m)
    (hm1 :
      letI := sectionsModule f (natTensorPow L (1 + m)) ⊤
      Module.finrank k Γ(natTensorPow L (1 + m), ⊤) = 1 + m) :
    letI := sectionsModule f (natTensorPow L m) ⊤
    letI := sectionsModule f (natTensorPow L (1 + m)) ⊤
    LinearMap.range (mulSectionsLinear f L a m) ≠ ⊤ := by
  let := sectionsModule f (natTensorPow L m) ⊤
  let := sectionsModule f (natTensorPow L (1 + m)) ⊤
  intro h
  have : FiniteDimensional k Γ(natTensorPow L (1 + m), ⊤) :=
    Module.finite_of_finrank_pos (by rw [hm1]; omega)
  have : FiniteDimensional k Γ(natTensorPow L m, ⊤) :=
    Module.finite_of_finrank_pos (by rw [hm]; omega)
  have := LinearMap.finrank_range_le (mulSectionsLinear f L a m)
  rw [h, finrank_top, hm1, hm] at this
  omega

/-- An element outside the prime `p` becomes a unit in the residue field at `p`. -/
private theorem isUnit_algebraMap_residueField {p : Ideal A} [p.IsPrime] {g : A} (hg : g ∉ p) :
    IsUnit (algebraMap A p.ResidueField g) :=
  IsUnit.mk0 _ (by rwa [Ne, Ideal.algebraMap_residueField_eq_zero])

/-- The fibre of a proper smooth family of relative dimension one is again so. -/
private theorem fibreFamily_isProper_smooth {R : Type u} [CommRing R]
    (F : PointedFamily (Spec (.of R))) [IsProper F.map] [SmoothOfRelativeDimension 1 F.map]
    (p : Ideal R) [p.IsPrime] :
    IsProper (F.fibreFamily p).map ∧ SmoothOfRelativeDimension 1 (F.fibreFamily p).map :=
  ⟨inferInstanceAs (IsProper (Limits.pullback.snd F.map _)),
    smoothOfRelativeDimension_pullback_map F _⟩

/-- **A section of `O(0)^{⊗ (1 + n)}` with a pole of exact order `1 + n` on the fibre.** If on the
fibre at `p` the sections of `O(0)^{⊗ n}` and `O(0)^{⊗ (1 + n)}` have dimensions `n` and `1 + n`
and the higher cohomology of the latter vanishes, some section over the base restricts on the fibre
to a section not divisible by the canonical section `s` of `O(0)`. -/
theorem exists_restrictSection_notMem_range [IsNoetherianRing A] [IsProper E.map]
    (p : Ideal A) [p.IsPrime] (n : ℕ) (hn : 0 < n)
    (hvan : ∀ i : ℕ, 0 < i → Subsingleton (cohomologyOverField p.ResidueField
      (E.fibreFamily p).map (natTensorPow (E.fibreFamily p).zeroSheaf (1 + n)) i))
    (hdim :
      letI := sectionsModule (E.fibreFamily p).map (natTensorPow (E.fibreFamily p).zeroSheaf n) ⊤
      Module.finrank p.ResidueField Γ(natTensorPow (E.fibreFamily p).zeroSheaf n, ⊤) = n)
    (hdim' :
      letI := sectionsModule (E.fibreFamily p).map
          (natTensorPow (E.fibreFamily p).zeroSheaf (1 + n)) ⊤
      Module.finrank p.ResidueField Γ(natTensorPow (E.fibreFamily p).zeroSheaf (1 + n), ⊤) =
        1 + n) :
    ∃ x : Γ(natTensorPow E.zeroSheaf (1 + n), ⊤),
      E.restrictSection (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))) (1 + n) x ∉
        Set.range (mulSections (E.fibreFamily p).zeroSheaf (m := n)
          (E.fibreFamily p).zeroSection) := by
  obtain ⟨g, hg, m, H⟩ := E.exists_isBaseChange_restrictSection_of_isUnit p (1 + n) hvan
  obtain ⟨⟨ρ, hρ, hbc⟩, -⟩ :=
    H (algebraMap A p.ResidueField) (isUnit_algebraMap_residueField hg)
  let : Algebra A p.ResidueField := (algebraMap A p.ResidueField).toAlgebra
  let := sectionsModule E.map (natTensorPow E.zeroSheaf (1 + n)) ⊤
  let := sectionsModule (E.fibreFamily p).map (natTensorPow (E.fibreFamily p).zeroSheaf n) ⊤
  let := sectionsModule (E.fibreFamily p).map
    (natTensorPow (E.fibreFamily p).zeroSheaf (1 + n)) ⊤
  let : Module A Γ(natTensorPow (E.fibreFamily p).zeroSheaf (1 + n), ⊤) :=
    Module.compHom _ (algebraMap A p.ResidueField)
  let : IsScalarTower A p.ResidueField Γ(natTensorPow (E.fibreFamily p).zeroSheaf (1 + n), ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : Stacks.Ample.IsInvertibleModule (E.fibreFamily p).total (E.fibreFamily p).zeroSheaf :=
    isInvertibleModule_zeroSheaf _
  obtain ⟨x, hx⟩ := exists_not_mem_of_isBaseChange hbc
    (range_mulSectionsLinear_ne_top (E.fibreFamily p).map (E.fibreFamily p).zeroSheaf
      (E.fibreFamily p).zeroSection n hn hdim hdim')
  refine ⟨x, fun hmem => hx ?_⟩
  obtain ⟨z, hz⟩ := hmem
  refine ⟨z, ?_⟩
  rw [hρ]
  exact hz

/-- The action of the base ring on sections, read in the section ring: a scalar multiple is the
product with the image of the scalar in degree zero. -/
theorem toSectionRing_baseSmul {B : Type u} [CommRing B] {X : Scheme.{u}} (f : X ⟶ Spec (.of B))
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {n : ℕ} (b : B)
    (t : Γ(natTensorPow L n, ⊤)) :
    letI := sectionsModule f (natTensorPow L n) ⊤
    toSectionRing L n (b • t) = toSectionRing L n t *
      Stacks.AlgebraicGeometry.GradedSectionRingMap.degreeZeroHom L ((baseRingHom f ⊤).hom b) :=
  toSectionRing_smul L _ t

/-- **The expansion of `y²` in the Weierstrass monomials, near a point of the base.** Let `E` be a
proper family over `Spec A`, `A` Noetherian, smooth of relative dimension one, whose fibre at the
prime `p` has `H⁰ = κ(p)` and genus one, and let `x`, `y` be sections of `O(0)^{⊗ 2}`, `O(0)^{⊗ 3}`
whose restrictions to the fibre are not divisible by the canonical section `s` of `O(0)`. There are
`g ∉ p` and `d, e ∈ A_g` with numerators `d', e' ∉ p` such that over every `A_g`-algebra `B` in
which `d` and `e` are units, the restriction of `y²` is `∑ cᵢ wᵢ` in the Weierstrass monomials
`s⁶, s⁴x, s³y, s²x², sxy, x³`, with `c₅` a unit. -/
theorem exists_weierstrassCoefficients [IsNoetherianRing A] [IsProper E.map]
    (p : Ideal A) [p.IsPrime]
    (h0 : Module.finrank p.ResidueField (structureSheafCohomology (E.fibreFamily p).map 0) = 1)
    (h1 : genus (E.fibreFamily p).map = 1)
    {x : Γ(natTensorPow E.zeroSheaf 2, ⊤)} {y : Γ(natTensorPow E.zeroSheaf 3, ⊤)}
    (hx : E.restrictSection (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))) 2 x ∉
        Set.range (mulSections (E.fibreFamily p).zeroSheaf (m := 1)
          (E.fibreFamily p).zeroSection))
    (hy : E.restrictSection (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))) 3 y ∉
        Set.range (mulSections (E.fibreFamily p).zeroSheaf (m := 2)
          (E.fibreFamily p).zeroSection)) :
    ∃ g : A, g ∉ p ∧ ∃ (d e : Localization.Away g) (kd ke : ℕ) (d' e' : A),
      d * algebraMap A (Localization.Away g) g ^ kd = algebraMap A (Localization.Away g) d' ∧
      e * algebraMap A (Localization.Away g) g ^ ke = algebraMap A (Localization.Away g) e' ∧
      d' ∉ p ∧ e' ∉ p ∧
      ∀ {B : Type u} [CommRing B] (ψ : Localization.Away g →+* B), IsUnit (ψ d) → IsUnit (ψ e) →
        letI := sectionsModule (E.baseChange (ψ.comp (algebraMap A (Localization.Away g)))).map
          (natTensorPow (E.baseChange (ψ.comp (algebraMap A (Localization.Away g)))).zeroSheaf 6) ⊤
        ∃ c : Fin 6 → B, IsUnit (c 5) ∧
          E.restrictSection (Spec.map (CommRingCat.ofHom
              (ψ.comp (algebraMap A (Localization.Away g))))) 6 (ySq E.zeroSheaf y) =
            ∑ i, c i • E.restrictSection (Spec.map (CommRingCat.ofHom
              (ψ.comp (algebraMap A (Localization.Away g))))) 6
              (weierstrassMonomials E.zeroSheaf E.zeroSection x y i) := by
  -- the fibre at `p`
  obtain ⟨_, _⟩ := E.fibreFamily_isProper_smooth p
  have : Stacks.Ample.IsInvertibleModule (E.fibreFamily p).total (E.fibreFamily p).zeroSheaf :=
    isInvertibleModule_zeroSheaf _
  have hli := linearIndependent_weierstrassMonomials h0 h1 hx hy
  have hsp := span_weierstrassMonomials h0 h1 hx hy
  have hcf := coeff_ySq_ne_zero h0 h1 hx hy
  -- cohomology and base change in degree six, on the fibre and over `A_{g₆}`
  obtain ⟨g₆, hg₆, m₆, G₆⟩ := E.exists_isBaseChange_restrictSection_of_isUnit p 6
    (fun i hi => (E.fibreFamily p).subsingleton_cohomologyOverField_zeroSheaf h0 h1
      (by norm_num) hi)
  obtain ⟨ρκ, hρκ, hbcκ⟩ :=
    (G₆ (algebraMap A p.ResidueField) (isUnit_algebraMap_residueField hg₆)).1
  have G₁ := G₆ (algebraMap A (Localization.Away g₆)) (IsLocalization.Away.algebraMap_isUnit g₆)
  obtain ⟨ρ₁, hρ₁, hbc₁⟩ := G₁.1
  have b₁ := G₁.2.some
  have hι₀ : IsUnit (algebraMap A p.ResidueField g₆) := isUnit_algebraMap_residueField hg₆
  obtain ⟨ι₁, hι₁⟩ : ∃ ι₁ : Localization.Away g₆ →+* p.ResidueField,
      ι₁.comp (algebraMap A (Localization.Away g₆)) = algebraMap A p.ResidueField :=
    ⟨_, IsLocalization.Away.lift_comp g₆ hι₀⟩
  let := sectionsModule E.map (natTensorPow E.zeroSheaf 6) ⊤
  let := sectionsModule (E.fibreFamily p).map (natTensorPow (E.fibreFamily p).zeroSheaf 6) ⊤
  let := sectionsModule (E.baseChange (algebraMap A (Localization.Away g₆))).map
    (natTensorPow (E.baseChange (algebraMap A (Localization.Away g₆))).zeroSheaf 6) ⊤
  have hfun : (fun i => ρκ (weierstrassMonomials E.zeroSheaf E.zeroSection x y i)) =
      weierstrassMonomials (E.fibreFamily p).zeroSheaf (E.fibreFamily p).zeroSection
        (E.restrictSection (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))) 2 x)
        (E.restrictSection (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))) 3 y) := by
    funext i
    rw [hρκ]
    exact E.restrictSection_weierstrassMonomials _ x y i
  have hzκ : ρκ (ySq E.zeroSheaf y) = ySq (E.fibreFamily p).zeroSheaf
      (E.restrictSection (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))) 3 y) := by
    rw [hρκ]
    exact E.restrictSection_ySq _ y
  obtain ⟨d, e, hd, he, Hsp⟩ := IsBaseChange.exists_det_spread.{_, _, _, _, _, _, _, u, u}
    (algebraMap A (Localization.Away g₆)) ι₁ hι₁ ρ₁ hbc₁
    b₁ ρκ hbcκ (weierstrassMonomials E.zeroSheaf E.zeroSection x y) (ySq E.zeroSheaf y) 5
    (by rw [hfun]; exact hli) (by rw [hfun]; exact hsp)
    (fun c hc => hcf c (by
      rw [← hzκ, hc]
      exact Finset.sum_congr rfl fun i _ => congrArg (c i • ·) (congrFun hfun i)))
  -- numerators of the two determinants
  obtain ⟨kd, d', hd'⟩ := IsLocalization.Away.surj g₆ d
  obtain ⟨ke, e', he'⟩ := IsLocalization.Away.surj g₆ e
  have hι₁a : ∀ a, ι₁ (algebraMap A (Localization.Away g₆) a) = algebraMap A p.ResidueField a :=
    fun a => RingHom.congr_fun hι₁ a
  have hnum : ∀ (z : Localization.Away g₆) (k : ℕ) (a : A),
      z * algebraMap A (Localization.Away g₆) g₆ ^ k = algebraMap A (Localization.Away g₆) a →
      ι₁ z ≠ 0 → a ∉ p := by
    intro z k a hz hz0 ha
    have h' := congrArg ι₁ hz
    rw [map_mul, map_pow, hι₁a, hι₁a, (Ideal.algebraMap_residueField_eq_zero).2 ha] at h'
    exact mul_ne_zero hz0 (pow_ne_zero _ hι₀.ne_zero) h'
  refine ⟨g₆, hg₆, d, e, kd, ke, d', e', hd', he', hnum d kd d' hd' hd, hnum e ke e' he' he,
    fun {B} _ ψ hψd hψe => ?_⟩
  obtain ⟨ρB, hρB, hbcB⟩ := (G₆ (ψ.comp (algebraMap A (Localization.Away g₆)))
    ((IsLocalization.Away.algebraMap_isUnit g₆).map ψ)).1
  let := sectionsModule (E.baseChange (ψ.comp (algebraMap A (Localization.Away g₆)))).map
    (natTensorPow (E.baseChange (ψ.comp (algebraMap A (Localization.Away g₆)))).zeroSheaf 6) ⊤
  obtain ⟨c, hc5, hc⟩ := Hsp ψ rfl ρB hbcB hψd hψe
  refine ⟨c, hc5, ?_⟩
  rwa [← hρB]

/-- **The Weierstrass equation from an expansion of `y²`.** If `y² = ∑ cᵢ wᵢ` in the Weierstrass
monomials `s⁶, s⁴x, s³y, s²x², sxy, x³` with `c₅ = u` a unit, then `X = u x` and `Y = u y` satisfy
the Weierstrass equation `Y² + a₁ s X Y + a₃ s³ Y = X³ + a₂ s² X² + a₄ s⁴ X + a₆ s⁶` of
`a₁ = -c₄`, `a₂ = c₃`, `a₃ = -u c₂`, `a₄ = u c₁`, `a₆ = u² c₀`. -/
theorem exists_weierstrassEquation_of_expansion {B : Type u} [CommRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (s : Γ(natTensorPow L 1, ⊤)) (x : Γ(natTensorPow L 2, ⊤)) (y : Γ(natTensorPow L 3, ⊤))
    (c : Fin 6 → B) (hc5 : IsUnit (c 5))
    (hc : letI := sectionsModule f (natTensorPow L 6) ⊤
      ySq L y = ∑ i, c i • weierstrassMonomials L s x y i) :
    letI := sectionsModule f (natTensorPow L 2) ⊤
    letI := sectionsModule f (natTensorPow L 3) ⊤
    letI := sectionsModule f (natTensorPow L 6) ⊤
    ∃ (u : Bˣ) (C : WeierstrassCurve B),
      ySq L ((u : B) • y) + C.a₁ • weierstrassMonomials L s ((u : B) • x) ((u : B) • y) 4 +
          C.a₃ • weierstrassMonomials L s ((u : B) • x) ((u : B) • y) 2 =
        weierstrassMonomials L s ((u : B) • x) ((u : B) • y) 5 +
          C.a₂ • weierstrassMonomials L s ((u : B) • x) ((u : B) • y) 3 +
          C.a₄ • weierstrassMonomials L s ((u : B) • x) ((u : B) • y) 1 +
          C.a₆ • weierstrassMonomials L s ((u : B) • x) ((u : B) • y) 0 := by
  let := sectionsModule f (natTensorPow L 2) ⊤
  let := sectionsModule f (natTensorPow L 3) ⊤
  let := sectionsModule f (natTensorPow L 6) ⊤
  refine ⟨hc5.unit, WeierstrassCurve.mk (-c 4) (c 3) (-(c 5 * c 2)) (c 5 * c 1) (c 5 ^ 2 * c 0),
    ?_⟩
  have hW : ∀ (x' : Γ(natTensorPow L 2, ⊤)) (y' : Γ(natTensorPow L 3, ⊤)) (i : Fin 6),
      toSectionRing L 6 (weierstrassMonomials L s x' y' i) =
        ![toSectionRing L 1 s ^ 6, toSectionRing L 1 s ^ 4 * toSectionRing L 2 x',
          toSectionRing L 1 s ^ 3 * toSectionRing L 3 y',
          toSectionRing L 1 s ^ 2 * toSectionRing L 2 x' ^ 2,
          toSectionRing L 1 s * toSectionRing L 2 x' * toSectionRing L 3 y',
          toSectionRing L 2 x' ^ 3] i :=
    fun x' y' i => congrFun (toSectionRing_weierstrassMonomials L s x' y') i
  have hc' := congrArg (toSectionRing L 6) hc
  rw [Fin.sum_univ_six] at hc'
  simp only [toSectionRing_add, toSectionRing_baseSmul f, toSectionRing_ySq, hW,
    Matrix.cons_val] at hc'
  apply toSectionRing_injective L 6
  simp only [toSectionRing_add, toSectionRing_baseSmul f, toSectionRing_ySq, hW, Matrix.cons_val,
    IsUnit.unit_spec, map_neg, map_mul, map_pow]
  linear_combination
    (Stacks.AlgebraicGeometry.GradedSectionRingMap.degreeZeroHom L
      ((baseRingHom f ⊤).hom (c 5))) ^ 2 * hc'

/-- **A Weierstrass equation for an elliptic curve near a point of an affine Noetherian base,
from sections of the powers of `O(0)`.** Let `E` be a proper family over `Spec A`, `A` Noetherian,
smooth of relative dimension one, whose fibre at the prime `p` has `H⁰ = κ(p)` and genus one.
There are sections `x` of `O(0)^{⊗ 2}` and `y` of `O(0)^{⊗ 3}` whose restrictions to the fibre at
`p` are not divisible by the canonical section `s` of `O(0)`, and `h ∉ p`, such that over every
`A`-algebra `B` in which `h` is a unit there are a unit `u` and a Weierstrass curve `C` over `B`
with `X = u x`, `Y = u y` satisfying `Y² + a₁ s X Y + a₃ s³ Y = X³ + a₂ s² X² + a₄ s⁴ X + a₆ s⁶`
in `Γ(O(0)^{⊗ 6})` of the base change of `E` to `B`. -/
theorem exists_weierstrassEquation_sections [IsNoetherianRing A] [IsProper E.map]
    (p : Ideal A) [p.IsPrime]
    (h0 : Module.finrank p.ResidueField (structureSheafCohomology (E.fibreFamily p).map 0) = 1)
    (h1 : genus (E.fibreFamily p).map = 1) :
    ∃ h : A, h ∉ p ∧ ∃ (x : Γ(natTensorPow E.zeroSheaf 2, ⊤))
      (y : Γ(natTensorPow E.zeroSheaf 3, ⊤)),
      E.restrictSection (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))) 2 x ∉
        Set.range (mulSections (E.fibreFamily p).zeroSheaf (m := 1)
          (E.fibreFamily p).zeroSection) ∧
      E.restrictSection (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))) 3 y ∉
        Set.range (mulSections (E.fibreFamily p).zeroSheaf (m := 2)
          (E.fibreFamily p).zeroSection) ∧
      ∀ {B : Type u} [CommRing B] (φ : A →+* B), IsUnit (φ h) →
        letI := sectionsModule (E.baseChange φ).map (natTensorPow (E.baseChange φ).zeroSheaf 2) ⊤
        letI := sectionsModule (E.baseChange φ).map (natTensorPow (E.baseChange φ).zeroSheaf 3) ⊤
        letI := sectionsModule (E.baseChange φ).map (natTensorPow (E.baseChange φ).zeroSheaf 6) ⊤
        ∃ (u : Bˣ) (C : WeierstrassCurve B),
          let X := (u : B) • E.restrictSection (Spec.map (CommRingCat.ofHom φ)) 2 x
          let Y := (u : B) • E.restrictSection (Spec.map (CommRingCat.ofHom φ)) 3 y
          let W := weierstrassMonomials (E.baseChange φ).zeroSheaf (E.baseChange φ).zeroSection X Y
          ySq (E.baseChange φ).zeroSheaf Y + C.a₁ • W 4 + C.a₃ • W 2 =
            W 5 + C.a₂ • W 3 + C.a₄ • W 1 + C.a₆ • W 0 := by
  obtain ⟨_, _⟩ := E.fibreFamily_isProper_smooth p
  have H1 : ∀ n : ℕ, 1 ≤ n → ∀ i : ℕ, 0 < i → Subsingleton (cohomologyOverField p.ResidueField
      (E.fibreFamily p).map (natTensorPow (E.fibreFamily p).zeroSheaf n) i) :=
    fun n hn i hi => (E.fibreFamily p).subsingleton_cohomologyOverField_zeroSheaf h0 h1 hn hi
  have H2 := fun n (hn : 1 ≤ n) => (E.fibreFamily p).finrank_sections_zeroSheaf h0 h1 hn
  obtain ⟨x, hx⟩ := E.exists_restrictSection_notMem_range p 1 one_pos (H1 (1 + 1) (by norm_num))
    (H2 1 le_rfl) (H2 (1 + 1) (by norm_num))
  obtain ⟨y, hy⟩ := E.exists_restrictSection_notMem_range p 2 two_pos (H1 (1 + 2) (by norm_num))
    (H2 2 (by norm_num)) (H2 (1 + 2) (by norm_num))
  obtain ⟨g, hg, d, e, kd, ke, d', e', hd', he', hd'p, he'p, H⟩ :=
    E.exists_weierstrassCoefficients p h0 h1 hx hy
  have hhp : g * d' * e' ∉ p := by
    intro hh
    rcases (‹p.IsPrime›.mul_mem_iff_mem_or_mem).1 hh with hh | hh
    · rcases (‹p.IsPrime›.mul_mem_iff_mem_or_mem).1 hh with hh | hh
      exacts [hg hh, hd'p hh]
    · exact he'p hh
  refine ⟨g * d' * e', hhp, x, y, hx, hy, fun {B} _ φ hφ => ?_⟩
  have hu : ∀ a : A, a ∣ g * d' * e' → IsUnit (φ a) :=
    fun a ha => isUnit_of_dvd_unit (map_dvd _ ha) hφ
  have hgu := hu g ⟨d' * e', by ring⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Localization.Away g →+* B,
      ψ.comp (algebraMap A (Localization.Away g)) = φ :=
    ⟨_, IsLocalization.Away.lift_comp g hgu⟩
  have hunitψ : ∀ (z : Localization.Away g) (k : ℕ) (a : A),
      z * algebraMap A (Localization.Away g) g ^ k = algebraMap A (Localization.Away g) a →
      a ∣ g * d' * e' → IsUnit (ψ z) := by
    intro z k a hz ha
    have h' := congrArg ψ hz
    rw [map_mul, map_pow, ← RingHom.comp_apply, ← RingHom.comp_apply ψ, hψ] at h'
    exact isUnit_of_mul_isUnit_left (h' ▸ hu a ha)
  have Hc := H ψ (hunitψ d kd d' hd' ⟨g * e', by ring⟩) (hunitψ e ke e' he' ⟨g * d', by ring⟩)
  subst hψ
  have : Stacks.Ample.IsInvertibleModule
      (E.baseChange (ψ.comp (algebraMap A (Localization.Away g)))).total
      (E.baseChange (ψ.comp (algebraMap A (Localization.Away g)))).zeroSheaf :=
    isInvertibleModule_zeroSheaf _
  obtain ⟨c, hc5, hc⟩ := Hc
  refine exists_weierstrassEquation_of_expansion _ _ _ _ _ c hc5 ?_
  rw [restrictSection_ySq] at hc
  rw [hc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [restrictSection_weierstrassMonomials]

end AlgebraicGeometry.ModuliEllipticCurves.PointedFamily

end
