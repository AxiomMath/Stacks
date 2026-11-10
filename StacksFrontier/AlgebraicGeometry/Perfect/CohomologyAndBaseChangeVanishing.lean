module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleDegreeZero
public import StacksFrontier.Algebra.Module.FlatComplexBaseChange
public import StacksFrontier.Homology.Perfect.SingleDegreeFibre
public import StacksFrontier.Homology.Perfect.LargeUniverse
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsAdjunctionComp
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.PullbackSection
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology and base change when the higher cohomology of a fibre vanishes

Let `A` be a Noetherian ring, `f : X ⟶ Spec A` a proper morphism and `F` a coherent `𝒪_X`-module
flat over `A`. If the fibre `X_p` over a prime `p` has no cohomology of `F` in positive degrees,
then over a principal open `D(g) ∋ p` the formation of `Γ(X, F)` commutes with every base change
and the higher cohomology of every base change vanishes.

## Main results

* `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.exists_away_isZero_homology`: the base
  change to `A_g` of the Čech model of `RΓ(X, F)` has no homology outside degree `0`.
* `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.exists_away_cohomologyBaseChange`: for every
  `A_g`-algebra `B` and every base change `X'` of `X` to `B`, the pullback of `F` to `X'` has no
  cohomology in positive degrees, and the canonical pullback of sections
  `Γ(X, F) → Γ(X', g'^* F)` is a base change along `A → B`.

## Implementation notes

The vanishing near `p` comes from the derived category: the Čech model of a finite affine cover
with affine intersections computes `RΓ(X, F)`, which is perfect by [Stacks, Tag 07VK] (1), and
whose derived fibre at `p` is the Čech model of the fibre, termwise and hence derivedly because
the model is termwise flat. A perfect complex whose derived fibre is concentrated in degree `0`
is, near `p`, a free module in degree `0`
(`StacksDraft.Perfect.exists_away_iso_singleFunctor_free_of_fibre_concentrated`). The base
change statement is then module theory: an exact bounded complex of flat modules stays exact
after any tensor product and the kernel of its first differential commutes with it
(`StacksDraft.FlatComplex.universallyExact`), and the kernel of the first Čech differential is
the module of global sections (`Stacks.Cech.range_sectionsToAlternatingₗ`), compatibly with the
base-change isomorphism of Čech cochains.

## References

* [Stacks Project, Tag 07VK](https://stacks.math.columbia.edu/tag/07VK)
* [Stacks Project, Tag 0BDK](https://stacks.math.columbia.edu/tag/0BDK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.ProperFlatGlobalSections

attribute [local instance 10000] HasDerivedCategory.standard

section Model

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  {I : Type u} [Finite I] [LinearOrder I] (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
  (F : X.Modules) [F.IsQuasicoherent]

/-- The Čech model is perfect. -/
theorem isPerfect_Q_baseAlternatingCechComplex [IsNoetherianRing A] [IsProper f] [F.IsCoherent]
    (hUaff : ∀ i, IsAffineOpen (U i))
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)))
    (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj (baseAlternatingCechComplex f U hU F)) :=
  StacksDraft.Perfect.isPerfect_of_iso
    (alternatingCechIsoDerivedGlobalSectionsOverBase f U hU F haff)
    (isPerfect_derivedGlobalSectionsOverBase f U hU F hUaff haff hflat
      AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase.{u})

/-- Derived extension of scalars of the Čech model is computed termwise. -/
def totalDerivedExtensionScalarsModelIso [IsSeparated f] {B : Type u} [CommRing B] (φ : A →+* B)
    (hUaff : ∀ i, IsAffineOpen (U i)) (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} φ).functor.obj
        (DerivedCategory.Q.obj (baseAlternatingCechComplex f U hU F)) ≅
      DerivedCategory.Q.obj (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (baseAlternatingCechComplex f U hU F)) := by
  let _ : Fintype I := Fintype.ofFinite I
  have : ∀ i, Module.Flat A ((baseAlternatingCechComplex f U hU F).X i) :=
    flat_baseAlternatingCechComplex_X f U hU F hUaff hflat
  have := (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    φ).comparison_isIso_of_flat (baseAlternatingCechComplex f U hU F) (Fintype.card I : ℤ)
  exact @asIso _ _ _ _ _ this

/-- **The derived fibre of the Čech model at `p` is the cohomology of the fibre.** If the fibre
`X_p` has no cohomology in positive degrees, the derived fibre of the Čech model vanishes in every
nonzero degree. -/
theorem finrank_derivedFibreHomology_eq_zero [IsSeparated f]
    (hUaff : ∀ i, IsAffineOpen (U i)) (hflat : IsFlatOver f.toLRSHom.toShHom F)
    (p : Ideal A) [p.IsPrime] {Xp : Scheme.{u}} {fp : Xp ⟶ Spec (.of p.ResidueField)}
    {gp : Xp ⟶ X}
    (hsq : IsPullback gp fp f (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))
    (hvan : ∀ i : ℕ, 0 < i → Subsingleton
      (((moduleGlobalSections Xp).rightDerived i).obj ((Scheme.Modules.pullback gp).obj F)))
    (j : ℤ) (hj : j ≠ 0) :
    Module.finrank p.ResidueField (StacksDraft.Perfect.derivedFibreHomology.{u, u} p
      (DerivedCategory.Q.obj (baseAlternatingCechComplex f U hU F)) j) = 0 := by
  have : ((Scheme.Modules.pullback gp).obj F).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback gp F
  let K' := baseAlternatingCechComplex fp (fun i => gp ⁻¹ᵁ U i) (top_eq_iSup_preimage gp U hU)
    ((Scheme.Modules.pullback gp).obj F)
  have hK' : IsZero (K'.homology j) := by
    rcases lt_or_gt_of_ne hj with hneg | hpos
    · exact ShortComplex.isZero_homology_of_isZero_X₂ (K'.sc j)
        (CochainComplex.isZero_of_isStrictlyGE K' 0 j hneg)
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, j = m := ⟨j.toNat, (Int.toNat_of_nonneg hpos.le).symm⟩
      refine IsZero.of_iso ?_ (homologyBaseAlternatingCechComplexIso fp _
        (top_eq_iSup_preimage gp U hU) _
        (iInf_preimage_isAffineOpen (algebraMap A p.ResidueField) hsq U hUaff) m)
      exact @ModuleCat.isZero_of_subsingleton _ _ _ (hvan m (by exact_mod_cast hpos))
  have := ModuleCat.subsingleton_of_isZero (hK'.of_iso ((DerivedCategory.homologyFunctor _ j).mapIso
      (totalDerivedExtensionScalarsModelIso f U hU F (algebraMap A p.ResidueField) hUaff hflat) ≪≫
    (DerivedCategory.homologyFunctorFactors _ j).app _ ≪≫
    (HomologicalComplex.homologyFunctor _ _ j).mapIso
      (baseAlternatingCechComplexBaseChangeIso (algebraMap A p.ResidueField) hsq F U hU hUaff)))
  exact Module.finrank_zero_of_subsingleton

/-- **Near a point whose fibre has no higher cohomology the Čech model is exact in positive
degrees.** If the fibre `X_p` has no cohomology in positive degrees, then on a principal open
`D(g) ∋ p` the base change of the Čech model to `A_g` has no homology outside degree `0`. -/
theorem exists_away_isZero_homology [IsNoetherianRing A] [IsProper f] [F.IsCoherent]
    (hUaff : ∀ i, IsAffineOpen (U i))
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)))
    (hflat : IsFlatOver f.toLRSHom.toShHom F)
    (p : Ideal A) [p.IsPrime] {Xp : Scheme.{u}} {fp : Xp ⟶ Spec (.of p.ResidueField)}
    {gp : Xp ⟶ X}
    (hsq : IsPullback gp fp f (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))
    (hvan : ∀ i : ℕ, 0 < i → Subsingleton
      (((moduleGlobalSections Xp).rightDerived i).obj ((Scheme.Modules.pullback gp).obj F))) :
    ∃ g : A, g ∉ p ∧ (∀ j : ℤ, j ≠ 0 → IsZero
      ((((ModuleCat.extendScalars.{u, u, u}
        (algebraMap A (Localization.Away g))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (baseAlternatingCechComplex f U hU F)).homology j)) ∧
      ∃ n : ℕ, Nonempty
        ((((ModuleCat.extendScalars.{u, u, u}
          (algebraMap A (Localization.Away g))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (baseAlternatingCechComplex f U hU F)).homology 0 ≅
          ModuleCat.of (Localization.Away g) (ULift.{u} (Fin n → Localization.Away g))) := by
  obtain ⟨g, hg, ⟨e⟩⟩ :=
    StacksDraft.Perfect.exists_away_iso_singleFunctor_free_of_fibre_concentrated.{u, u} p
      (DerivedCategory.Q.obj (baseAlternatingCechComplex f U hU F))
      (isPerfect_Q_baseAlternatingCechComplex f U hU F hUaff haff hflat) 0
      (fun j hj => finrank_derivedFibreHomology_eq_zero f U hU F hUaff hflat p hsq hvan j hj)
  refine ⟨g, hg, fun j hj => ?_, _, ⟨((DerivedCategory.homologyFunctorFactors _ 0).app _).symm ≪≫
      (DerivedCategory.homologyFunctor _ 0).mapIso
        ((totalDerivedExtensionScalarsModelIso f U hU F _ hUaff hflat).symm ≪≫ e) ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _⟩⟩
  refine IsZero.of_iso ?_
    (((DerivedCategory.homologyFunctorFactors _ j).app _).symm ≪≫
      (DerivedCategory.homologyFunctor _ j).mapIso
        ((totalDerivedExtensionScalarsModelIso f U hU F _ hUaff hflat).symm ≪≫ e) ≪≫
      (DerivedCategory.homologyFunctorFactors _ j).app _)
  exact HomologicalComplex.isZero_single_obj_homology _ _ _ _ hj

/-- Base change of the `ℤ`-indexed Čech model is the extension by zero of the base change of the
alternating Čech complex. -/
def baseChangeModelIsoExtend {B : Type u} [CommRing B] (φ : A →+* B) :
    ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (baseAlternatingCechComplex f U hU F) ≅
      (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (Stacks.Cech.alternatingCechModuleComplex f U F)).extend ComplexShape.embeddingUpNat :=
  ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      (baseAlternatingCechComplexIsoExtend f U hU F) ≪≫
    (@Stacks.DerivedIndexing.mapExtendIso ℕ ℤ (ComplexShape.up ℕ) (ComplexShape.up ℤ)
        (ModuleCat.{u} A) (ModuleCat.{u} B) _ _ _ _ _ _
        (ModuleCat.extendScalars.{u, u, u} φ) inferInstance ComplexShape.embeddingUpNat
        (Stacks.Cech.alternatingCechModuleComplex f U F)).symm

include hU in
/-- **The base-changed alternating Čech complex is exact in positive degrees near `p`.** -/
theorem exists_away_exactAt_alternating [IsNoetherianRing A] [IsProper f] [F.IsCoherent]
    (hUaff : ∀ i, IsAffineOpen (U i))
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)))
    (hflat : IsFlatOver f.toLRSHom.toShHom F)
    (p : Ideal A) [p.IsPrime] {Xp : Scheme.{u}} {fp : Xp ⟶ Spec (.of p.ResidueField)}
    {gp : Xp ⟶ X}
    (hsq : IsPullback gp fp f (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))
    (hvan : ∀ i : ℕ, 0 < i → Subsingleton
      (((moduleGlobalSections Xp).rightDerived i).obj ((Scheme.Modules.pullback gp).obj F))) :
    ∃ g : A, g ∉ p ∧ (∀ n : ℕ,
      (((ModuleCat.extendScalars.{u, u, u}
        (algebraMap A (Localization.Away g))).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (Stacks.Cech.alternatingCechModuleComplex f U F)).ExactAt
          (n + 1)) ∧
      ∃ n : ℕ, Nonempty
        ((((ModuleCat.extendScalars.{u, u, u}
          (algebraMap A (Localization.Away g))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (Stacks.Cech.alternatingCechModuleComplex f U F)).homology 0 ≅
          ModuleCat.of (Localization.Away g) (ULift.{u} (Fin n → Localization.Away g))) := by
  obtain ⟨g, hg, hz, n, ⟨e⟩⟩ :=
    exists_away_isZero_homology f U hU F hUaff haff hflat p hsq hvan
  refine ⟨g, hg, fun n => ?_, n, ⟨(HomologicalComplex.extendHomologyIso _
      ComplexShape.embeddingUpNat (j := 0) (j' := ((0 : ℕ) : ℤ)) rfl).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ ((0 : ℕ) : ℤ)).mapIso
      (baseChangeModelIsoExtend f U hU F _).symm ≪≫ e⟩⟩
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hz ((n + 1 : ℕ) : ℤ) (by omega)).of_iso
    ((HomologicalComplex.extendHomologyIso _ ComplexShape.embeddingUpNat
      (j := n + 1) (j' := ((n + 1 : ℕ) : ℤ)) rfl).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ ((n + 1 : ℕ) : ℤ)).mapIso
      (baseChangeModelIsoExtend f U hU F _).symm)

end Model


section Universal

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  {I : Type u} [Fintype I] (U : I → X.Opens) (F : X.Modules)

/-- Exactness of a base-changed complex of modules is exactness of the base-changed linear
maps. -/
theorem exactAt_extendScalars_iff {B : Type u} [CommRing B] (φ : A →+* B)
    (K : CochainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) :
    letI : Algebra A B := φ.toAlgebra
    (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K).ExactAt (n + 1) ↔
      Function.Exact ((K.d n (n + 1)).hom.baseChange B)
        ((K.d (n + 1) (n + 2)).hom.baseChange B) := by
  let : Algebra A B := φ.toAlgebra
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff_range_eq_ker, LinearMap.exact_iff]
  exact eq_comm

/-- Extension of scalars along `α` and then along `ψ` is extension of scalars along `ψ ∘ α`,
on underlying elements and compatibly with every morphism. -/
theorem extendScalarsComp_naturality {C B : Type u} [CommRing C] [CommRing B] (α : A →+* C)
    (ψ : C →+* B) {M N : ModuleCat.{u} A} (h : M ⟶ N)
    (x : (ModuleCat.extendScalars.{u, u, u} (ψ.comp α)).obj M) :
    ((ModuleCat.extendScalarsComp α ψ).hom.app N).hom
        (((ModuleCat.extendScalars.{u, u, u} (ψ.comp α)).map h).hom x) =
      ((ModuleCat.extendScalars.{u, u, u} ψ).map
        ((ModuleCat.extendScalars.{u, u, u} α).map h)).hom
          (((ModuleCat.extendScalarsComp α ψ).hom.app M).hom x) :=
  congr($((ModuleCat.extendScalarsComp α ψ).hom.naturality h).hom x)

/-- A ladder of bijections transports exactness of a pair of maps. -/
theorem exact_of_ladder_equiv {M N P M' N' P' : Type*} [Zero P] [Zero P']
    {f₁ : M → N} {f₂ : N → P} {g₁ : M' → N'} {g₂ : N' → P'} (e₁ : M ≃ M') (e₂ : N ≃ N')
    (e₃ : P → P') (he₃ : ∀ p, e₃ p = 0 ↔ p = 0) (h₁ : ∀ x, g₁ (e₁ x) = e₂ (f₁ x))
    (h₂ : ∀ y, g₂ (e₂ y) = e₃ (f₂ y)) (H : Function.Exact g₁ g₂) : Function.Exact f₁ f₂ := by
  intro y
  rw [← he₃, ← h₂, H (e₂ y)]
  constructor
  · rintro ⟨x', hx'⟩
    refine ⟨e₁.symm x', e₂.injective ?_⟩
    rw [← h₁, Equiv.apply_symm_apply, hx']
  · rintro ⟨x, rfl⟩
    exact ⟨e₁ x, h₁ x⟩

/-- The localization `A_g`, viewed as an `A`-module through restriction of scalars, is flat. -/
@[ega "0 6.3.1" "principal localization"]
theorem flat_restrictScalars_localization (g : A) :
    Module.Flat A ((ModuleCat.restrictScalars.{u} (algebraMap A (Localization.Away g))).obj
      (ModuleCat.of (Localization.Away g) (Localization.Away g))) := by
  let e : Localization.Away g ≃ₗ[A] ((ModuleCat.restrictScalars.{u}
      (algebraMap A (Localization.Away g))).obj
        (ModuleCat.of (Localization.Away g) (Localization.Away g))) :=
    { toFun := fun c => c
      invFun := fun c => c
      map_add' := fun _ _ => rfl
      map_smul' := fun a c => by
        change a • c = algebraMap A (Localization.Away g) a * c
        rw [Algebra.smul_def]
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Module.Flat.of_linearEquiv e.symm

/-- **Base change of a complex of flat modules which is exact in positive degrees after a
localization.** Let `L` be a bounded complex of flat `A`-modules whose base change to `A_g` is
exact in every positive degree. Then for every `A_g`-algebra `B` the base change of `L` to `B` is
exact in every positive degree, and for every `ι : T ⟶ L⁰` which is injective with image the
kernel of the first differential, the base change of `ι` to `B` is injective with image the kernel
of the base change of that differential. -/
theorem baseChange_exact_of_exactAt_localization (L : CochainComplex (ModuleCat.{u} A) ℕ)
    [∀ n, Module.Flat A (L.X n)] (N : ℕ) (hN : ∀ m, N < m → Subsingleton (L.X m)) (g : A)
    (hex : ∀ n, (((ModuleCat.extendScalars.{u, u, u}
      (algebraMap A (Localization.Away g))).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj L).ExactAt (n + 1))
    {B : Type u} [CommRing B] (ψ : Localization.Away g →+* B) :
    (∀ n, (((ModuleCat.extendScalars.{u, u, u}
      (ψ.comp (algebraMap A (Localization.Away g)))).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj L).ExactAt (n + 1)) ∧
    ∀ {T : ModuleCat.{u} A} (ι : T ⟶ L.X 0), Function.Injective ι.hom →
      LinearMap.range ι.hom = LinearMap.ker (L.d 0 1).hom →
      letI : Algebra A B := (ψ.comp (algebraMap A (Localization.Away g))).toAlgebra
      Function.Injective (ι.hom.baseChange B) ∧
        Function.Exact (ι.hom.baseChange B) ((L.d 0 1).hom.baseChange B) := by
  set C := Localization.Away g
  set α := algebraMap A C
  let LC := ((ModuleCat.extendScalars.{u, u, u} α).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj L
  let dC : ∀ n, LC.X n →ₗ[C] LC.X (n + 1) := fun n => (LC.d n (n + 1)).hom
  have hflatC : ∀ n, Module.Flat C (LC.X n) := fun n => by
    let : Algebra A C := α.toAlgebra
    exact Module.Flat.baseChange A C (L.X n)
  have hsubC : ∀ m, N < m → Subsingleton (LC.X m) := fun m hm => by
    have := hN m hm
    exact StacksDraft.FlatComplex.subsingleton_tensor (R := A)
      (P := (ModuleCat.restrictScalars.{u} α).obj (ModuleCat.of C C)) (M := L.X m)
  have hexC : ∀ m, Function.Exact (dC m) (dC (m + 1)) := fun m =>
    (exactAt_extendScalars_iff α L m).1 (hex m)
  let : Algebra C B := ψ.toAlgebra
  obtain ⟨hPex, -, -⟩ := (StacksDraft.FlatComplex.universallyExact.{u, u, u} dC N hsubC 0
    fun m _ => hexC m).2 B
  let eL : ∀ M : ModuleCat.{u} A, (ModuleCat.extendScalars.{u, u, u} (ψ.comp α)).obj M ≃ₗ[B]
      (ModuleCat.extendScalars.{u, u, u} ψ).obj ((ModuleCat.extendScalars.{u, u, u} α).obj M) :=
    fun M => ((ModuleCat.extendScalarsComp α ψ).app M).toLinearEquiv
  let : Algebra A B := (ψ.comp α).toAlgebra
  have hnat : ∀ {M N : ModuleCat.{u} A} (h : M ⟶ N) (x : (ModuleCat.extendScalars.{u, u, u}
      (ψ.comp α)).obj M), (((ModuleCat.extendScalars.{u, u, u} α).map h).hom.lTensor B)
        (eL M x) = eL N ((h.hom.baseChange B) x) := fun h x => by
    rw [← LinearMap.baseChange_eq_lTensor]
    exact (extendScalarsComp_naturality α ψ h x).symm
  have key : ∀ {M N P : ModuleCat.{u} A} (h₁ : M ⟶ N) (h₂ : N ⟶ P),
      Function.Exact (((ModuleCat.extendScalars.{u, u, u} α).map h₁).hom.lTensor B)
        (((ModuleCat.extendScalars.{u, u, u} α).map h₂).hom.lTensor B) →
      Function.Exact (h₁.hom.baseChange B) (h₂.hom.baseChange B) := fun h₁ h₂ H =>
    exact_of_ladder_equiv (eL _).toEquiv (eL _).toEquiv (eL _)
      (fun _ => (eL _).map_eq_zero_iff) (hnat h₁) (hnat h₂) H
  have keyinj : ∀ {M N : ModuleCat.{u} A} (h : M ⟶ N),
      Function.Injective (((ModuleCat.extendScalars.{u, u, u} α).map h).hom.lTensor B) →
      Function.Injective (h.hom.baseChange B) := fun h H x y hxy => by
    refine (eL _).injective (H ?_)
    rw [hnat h x, hnat h y]
    exact congrArg (eL _) hxy
  refine ⟨fun n => (exactAt_extendScalars_iff (ψ.comp α) L n).2
    (key (L.d n (n + 1)) (L.d (n + 1) (n + 2)) (hPex n (Nat.zero_le _))), ?_⟩
  intro T ι hι hrange
  have hfl : Module.Flat A ((ModuleCat.restrictScalars.{u} α).obj (ModuleCat.of C C)) :=
    flat_restrictScalars_localization g
  have hinjC : Function.Injective ((ModuleCat.extendScalars.{u, u, u} α).map ι).hom :=
    Module.Flat.lTensor_preserves_injective_linearMap
      (M := (ModuleCat.restrictScalars.{u} α).obj (ModuleCat.of C C)) ι.hom hι
  have hexC0 : Function.Exact ((ModuleCat.extendScalars.{u, u, u} α).map ι).hom (dC 0) :=
    (Module.Flat.lTensor_exact (M := (ModuleCat.restrictScalars.{u} α).obj (ModuleCat.of C C))
      (LinearMap.exact_iff.2 hrange.symm) :)
  obtain ⟨hi, hx⟩ := StacksDraft.FlatComplex.lTensor_injective_and_exact_of_range_eq_ker dC N
    hsubC hexC ((ModuleCat.extendScalars.{u, u, u} α).map ι).hom hinjC
    (LinearMap.exact_iff.1 hexC0).symm B
  exact ⟨keyinj ι hi, key ι (L.d 0 1) hx⟩

/-- The kernel of the first differential of a complex of modules indexed by `ℕ` is the kernel of
the differential of its degree-zero short complex. -/
theorem ker_d_zero_one_eq {R : Type u} [CommRing R] (K : CochainComplex (ModuleCat.{u} R) ℕ) :
    LinearMap.ker (K.d 0 1).hom = LinearMap.ker (K.sc 0).g.hom := by
  have h : (ComplexShape.up ℕ).next 0 = 1 := CochainComplex.next ℕ 0
  have hinj : Function.Injective (K.XIsoOfEq h.symm).hom.hom :=
    (K.XIsoOfEq h.symm).toLinearEquiv.injective
  change LinearMap.ker (K.d 0 1).hom = LinearMap.ker (K.d 0 ((ComplexShape.up ℕ).next 0)).hom
  rw [← K.d_comp_XIsoOfEq_hom h.symm 0, ModuleCat.hom_comp, LinearMap.ker_comp,
    LinearMap.ker_eq_bot.2 hinj, Submodule.comap_bot]

/-- The degree-zero homology of a complex of modules indexed by `ℕ` is the kernel of its first
differential. -/
def kerEquivHomologyZero {R : Type u} [CommRing R] (K : CochainComplex (ModuleCat.{u} R) ℕ) :
    LinearMap.ker (K.d 0 1).hom ≃ₗ[R] K.homology 0 :=
  (LinearEquiv.ofEq (LinearMap.ker (K.d 0 1).hom) (LinearMap.ker (K.sc 0).g.hom)
      (ker_d_zero_one_eq K)).trans
    ((K.sc 0).moduleCatCyclesIso.symm ≪≫ K.isoHomologyπ₀).toLinearEquiv

/-- A complex of modules indexed by `ℕ` whose degree-zero homology is free of rank `n` has a
basis of `n` elements of the kernel of its first differential. -/
def basisKerOfHomologyZeroIso {R : Type u} [CommRing R] (K : CochainComplex (ModuleCat.{u} R) ℕ)
    {n : ℕ} (e : K.homology 0 ≅ ModuleCat.of R (ULift.{u} (Fin n → R))) :
    Module.Basis (Fin n) R (LinearMap.ker (K.d 0 1).hom) :=
  ((Pi.basisFun R (Fin n)).map (ULift.moduleEquiv (R := R)).symm).map
    ((kerEquivHomologyZero K).trans e.toLinearEquiv).symm

end Universal

section Main

open Stacks.Cech

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (F : X.Modules)

/-- **Cohomology and base change at a point whose fibre has no higher cohomology.** Let `A` be
Noetherian, `f : X ⟶ Spec A` proper and `F` a coherent `𝒪_X`-module flat over `A`, and let `p` be
a prime of `A` such that the fibre `X_p` has no cohomology of `F` in positive degrees. Then there
is `g ∉ p` such that for every `A_g`-algebra `B` (given by `ψ : A_g ⟶ B`) and every base change
`X'` of `X` to `B`, the pullback of `F` to `X'` has no cohomology in positive degrees, and its
global sections are the base change of `Γ(X, F)` along `A ⟶ B`, through the canonical pullback of
sections. -/
theorem exists_away_cohomologyBaseChange [IsNoetherianRing A] [IsProper f] [F.IsCoherent]
    (hflat : IsFlatOver f.toLRSHom.toShHom F)
    (p : Ideal A) [p.IsPrime] {Xp : Scheme.{u}} {fp : Xp ⟶ Spec (.of p.ResidueField)}
    {gp : Xp ⟶ X}
    (hsq : IsPullback gp fp f (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))
    (hvan : ∀ i : ℕ, 0 < i → Subsingleton
      (((moduleGlobalSections Xp).rightDerived i).obj ((Scheme.Modules.pullback gp).obj F))) :
    ∃ g : A, g ∉ p ∧ ∃ n : ℕ, ∀ {B : Type u} [CommRing B] (ψ : Localization.Away g →+* B)
      {X' : Scheme.{u}} {f' : X' ⟶ Spec (.of B)} {g' : X' ⟶ X}
      (hsq' : IsPullback g' f' f
        (Spec.map (CommRingCat.ofHom (ψ.comp (algebraMap A (Localization.Away g)))))),
      (∀ i : ℕ, 0 < i → Subsingleton
        (((moduleGlobalSections X').rightDerived i).obj ((Scheme.Modules.pullback g').obj F))) ∧
      letI : Algebra A B := (ψ.comp (algebraMap A (Localization.Away g))).toAlgebra
      letI := sectionsModule f F ⊤
      letI := sectionsModule f' ((Scheme.Modules.pullback g').obj F) (g' ⁻¹ᵁ ⊤)
      letI := baseSectionsModule g' F (ψ.comp (algebraMap A (Localization.Away g))) f' (g' ⁻¹ᵁ ⊤)
      letI := isScalarTowerBaseSections g' F (ψ.comp (algebraMap A (Localization.Away g))) f'
        (g' ⁻¹ᵁ ⊤)
      IsBaseChange B (pullbackSectionsBaseₗ g' F (ψ.comp (algebraMap A (Localization.Away g))) f f'
        (fun W => baseRingHom_comp_app _ f f' g' hsq' W) ⊤) ∧
      Nonempty (Module.Basis (Fin n) B Γ((Scheme.Modules.pullback g').obj F, g' ⁻¹ᵁ ⊤)) := by
  classical
  obtain ⟨hqc, -⟩ := CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  obtain ⟨I, hI, hlo, U, hU, hUaff, haff⟩ := exists_finiteAffineCover_of_isProper f
  obtain ⟨g, hg, hex, n, ⟨eH⟩⟩ :=
    exists_away_exactAt_alternating f U hU F hUaff haff hflat p hsq hvan
  refine ⟨g, hg, n, fun {B} _ ψ X' f' g' hsq' => ?_⟩
  set φ := ψ.comp (algebraMap A (Localization.Away g))
  let L := alternatingCechModuleComplex f U F
  have : ∀ n, Module.Flat A (L.X n) := alternatingCechModuleComplex_flat f U F hUaff hflat
  have hN : ∀ m, Fintype.card I < m → Subsingleton (L.X m) := fun m hm =>
    subsingleton_alternatingSubmodule f U F hm.le
  obtain ⟨hBex, hBrow⟩ := baseChange_exact_of_exactAt_localization L (Fintype.card I) hN g hex ψ
  let U' : I → X'.Opens := fun i => g' ⁻¹ᵁ U i
  have hU'eq : ∀ i, U' i = g' ⁻¹ᵁ U ((Equiv.refl I) i) := fun _ => rfl
  have : ((Scheme.Modules.pullback g').obj F).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback g' F
  let D := cechBaseChangeData φ f f' g' hsq' F U hUaff U' (Equiv.refl I) hU'eq
  have hU' : (⊤ : X'.Opens) = ⨆ i, U' i := top_eq_iSup_preimage g' U hU
  have haff' := iInf_preimage_isAffineOpen φ hsq' U hUaff
  constructor
  · intro i hi
    obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    have hz : IsZero ((alternatingCechModuleComplex f' U'
        ((Scheme.Modules.pullback g').obj F)).homology (n + 1)) :=
      ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (hBex n)).of_iso
        ((HomologicalComplex.homologyFunctor _ _ (n + 1)).mapIso D.alternatingIso).symm
    have hz' : IsZero ((baseAlternatingCechComplex f' U' hU'
        ((Scheme.Modules.pullback g').obj F)).homology ((n + 1 : ℕ) : ℤ)) :=
      hz.of_iso ((HomologicalComplex.homologyFunctor _ _ ((n + 1 : ℕ) : ℤ)).mapIso
          (baseAlternatingCechComplexIsoExtend f' U' hU' _) ≪≫
        HomologicalComplex.extendHomologyIso _ ComplexShape.embeddingUpNat
          (j := n + 1) (j' := ((n + 1 : ℕ) : ℤ)) rfl)
    exact (ModuleCat.subsingleton_of_isZero
      (hz'.of_iso (homologyBaseAlternatingCechComplexIso f' U' hU' _ haff' (n + 1)).symm) :)
  · let : Algebra A B := φ.toAlgebra
    have hbase : ∀ W : X.Opens,
        baseRingHom f W ≫ g'.app W = CommRingCat.ofHom φ ≫ baseRingHom f' (g' ⁻¹ᵁ W) :=
      fun W => baseRingHom_comp_app φ f f' g' hsq' W
    have hUW : ∀ i, U i ≤ (⊤ : X.Opens) := fun _ => le_top
    have hcov : (⊤ : X.Opens) ≤ ⨆ i, U i := hU.le
    have hUW' := preimage_le_of_le U hUW g' U' (Equiv.refl I) hU'eq
    have hcov' : g' ⁻¹ᵁ (⊤ : X.Opens) ≤ ⨆ i, U' i := le_top.trans hU'.le
    let := sectionsModule f F ⊤
    let := sectionsModule f' ((Scheme.Modules.pullback g').obj F) (g' ⁻¹ᵁ ⊤)
    let := baseSectionsModule g' F φ f' (g' ⁻¹ᵁ ⊤)
    let := isScalarTowerBaseSections g' F φ f' (g' ⁻¹ᵁ ⊤)
    let := cochainModule f U F 0
    let := cochainModule f U F 1
    let := cochainModule f' U' ((Scheme.Modules.pullback g').obj F) 0
    let := cochainModule f' U' ((Scheme.Modules.pullback g').obj F) 1
    let := baseAlternatingModule g' U' F φ f' 0
    let := baseAlternatingModule g' U' F φ f' 1
    let := isScalarTowerBaseAlternating g' U' F φ f' 0
    let := isScalarTowerBaseAlternating g' U' F φ f' 1
    have hd0 : (L.d 0 1).hom = alternatingCechModuleD f U F 0 := by
      rw [alternatingCechModuleComplex_d f U F 0]
      rfl
    have hrange := range_sectionsToAlternatingₗ f U F hUW hcov
    obtain ⟨inj₁, exact₁⟩ := hBrow (T := ModuleCat.of A Γ(F, ⊤))
      (ModuleCat.ofHom (sectionsToAlternatingₗ f U F hUW))
      (sectionsToAlternatingₗ_injective f U F hUW hcov) (by rwa [hd0])
    rw [hd0] at exact₁
    have hIBC : IsBaseChange B (pullbackSectionsBaseₗ g' F φ f f' hbase ⊤) := by
      refine StacksDraft.FlatComplex.isBaseChange_of_left_exact_of_baseChange B
        (pullbackSectionsBaseₗ g' F φ f f' hbase ⊤)
        (alternatingCochainBaseChangeₗ g' U U' (Equiv.refl I) F hU'eq φ f f' hbase 0)
        (alternatingCochainBaseChangeₗ g' U U' (Equiv.refl I) F hU'eq φ f f' hbase 1)
        (f := sectionsToAlternatingₗ f U F hUW) (g := alternatingCechModuleD f U F 0)
        (f' := sectionsToAlternatingₗ f' U' ((Scheme.Modules.pullback g').obj F) hUW')
        (g' := alternatingCechModuleD f' U' ((Scheme.Modules.pullback g').obj F) 0)
        ?_ ?_ (isBaseChange_alternatingCochainBaseChangeₗ g' U U' (Equiv.refl I) F hU'eq φ f f'
          hbase hsq' hUaff 0)
        (isBaseChange_alternatingCochainBaseChangeₗ g' U U' (Equiv.refl I) F hU'eq φ f f'
          hbase hsq' hUaff 1) exact₁ inj₁
        (LinearMap.exact_iff.2 (range_sectionsToAlternatingₗ f' U'
          ((Scheme.Modules.pullback g').obj F) hUW' hcov').symm)
        (sectionsToAlternatingₗ_injective f' U' ((Scheme.Modules.pullback g').obj F) hUW' hcov')
      · ext s
        exact congrArg Subtype.val (alternatingCochainBaseChangeₗ_sectionsToAlternatingₗ f U F hUW
          g' U' (Equiv.refl I) hU'eq φ f' hbase s)
      · ext s
        exact (cochainBaseChange_cechD g' U U' (Equiv.refl I) F hU'eq 0 s.1).symm
    set α := algebraMap A (Localization.Away g)
    let N := (ModuleCat.extendScalars.{u, u, u} α).obj (ModuleCat.of A Γ(F, ⊤))
    let LC := ((ModuleCat.extendScalars.{u, u, u} α).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj L
    let ιC : N ⟶ LC.X 0 := (ModuleCat.extendScalars.{u, u, u} α).map
      (ModuleCat.ofHom (sectionsToAlternatingₗ f U F hUW))
    have hfl : Module.Flat A ((ModuleCat.restrictScalars.{u} α).obj
        (ModuleCat.of (Localization.Away g) (Localization.Away g))) :=
      flat_restrictScalars_localization g
    have hinjC : Function.Injective ιC.hom :=
      Module.Flat.lTensor_preserves_injective_linearMap
        (M := (ModuleCat.restrictScalars.{u} α).obj
          (ModuleCat.of (Localization.Away g) (Localization.Away g)))
        (sectionsToAlternatingₗ f U F hUW) (sectionsToAlternatingₗ_injective f U F hUW hcov)
    have hexC : Function.Exact ιC.hom (LC.d 0 1).hom :=
      (Module.Flat.lTensor_exact (M := (ModuleCat.restrictScalars.{u} α).obj
          (ModuleCat.of (Localization.Away g) (Localization.Away g)))
        (LinearMap.exact_iff.2 hrange.symm :
          Function.Exact (sectionsToAlternatingₗ f U F hUW) (alternatingCechModuleD f U F 0)) :)
    let eN : N ≃ₗ[Localization.Away g] LinearMap.ker (LC.d 0 1).hom :=
      (LinearEquiv.ofInjective ιC.hom hinjC).trans
        (LinearEquiv.ofEq _ _ (LinearMap.exact_iff.1 hexC).symm)
    let bN : Module.Basis (Fin n) (Localization.Away g) N :=
      (basisKerOfHomologyZeroIso LC eH).map eN.symm
    let : Algebra (Localization.Away g) B := ψ.toAlgebra
    let b1 : Module.Basis (Fin n) B ((ModuleCat.extendScalars.{u, u, u} ψ).obj N) :=
      Algebra.TensorProduct.basis B bN
    let e1 := ((ModuleCat.extendScalarsComp α ψ).app (ModuleCat.of A Γ(F, ⊤))).toLinearEquiv
    let b2 : Module.Basis (Fin n) B
        ((ModuleCat.extendScalars.{u, u, u} (ψ.comp α)).obj (ModuleCat.of A Γ(F, ⊤))) :=
      b1.map e1.symm
    exact ⟨hIBC, ⟨b2.map hIBC.equiv⟩⟩

end Main

section FieldBridge

/-- The cohomology `cohomologyOverField k f G i` of a module on a scheme over a field is the
derived global sections of `G`, with the scalars restricted along `k → Γ(X, 𝒪_X)`; so its
vanishing is the vanishing of the derived global sections, in the form the hypothesis of
`exists_away_cohomologyBaseChange` takes. -/
theorem subsingleton_rightDerived_of_cohomologyOverField {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (G : X.Modules) (i : ℕ)
    (h : Subsingleton (cohomologyOverField k f G i)) :
    Subsingleton (((moduleGlobalSections X).rightDerived i).obj G) :=
  h

/-- **The pullback of sections in `exists_away_cohomologyBaseChange` is the canonical pullback of
sections** `AlgebraicGeometry.pullbackSectionHom`, at `⊤` and its preimage. -/
theorem pullbackSectionsBaseₗ_top_apply {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of B)) (g' : X' ⟶ X)
    (F : X.Modules)
    (hbase : ∀ W : X.Opens,
      Stacks.Cech.baseRingHom f W ≫ g'.app W =
        CommRingCat.ofHom φ ≫ Stacks.Cech.baseRingHom f' (g' ⁻¹ᵁ W)) (s : Γ(F, ⊤)) :
    Stacks.Cech.pullbackSectionsBaseₗ g' F φ f f' hbase ⊤ s =
      AlgebraicGeometry.pullbackSectionHom g' F ⊤ (g' ⁻¹ᵁ ⊤) le_rfl s := by
  have key : ∀ (V : X'.Opens) (x : ((Scheme.Modules.pullback g').obj F).presheaf.obj (op V)),
      ((Scheme.Modules.pullback g').obj F).presheaf.map (𝟙 (op V)) x = x := fun V x => by
    rw [CategoryTheory.Functor.map_id]
    rfl
  rw [AlgebraicGeometry.pullbackSectionHom,
    show (homOfLE (le_rfl : g' ⁻¹ᵁ (⊤ : X.Opens) ≤ g' ⁻¹ᵁ ⊤)).op = 𝟙 _ from rfl]
  exact (key (g' ⁻¹ᵁ ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app F).app ⊤ s)).symm

end FieldBridge

end Stacks.AlgebraicGeometry.ProperFlatGlobalSections

end
