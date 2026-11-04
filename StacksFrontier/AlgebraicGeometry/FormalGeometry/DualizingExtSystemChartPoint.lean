module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DualizingExtFunctorShift
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DualizingExtSystemChartVertex
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DualizingExtSystemChartTransport
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import StacksFrontier.RingTheory.AdicCompletion.QuotientDimensionSplit
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.LocalDualityKernelVanishing

/-!
# Stacks 0EHK, the per-point step at a prime of the chart ring

Let `B` be a Noetherian ring, `I_B` an ideal, `X` a finite `B`-module with adic tower
`T_n = X/I_B^{n+1}X`, `ω_B` a dualizing complex and `𝔮 ⊇ I_B` a prime. Write
`R = (B_𝔮)^∧_{I B_𝔮}`. If over `R` the complex `ω_B ⊗ᴸ R` becomes normalized after the shift
`[-e]`, and the canonical maps `H^{i-e}_𝔪(R ⊗ X) → H^{i-e}_𝔪(R ⊗ T_n)` reach the stable images of
the tower (the form of [Stacks, Tag 0EFR] proved in
`StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapCanonicalAdicQuotientRange`), then for
every `n` the kernel of `β_n : Ext^{-i}_B(T_n, ω_B) → Ext^{-i}_B(X, ω_B)` dies in some later term
after localizing at `𝔮`. This is the per-point paragraph of the source's proof: the local
duality theorem at `R`, flat base change of `Ext` along `B → R`, and faithful flatness of
`B_𝔮 → R`.

## Main results

* `Stacks.Algebraization.notMem_support_of_one_tmul_eq_zero` — a submodule all of whose elements
  die in `R ⊗_B -` is not supported at `𝔮`.
* `Stacks.Algebraization.exists_notMem_support_range_ker_of_localDuality` — the per-point step.

## References

* [Stacks Project, Tag 0EHK](https://stacks.math.columbia.edu/tag/0EHK)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization



section Point

variable {B : Type u} [CommRing B] [IsNoetherianRing B] (IB : Ideal B) (q : PrimeSpectrum B)

/-- The completed local ring `(B_𝔮)^∧_{I B_𝔮}`. -/
public abbrev pointCompletion : Type u :=
  AdicCompletion (IB.map (algebraMap B (Localization.AtPrime q.asIdeal)))
    (Localization.AtPrime q.asIdeal)

omit [IsNoetherianRing B] in
/-- **A submodule all of whose elements die in `B_𝔮 ⊗_B -` is not supported at `𝔮`.** -/
public theorem notMem_support_of_one_tmul_eq_zero {W : Type u} [AddCommGroup W] [Module B W]
    (Y : Submodule B W)
    (hY : ∀ y ∈ Y, ((1 : Localization.AtPrime q.asIdeal) ⊗ₜ[B] y :
      Localization.AtPrime q.asIdeal ⊗[B] W) = 0) :
    q ∉ Module.support B Y := by
  rw [Module.notMem_support_iff, LocalizedModule.subsingleton_iff]
  intro y
  have h3 : TensorProduct.mk B (Localization.AtPrime q.asIdeal) W 1 (y : W) =
      TensorProduct.mk B (Localization.AtPrime q.asIdeal) W 1 0 :=
    (hY y.1 y.2).trans (map_zero _).symm
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := q.asIdeal.primeCompl) h3
  exact ⟨c, c.2, Subtype.ext (hc.trans (smul_zero _))⟩

/-- **An element of a finite module over a Noetherian local ring which dies in the base change
to an adic completion at an ideal in the maximal ideal is zero**: the completion of a finite
module is its base change, and a finite module is Hausdorff there by Krull's intersection
theorem. -/
public theorem eq_zero_of_one_tmul_adicCompletion {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) {V : Type u}
    [AddCommGroup V] [Module R V] [Module.Finite R V] (v : V)
    (hv : ((1 : AdicCompletion I R) ⊗ₜ[R] v : AdicCompletion I R ⊗[R] V) = 0) : v = 0 := by
  have h1 := congrArg (AdicCompletion.ofTensorProduct I V) hv
  rw [AdicCompletion.ofTensorProduct_tmul, one_smul, map_zero] at h1
  have : IsHausdorff I V := IsHausdorff.of_le_jacobson I V
    (le_trans hI (IsLocalRing.maximalIdeal_le_jacobson ⊥))
  exact (AdicCompletion.of_injective I V) (h1.trans (map_zero _).symm)

/-- The comparison from the carrier of an extension of scalars to the tensor product,
`s ⊗ m ↦ s ⊗ m`. -/
public def extendScalarsToTensor {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).obj M →+ S ⊗[R] M :=
  (TensorProduct.lift
    { toFun := fun (x : (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) =>
        TensorProduct.mk R S M (show S from x)
      map_add' := fun x y => by
        ext m
        exact TensorProduct.add_tmul (show S from x) (show S from y) m
      map_smul' := fun r x => by
        ext m
        change ((algebraMap R S r * show S from x) ⊗ₜ[R] m : S ⊗[R] M) = r • ((show S from x) ⊗ₜ m)
        rw [← Algebra.smul_def, TensorProduct.smul_tmul'] }).toAddMonoidHom

/-- `extendScalarsToTensor` sends `s ⊗ m` to `s ⊗ m`. -/
public theorem extendScalarsToTensor_tmul {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (M : ModuleCat.{u} R) (s : S) (m : M) :
    extendScalarsToTensor M (s ⊗ₜ[R, algebraMap R S] m) = s ⊗ₜ[R] m :=
  rfl

/-- An element killed by a natural transformation's target map... (helper): kernels transfer
across a natural isomorphism of contravariant functors. -/
public theorem map_eq_zero_iff_of_natIso {C : Type*} [Category C] {R : Type u} [Ring R]
    {F G : Cᵒᵖ ⥤ ModuleCat.{u} R} (e : F ≅ G) {X Y : C} (g : X ⟶ Y) (y : F.obj (op Y)) :
    (F.map g.op).hom y = 0 ↔ (G.map g.op).hom ((e.hom.app (op Y)).hom y) = 0 := by
  have hn := congrArg (fun φ => φ.hom y) (e.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hn
  rw [← hn]
  exact ⟨fun h => by rw [h, map_zero], fun h =>
    (ConcreteCategory.bijective_of_isIso (e.hom.app (op X))).1 (h.trans (map_zero _).symm)⟩

/-- `(B_𝔮)^∧` is local. -/
public theorem isLocalRing_pointCompletion (hq : IB ≤ q.asIdeal) :
    IsLocalRing (pointCompletion IB q) :=
  Stacks.AdicCompletionDimension.isLocalRing_adicCompletion_of_le_maximalIdeal _ (by
    rw [Ideal.map_le_iff_le_comap]
    exact hq.trans (IsLocalization.AtPrime.comap_maximalIdeal (Localization.AtPrime q.asIdeal)
      q.asIdeal).ge)

/-- `(B_𝔮)^∧` is Noetherian. -/
public instance isNoetherianRing_pointCompletion : IsNoetherianRing (pointCompletion IB q) :=
  AdicCompletion.isNoetherianRing _

/-- `B → (B_𝔮)^∧` is flat. -/
public theorem flat_algebraMap_pointCompletion : (algebraMap B (pointCompletion IB q)).Flat := by
  rw [RingHom.flat_algebraMap_iff]
  have : Module.Flat B (Localization.AtPrime q.asIdeal) :=
    IsLocalization.flat _ q.asIdeal.primeCompl
  have : Module.Flat (Localization.AtPrime q.asIdeal) (pointCompletion IB q) :=
    AdicCompletion.flat_of_isNoetherian _
  exact Module.Flat.trans B (Localization.AtPrime q.asIdeal) (pointCompletion IB q)

open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars) in
/-- The dualizing complex `ω_B` transported to `B_𝔮`. -/
public abbrev pointLocalComplex (ωB : DerivedCategory (ModuleCat.{u} B)) :
    DerivedCategory (ModuleCat.{u} (Localization.AtPrime q.asIdeal)) :=
  (totalDerivedExtensionScalars.{u, u, u}
    (algebraMap B (Localization.AtPrime q.asIdeal))).functor.obj ωB

open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars) in
/-- The dualizing complex `ω_B` transported to `(B_𝔮)^∧`. -/
public abbrev pointCompletionComplex (ωB : DerivedCategory (ModuleCat.{u} B)) :
    DerivedCategory (ModuleCat.{u} (pointCompletion IB q)) :=
  (totalDerivedExtensionScalars.{u, u, u}
    (algebraMap (Localization.AtPrime q.asIdeal) (pointCompletion IB q))).functor.obj
      (pointLocalComplex q ωB)

/-- The base change comparison along a flat `A → S` with the chosen derived extension of scalars
is invertible at a finite module. -/
private theorem isIso_dualizingExtFunctorBaseChange_app_totalDerived {A S : Type u} [CommRing A]
    [IsNoetherianRing A] [CommRing S] [Algebra A S] (hf : (algebraMap A S).Flat)
    (ω : DerivedCategory (ModuleCat.{u} A)) (hωge : ∃ b : ℤ, ω.IsGE b) (i : ℤ)
    (K : ModuleCat.{u} A) [Module.Finite A K] :
    let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A S)
    IsIso (((@dualizingExtFunctorBaseChange A S _ _ _ D.functor D.comparison D.isLeftDerived hf ω
      i)).app (op K)) := by
  intro D
  exact @isIso_dualizingExtFunctorBaseChange_app A S _ _ _ D.functor D.comparison D.isLeftDerived
    _ hf ω hωge i K inferInstance

open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars) in
/-- The base change comparison along `B → B_𝔮` is invertible at a finite module. -/
public theorem isIso_pointLocalBaseChange_app (ωB : DerivedCategory (ModuleCat.{u} B))
    (hωB : Dualizing.IsDualizingComplex ωB) (i : ℤ) (K : ModuleCat.{u} B) [Module.Finite B K] :
    IsIso ((dualizingExtFunctorLocalizationBaseChange q.asIdeal.primeCompl ωB i).app (op K)) :=
  isIso_dualizingExtFunctorBaseChange_app_totalDerived
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ q.asIdeal.primeCompl)) ωB
    (exists_isGE_of_isDualizingComplex ωB hωB) i K

open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars) in
/-- The base change comparison along `B_𝔮 → (B_𝔮)^∧` is invertible at a finite module. -/
public theorem isIso_pointCompletionBaseChange_app (ωB : DerivedCategory (ModuleCat.{u} B))
    (hωB : Dualizing.IsDualizingComplex ωB) (i : ℤ)
    (K : ModuleCat.{u} (Localization.AtPrime q.asIdeal))
    [Module.Finite (Localization.AtPrime q.asIdeal) K] :
    IsIso ((dualizingExtFunctorAdicCompletionBaseChange
      (IB.map (algebraMap B (Localization.AtPrime q.asIdeal))) (pointLocalComplex q ωB) i).app
        (op K)) :=
  isIso_dualizingExtFunctorBaseChange_app_totalDerived
    (RingHom.flat_algebraMap_iff.mpr (AdicCompletion.flat_of_isNoetherian _)) _
    (exists_isGE_of_isDualizingComplex _
      (Dualizing.isDualizingComplex_totalDerivedExtensionScalars_isLocalization
        q.asIdeal.primeCompl ωB hωB)) i K

/-- The adic tower of a `B`-module, transported to `(B_𝔮)^∧` through `B_𝔮`. -/
public abbrev pointTower (X : ModuleCat.{u} B) : ℕᵒᵖ ⥤ ModuleCat.{u} (pointCompletion IB q) :=
  Stacks.Examples.adicQuotientTower IB X ⋙
    ModuleCat.extendScalars.{u, u, u} (algebraMap B (Localization.AtPrime q.asIdeal)) ⋙
      ModuleCat.extendScalars.{u, u, u}
        (algebraMap (Localization.AtPrime q.asIdeal) (pointCompletion IB q))

/-- The projections of a `B`-module onto its adic tower, transported to `(B_𝔮)^∧`. -/
public abbrev pointTowerProj (X : ModuleCat.{u} B) (n : ℕ) :
    (ModuleCat.extendScalars.{u, u, u}
        (algebraMap (Localization.AtPrime q.asIdeal) (pointCompletion IB q))).obj
      ((ModuleCat.extendScalars.{u, u, u} (algebraMap B (Localization.AtPrime q.asIdeal))).obj X)
      ⟶ (pointTower IB q X).obj (op n) :=
  (ModuleCat.extendScalars.{u, u, u}
      (algebraMap (Localization.AtPrime q.asIdeal) (pointCompletion IB q))).map
    ((ModuleCat.extendScalars.{u, u, u} (algebraMap B (Localization.AtPrime q.asIdeal))).map
      (ModuleCat.ofHom (Submodule.mkQ _)))

/-- **Stacks 0EHK, the per-point step at a prime of the chart ring.** Let `𝔮 ⊇ I_B` be a prime of
the Noetherian ring `B`, `X` a finite `B`-module with adic tower `T`, `ω_B` a dualizing complex,
and write `R = (B_𝔮)^∧`. Suppose that `ω_R[-e]` is normalized and that over `R` the canonical maps
`H^{i-e}_𝔪(R ⊗ X) → H^{i-e}_𝔪(R ⊗ T_n)` reach the stable images of the tower. Then for every `n`
the kernel of `Ext^{-i}_B(T_n, ω_B) → Ext^{-i}_B(X, ω_B)` dies, after localizing at `𝔮`, in some
later `Ext^{-i}_B(T_m, ω_B)`. -/
public theorem exists_notMem_support_range_ker_of_localDuality (hq : IB ≤ q.asIdeal)
    (X : ModuleCat.{u} B) [Module.Finite B X] (ωB : DerivedCategory (ModuleCat.{u} B))
    (hωB : Dualizing.IsDualizingComplex ωB) (i e : ℤ)
    (hnorm : letI := isLocalRing_pointCompletion IB q hq
      Dualizing.IsNormalizedDualizingComplex.{u, u} ((pointCompletionComplex IB q ωB)⟦-e⟧))
    (hsurj : letI := isLocalRing_pointCompletion IB q hq
      ∀ n : ℕ, ∃ m : ℕ, ∃ h : n ≤ m,
        LinearMap.range ((Stacks.LocalCohomology.localCohomologyModuleFunctor
            (pointCompletion IB q) (i - e)).map ((pointTower IB q X).map (homOfLE h).op)).hom ≤
          LinearMap.range ((Stacks.LocalCohomology.localCohomologyModuleFunctor
            (pointCompletion IB q) (i - e)).map (pointTowerProj IB q X n)).hom) :
    ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), q ∉ Module.support B
      (LinearMap.range (((dualizingExtSystem (Stacks.Examples.adicQuotientTower IB X) ωB i).map
          (homOfLE h)).hom ∘ₗ (LinearMap.ker ((dualizingExtFunctor ωB i).map
            (ModuleCat.ofHom (Submodule.mkQ _) :
              X ⟶ (Stacks.Examples.adicQuotientTower IB X).obj (op n)).op).hom).subtype)) := by
  let := isLocalRing_pointCompletion IB q hq
  let Bq := Localization.AtPrime q.asIdeal
  let R := pointCompletion IB q
  let e₁ := ModuleCat.extendScalars.{u, u, u} (algebraMap B Bq)
  let e₂ := ModuleCat.extendScalars.{u, u, u} (algebraMap Bq R)
  let T := Stacks.Examples.adicQuotientTower IB X
  let ωq := pointLocalComplex q ωB
  let ωR := pointCompletionComplex IB q ωB
  let θ₁ := dualizingExtFunctorLocalizationBaseChange q.asIdeal.primeCompl ωB i
  let θ₂ := dualizingExtFunctorAdicCompletionBaseChange (IB.map (algebraMap B Bq)) ωq i
  -- the composite comparison `Ext_B(K, ω_B) → Ext_R(R ⊗ K, ω_R)`
  let u₁ : ∀ K : ModuleCat.{u} B, (dualizingExtFunctor ωB i).obj (op K) →ₗ[B]
      (ModuleCat.restrictScalars (algebraMap B Bq)).obj
        (e₁.obj ((dualizingExtFunctor ωB i).obj (op K))) := fun K =>
    ((ModuleCat.extendRestrictScalarsAdj (algebraMap B Bq)).unit.app _).hom
  let u₂ : ∀ K : ModuleCat.{u} B, (dualizingExtFunctor ωq i).obj (op (e₁.obj K)) →ₗ[Bq]
      (ModuleCat.restrictScalars (algebraMap Bq R)).obj
        (e₂.obj ((dualizingExtFunctor ωq i).obj (op (e₁.obj K)))) := fun K =>
    ((ModuleCat.extendRestrictScalarsAdj (algebraMap Bq R)).unit.app _).hom
  let Θ : ∀ K : ModuleCat.{u} B, (dualizingExtFunctor ωB i).obj (op K) →
      (dualizingExtFunctor ωR i).obj (op (e₂.obj (e₁.obj K))) := fun K x =>
    (θ₂.app (op (e₁.obj K))).hom (u₂ K ((θ₁.app (op K)).hom (u₁ K x)))
  have hΘ0 : ∀ K : ModuleCat.{u} B, Θ K 0 = 0 := fun K => by
    let Θ' : (dualizingExtFunctor ωB i).obj (op K) →+
        (dualizingExtFunctor ωR i).obj (op (e₂.obj (e₁.obj K))) :=
      (θ₂.app (op (e₁.obj K))).hom.toAddMonoidHom.comp ((u₂ K).toAddMonoidHom.comp
        ((θ₁.app (op K)).hom.toAddMonoidHom.comp (u₁ K).toAddMonoidHom))
    exact Θ'.map_zero
  have hΘ : ∀ {K K' : ModuleCat.{u} B} (g : K ⟶ K') (y : (dualizingExtFunctor ωB i).obj (op K')),
      Θ K ((dualizingExtFunctor ωB i).map g.op |>.hom y) =
        ((dualizingExtFunctor ωR i).map (e₂.map (e₁.map g)).op).hom (Θ K' y) := by
    intro K K' g y
    have h1 := congrArg (fun φ => φ.hom (u₁ K' y)) (θ₁.naturality g.op)
    have h2 := congrArg (fun φ => φ.hom (u₂ K' ((θ₁.app (op K')).hom (u₁ K' y))))
      (θ₂.naturality (e₁.map g).op)
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp] at h1 h2
    show (θ₂.app (op (e₁.obj K))).hom (u₂ K ((θ₁.app (op K)).hom
      (u₁ K (((dualizingExtFunctor ωB i).map g.op).hom y)))) = _
    have h1' : (θ₁.app (op K)).hom (u₁ K (((dualizingExtFunctor ωB i).map g.op).hom y)) =
        ((dualizingExtFunctor ωq i).map (e₁.map g).op).hom
          ((θ₁.app (op K')).hom (u₁ K' y)) := h1
    rw [h1']
    exact h2
  have hfin₁ : ∀ (K : ModuleCat.{u} B) [Module.Finite B K], Module.Finite Bq (e₁.obj K) :=
    fun K _ => Stacks.DerivedTensorHomDiagonal.finite_extendScalars (algebraMap B Bq) K
  have hfin₂ : ∀ (K : ModuleCat.{u} B) [Module.Finite B K], Module.Finite R (e₂.obj (e₁.obj K)) :=
    fun K _ => have := hfin₁ K
      Stacks.DerivedTensorHomDiagonal.finite_extendScalars (algebraMap Bq R) (e₁.obj K)
  have hωq : Dualizing.IsDualizingComplex ωq :=
    Dualizing.isDualizingComplex_totalDerivedExtensionScalars_isLocalization
      q.asIdeal.primeCompl ωB hωB
  -- `Θ` is injective at a finite module, up to localization at `𝔮`
  have hΘinj : ∀ (K : ModuleCat.{u} B) [Module.Finite B K]
      (z : (dualizingExtFunctor ωB i).obj (op K)),
      Θ K z = 0 → ((1 : Bq) ⊗ₜ[B] z : Bq ⊗[B] (dualizingExtFunctor ωB i).obj (op K)) = 0 := by
    intro K _ z hz
    have := isIso_pointLocalBaseChange_app q ωB hωB i K
    have := hfin₁ K
    have := isIso_pointCompletionBaseChange_app IB q ωB hωB i (e₁.obj K)
    have : Module.Finite Bq ((dualizingExtFunctor ωq i).obj (op (e₁.obj K))) :=
      finite_dualizingExtFunctor_obj _ inferInstance ωq hωq i
    have h2 : u₂ K ((θ₁.app (op K)).hom (u₁ K z)) = 0 :=
      (ConcreteCategory.bijective_of_isIso (θ₂.app (op (e₁.obj K)))).1
        (hz.trans (map_zero _).symm)
    have h3 := (congrArg (extendScalarsToTensor (S := R)
      ((dualizingExtFunctor ωq i).obj (op (e₁.obj K)))) h2).trans (map_zero _)
    have h4 := eq_zero_of_one_tmul_adicCompletion (IB.map (algebraMap B Bq)) (by
      rw [Ideal.map_le_iff_le_comap]
      exact hq.trans (IsLocalization.AtPrime.comap_maximalIdeal Bq q.asIdeal).ge) _ h3
    have h5 : u₁ K z = 0 :=
      (ConcreteCategory.bijective_of_isIso (θ₁.app (op K))).1 (h4.trans (map_zero _).symm)
    exact (congrArg (extendScalarsToTensor (S := Bq)
      ((dualizingExtFunctor ωB i).obj (op K))) h5).trans (map_zero _)
  -- local duality at `R`, in the normalized degree
  have hfinT : ∀ n : ℕ, Module.Finite R ((pointTower IB q X).obj (op n)) := fun n => by
    have : Module.Finite B (T.obj (op n)) := Module.Finite.quotient B _
    exact hfin₂ _
  have hPP := Dualizing.LocalDuality.exists_map_eq_zero_of_dualizingExt_ker
    ((pointCompletionComplex IB q ωB)⟦-e⟧) hnorm (i - e) (e₂.obj (e₁.obj X)) (pointTower IB q X)
    hfinT (pointTowerProj IB q X) hsurj
  let Φ := dualizingExtFunctorShiftNeg ωR e i
  intro n
  obtain ⟨m, h, hm⟩ := hPP n
  refine ⟨m, h, notMem_support_of_one_tmul_eq_zero q _ ?_⟩
  rintro _ ⟨⟨x, hx0⟩, rfl⟩
  have : Module.Finite B (T.obj (op m)) := Module.Finite.quotient B _
  refine hΘinj (T.obj (op m)) _ ?_
  refine (hΘ (T.map (homOfLE h).op) x).trans ?_
  have hx : Θ X (((dualizingExtFunctor ωB i).map (ModuleCat.ofHom (Submodule.mkQ _) :
      X ⟶ T.obj (op n)).op).hom x) = 0 := by
    rw [LinearMap.mem_ker.mp hx0]
    exact hΘ0 X
  rw [hΘ] at hx
  have hx' := (map_eq_zero_iff_of_natIso Φ _ _).mp hx
  have := hm _ hx'
  exact (map_eq_zero_iff_of_natIso Φ _ _).mpr this

end Point

end Stacks.Algebraization

end
