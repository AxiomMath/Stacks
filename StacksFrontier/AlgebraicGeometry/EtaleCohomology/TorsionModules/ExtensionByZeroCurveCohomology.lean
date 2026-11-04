module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.ConstructibleCurveCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification

/-!
# Cohomology of extensions by zero of constructible torsion sheaves into a curve

Let `k` be an algebraically closed field, `Y` a separated scheme of finite type over `k` of
dimension at most one, `t : X ⟶ Y` an étale morphism from a quasi-compact quasi-separated scheme,
`Λ` a Noetherian ring, and `F` a constructible sheaf of `Λ`-modules on `X_étale` whose torsion is
prime to an integer `p`. If every prime prime to `p` is prime to the characteristic of `k`, or `Y`
is proper, then `H^q(Y, t_!F)` is a finite `Λ`-module for every `q`.

For `t` the identity this is Tag 0GJI
(`module_finite_etaleCohomology_of_isPrimeToCharacteristicTorsion_of_forall`); for `t` the open
immersion of `X` into the closure of `X` in a compactification it is the input of Tag 0GKR. The
proof is the same descending induction on `q`, with the generators `j_{U!}Λ̲` of `X_étale` carried
to `Y` by `t_!`: `t_! j_{U!} = (t ∘ j_U)_!`.

## Main results

* `exists_nsmul_id_eq_zero_of_isBigSiteConstructibleEtaleModule`: a constructible sheaf whose
  torsion is prime to `p` on a quasi-compact quasi-separated scheme is killed by a single positive
  integer prime to `p`.
* `module_finite_etaleCohomology_extensionByZero_of_forall`: the finiteness statement above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

attribute [-instance] hasSheafifyEtale

attribute [local instance] moduleCat_hasLimitsOfSize SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 10000] hasColimit_discrete_fin_etaleModules

section Exponent

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

/-- **A constructible sheaf of `Λ`-modules whose torsion is prime to `p`, on a quasi-compact
quasi-separated scheme, is killed by a single positive integer prime to `p`.** It is a quotient of
a finite direct sum of generators `j_{U!}Λ̲` with `U` affine, and each summand of the quotient map
is killed by such an integer (`exists_nsmul_eq_zero_of_hom_etaleModuleShriekConstant`). -/
theorem exists_nsmul_id_eq_zero_of_isBigSiteConstructibleEtaleModule [CompactSpace X.obj]
    [QuasiSeparatedSpace X.obj] (p : ℕ) (F : EtaleModules.{u, r} Λ X.obj)
    (hc : IsBigSiteConstructibleEtaleModule B X Λ F)
    (ht : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.obj.smallEtaleTopology p
      ((etaleModuleForgetAb.{u, r} Λ X.obj).obj F)) :
    ∃ N : ℕ, 0 < N ∧ N.Coprime p ∧ N • 𝟙 F = 0 := by
  classical
  obtain ⟨n, V, hV, φ, hφ⟩ := exists_epi_sigma_smallEtaleShriekGenerator B X Λ F hc
  have hN : ∀ i, ∃ N : ℕ, 0 < N ∧ N.Coprime p ∧
      N • (Sigma.ι (fun i => smallEtaleShriekGenerator B X Λ (V i)) i ≫ φ) = 0 := fun i => by
    have : Etale (B.inclusion.map (V i).obj.hom) := (V i).property
    have : IsAffine (B.inclusion.obj (V i).obj.left) := hV i
    exact exists_nsmul_eq_zero_of_hom_etaleModuleShriekConstant p F ht
      (B.inclusion.map (V i).obj.hom) _
  choose N hN0 hNp hNφ using hN
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN0 i, Nat.Coprime.prod_left fun i _ => hNp i,
    (cancel_epi φ).1 ?_⟩
  rw [comp_zero, Preadditive.comp_nsmul, Category.comp_id]
  refine Sigma.hom_ext _ _ fun i => ?_
  obtain ⟨c, hc⟩ : N i ∣ ∏ i, N i := Finset.dvd_prod_of_mem N (Finset.mem_univ i)
  rw [Preadditive.comp_nsmul, comp_zero, hc, mul_nsmul, hNφ i, smul_zero]

end Exponent

section Generators

/-- An additive functor carries `N • 𝟙 X` to `N • 𝟙 (F.obj X)`. -/
private theorem map_nsmul_id {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (F : C ⥤ D) [F.Additive] (N : ℕ) (X : C) :
    F.map (N • 𝟙 X) = N • 𝟙 (F.obj X) := by
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (π : Y ⟶ Spec (.of k))
  [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π] (Λ : Type r) [CommRing Λ]
  [IsNoetherianRing Λ]

/-- **The cohomology of `e_!(Λ/N)̲` on a curve is finite**, for an étale `e : W ⟶ Y` with `W`
affine and an integer `N > 0` prime to `p`: the `𝔽_ℓ`-basis trick for `M ↦ e_!(M̲)` at `M = Λ/N`,
with input the finiteness of `H^q(Y, e_!(ℤ/ℓ))` for the primes `ℓ ∣ N`. -/
theorem module_finite_etaleCohomology_cokernel_nsmul_etaleModuleShriekConstant
    (hdim : topologicalKrullDim Y ≤ 1) (p : ℕ)
    (hp : ∀ ℓ : ℕ, ℓ.Prime → ℓ.Coprime p → ℓ.Coprime (ringExpChar k) ∨ IsProper π)
    {W : Scheme.{u}} (e : W ⟶ Y) [Etale e] [IsAffine W] (N : ℕ) (hN : 0 < N)
    (hNp : N.Coprime p) (q : ℕ) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ Y).rightDerived q).obj
      (cokernel (N • 𝟙 ((etaleModuleShriekConstant.{u, r} Λ e).obj
        (ModuleCat.of Λ (ULift.{max (u + 1) r} Λ)))))) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace π
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated π
  let M₀ := ModuleCat.of Λ (ULift.{max (u + 1) r} Λ)
  let C₀ : ModuleCat.{max (u + 1) r} Λ := cokernel (N • 𝟙 M₀)
  let T := etaleModuleShriekConstant.{u, r} Λ e
  let iso : T.obj C₀ ≅ cokernel (N • 𝟙 (T.obj M₀)) :=
    PreservesCokernel.iso T (N • 𝟙 M₀) ≪≫ cokernelIsoOfEq (map_nsmul_id T N M₀)
  have : Module.Finite Λ C₀ :=
    Module.Finite.of_surjective (cokernel.π (N • 𝟙 M₀)).hom
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  have hM : ∀ m : C₀, N • m = 0 := fun m => by
    obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (cokernel.π (N • 𝟙 M₀))).1
      inferInstance m
    rw [← map_nsmul]
    exact congrArg (fun f => f.hom y) (cokernel.condition (N • 𝟙 M₀))
  have hfin := module_finite_etaleCohomology_etaleModuleShriekConstant e N hN
    (fun ℓ hℓ hdvd q' => finite_rightDerived_etaleAbelianShriekConstant_zmod_of_isAffine π hdim e
      ℓ hℓ (hp ℓ hℓ (Nat.Coprime.coprime_dvd_left hdvd hNp)) q') C₀ hM q
  exact Module.Finite.equiv
    (((etaleModuleGlobalSections.{u, r} Λ Y).rightDerived q).mapIso iso).toLinearEquiv

omit [IsNoetherianRing Λ] in
include π in
/-- **The cohomology above degree two of a sheaf on a curve killed by a positive integer is
finite**, since it vanishes (Tag 0A53). -/
theorem module_finite_etaleCohomology_of_nsmul_id_eq_zero_of_two_lt
    (hdim : topologicalKrullDim Y ≤ 1) (G : EtaleModules.{u, r} Λ Y) (N : ℕ) (hN : 0 < N)
    (hG : N • 𝟙 G = 0) (q : ℕ) (hq : 2 < q) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ Y).rightDerived q).obj G) := by
  have htor := isPrimeToCharacteristicTorsion_of_nsmul_id_eq_zero 1
    ((etaleModuleForgetAb.{u, r} Λ Y).obj G) N hN (Nat.coprime_one_right N)
    (by rw [← map_nsmul_id, hG, Functor.map_zero])
  have hG' : Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology
      ((etaleModuleForgetAb.{u, r} Λ Y).obj G) := fun V x => by
    obtain ⟨R, hR, h⟩ := htor V x
    exact ⟨R, hR, fun W g hg => by
      obtain ⟨n, hn, -, hz⟩ := h W g hg
      exact ⟨n, hn, hz⟩⟩
  have := subsingleton_etaleModuleCohomology_of_two_lt π hdim G hG' q hq
  have : Finite (((etaleModuleGlobalSections.{u, r} Λ Y).rightDerived q).obj G) :=
    Finite.of_subsingleton
  exact Module.Finite.of_finite

end Generators

section Main

variable {k : Type u} [Field k] [IsAlgClosed k] (B : BigEtaleSite.{u}) (X : B.Scheme)
  [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] {Y : Scheme.{u}} (π : Y ⟶ Spec (.of k))
  [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π] (t : X.obj ⟶ Y) [Etale t]
  (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

omit [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] in
/-- **The cohomology of `t_!` of `j_{V!}(Λ/N)̲` on a curve is finite**, for `V` affine and étale
over `X` and an integer `N > 0` prime to `p`, since `t_! j_{V!} = (t ∘ j_V)_!`. -/
theorem module_finite_etaleCohomology_extensionByZero_cokernel_nsmul_smallEtaleShriekGenerator
    (hdim : topologicalKrullDim Y ≤ 1) (p : ℕ)
    (hp : ∀ ℓ : ℕ, ℓ.Prime → ℓ.Coprime p → ℓ.Coprime (ringExpChar k) ∨ IsProper π)
    (V : SmallEtale B X.obj X.property) (hV : IsAffine V.obj.left.obj) (N : ℕ) (hN : 0 < N)
    (hNp : N.Coprime p) (q : ℕ) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ Y).rightDerived q).obj
      ((etaleModuleExtensionByZero.{u, r} Λ t).obj
        (cokernel (N • 𝟙 (smallEtaleShriekGenerator B X Λ V))))) := by
  have : Etale (B.inclusion.map V.obj.hom) := V.property
  have : IsAffine (B.inclusion.obj V.obj.left) := hV
  let L := etaleModuleExtensionByZero.{u, r} Λ t
  let P := smallEtaleShriekGenerator B X Λ V
  let e := B.inclusion.map V.obj.hom ≫ t
  let M₀ := ModuleCat.of Λ (ULift.{max (u + 1) r} Λ)
  let eP : L.obj P ≅ (etaleModuleShriekConstant.{u, r} Λ e).obj M₀ :=
    ((etaleModuleExtensionByZeroCompIso.{u, r} Λ (B.inclusion.map V.obj.hom) t).app
      ((constantSheaf (B.inclusion.obj V.obj.left).smallEtaleTopology
        (ModuleCat.{max (u + 1) r} Λ)).obj M₀)).symm
  have hcomm : (N • 𝟙 (L.obj P)) ≫ eP.hom = eP.hom ≫ (N • 𝟙 _) := by
    rw [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]
  let eQ : L.obj (cokernel (N • 𝟙 P)) ≅
      cokernel (N • 𝟙 ((etaleModuleShriekConstant.{u, r} Λ e).obj M₀)) :=
    PreservesCokernel.iso L (N • 𝟙 P) ≪≫ cokernelIsoOfEq (map_nsmul_id L N P) ≪≫
      cokernel.mapIso _ _ eP eP hcomm
  have hfin := module_finite_etaleCohomology_cokernel_nsmul_etaleModuleShriekConstant π Λ hdim
    p hp e N hN hNp q
  exact Module.Finite.equiv
    (((etaleModuleGlobalSections.{u, r} Λ Y).rightDerived q).mapIso eQ).symm.toLinearEquiv

omit [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] [IsNoetherianRing Λ] in
/-- **The cohomology of `t_!` of a finite direct sum is finite** if that of `t_!` of each summand
is. -/
theorem module_finite_etaleCohomology_extensionByZero_sigma (q : ℕ) {n : ℕ}
    (Q : Fin n → EtaleModules.{u, r} Λ X.obj)
    (hQ : ∀ i, Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ Y).rightDerived q).obj
      ((etaleModuleExtensionByZero.{u, r} Λ t).obj (Q i)))) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ Y).rightDerived q).obj
      ((etaleModuleExtensionByZero.{u, r} Λ t).obj (∐ Q))) := by
  let L := etaleModuleExtensionByZero.{u, r} Λ t
  have := (hasFiniteCoproducts_etaleModules Λ X.obj).out n
  have := (hasFiniteCoproducts_etaleModules Λ Y).out n
  have : PreservesColimitsOfShape (Discrete (Fin n)) L :=
    (etaleModuleExtensionByZeroAdj.{u, r} Λ t).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  have := module_finite_etaleModuleCohomology_sigma q (fun i => L.obj (Q i)) hQ
  exact Module.Finite.equiv
    (((etaleModuleGlobalSections.{u, r} Λ Y).rightDerived q).mapIso
      (PreservesCoproduct.iso L Q)).symm.toLinearEquiv

/-- **The induction step for the finiteness of the cohomology of `t_!G`**: if `H^{q+1}(Y, t_!K)` is
finite for every constructible `K` killed by `N`, then so is `H^q(Y, t_!G)` for every constructible
`G` killed by `N`. With `G` a quotient of `⊕_i j_{U_i!}(Λ/N)̲` with kernel `K`, the sequence
`H^q(Y, t_!(⊕_i j_{U_i!}(Λ/N)̲)) ⟶ H^q(Y, t_!G) ⟶ H^{q+1}(Y, t_!K)` is exact with finite outer
terms. -/
theorem module_finite_etaleCohomology_extensionByZero_of_module_finite_succ
    (hdim : topologicalKrullDim Y ≤ 1) (p : ℕ)
    (hp : ∀ ℓ : ℕ, ℓ.Prime → ℓ.Coprime p → ℓ.Coprime (ringExpChar k) ∨ IsProper π) (q : ℕ)
    (N : ℕ) (hN : 0 < N) (hNp : N.Coprime p)
    (ih : ∀ K : EtaleModules.{u, r} Λ X.obj, IsBigSiteConstructibleEtaleModule B X Λ K →
      N • 𝟙 K = 0 → Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ Y).rightDerived
        (q + 1)).obj ((etaleModuleExtensionByZero.{u, r} Λ t).obj K)))
    (G : EtaleModules.{u, r} Λ X.obj) (hcG : IsBigSiteConstructibleEtaleModule B X Λ G)
    (hNG : N • 𝟙 G = 0) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ Y).rightDerived q).obj
      ((etaleModuleExtensionByZero.{u, r} Λ t).obj G)) := by
  classical
  have := isWeakSerreClass_isBigSiteConstructibleEtaleModule B X Λ
  let L := etaleModuleExtensionByZero.{u, r} Λ t
  obtain ⟨n, V, hV, φ, hφ⟩ := exists_epi_sigma_smallEtaleShriekGenerator B X Λ G hcG
  let P := fun i => smallEtaleShriekGenerator B X Λ (V i)
  have hNφ : ∀ i, N • (Sigma.ι P i ≫ φ) = 0 := fun i => by
    rw [← Preadditive.comp_nsmul,
      show N • φ = φ ≫ (N • 𝟙 G) by rw [Preadditive.comp_nsmul, Category.comp_id],
      hNG, comp_zero, comp_zero]
  let Q := fun i => cokernel (N • 𝟙 (P i))
  let φ' : ∀ i, Q i ⟶ G := fun i => cokernel.desc _ (Sigma.ι P i ≫ φ)
    (by rw [Preadditive.nsmul_comp, Category.id_comp, hNφ i])
  let Φ : (∐ Q) ⟶ G := Sigma.desc φ'
  have hfac : Limits.Sigma.map (fun i => cokernel.π (N • 𝟙 (P i))) ≫ Φ = φ := by
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [Sigma.ι_map_assoc, Sigma.ι_desc, cokernel.π_desc]
  have : Epi Φ := by
    rw [← hfac] at hφ
    exact epi_of_epi (Limits.Sigma.map fun i => cokernel.π (N • 𝟙 (P i))) Φ
  let S := ShortComplex.mk (kernel.ι Φ) Φ (kernel.condition Φ)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (S.exact_of_f_is_kernel (kernelIsKernel Φ)) inferInstance
      inferInstance
  have hgen : ∀ i, IsBigSiteConstructibleEtaleModule B X Λ (P i) := fun i => by
    have : IsAffine (V i).obj.left.obj := hV i
    exact isConstructibleEtaleModule_etaleModuleShriekConstant B X Λ (V i)
  have hK : IsBigSiteConstructibleEtaleModule B X Λ (kernel Φ) :=
    (IsBigSiteConstructibleEtaleModule B X Λ).prop_kernel Φ
      ((IsBigSiteConstructibleEtaleModule B X Λ).prop_coproduct fun i =>
        (IsBigSiteConstructibleEtaleModule B X Λ).prop_cokernel _ (hgen i) (hgen i)) hcG
  have hNSum : N • 𝟙 (∐ Q) = 0 := by
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [Preadditive.comp_nsmul, Category.comp_id, comp_zero, ← Category.id_comp (Sigma.ι Q i),
      ← Preadditive.nsmul_comp, nsmul_id_cokernel_nsmul_id_eq_zero (P i) N, zero_comp]
  have hNK : N • 𝟙 (kernel Φ) = 0 := by
    refine (cancel_mono (kernel.ι Φ)).1 ?_
    rw [Preadditive.nsmul_comp, Category.id_comp, zero_comp, ← Category.comp_id (kernel.ι Φ),
      ← Preadditive.comp_nsmul, hNSum, comp_zero]
  -- the cohomology of `t_!` of the sum is finite
  have h₁ := module_finite_etaleCohomology_extensionByZero_sigma B X t Λ q Q fun i =>
    module_finite_etaleCohomology_extensionByZero_cokernel_nsmul_smallEtaleShriekGenerator B X π t
      Λ hdim p hp (V i) (hV i) N hN hNp q
  let D := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (etaleModuleGlobalSections.{u, r} Λ Y)
  exact TorsionModules.module_finite_of_exact Λ _ (D.exact_δ₁ (hS.map_of_exact L) q) h₁
    (ih (kernel Φ) hK hNK)

/-- **The cohomology of `t_!F` is finite, for `F` constructible and killed by an integer prime to
`p`**, `t : X ⟶ Y` étale into a curve `Y` over `k`, and every prime prime to `p` prime to the
characteristic of `k` or `Y` proper.

Descending induction on `q`, starting above degree two where the cohomology of the torsion sheaf
`t_!F` on `Y` vanishes (Tag 0A53): `F` is a quotient of `⊕_i j_{U_i!}(Λ/N)̲`, the kernel is again
constructible and killed by `N`, `t_!` is exact and carries `j_{U_i!}` to `(t ∘ j_{U_i})_!`, and
`H^q(Y, t_!(⊕_i j_{U_i!}(Λ/N)̲)) ⟶ H^q(Y, t_!F) ⟶ H^{q+1}(Y, t_!K)` is exact with finite outer
terms. -/
theorem module_finite_etaleCohomology_extensionByZero_of_nsmul_id_eq_zero
    (hdim : topologicalKrullDim Y ≤ 1) (p : ℕ)
    (hp : ∀ ℓ : ℕ, ℓ.Prime → ℓ.Coprime p → ℓ.Coprime (ringExpChar k) ∨ IsProper π) (q : ℕ)
    (F : EtaleModules.{u, r} Λ X.obj) (hc : IsBigSiteConstructibleEtaleModule B X Λ F) (N : ℕ)
    (hN : 0 < N) (hNp : N.Coprime p) (hNF : N • 𝟙 F = 0) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ Y).rightDerived q).obj
      ((etaleModuleExtensionByZero.{u, r} Λ t).obj F)) := by
  let L := etaleModuleExtensionByZero.{u, r} Λ t
  have hvan : ∀ (q : ℕ), 2 < q → ∀ G : EtaleModules.{u, r} Λ X.obj, N • 𝟙 G = 0 →
      Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ Y).rightDerived q).obj (L.obj G)) :=
    fun q hq G hG => module_finite_etaleCohomology_of_nsmul_id_eq_zero_of_two_lt π Λ hdim
      (L.obj G) N hN
      (by rw [← map_nsmul_id, hG, Functor.map_zero]) q hq
  suffices h : ∀ m q : ℕ, 3 ≤ q + m → ∀ G : EtaleModules.{u, r} Λ X.obj,
      IsBigSiteConstructibleEtaleModule B X Λ G → N • 𝟙 G = 0 →
      Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ Y).rightDerived q).obj (L.obj G)) from
    h 3 q (by omega) F hc hNF
  intro m
  induction m with
  | zero => exact fun q hq G _ hG => hvan q (by omega) G hG
  | succ m ih =>
    intro q hq G hcG hNG
    by_cases hq3 : 3 ≤ q
    · exact hvan q (by omega) G hNG
    exact module_finite_etaleCohomology_extensionByZero_of_module_finite_succ B X π t Λ hdim p hp
      q N hN hNp (ih (q + 1) (by omega)) G hcG hNG

/-- **The cohomology of `t_!F` is finite, for `F` constructible with torsion prime to `p`**, `t`
étale into a curve over `k`, and every prime prime to `p` prime to the characteristic of `k` or the
curve proper. -/
theorem module_finite_etaleCohomology_extensionByZero_of_forall
    (hdim : topologicalKrullDim Y ≤ 1) (p : ℕ)
    (hp : ∀ ℓ : ℕ, ℓ.Prime → ℓ.Coprime p → ℓ.Coprime (ringExpChar k) ∨ IsProper π) (q : ℕ)
    (F : EtaleModules.{u, r} Λ X.obj) (hc : IsBigSiteConstructibleEtaleModule B X Λ F)
    (ht : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.obj.smallEtaleTopology p
      ((etaleModuleForgetAb.{u, r} Λ X.obj).obj F)) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ Y).rightDerived q).obj
      ((etaleModuleExtensionByZero.{u, r} Λ t).obj F)) := by
  obtain ⟨N, hN, hNp, hNF⟩ :=
    exists_nsmul_id_eq_zero_of_isBigSiteConstructibleEtaleModule B X Λ p F hc ht
  exact module_finite_etaleCohomology_extensionByZero_of_nsmul_id_eq_zero B X π t Λ hdim p hp q F
    hc N hN hNp hNF

end Main

end Stacks.EtaleCohomology

end
