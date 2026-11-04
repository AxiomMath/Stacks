module

public import StacksFrontier.Algebra.Homology.CyclesFiveLemma
public import StacksFrontier.Algebra.Homology.TermwiseAdicCompletion
public import StacksFrontier.RingTheory.LocalCohomology.EssentiallyConstantConsequences
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.CechFunctor

/-!
# The Čech complex of `M / IⁿM` is the Čech complex of `M` modulo `Iⁿ`

Let `g₁, …, g_r` be elements of a commutative ring `A`, let `I` be an ideal and let `M` be an
`A`-module. Localization is exact and commutes with direct sums, so the map of extended Čech
complexes `C^•(g; M) ⟶ C^•(g; M / IⁿM)` induced by the quotient map is, in every degree,
surjective with kernel `Iⁿ C^•(g; M)`. In other words `C^•(g; M / IⁿM)` is the quotient of
`C^•(g; M)` by `Iⁿ`, degree by degree. Consequently, a compatible family of degree-one Čech
cocycles of the `M / IⁿM` comes from a degree-one cocycle of `M` when `M` is `I`-adically complete
and the termwise completion map of `C^•(g; M)` is an isomorphism on `H⁰` and `H¹`.

## Main results

* `Stacks.LocalCohomology.ker_lmap_eq_smul_top`: a direct sum of linear maps each with kernel
  `J • ⊤` has kernel `J • ⊤`.
* `Stacks.LocalCohomology.ker_isLocalizedModule_map_eq_smul_top`: localization preserves a kernel
  of the form `J • ⊤`.
* `Stacks.LocalCohomology.surjective_and_ker_extendedCechComplexMap_f`: the map of extended Čech
  complexes induced by a surjection with kernel `J • ⊤` is, in every degree, surjective with
  kernel `J • ⊤`.
* `Stacks.LocalCohomology.exists_cycles_lift_of_isIso_homologyMap`: if the termwise completion
  map of `C^•(g; M)` is an isomorphism on `H⁰` and `H¹` and `M` is `I`-adically complete, then
  every compatible family of degree-one cocycles of the `C^•(g; M / IⁿM)` comes from a
  degree-one cocycle of `C^•(g; M)`.

## References

* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A]

/-! ### Kernels of direct sums and of localizations -/

/-- **A direct sum of linear maps each with kernel `J • ⊤` has kernel `J • ⊤`.** -/
theorem ker_lmap_eq_smul_top {ι : Type*} {P Q : ι → Type*} [∀ s, AddCommGroup (P s)]
    [∀ s, Module A (P s)] [∀ s, AddCommGroup (Q s)] [∀ s, Module A (Q s)]
    (φ : ∀ s, P s →ₗ[A] Q s) (J : Ideal A) (h : ∀ s, LinearMap.ker (φ s) = J • ⊤) :
    LinearMap.ker (DirectSum.lmap φ) = J • ⊤ := by
  classical
  apply le_antisymm
  · intro x hx
    have hcomp (s : ι) : x s ∈ J • (⊤ : Submodule A (P s)) := by
      rw [← h s, LinearMap.mem_ker]
      simpa using congrArg (fun y : DirectSum ι Q => y s) (LinearMap.mem_ker.1 hx)
    rw [← DirectSum.sum_support_of x]
    refine Submodule.sum_mem _ fun s _ => ?_
    have hmap : Submodule.map (DirectSum.lof A ι P s) (J • ⊤) ≤ J • ⊤ := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact hmap ⟨x s, hcomp s, rfl⟩
  · refine Submodule.smul_le.2 fun a ha y _ => ?_
    rw [LinearMap.mem_ker]
    ext s
    rw [DirectSum.lmap_apply, DirectSum.smul_apply, DirectSum.zero_apply, ← LinearMap.mem_ker, h s]
    exact Submodule.smul_mem_smul ha Submodule.mem_top

/-- **Localization preserves a kernel of the form `J • ⊤`.** If `q : M ⟶ N` has kernel
`J • ⊤`, so does the induced map of localizations at any submonoid. -/
theorem ker_isLocalizedModule_map_eq_smul_top (S : Submonoid A) {M N M' N' : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [AddCommGroup M'] [Module A M']
    [AddCommGroup N'] [Module A N'] (f : M →ₗ[A] M') (f' : N →ₗ[A] N')
    [IsLocalizedModule S f] [IsLocalizedModule S f'] (q : M →ₗ[A] N) (J : Ideal A)
    (hq : LinearMap.ker q = J • ⊤) :
    LinearMap.ker (IsLocalizedModule.map S f f' q) = J • ⊤ := by
  rw [LinearMap.ker_localizedMap_eq_localized₀_ker, hq, Submodule.localized₀_smul,
    Submodule.localized₀_top]

/-! ### The Čech complex modulo `Iⁿ` -/

variable {r : ℕ} (g : Fin r → A)

/-- The map induced on a term of the Čech complex is the direct sum of the maps induced on the
localized summands. -/
theorem cechTermMap_eq_lmap {M N : ModuleCat.{u} A} (q : M ⟶ N) (p : ℕ) :
    cechTermMap g q p =
      DirectSum.lmap (ι := {s : Finset (Fin r) // s.card = p})
        (M := fun s => _root_.Cech.cechMod g M s.1) (N := fun s => _root_.Cech.cechMod g N s.1)
        (fun s => cechModMap g q s.1) := by
  classical
  refine DirectSum.linearMap_ext A fun s => LinearMap.ext fun x => ?_
  show cechTermMap g q p (DirectSum.lof A _ (fun s => _root_.Cech.cechMod g M s.1) s x) =
    DirectSum.lmap _ (DirectSum.lof A _ (fun s => _root_.Cech.cechMod g M s.1) s x)
  rw [cechTermMap_lof, DirectSum.lmap_lof]

/-- The map induced on a term of the Čech complex by a surjection is surjective. -/
theorem surjective_cechTermMap {M N : ModuleCat.{u} A} (q : M ⟶ N)
    (hq : Function.Surjective q.hom) (p : ℕ) : Function.Surjective (cechTermMap g q p) := by
  rw [cechTermMap_eq_lmap, DirectSum.lmap_surjective]
  exact fun s => IsLocalizedModule.map_surjective _ _ _ _ hq

/-- The map induced on a term of the Čech complex by a map with kernel `J • ⊤` has kernel
`J • ⊤`. -/
theorem ker_cechTermMap {M N : ModuleCat.{u} A} (q : M ⟶ N) (J : Ideal A)
    (hq : LinearMap.ker q.hom = J • ⊤) (p : ℕ) :
    LinearMap.ker (cechTermMap g q p) = J • ⊤ := by
  rw [cechTermMap_eq_lmap]
  exact ker_lmap_eq_smul_top _ J fun s => ker_isLocalizedModule_map_eq_smul_top _ _ _ _ J hq

/-- The surjectivity and the kernel of a map of modules transport along linear equivalences of
its source and target. -/
private theorem surjective_and_ker_of_conj {P Q P' Q' : Type*} [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q] [AddCommGroup P'] [Module A P'] [AddCommGroup Q']
    [Module A Q'] (eP : P' ≃ₗ[A] P) (eQ : Q' ≃ₗ[A] Q) (φ : P →ₗ[A] Q) (J : Ideal A)
    (hs : Function.Surjective φ) (hk : LinearMap.ker φ = J • ⊤) :
    Function.Surjective (eQ.symm.toLinearMap ∘ₗ φ ∘ₗ eP.toLinearMap) ∧
      LinearMap.ker (eQ.symm.toLinearMap ∘ₗ φ ∘ₗ eP.toLinearMap) = J • ⊤ := by
  refine ⟨eQ.symm.surjective.comp (hs.comp eP.surjective), ?_⟩
  rw [LinearEquiv.ker_comp, LinearMap.ker_comp, hk, Submodule.comap_equiv_eq_map_symm,
    Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]

/-- **The map of extended Čech complexes induced by a surjection with kernel `J • ⊤` is, in every
degree, surjective with kernel `J • ⊤`.** -/
theorem surjective_and_ker_extendedCechComplexMap_f {M N : ModuleCat.{u} A} (q : M ⟶ N)
    (J : Ideal A) (hs : Function.Surjective q.hom) (hk : LinearMap.ker q.hom = J • ⊤) (n : ℤ) :
    Function.Surjective ((extendedCechComplexMap.{0} g q).f n).hom ∧
      LinearMap.ker ((extendedCechComplexMap.{0} g q).f n).hom = J • ⊤ := by
  by_cases hn : 0 ≤ n
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, n = (p : ℤ) := ⟨n.toNat, (Int.toNat_of_nonneg hn).symm⟩
    have hp : ComplexShape.embeddingUpNat.f p = (p : ℤ) := by simp
    have e : (extendedCechComplexMap.{0} g q).f (p : ℤ) = _ :=
      HomologicalComplex.extendMap_f (cechComplexMap.{0} g q) ComplexShape.embeddingUpNat hp
    rw [e]
    exact surjective_and_ker_of_conj
      (HomologicalComplex.extendXIso (_root_.Cech.cechComplex g M) ComplexShape.embeddingUpNat
        hp).toLinearEquiv
      (HomologicalComplex.extendXIso (_root_.Cech.cechComplex g N) ComplexShape.embeddingUpNat
        hp).toLinearEquiv
      (cechTermMap g q p) J (surjective_cechTermMap g q hs p) (ker_cechTermMap g q J hk p)
  · have hz : ∀ i : ℕ, ComplexShape.embeddingUpNat.f i ≠ n := fun i hi => by
      simp only [ComplexShape.embeddingUpNat_f] at hi
      omega
    have hN : Subsingleton ((extendedCechComplex.{0} g N).X n) :=
      (ModuleCat.isZero_iff_subsingleton).1 (HomologicalComplex.isZero_extend_X _ _ n hz)
    have hM : Subsingleton ((extendedCechComplex.{0} g M).X n) :=
      (ModuleCat.isZero_iff_subsingleton).1 (HomologicalComplex.isZero_extend_X _ _ n hz)
    exact ⟨fun y => ⟨0, Subsingleton.elim _ _⟩, Subsingleton.elim _ _⟩

/-! ### Lifting compatible families of Čech cocycles -/

variable (I : Ideal A) (M : ModuleCat.{u} A)

/-- The tower `n ↦ C^•(g; M / IⁿM)` of extended Čech complexes. -/
abbrev cechQuotientTower : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  idealPowerQuotientTower.{u, 0} I M ⋙ extendedCechFunctor.{0} g

/-- The maps `C^•(g; M) ⟶ C^•(g; M / IⁿM)` induced by the quotient maps. -/
abbrev cechQuotientProj (n : ℕ) :
    extendedCechComplex.{0} g M ⟶ (cechQuotientTower g I M).obj (op n) :=
  extendedCechComplexMap.{0} g ((idealPowerQuotientCone.{u, 0} I M).π.app (op n))

/-- **Every compatible family of degree-one cocycles of the `C^•(g; M / IⁿM)` comes from a
degree-one cocycle of `C^•(g; M)`**, provided `M` is `I`-adically complete and the termwise
`I`-adic completion map of `C^•(g; M)` is an isomorphism on `H⁰` and on `H¹`. -/
theorem exists_cycles_lift_of_isIso_homologyMap [IsAdicComplete I M]
    [IsIso (HomologicalComplex.homologyMap
      (HomologicalComplex.toTermwiseAdicCompletion I (extendedCechComplex.{0} g M)) 0)]
    [IsIso (HomologicalComplex.homologyMap
      (HomologicalComplex.toTermwiseAdicCompletion I (extendedCechComplex.{0} g M)) 1)]
    (z : ∀ n : ℕ, ((cechQuotientTower g I M).obj (op n)).cycles 1)
    (hz : ∀ (m n : ℕ) (h : m ≤ n),
      (HomologicalComplex.cyclesMap ((cechQuotientTower g I M).map (homOfLE h).op) 1).hom (z n) =
        z m) :
    ∃ w : (extendedCechComplex.{0} g M).cycles 1, ∀ n : ℕ,
      (HomologicalComplex.cyclesMap (cechQuotientProj g I M n) 1).hom w = z n := by
  let K := extendedCechComplex.{0} g M
  let φ := HomologicalComplex.toTermwiseAdicCompletion I K
  have hzero : ∀ L : CochainComplex (ModuleCat.{u} A) ℤ, IsZero (L.X (-1)) → L.d (-1) 0 = 0 :=
    fun L hL => hL.eq_of_src _ _
  have hK : IsZero (K.X (-1)) := isZero_extendedCechComplex_X g M (-1) (Or.inl (by omega))
  have hKc : IsZero ((HomologicalComplex.termwiseAdicCompletion I K).X (-1)) :=
    (AdicCompletion.moduleCatFunctor I).map_isZero hK
  have h0 : IsIso (φ.f 0) := by
    have hb : Function.Bijective (AdicCompletion.of I (K.X 0)) := by
      have e : (K.X 0) ≃ₗ[A] M := (extendedCechXZeroIso g M).toLinearEquiv
      have hM : Function.Bijective (AdicCompletion.of I M) :=
        AdicCompletion.of_bijective_iff.2 inferInstance
      have hcomm : ((AdicCompletion.congr I e).restrictScalars A).toLinearMap ∘ₗ
          AdicCompletion.of I (K.X 0) =
          AdicCompletion.of I M ∘ₗ e.toLinearMap := by
        refine LinearMap.ext fun x => ?_
        simp [AdicCompletion.congr_apply, AdicCompletion.map_of]
      have : Function.Bijective
          (((AdicCompletion.congr I e).restrictScalars A).toLinearMap ∘ₗ
            AdicCompletion.of I (K.X 0)) := by
        rw [hcomm]
        exact hM.comp e.bijective
      exact (Function.Bijective.of_comp_iff' (AdicCompletion.congr I e).bijective _).1 this
    exact (ConcreteCategory.isIso_iff_bijective _).2 hb
  have hcyc : IsIso (HomologicalComplex.cyclesMap φ 1) :=
    HomologicalComplex.isIso_cyclesMap_one_of_isIso_homologyMap φ (hzero _ hK) (hzero _ hKc)
  have hZ : Function.Surjective (HomologicalComplex.cyclesMap φ 1).hom :=
    ((ConcreteCategory.isIso_iff_bijective _).1 hcyc).2
  refine HomologicalComplex.exists_cyclesMap_eq_of_surjective_cyclesMap_toTermwiseAdicCompletion
    I (cechQuotientTower g I M) (cechQuotientProj g I M) ?_ ?_ ?_ hZ z hz
  · exact fun m n h => ((extendedCechFunctor.{0} g).map_comp _ _).symm.trans
      (congrArg (extendedCechFunctor.{0} g).map
        ((idealPowerQuotientCone.{u, 0} I M).w (homOfLE h).op))
  · exact fun n p => (surjective_and_ker_extendedCechComplexMap_f g _ (I ^ n)
      (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _) p).1
  · exact fun n p => (surjective_and_ker_extendedCechComplexMap_f g _ (I ^ n)
      (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _) p).2

end Stacks.LocalCohomology

end
