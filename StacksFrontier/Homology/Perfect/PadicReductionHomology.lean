module

public import StacksFrontier.Algebra.Homology.NSMulHomologySequence
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.PseudoCoherent
public import StacksFrontier.Homology.Perfect.ZModPrimePowerBaseChange
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction

/-!
# Cohomology of the reduction of a perfect `ℤ_ℓ`-complex modulo `ℓᵐ`

Let `K` be a perfect object of `D(ℤ_ℓ)`, `Y` an object of `D(ℤ/ℓᵐ)` and `g : K ⟶ Res Y` a morphism
whose adjoint `K ⊗ᴸ ℤ/ℓᵐ ⟶ Y` is an isomorphism. Then on cohomology `Hⁱ(g) : Hⁱ(K) → Hⁱ(Y)`

* has kernel `ℓᵐ Hⁱ(K)` (`StacksDraft.Perfect.exists_nsmul_eq_of_homologyMap_eq_zero`), and
* has cokernel killed by every `c` killing the `ℓᵐ`-torsion of `Hⁱ⁺¹(K)`
  (`StacksDraft.Perfect.exists_homologyMap_eq_nsmul`).

This is the universal coefficient sequence `0 → Hⁱ(K)/ℓᵐ → Hⁱ(K ⊗ᴸ ℤ/ℓᵐ) → Hⁱ⁺¹(K)[ℓᵐ] → 0`:
representing `K` by a bounded complex `P` of finite projective (hence torsion-free) modules, the
derived base change is computed termwise, the unit `P ⟶ P ⊗ ℤ/ℓᵐ` is onto with kernel `ℓᵐ P`, and
`CochainComplex.exists_nsmul_eq_of_homologyMap_eq_zero` and
`CochainComplex.exists_homologyMap_eq_nsmul` apply.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v

namespace StacksDraft.Perfect

attribute [local instance] HasDerivedCategory.standard

variable {ℓ : ℕ} [Fact ℓ.Prime] (m : ℕ)

/-- The unit `M → ℤ/ℓᵐ ⊗ M` kills `ℓᵐ M`. -/
theorem extendRestrictScalarsAdj_unit_app_nsmul (M : ModuleCat.{v} ℤ_[ℓ]) (x : M) :
    (ModuleCat.extendRestrictScalarsAdj.{v} (PadicInt.toZModPow (p := ℓ) m)).unit.app M
      ((ℓ ^ m) • x) = 0 := by
  rw [map_nsmul]
  generalize (ModuleCat.extendRestrictScalarsAdj.{v} (PadicInt.toZModPow (p := ℓ) m)).unit.app
    M x = y
  have hz : ∀ z : (ModuleCat.extendScalars.{0, 0, v} (PadicInt.toZModPow (p := ℓ) m)).obj M,
      (ℓ ^ m) • z = 0 := fun z => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod (ℓ ^ m)), ZMod.natCast_self, zero_smul]
  exact hz y

/-- For a projective `ℤ_ℓ`-module `M`, the sequence `0 → M →^{ℓᵐ} M → ℤ/ℓᵐ ⊗ M → 0` is short
exact. -/
theorem shortExact_nsmul_extendRestrictScalarsAdj_unit (M : ModuleCat.{v} ℤ_[ℓ])
    [Module.Projective ℤ_[ℓ] M] :
    (ShortComplex.mk ((ℓ ^ m) • 𝟙 M)
      ((ModuleCat.extendRestrictScalarsAdj.{v} (PadicInt.toZModPow (p := ℓ) m)).unit.app M)
      (by ext x; exact extendRestrictScalarsAdj_unit_app_nsmul m M x)).ShortExact := by
  have hsurj : Function.Surjective (PadicInt.toZModPow (p := ℓ) m) :=
    ZMod.ringHom_surjective _
  have hreg : IsRegular ((ℓ : ℤ_[ℓ]) ^ m) :=
    isRegular_iff_ne_zero.2 (pow_ne_zero m (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero))
  have hinj : Function.Injective (fun x : M => (ℓ ^ m) • x) := by
    intro x y hxy
    apply (hreg.isSMulRegular (M := M))
    simpa [← Nat.cast_smul_eq_nsmul ℤ_[ℓ], Nat.cast_pow] using hxy
  refine
    { exact := (ShortComplex.moduleCat_exact_iff _).2 fun x hx => ?_
      mono_f := (ModuleCat.mono_iff_injective _).2 hinj
      epi_g := (ModuleCat.epi_iff_surjective _).2
        (Stacks.InverseSystem.surjective_extendRestrictScalarsAdj_unit_app hsurj M) }
  have hmem := Stacks.InverseSystem.mem_ker_smul_top_of_extendRestrictScalarsAdj_unit_app_eq_zero
    hsurj x hx
  rw [PadicInt.ker_toZModPow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨y, -, hy⟩ := hmem
  refine ⟨y, ?_⟩
  change (ℓ ^ m) • y = x
  rw [← hy, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

/-- For a complex `P` of projective `ℤ_ℓ`-modules, the sequence `0 → P →^{ℓᵐ} P → ℤ/ℓᵐ ⊗ P → 0`
of cochain complexes (the second map the termwise unit of extension of scalars) is short
exact. -/
theorem shortExact_nsmul_extendRestrictScalarsAdj_mapHomologicalComplex_unit
    (P : CochainComplex (ModuleCat.{v} ℤ_[ℓ]) ℤ) [∀ j, Module.Projective ℤ_[ℓ] (P.X j)]
    (w : ((ℓ ^ m) • 𝟙 P) ≫
      ((ModuleCat.extendRestrictScalarsAdj.{v}
        (PadicInt.toZModPow (p := ℓ) m)).mapHomologicalComplex
        (ComplexShape.up ℤ)).unit.app P = 0) :
    (ShortComplex.mk ((ℓ ^ m) • 𝟙 P)
      (((ModuleCat.extendRestrictScalarsAdj.{v}
        (PadicInt.toZModPow (p := ℓ) m)).mapHomologicalComplex
        (ComplexShape.up ℤ)).unit.app P) w).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun j =>
    shortExact_nsmul_extendRestrictScalarsAdj_unit m (P.X j)

/-- Precomposing and postcomposing with isomorphisms preserves the two properties "the kernel is
`n`-divisible" and "the cokernel is killed by `c`". -/
theorem kernel_cokernel_of_comp_comp {R : Type} [Ring R] {A A' B' B : ModuleCat.{v} R}
    (α : A ⟶ A') [IsIso α] (ψ : A' ⟶ B') (β : B' ⟶ B) [IsIso β] (n c : ℕ)
    (h₁ : ∀ x, ψ x = 0 → ∃ x', x = n • x') (h₂ : ∀ y, ∃ x, ψ x = c • y) :
    (∀ x, (α ≫ ψ ≫ β) x = 0 → ∃ x', x = n • x') ∧ ∀ y, ∃ x, (α ≫ ψ ≫ β) x = c • y := by
  refine ⟨fun x hx => ?_, fun y => ?_⟩
  · have hx' : ψ (α x) = 0 := by simpa using congrArg (inv β) hx
    obtain ⟨x', hx'⟩ := h₁ _ hx'
    refine ⟨inv α x', ?_⟩
    simpa [map_nsmul] using congrArg (inv α) hx'
  · obtain ⟨x, hx⟩ := h₂ (inv β y)
    refine ⟨inv α x, ?_⟩
    simp [hx, map_nsmul]

/-- **Universal coefficients for the reduction of a perfect `ℤ_ℓ`-complex modulo `ℓᵐ`.** Let `K`
be perfect and `g : K ⟶ Res Y` a morphism whose adjoint `K ⊗ᴸ ℤ/ℓᵐ ⟶ Y` is an isomorphism. Then
the kernel of `Hⁱ(g)` is `ℓᵐ Hⁱ(K)`, and the cokernel of `Hⁱ(g)` is killed by every `c` killing
the `ℓᵐ`-torsion of `Hⁱ⁺¹(K)`. -/
theorem homologyMap_reduction (K : DerivedCategory (ModuleCat.{v} ℤ_[ℓ])) (hK : IsPerfect K)
    (Y : DerivedCategory (ModuleCat.{v} (ZMod (ℓ ^ m))))
    (g : K ⟶ (ModuleCat.restrictScalars.{v} (PadicInt.toZModPow (p := ℓ) m)).mapDerivedCategory.obj
      Y)
    (hg : IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison
      (PadicInt.toZModPow (p := ℓ) m) g)) (i : ℤ) (c : ℕ)
    (hc : ∀ z : (DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) (i + 1)).obj K,
      (ℓ ^ m) • z = 0 → c • z = 0) :
    (∀ x, (DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) i).map g x = 0 →
        ∃ x', x = (ℓ ^ m) • x') ∧
      ∀ y, ∃ x, (DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) i).map g x = c • y := by
  obtain ⟨P, a, b, -, hb, -, hproj, ⟨e⟩⟩ := hK
  have := hproj
  let f := PadicInt.toZModPow (p := ℓ) m
  let D := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{0, v, 0} f
  have hD := D.isLeftDerived
  let adj := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{0, 0, v}
    ℤ_[ℓ] (ZMod (ℓ ^ m)) _ _ f _ _ D.functor D.comparison hD
  let Res := (ModuleCat.restrictScalars.{v} f).mapDerivedCategory
  let g' := StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison f g
  have : IsIso g' := hg
  have hgg : g = adj.unit.app K ≫ Res.map g' :=
    ((adj.homEquiv K Y).apply_symm_apply g).symm.trans (adj.homEquiv_unit K Y g')
  have hnat : adj.unit.app K = e.hom ≫ adj.unit.app (DerivedCategory.Q.obj P) ≫
      Res.map (D.functor.map e.inv) := by
    have h := adj.unit.naturality e.hom
    simp only [Functor.id_map, Functor.comp_map] at h
    rw [reassoc_of% h, ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      e.hom_inv_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  have : ∀ j, Module.Flat ℤ_[ℓ] (P.X j) := fun j => inferInstance
  have hflat : CochainComplex.KFlat P := CochainComplex.KFlat.kFlat_of_flat.{0, v} P b
  have hu :=
    @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app_eq_of_kFlat
      ℤ_[ℓ] (ZMod (ℓ ^ m)) _ _ f _ _ D.functor D.comparison hD P hflat
  set u := ((ModuleCat.extendRestrictScalarsAdj.{v} f).mapHomologicalComplex
    (ComplexShape.up ℤ)).unit.app P
  obtain ⟨β₀, hβ₀, hβ₀iso⟩ : ∃ β₀, g = e.hom ≫ DerivedCategory.Q.map u ≫ β₀ ∧ IsIso β₀ := by
    rw [hgg, hnat, hu]
    simp only [Category.assoc]
    exact ⟨_, rfl, inferInstance⟩
  let H := DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) i
  let φ := DerivedCategory.homologyFunctorFactors (ModuleCat.{v} ℤ_[ℓ]) i
  have hQ : H.map (DerivedCategory.Q.map u) = φ.hom.app P ≫
      (HomologicalComplex.homologyFunctor _ _ i).map u ≫ φ.inv.app _ :=
    (NatIso.naturality_2 φ u).symm
  have hHg : H.map g = (H.map e.hom ≫ φ.hom.app P) ≫
      (HomologicalComplex.homologyFunctor _ _ i).map u ≫ (φ.inv.app _ ≫ H.map β₀) := by
    rw [hβ₀, Functor.map_comp, Functor.map_comp, hQ]
    simp only [Category.assoc]
  -- the torsion bound on `Hⁱ⁺¹(P)`
  let φ' := DerivedCategory.homologyFunctorFactors (ModuleCat.{v} ℤ_[ℓ]) (i + 1)
  let γ := (DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) (i + 1)).mapIso e ≪≫ φ'.app P
  have hc' : ∀ z : (HomologicalComplex.homologyFunctor (ModuleCat.{v} ℤ_[ℓ])
      (ComplexShape.up ℤ) (i + 1)).obj P, (ℓ ^ m) • z = 0 → c • z = 0 := by
    intro z hz
    have h1 : (ℓ ^ m) • γ.inv z = 0 := by simpa [map_nsmul] using congrArg γ.inv hz
    have h2 := congrArg γ.hom (hc _ h1)
    simpa [map_nsmul, Iso.inv_hom_id_apply] using h2
  have w : ((ℓ ^ m) • 𝟙 P) ≫ u = 0 := by
    ext j x
    exact extendRestrictScalarsAdj_unit_app_nsmul m (P.X j) x
  have hS := shortExact_nsmul_extendRestrictScalarsAdj_mapHomologicalComplex_unit m P w
  rw [hHg]
  exact kernel_cokernel_of_comp_comp _ _ _ _ _
    (CochainComplex.exists_nsmul_eq_of_homologyMap_eq_zero w hS i)
    (CochainComplex.exists_homologyMap_eq_nsmul w hS i c hc')

end StacksDraft.Perfect
