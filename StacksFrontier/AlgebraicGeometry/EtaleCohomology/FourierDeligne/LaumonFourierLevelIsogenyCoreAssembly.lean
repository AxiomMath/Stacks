module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LaumonFourierLevelIsogenyCore
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.EtaleModuleRestrictScalarsIsogenyLift
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HigherDirectImageShriekLevelIsogeny

/-!
# Assembly of the level isogeny over the integers of `E`

The level isogeny `Stacks.EtaleCohomology.LaumonFourierLevelIsogenyCoreInput` of Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) is a chain of comparisons of sheaves of
`ℤ_ℓ`-modules on `V'` at a level `N'`, `Λ = O_E/ℓ^{N'+1}`:

* the Fourier side: `jV'⁻¹ H¹Φ(ℱ_{σ_E mod ℓ^{N'+1}})` against `jV'⁻¹ R¹pr₂!` of the level `N'` of
  the Fourier family sheaf `K` (`Stacks.EtaleCohomology.LaumonFourierFamilyLevelIsogenyInput`);
* S7c: `jV'⁻¹ R¹pr₂!(K_{N'})` against the level `N'` of Laumon's `G = R¹g'_!(K|_{U'})`
  `Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf.exists_higherDirectImageShriek_levelIsogeny`;
* the representation side: the level `N'` of `G` against `ℱ_{τ_E mod ℓ^{N'+1}}` through the
  isogeny `φ, ψ₀` of `G` with `ℱ_ρ` and the matrices `P, Q`
  (`Stacks.EtaleCohomology.LaumonFourierRepresentationLevelIsogenyInput`).

Each comparison is an `ℓᶜ`-isogeny with `c` independent of `N'`, and commutes with the action of
the integral part `O ⊆ O_E` of `E` acting on `K` and `G` up to a bounded power of `ℓ`. As
`ℓˢ O_E ⊆ O` (`Stacks.EtaleCohomology.exists_pow_mul_mem_of_forall_exists_pow_mul_mem`), the
composite commutes with all of `O_E` up to a bounded power of `ℓ`, and lifts to an isogeny of
sheaves of `Λ`-modules (`Stacks.EtaleCohomology.exists_isogeny_of_etaleModuleRestrictScalars`).

## Main definitions

* `Stacks.EtaleCohomology.LaumonFourierRepresentationLevelIsogenyInput`.
* `Stacks.EtaleCohomology.LaumonFourierFamilyLevelIsogenyInput`.

## Main results

* `Stacks.EtaleCohomology.exists_pow_mul_mem_of_forall_exists_pow_mul_mem`.
* `Stacks.EtaleCohomology.exists_isogeny_of_restrictScalars_chain`.
* `Stacks.EtaleCohomology.laumonFourierLevelIsogenyCoreInput_of_levelIsogenies`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.SmallEtale
  Matrix Polynomial Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

section Index

attribute [local instance] padicIntAlgebraOfRat

/-- **An order of `E` has bounded index in `O_E`**: if a subring `O` of `E` contains `ℤ_ℓ` and an
`ℓ`-power multiple of every element of `E`, then `ℓˢ O_E ⊆ O` for one `s`. -/
theorem exists_pow_mul_mem_of_forall_exists_pow_mul_mem (ℓ : ℕ) [Fact ℓ.Prime] {E : Type}
    [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] (O : Subring E)
    (h₁ : ∀ c : ℤ_[ℓ], algebraMap ℚ_[ℓ] E c ∈ O) (h₂ : ∀ e : E, ∃ N : ℕ, (ℓ : E) ^ N * e ∈ O) :
    ∃ s : ℕ, ∀ o : integralClosure ℤ_[ℓ] E, (ℓ : E) ^ s * (o : E) ∈ O := by
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ_[ℓ]
    (integralClosure ℤ_[ℓ] E)).FG)
  choose N hN using fun o : integralClosure ℤ_[ℓ] E => h₂ o
  refine ⟨∑ o ∈ S, N o, fun o => ?_⟩
  have hmem : o ∈ Submodule.span ℤ_[ℓ] (S : Set (integralClosure ℤ_[ℓ] E)) := hS ▸ trivial
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    have hle : N x ≤ ∑ o ∈ S, N o := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx
    rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
    exact O.mul_mem (O.pow_mem (by simp) _) (hN x)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subalgebra.coe_add, mul_add]
    exact O.add_mem hx hy
  | smul c x _ hx =>
    rw [Subalgebra.coe_smul, Algebra.smul_def, mul_left_comm]
    exact O.mul_mem (h₁ c) hx

end Index

section Calculus

variable {C : Type*} [Category* C] [Preadditive C]

/-- Composites of `ℓᵃ`- and `ℓᵇ`-isogenies compose to `ℓ^{a+b}`. -/
theorem comp_comp_eq_pow_nsmul {X Y Z : C} (f : X ⟶ Y) (f' : Y ⟶ X) (g : Y ⟶ Z) (g' : Z ⟶ Y)
    {ℓ a b : ℕ} (h₁ : f ≫ f' = ℓ ^ a • 𝟙 _) (h₂ : g ≫ g' = ℓ ^ b • 𝟙 _) :
    (f ≫ g) ≫ (g' ≫ f') = ℓ ^ (a + b) • 𝟙 _ := by
  rw [Category.assoc, reassoc_of% h₂, Preadditive.nsmul_comp, Category.id_comp,
    Preadditive.comp_nsmul, h₁, smul_smul, ← pow_add, add_comm]

/-- Composites of maps commuting up to `ℓ^{t₁}` and `ℓ^{t₂}` commute up to `ℓ^{t₁+t₂}`. -/
theorem pow_nsmul_comp_comp_eq {X Y Z : C} (a : X ⟶ X) (b : Y ⟶ Y) (c : Z ⟶ Z) (f : X ⟶ Y)
    (g : Y ⟶ Z) {ℓ t₁ t₂ : ℕ} (hf : ℓ ^ t₁ • (a ≫ f) = ℓ ^ t₁ • (f ≫ b))
    (hg : ℓ ^ t₂ • (b ≫ g) = ℓ ^ t₂ • (g ≫ c)) :
    ℓ ^ (t₁ + t₂) • (a ≫ f ≫ g) = ℓ ^ (t₁ + t₂) • ((f ≫ g) ≫ c) := by
  have hf' : ℓ ^ t₁ • (a ≫ f ≫ g) = ℓ ^ t₁ • (f ≫ b ≫ g) := by
    have := congrArg (· ≫ g) hf
    simpa only [Preadditive.nsmul_comp, Category.assoc] using this
  have hg' : ℓ ^ t₂ • (f ≫ b ≫ g) = ℓ ^ t₂ • (f ≫ g ≫ c) := by
    have := congrArg (f ≫ ·) hg
    simpa only [Preadditive.comp_nsmul] using this
  rw [pow_add, mul_comm, ← smul_smul, hf', smul_comm, hg', smul_comm, smul_smul, ← pow_add,
    add_comm, Category.assoc]

/-- Componentwise, an `ℓⁿ`-isogeny of functors is an `ℓⁿ`-isogeny. -/
private theorem app_comp_app_eq_nsmul {J : Type*} [Category* J] {F G : J ⥤ C} {f : F ⟶ G}
    {g : G ⟶ F} {n : ℕ} (h : f ≫ g = n • 𝟙 _) (X : J) : f.app X ≫ g.app X = n • 𝟙 _ := by
  rw [← NatTrans.comp_app, h, NatTrans.app_nsmul, NatTrans.id_app]

/-- Equal composites of natural transformations have equal components. -/
private theorem app_comp_app_eq_comp_app {J D : Type*} [Category* J] [Category* D]
    {F G H K : J ⥤ D}
    {a : F ⟶ G} {b : G ⟶ H} {c : F ⟶ K} {d : K ⟶ H} (h : a ≫ b = c ≫ d) (X : J) :
    a.app X ≫ b.app X = c.app X ≫ d.app X := by
  rw [← NatTrans.comp_app, h, NatTrans.comp_app]

end Calculus

section SMul

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') {X : Scheme.{u}}

/-- Restriction of scalars of multiplication by `n a` is `n` times that of multiplication by
`a`. -/
theorem etaleModuleRestrictScalars_map_etaleModuleSMul_natCast_mul (A : EtaleModules.{u, 0} Λ' X)
    (n : ℕ) (a : Λ') :
    (etaleModuleRestrictScalars ρ X).map ((etaleModuleSMul X ((n : Λ') * a)).app A) =
      n • (etaleModuleRestrictScalars ρ X).map ((etaleModuleSMul X a).app A) := by
  apply Sheaf.hom_ext
  ext U x
  show ((n : Λ') * a) • (show A.obj.obj U from x) = n • (a • (show A.obj.obj U from x))
  rw [mul_smul, Nat.cast_smul_eq_nsmul]

/-- **The chain of comparisons lifts**: an `ℓ^{c_B}`-isogeny `ρ_* A ⇄ M₁`, an `ℓ^{c_S}`-isogeny
`M₁ ⇄ M₂` and an `ℓ^{c_A}`-isogeny `M₂ ⇄ ρ_* A'` such that, for every `l ∈ Λ'`, multiplication by
`ℓˢ π(r)` on `A`, `A'` (`π : R → Λ'` surjective) is intertwined (up to `ℓ^{t_B}`, exactly, up to
`ℓ^{t_A}`) with endomorphisms of `M₁`, `M₂`, give an
`ℓ^{c_B + c_S + c_A + 2(t_B + t_A + s)}`-isogeny of sheaves of `Λ'`-modules `A ⇄ A'`. -/
theorem exists_isogeny_of_restrictScalars_chain {Λ Λ' : Type} [CommRing Λ] [CommRing Λ']
    (ρ : Λ →+* Λ') {X : Scheme.{u}} {A A' : EtaleModules.{u, 0} Λ' X}
    {M₁ M₂ : EtaleModules.{u, 0} Λ X} {ℓ cB cS cA tB tA s : ℕ} {R : Type} [CommRing R]
    (π : R →+* Λ') (hπ : Function.Surjective π)
    (hb : (etaleModuleRestrictScalars ρ X).obj A ⟶ M₁)
    (hb' : M₁ ⟶ (etaleModuleRestrictScalars ρ X).obj A) (Ψ : M₁ ⟶ M₂) (Φ : M₂ ⟶ M₁)
    (ha : M₂ ⟶ (etaleModuleRestrictScalars ρ X).obj A')
    (ha' : (etaleModuleRestrictScalars ρ X).obj A' ⟶ M₂)
    (hbb' : hb ≫ hb' = ℓ ^ cB • 𝟙 _) (hb'b : hb' ≫ hb = ℓ ^ cB • 𝟙 _)
    (hΨΦ : Ψ ≫ Φ = ℓ ^ cS • 𝟙 _) (hΦΨ : Φ ≫ Ψ = ℓ ^ cS • 𝟙 _)
    (haa' : ha ≫ ha' = ℓ ^ cA • 𝟙 _) (ha'a : ha' ≫ ha = ℓ ^ cA • 𝟙 _)
    (h : ∀ r : R, ∃ (r₂ : R) (_ : π r₂ = ((ℓ ^ s : ℕ) : Λ') * π r) (aK : M₁ ⟶ M₁) (aG : M₂ ⟶ M₂),
      ℓ ^ tB • ((etaleModuleRestrictScalars ρ X).map
          ((etaleModuleSMul X (π r₂)).app A) ≫ hb) = ℓ ^ tB • (hb ≫ aK) ∧
      ℓ ^ tB • (aK ≫ hb') = ℓ ^ tB • (hb' ≫ (etaleModuleRestrictScalars ρ X).map
          ((etaleModuleSMul X (π r₂)).app A)) ∧
      aK ≫ Ψ = Ψ ≫ aG ∧ aG ≫ Φ = Φ ≫ aK ∧
      ℓ ^ tA • (aG ≫ ha) = ℓ ^ tA • (ha ≫ (etaleModuleRestrictScalars ρ X).map
          ((etaleModuleSMul X (π r₂)).app A')) ∧
      ℓ ^ tA • ((etaleModuleRestrictScalars ρ X).map
          ((etaleModuleSMul X (π r₂)).app A') ≫ ha') = ℓ ^ tA • (ha' ≫ aG)) :
    ∃ (f : A ⟶ A') (g : A' ⟶ A), f ≫ g = ℓ ^ (cB + (cS + cA) + 2 * (tB + tA + s)) • 𝟙 _ ∧
      g ≫ f = ℓ ^ (cB + (cS + cA) + 2 * (tB + tA + s)) • 𝟙 _ := by
  have hFG := comp_comp_eq_pow_nsmul hb hb' (Ψ ≫ ha) (ha' ≫ Φ) hbb'
    (comp_comp_eq_pow_nsmul _ _ ha ha' hΨΦ haa')
  have hGF := comp_comp_eq_pow_nsmul (ha' ≫ Φ) (Ψ ≫ ha) hb' hb
    (comp_comp_eq_pow_nsmul ha' ha _ _ ha'a hΦΨ) hb'b
  rw [show cA + cS + cB = cB + (cS + cA) by omega] at hGF
  refine exists_isogeny_of_etaleModuleRestrictScalars ρ (hb ≫ Ψ ≫ ha) ((ha' ≫ Φ) ≫ hb')
    (t := tB + tA + s) hFG hGF (fun l => ?_) (fun l => ?_)
  all_goals
    obtain ⟨r, rfl⟩ := hπ l
    obtain ⟨r₂, hr₂, aK, aG, hb₁, hb₂, hK, hG, ha₁, ha₂⟩ := h r
    rw [hr₂] at hb₁ hb₂ ha₁ ha₂
    rw [etaleModuleRestrictScalars_map_etaleModuleSMul_natCast_mul] at hb₁ hb₂ ha₁ ha₂
  · have key := pow_nsmul_comp_comp_eq _ aK _ hb (Ψ ≫ ha) hb₁
      (pow_nsmul_comp_comp_eq aK aG _ Ψ ha (t₁ := 0) (by rw [hK]) ha₁)
    simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul, smul_smul, ← pow_add] at key
    rw [show tB + (0 + tA) + s = tB + tA + s by omega] at key
    exact key
  · have key := pow_nsmul_comp_comp_eq _ aG _ ha' (Φ ≫ hb') ha₂
      (pow_nsmul_comp_comp_eq aG aK _ Φ hb' (t₁ := 0) (by rw [hG]) hb₂)
    simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul, smul_smul, ← pow_add] at key
    rw [show tA + (0 + tB) + s = tB + tA + s by omega] at key
    simpa only [Category.assoc] using key

end SMul

section Pieces

attribute [local instance] padicIntAlgebraOfRat HasDerivedCategory.standard

/-- **The representation side of the level isogeny**: for an `O`-sheaf `G` on a connected
Noetherian `X` (`O` with fraction field `E = O[1/ℓ]`), an isogeny `φ, ψ₀` of `G` with `ℱ_ρ`, a
representation `τ` of `π₁(X, x̄)` over `E` with `Res_b τ = Q ρ₀ P`, `Q α(e) P = Res_b(e · 1)` for
the action `α` of `E` through `φ, ψ₀`, and an `O_E`-model `τ_E` of `τ`, there are exponents `c`,
`t`, independent of the level `N'`, and at every level `N'` an `ℓᶜ`-isogeny of sheaves of
`ℤ_ℓ`-modules between the level `N'` of `G` and `ℱ_{τ_E mod ℓ^{N'+1}}`, commuting up to `ℓᵗ` with
every `o ∈ O` (acting on the target through `O ⊆ O_E`). -/
def LaumonFourierRepresentationLevelIsogenyInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] [Fact ℓ.Prime]
    (X : B.Scheme) [ConnectedSpace X.1] [IsNoetherian X.1] (x : GeometricPoint X.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) (O : Type) [CommRing O] [Algebra ℤ_[ℓ] O] [Algebra O E]
    [IsLocalization (Submonoid.powers (ℓ : O)) E]
    (hOE : ∀ c : ℤ_[ℓ], algebraMap O E (algebraMap ℤ_[ℓ] O c) = algebraMap ℚ_[ℓ] E c)
    (G : LAdicSheaf.CoefficientSheaf B X ℓ O) {r : ℕ}
    (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)
    (φ : G.toLAdicSheaf ⟶ LAdicSheaf.representationSheaf B X x ρ hρ)
    (ψ₀ : LAdicSheaf.representationSheaf B X x ρ hρ ⟶ G.toLAdicSheaf) (N : ℕ)
    (hφψ : φ ≫ ψ₀ = (ℓ ^ N) • 𝟙 _) (hψφ : ψ₀ ≫ φ = (ℓ ^ N) • 𝟙 _) {mτ : ℕ}
    (τ : EtaleFundamentalGroup X.1 x →* GL (Fin mτ) E)
    (P : Matrix (Fin r) (Fin (mτ * d)) ℚ_[ℓ]) (Q : Matrix (Fin (mτ * d)) (Fin r) ℚ_[ℓ]),
    P * Q = 1 →
    (∀ e' : E, Q * isogenyCoefficientAlgHom B X x G ρ hρ φ ψ₀ N E hφψ hψφ hOE e' * P =
      restrictScalarsMatrix b (Matrix.scalar (Fin mτ) e')) →
    (∀ g : EtaleFundamentalGroup X.1 x,
      haveI := compactSpace_etaleFundamentalGroup X.1 x
      Q * (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))
        (integralModel ρ hρ g)).val * P = (restrictScalarsRep b τ g).val) →
    Q * P = 1 →
    ∀ (τO : EtaleFundamentalGroup X.1 x →* GL (Fin mτ) (integralClosure ℤ_[ℓ] E))
      (T : GL (Fin mτ) E),
      (∀ g, (τO g).val.map (algebraMap (integralClosure ℤ_[ℓ] E) E) = (T⁻¹ : GL (Fin mτ) E).val *
        (τ g).val * T.val) →
      ∀ (hτO : ∀ k : ℕ, IsOpen (((Matrix.GeneralLinearGroup.map
        (Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ k}))).comp τO).ker : Set
        (EtaleFundamentalGroup X.1 x))),
      ∃ c t : ℕ, ∀ N' : ℕ,
        ∃ (h : (LAdicSheaf.padicTower B X ℓ G.toLAdicSheaf).obj (op N') ⟶
          (etaleModuleRestrictScalars ((Ideal.Quotient.mk
          (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).comp
          (algebraMap ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))) X.1).obj
          ((lisseEtaleSheaf B X x (integralClosure ℤ_[ℓ] E ⧸ Ideal.span
          {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).obj
          (matrixContinuousModule.{u + 1, u + 1} (integralClosure ℤ_[ℓ] E ⧸ Ideal.span
          {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})
          ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk
          (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}))).comp τO) (hτO (N' + 1)))))
          (h' : (etaleModuleRestrictScalars ((Ideal.Quotient.mk
            (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).comp
            (algebraMap ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))) X.1).obj
            ((lisseEtaleSheaf B X x (integralClosure ℤ_[ℓ] E ⧸ Ideal.span
            {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).obj
            (matrixContinuousModule.{u + 1, u + 1}
            (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})
            ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk
            (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}))).comp τO) (hτO (N' + 1)))) ⟶
            (LAdicSheaf.padicTower B X ℓ G.toLAdicSheaf).obj (op N')),
          h ≫ h' = ℓ ^ c • 𝟙 _ ∧ h' ≫ h = ℓ ^ c • 𝟙 _ ∧
          ∀ (o : O) (o' : integralClosure ℤ_[ℓ] E), algebraMap O E o = algebraMap
            (integralClosure ℤ_[ℓ] E) E o' →
            ℓ ^ t • ((LAdicSheaf.padicTowerMap (G.act o)).app (op N') ≫ h) =
              ℓ ^ t • (h ≫ (etaleModuleRestrictScalars
                ((Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).comp
                (algebraMap ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))) X.1).map
                ((etaleModuleSMul X.1 (Ideal.Quotient.mk
                (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}) o')).app
                ((lisseEtaleSheaf B X x (integralClosure ℤ_[ℓ] E ⧸ Ideal.span
                {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).obj
                (matrixContinuousModule.{u + 1, u + 1}
                (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})
                ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk
                (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}))).comp τO)
                (hτO (N' + 1)))))) ∧
            ℓ ^ t • ((etaleModuleRestrictScalars ((Ideal.Quotient.mk
              (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).comp
              (algebraMap ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))) X.1).map
              ((etaleModuleSMul X.1 (Ideal.Quotient.mk
              (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}) o')).app
              ((lisseEtaleSheaf B X x (integralClosure ℤ_[ℓ] E ⧸ Ideal.span
              {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).obj
              (matrixContinuousModule.{u + 1, u + 1}
              (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})
              ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk
              (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}))).comp τO) (hτO (N' + 1))))) ≫
              h') =
              ℓ ^ t • (h' ≫ (LAdicSheaf.padicTowerMap (G.act o)).app (op N'))

/-- **The Fourier side of the level isogeny**: for an `O_E`-model `σ_E` of
`σ' = σ₁ ⊗ L_{ψ'}(a xⁿ)`, there are exponents `c`, `t`, independent of the level `N'`, and at
every level `N'` a nontrivial additive character `ψ_N : k' → Λ = O_E/ℓ^{N'+1}` with Fourier
transform `Φ` and an `ℓᶜ`-isogeny of sheaves of `ℤ_ℓ`-modules on `V'` between
`jV'⁻¹ H¹(Φ(ℱ_{σ_E mod ℓ^{N'+1}}))` and `jV'⁻¹ R¹pr₂!` of the level `N'` of the Fourier family
sheaf `K` (`Stacks.EtaleCohomology.laumonFourierFamilySheaf`), commuting up to `ℓᵗ` with every
element `o` of the integral part of `E` acting on `K` (acting on the source through `O_E`). -/
def LaumonFourierFamilyLevelIsogenyInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] [Fact ℓ.Prime]
    (k' : Type u) [Field k'] [Fintype k'] (p : ℕ) [Fact p.Prime] [CharP k' p], ℓ ≠ p →
    ∀ (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) (ψ' : AddChar k' E), ψ' ≠ 1 →
    (∃ ζ : E, IsPrimitiveRoot ζ p) → ∀ (n : ℕ) (a : k')
    (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
    (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (p₀ : (finiteEtaleFiberFunctor z).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonFourierKernel k' n a)))
    {m : ℕ} (σ₁ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) E) (hσ₁ : Continuous (restrictScalarsRep b σ₁))
    (p₁ : (finiteEtaleFiberFunctor (z.map (laumonFamilyPr₁ k'))).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial k') (Polynomial.C a * Polynomial.X ^ n)))
    (σO : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →* GL
      (Fin m) (integralClosure ℤ_[ℓ] E)) (T₁ : GL (Fin m) E),
    (∀ g, (σO g).val.map (algebraMap (integralClosure ℤ_[ℓ] E) E) =
      (T₁⁻¹ : GL (Fin m) E).val * (characterTwist σ₁ (Stacks.ArtinSchreier.artinSchreierCharacter
        k' (Polynomial k') (Polynomial.C a * Polynomial.X ^ n) ψ' (z.map (laumonFamilyPr₁ k'))
          p₁) g).val * T₁.val) →
    ∀ (hσO : ∀ k : ℕ, IsOpen (((Matrix.GeneralLinearGroup.map
      (Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ k}))).comp σO).ker : Set
      (EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')))))
      (jg : CompactificationOf (Over.mk (B.inclusion.map (laumonFamilyProjection k' B hS hL))))
        (V' : B.Scheme)
      (jV' : V' ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL),
      ∃ c t : ℕ, ∀ N' : ℕ,
        ∃ (ψN : AddChar k' (integralClosure ℤ_[ℓ] E ⧸ Ideal.span
          {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})) (_ : ∑ x, ψN x = 0)
          (p₀' : (finiteEtaleFiberFunctor (affineLineOrigin k')).obj
            (Stacks.ArtinSchreier.cover k' (Polynomial k') Polynomial.X))
          (j : CompactificationOf (Over.mk (Stacks.ArtinSchreier.affineLineStructureMap k')))
          (h : (etaleModuleRestrictScalars ((Ideal.Quotient.mk
            (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).comp
            (algebraMap ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))) V'.1).obj
            ((etaleModuleInverseImage.{u, 0} (integralClosure ℤ_[ℓ] E ⧸ Ideal.span
            {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}) (B.inclusion.map jV')).obj
                ((DerivedCategory.Plus.homologyFunctor _ 1).obj
                  ((fourierTransform k' (integralClosure ℤ_[ℓ] E ⧸ Ideal.span
                    {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}) ψN B p₀' j).obj
                    ((DerivedCategory.Plus.singleFunctor _ 0).obj
                      ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
                        (z.map (laumonFamilyPr₁ k'))
                          (integralClosure ℤ_[ℓ] E ⧸ Ideal.span
                          {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).obj
                          (matrixContinuousModule.{u + 1, u + 1}
                            (integralClosure ℤ_[ℓ] E ⧸ Ideal.span
                            {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})
                            ((Matrix.GeneralLinearGroup.map
                            (Ideal.Quotient.mk (Ideal.span
                            {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}))).comp σO)
                            (hσO (N' + 1)))))))) ⟶
            ((LAdicSheaf.padicTower B (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k'))
              B hS) ℓ (laumonFourierFamilySheaf k' B hS b ψ' n a z p₀ σ₁ hσ₁).toLAdicSheaf ⋙
              lowerShriekHomology ℤ_[ℓ] (B.inclusion.map (laumonFamilyProjection k' B hS hL)) jg
              1) ⋙ etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV')).obj (op N'))
          (h' : ((LAdicSheaf.padicTower B (Stacks.ArtinSchreier.specObject
            (Polynomial (Polynomial k')) B hS) ℓ (laumonFourierFamilySheaf k' B hS b ψ' n a z p₀ σ₁
            hσ₁).toLAdicSheaf ⋙ lowerShriekHomology ℤ_[ℓ]
            (B.inclusion.map (laumonFamilyProjection k' B hS hL)) jg 1) ⋙
            etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV')).obj (op N') ⟶
            (etaleModuleRestrictScalars ((Ideal.Quotient.mk
              (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).comp
              (algebraMap ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))) V'.1).obj
              ((etaleModuleInverseImage.{u, 0} (integralClosure ℤ_[ℓ] E ⧸ Ideal.span
              {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}) (B.inclusion.map jV')).obj
                ((DerivedCategory.Plus.homologyFunctor _ 1).obj
                  ((fourierTransform k' (integralClosure ℤ_[ℓ] E ⧸ Ideal.span
                    {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}) ψN B p₀' j).obj
                    ((DerivedCategory.Plus.singleFunctor _ 0).obj
                      ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
                        (z.map (laumonFamilyPr₁ k'))
                          (integralClosure ℤ_[ℓ] E ⧸ Ideal.span
                          {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).obj
                          (matrixContinuousModule.{u + 1, u + 1}
                            (integralClosure ℤ_[ℓ] E ⧸ Ideal.span
                            {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})
                            ((Matrix.GeneralLinearGroup.map
                            (Ideal.Quotient.mk (Ideal.span
                            {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}))).comp σO)
                            (hσO (N' + 1))))))))),
          h ≫ h' = ℓ ^ c • 𝟙 _ ∧ h' ≫ h = ℓ ^ c • 𝟙 _ ∧
          ∀ o (o' : integralClosure ℤ_[ℓ] E), algebraMap _ E o = algebraMap
            (integralClosure ℤ_[ℓ] E) E o' →
            ℓ ^ t • ((etaleModuleRestrictScalars ((Ideal.Quotient.mk
              (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).comp
              (algebraMap ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))) V'.1).map
              ((etaleModuleSMul V'.1 (Ideal.Quotient.mk
              (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}) o')).app
              ((etaleModuleInverseImage.{u, 0} (integralClosure ℤ_[ℓ] E ⧸ Ideal.span
              {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}) (B.inclusion.map jV')).obj
                ((DerivedCategory.Plus.homologyFunctor _ 1).obj
                  ((fourierTransform k' (integralClosure ℤ_[ℓ] E ⧸ Ideal.span
                    {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}) ψN B p₀' j).obj
                    ((DerivedCategory.Plus.singleFunctor _ 0).obj
                      ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
                        (z.map (laumonFamilyPr₁ k'))
                          (integralClosure ℤ_[ℓ] E ⧸ Ideal.span
                          {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).obj
                          (matrixContinuousModule.{u + 1, u + 1}
                            (integralClosure ℤ_[ℓ] E ⧸ Ideal.span
                            {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})
                            ((Matrix.GeneralLinearGroup.map
                            (Ideal.Quotient.mk (Ideal.span
                            {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}))).comp σO)
                            (hσO (N' + 1))))))))) ≫ h) =
              ℓ ^ t • (h ≫ (Functor.whiskerRight (Functor.whiskerRight
                (LAdicSheaf.padicTowerMap ((laumonFourierFamilySheaf k' B hS b ψ' n a z p₀ σ₁
                hσ₁).act o)) (lowerShriekHomology ℤ_[ℓ]
                (B.inclusion.map (laumonFamilyProjection k' B hS hL)) jg 1))
                (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV'))).app (op N')) ∧
            ℓ ^ t • ((Functor.whiskerRight (Functor.whiskerRight
              (LAdicSheaf.padicTowerMap ((laumonFourierFamilySheaf k' B hS b ψ' n a z p₀ σ₁ hσ₁).act
              o)) (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map (laumonFamilyProjection k' B hS hL))
              jg 1)) (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV'))).app (op N') ≫
              h') =
              ℓ ^ t • (h' ≫ (etaleModuleRestrictScalars
                ((Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).comp
                (algebraMap ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))) V'.1).map
                ((etaleModuleSMul V'.1 (Ideal.Quotient.mk
                (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}) o')).app
                ((etaleModuleInverseImage.{u, 0} (integralClosure ℤ_[ℓ] E ⧸ Ideal.span
                {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}) (B.inclusion.map jV')).obj
                ((DerivedCategory.Plus.homologyFunctor _ 1).obj
                  ((fourierTransform k' (integralClosure ℤ_[ℓ] E ⧸ Ideal.span
                    {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}) ψN B p₀' j).obj
                    ((DerivedCategory.Plus.singleFunctor _ 0).obj
                      ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
                        (z.map (laumonFamilyPr₁ k'))
                          (integralClosure ℤ_[ℓ] E ⧸ Ideal.span
                          {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).obj
                          (matrixContinuousModule.{u + 1, u + 1}
                            (integralClosure ℤ_[ℓ] E ⧸ Ideal.span
                            {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})
                            ((Matrix.GeneralLinearGroup.map
                            (Ideal.Quotient.mk (Ideal.span
                            {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}))).comp σO)
                            (hσO (N' + 1))))))))))

end Pieces

section Assembly

attribute [local instance] padicIntAlgebraOfRat HasDerivedCategory.standard

/-- **The level isogeny over the integers of `E` from its two sides**: the Fourier side
(`Stacks.EtaleCohomology.LaumonFourierFamilyLevelIsogenyInput`), S7c
(`Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf.exists_higherDirectImageShriek_levelIsogeny`)
and the representation side (`Stacks.EtaleCohomology.LaumonFourierRepresentationLevelIsogenyInput`)
compose to an `ℓ^{c_B + c_S + c_A}`-isogeny over `ℤ_ℓ` commuting with `O_E` up to
`ℓ^{t_B + t_A + s}` (`ℓˢ O_E ⊆ O`), which lifts to an isogeny of sheaves of
`O_E/ℓ^{N'+1}`-modules. -/
theorem laumonFourierLevelIsogenyCoreInput_of_levelIsogenies
    (hA : LaumonFourierRepresentationLevelIsogenyInput.{u})
    (hB : LaumonFourierFamilyLevelIsogenyInput.{u}) : LaumonFourierLevelIsogenyCoreInput.{u} := by
  intro B ℓ _ _ _ _ k' _ _ p _ _ hℓp E _ _ _ d b ψ' hψ' hζ n a hS hL z p₀ m σ₁ hσ₁ p₁ V' U'
    _ _ _ jV' jU g' _ _ _ jg' hjV hpb xV r ρ hρ φ ψ₀ N hφψ hψφ mτ τ P Q hPQ hα hτ hQP σO T₁ hT₁
    hσO τO T hT hτO
  have hc :
      CompactSpace ↥(B.inclusion.obj (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)) :=
    inferInstanceAs (CompactSpace ↥(Spec (.of (Polynomial k'))))
  have hq : QuasiSeparatedSpace
      ↥(B.inclusion.obj (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)) :=
    inferInstanceAs (QuasiSeparatedSpace ↥(Spec (.of (Polynomial k'))))
  have hcomp := @hasCompactification_of_compactSpace_quasiSeparatedSpace _ _
    (B.inclusion.map (laumonFamilyProjection k' B hS hL)) hc hq
    (isSeparated_laumonFamilyProjection k' B hS hL)
    (locallyOfFiniteType_laumonFamilyProjection k' B hS hL)
    (quasiCompact_laumonFamilyProjection k' B hS hL)
  have hS7c := LAdicSheaf.CoefficientSheaf.exists_higherDirectImageShriek_levelIsogeny B ℓ
      (laumonFamilyProjection k' B hS hL) hcomp.choose g' jg' jU jV' hpb
      (laumonFourierFamilySheaf k' B hS b ψ' n a z p₀ σ₁ hσ₁) 1
  choose cS Φ Ψ hΦΨ hΨΦ hnat using hS7c
  choose cB tB ψN hψN p₀' j hb hb' hbb' hb'b hbeq using hB B ℓ k' p hℓp E b ψ' hψ' hζ n a hS hL z
    p₀ σ₁ hσ₁ p₁ σO T₁ hT₁ hσO hcomp.choose V' jV'
  choose cA tA ha ha' haa' ha'a haeq using hA B ℓ V' xV E b _
    (algebraMap_conjIntegralSubring_algebraMap _ _)
    (laumonFourierRestrictedHigherDirectImage k' B hS ℓ b ψ' n a z p₀ σ₁ hσ₁ jU g' jg') ρ hρ φ ψ₀
    N hφψ hψφ τ P Q hPQ hα hτ hQP τO T hT hτO
  choose s hs using exists_pow_mul_mem_of_forall_exists_pow_mul_mem ℓ (conjIntegralSubring
    (representationSheafConj B (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) z
      (restrictScalarsRep b (laumonFourierFamilyRep k' ψ' n a z p₀ σ₁))
      (continuous_restrictScalarsRep_laumonFourierFamilyRep k' b ψ' n a z p₀ σ₁ hσ₁))
    (restrictScalarsScalarAlgHom b m)) (algebraMap_mem_conjIntegralSubring _ _)
    (exists_pow_mul_mem_conjIntegralSubring _ _)
  refine ⟨cB + (cS + cA) + 2 * (tB + tA + s), fun N' => ?_⟩
  refine ⟨ψN N', hψN N', p₀' N', j N', ?_⟩
  refine exists_isogeny_of_restrictScalars_chain _ _ Ideal.Quotient.mk_surjective (hb N') (hb' N')
    (Ψ.app (op N')) (Φ.app (op N')) (ha N') (ha' N') (hbb' N') (hb'b N')
    (app_comp_app_eq_nsmul hΨΦ _) (app_comp_app_eq_nsmul hΦΨ _) (haa' N') (ha'a N')
    (fun o' => ?_)
  let o : conjIntegralSubring (representationSheafConj B
      (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) z
      (restrictScalarsRep b (laumonFourierFamilyRep k' ψ' n a z p₀ σ₁))
      (continuous_restrictScalarsRep_laumonFourierFamilyRep k' b ψ' n a z p₀ σ₁ hσ₁))
      (restrictScalarsScalarAlgHom b m) := ⟨_, hs o'⟩
  have h1 : algebraMap (integralClosure ℤ_[ℓ] E) E
      (((ℓ ^ s : ℕ) : integralClosure ℤ_[ℓ] E) * o') = (ℓ : E) ^ s * (o' : E) := by
    simp
  have ho : algebraMap _ E o = algebraMap (integralClosure ℤ_[ℓ] E) E
      (((ℓ ^ s : ℕ) : integralClosure ℤ_[ℓ] E) * o') := by
    rw [h1]
    rfl
  have hmk : Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})
      (((ℓ ^ s : ℕ) : integralClosure ℤ_[ℓ] E) * o') =
        ((ℓ ^ s : ℕ) : integralClosure ℤ_[ℓ] E ⧸
          Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}) * Ideal.Quotient.mk _ o' := by
    rw [map_mul, map_natCast]
  have hb₀ := hbeq N' o _ ho
  have ha₀ := haeq N' o _ ho
  exact ⟨_, hmk, _, _, hb₀.1, hb₀.2, app_comp_app_eq_comp_app (hnat o).2 _,
    app_comp_app_eq_comp_app (hnat o).1 _, ha₀.1, ha₀.2⟩

end Assembly

end Stacks.EtaleCohomology

end
