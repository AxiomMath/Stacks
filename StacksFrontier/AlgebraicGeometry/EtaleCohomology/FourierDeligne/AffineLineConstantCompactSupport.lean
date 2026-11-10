module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.AffineLineUnitCompactSupport
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierCoefficientVanishing

/-!
# `Rf_!(M_{𝔸¹})` lives in degree two and detects `M`

Let `k` be a finite field with `q` elements, `Λ` a finite commutative ring in which `q` is
invertible, `M` a finite `Λ`-module and `f : 𝔸¹_k ⟶ Spec k` with any compactification. Then

* `Hⁱ_c(𝔸¹_k̄, M) = 0` for `i ≠ 2`, and `H²_c(𝔸¹_k̄, M) ≠ 0` when `M ≠ 0`;
* consequently `Hⁱ(Rf_!(M_{𝔸¹})) = 0` in `Sh(Spec k, Λ)` for `i ≠ 2`, and
  `H²(Rf_!(M_{𝔸¹})) = 0` only when `M = 0`.

This is the computation `RΓ_c(𝔸¹_k̄, Λ) = Λ(-1)[-2]` (without the Tate twist) used in the Fourier
inversion of Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH): the
composite of two Fourier transforms is the functor `D` of compactly supported cohomology along
the fibres of an affine line bundle, which is exact into degree two and reflects zero objects.

The proof is a dévissage from the case `Λ = M = ℤ/ℓ`
(`Stacks.EtaleCohomology.subsingleton_compactSupportSheafCohomology_unitSheaf_affineLine`):

* over `ℤ/ℓ`, a finite module is an extension of a smaller one by a line, and a nonzero one has a
  line as a retract;
* a `Λ`-module killed by a prime `ℓ ∤ q` is compared with the same group as a `ℤ/ℓ`-module by
  restriction of scalars along `ℤ/m → Λ` and `ℤ/m → ℤ/ℓ`, through the lisse sheaves of the
  modules with trivial action (Tag 03V2's comparison of `RΓ_c` with restriction of scalars);
* in general `0 → pM → M → M/pM → 0` for a prime `p ∣ #M`; in degree two the long exact
  sequence gives `H²_c(M) ↠ H²_c(M/pM)`, since `H³_c(pM) = 0`;
* finally the stalk of `Hⁱ(Rf_! K)` at `Spec k̄` is `Hⁱ(RΓ(Spec k̄, -))` of its inverse image,
  which is `Hⁱ_c(𝔸¹_k̄, M)` by Tag 0GK0.

## Main results

* `Stacks.EtaleCohomology.surjective_homology_compactSupportFrobeniusFunctor_map_g`.
* `Stacks.EtaleCohomology.isZero_homology_iff_isZero_homology_derivedGlobalSections_inverseImage`.
* `Stacks.EtaleCohomology.subsingleton_compactSupportSheafCohomology_constantSheaf_affineLine` and
  `Stacks.EtaleCohomology.nontrivial_compactSupportSheafCohomology_two_constantSheaf_affineLine`.
* `Stacks.EtaleCohomology.isZero_homology_derivedLowerShriek_constantSheaf_affineLine` and
  `subsingleton_of_isZero_homology_two_derivedLowerShriek_constantSheaf_affineLine`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open Stacks.EtaleCohomology.ExtensionTorsor Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### The connecting map of `Hⁱ_c(X_k̄, -)` -/

section Connecting

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar]

omit [Fintype k] in
/-- **`Hⁱ_c(X_k̄, K₂) → Hⁱ_c(X_k̄, K₃)` is onto when `Hⁱ⁺¹_c(X_k̄, K₁) = 0`**, for a short exact
sequence `0 → K₁ → K₂ → K₃ → 0` of bounded below complexes: the long exact sequence of the
distinguished triangle of compactly supported cohomology. -/
theorem surjective_homology_compactSupportFrobeniusFunctor_map_g [Finite k]
    {S : ShortComplex (CochainComplex (EtaleModules.{u, 0} Λ X) ℤ)} (hS : S.ShortExact)
    (h₁ : CochainComplex.plus _ S.X₁) (h₂ : CochainComplex.plus _ S.X₂)
    (h₃ : CochainComplex.plus _ S.X₃) (i : ℤ)
    (hz : IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) (i + 1)).obj
      ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).obj ⟨S.X₁, h₁⟩))) :
    Function.Surjective
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
        ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map
          (ObjectProperty.homMk S.g : (⟨S.X₂, h₂⟩ : CochainComplex.Plus _) ⟶ ⟨S.X₃, h₃⟩))).hom := by
  cases nonempty_fintype k
  obtain ⟨p, hp⟩ := CharP.exists k
  have : CharP k p := hp
  obtain ⟨n, hpr, hn⟩ := FiniteField.card k p
  have : Fact p.Prime := ⟨hpr⟩
  have hT := compactSupportFrobeniusTriangle_distinguished.{u, 0} Λ f j kbar p n hn hS h₁ h₂ h₃
  have hepi := (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff _ hT i (i + 1) rfl).2
    (hz.eq_of_tgt _ _)
  exact (ModuleCat.epi_iff_surjective _).1 hepi

end Connecting

/-! ### Cohomology sheaves on `Spec k` are seen by `RΓ(Spec k̄, -)` -/

section Detect

variable (Λ : Type) [Ring Λ] (k : Type u) [Field k] [Fintype k] (Ω : Type u) [Field Ω]
  [IsSepClosed Ω] [Algebra k Ω]

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

omit [Fintype k] in
/-- **`Hⁱ(K) = 0` on `Spec k` iff `Hⁱ(RΓ(Spec Ω, K|_Ω)) = 0`**, `Ω` a separably closed extension
of `k`: inverse image to the surjection `Spec Ω ⟶ Spec k` is exact and detects zero objects, and
over `Ω` global sections are an exact equivalence. -/
theorem isZero_homology_iff_isZero_homology_derivedGlobalSections_inverseImage [Finite k]
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ (Spec (.of k)))) (i : ℤ) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj K) ↔
      IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
        ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
          ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ
            (Stacks.Frobenius.specAlgebraMap k Ω)).obj K))) := by
  cases nonempty_fintype k
  have : HasLimitsOfSize.{0, u} (ModuleCat.{u + 1} Λ) := ModuleCat.hasLimitsOfSize.{0, u, u + 1}
  have : HasSheafify (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    hasSheafifyEtale.{u, 0} (Spec (.of Ω)) Λ
  have := isEquivalence_globalSections_of_isSepClosed Ω (ModuleCat.{u + 1} Λ)
  let g := Stacks.Frobenius.specAlgebraMap k Ω
  let G := etaleModuleInverseImage.{u, 0} Λ g
  let Γ := etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))
  let H := (DerivedCategory.Plus.homologyFunctor _ i).obj K
  let e₁ : (DerivedCategory.Plus.homologyFunctor _ i).obj
      ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ g).obj K) ≅ G.obj H :=
    (DerivedCategory.Plus.homologyFunctor _ i).mapIso
        ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso G).app K) ≪≫
      (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso G i).app K
  let e₂ := (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso Γ i).app
    ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ g).obj K)
  refine ⟨fun hH => (Functor.map_isZero Γ ((Functor.map_isZero G hH).of_iso e₁)).of_iso e₂,
    fun h => ?_⟩
  have h1 : IsZero (G.obj H) := by
    refine IsZero.of_iso ?_ e₁.symm
    rw [IsZero.iff_id_eq_zero]
    exact Γ.map_injective (by
      rw [Γ.map_id, Functor.map_zero]
      exact (h.of_iso e₂.symm).eq_of_src _ _)
  exact isZero_of_forall_isZero_etaleModuleInverseImage Λ (ι := PUnit.{u + 1}) (fun _ => g)
    (iUnion_range_specAlgebraMap (k := k) Ω) H fun _ => h1

end Detect

/-! ### `H^q(RΓ(Spec k̄, (Rf_! G)|_{k̄}))` is `H^q_c(X_k̄, G)` -/

section Stalk

variable (Λ : Type) [Ring Λ] [Finite Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

/-- **`Hⁱ(RΓ(Spec k̄, (Rf_! G)|_{k̄})) ≅ Hⁱ_c(X_k̄, G)`** for a sheaf `G` (Tag 0GK0 and the
comparison of `Hⁱ_c(X_k̄, -)` with compactly supported cohomology over `k̄`). -/
def derivedLowerShriekSingleStalkIso (G : EtaleModules.{u, 0} Λ X) (i : ℤ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
        ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
          ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ
              (Stacks.Frobenius.specAlgebraMap k kbar)).obj
            ((derivedLowerShriek.{u, 0} f j Λ).obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))) ≅
      (compactSupportSheafCohomology Λ f j kbar i).obj G :=
  let g := Stacks.Frobenius.specAlgebraMap k kbar
  let K := (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) 0).obj G
  have sq : IsPullback (pullback.fst f g) (pullback.snd f g) f g := IsPullback.of_hasPullback f g
  compactlySupportedCohomologyGroupBaseChangeIso Λ sq j K (isTorsionPlus_of_finite Λ X K) i ≪≫
    (compactlySupportedCohomologyGroup.{u, 0} kbar (pullback.snd f g) (j.baseChange sq) Λ i).mapIso
      ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
        (etaleModuleInverseImage.{u, 0} Λ (pullback.fst f g)) 0).app G) ≪≫
    (compactSupportSheafCohomologyIsoCompactlySupportedCohomologyGroup Λ f j kbar G i).symm

end Stalk

/-! ### Constant coefficients on the affine line -/

section Constant

variable (k : Type u) [Field k] [Fintype k]

/-- **The constant sheaf functor on `𝔸¹_k`**, from `Λ`-modules to sheaves of `Λ`-modules on
`(𝔸¹_k)_étale`. -/
abbrev affineLineConstantSheaf (Λ : Type) [Ring Λ] :
    ModuleCat.{u + 1} Λ ⥤ EtaleModules.{u, 0} Λ (Spec (.of k[X])) :=
  constantSheaf (Spec (.of k[X])).smallEtaleTopology (ModuleCat.{u + 1} Λ)

/-- The constant sheaf functor on `𝔸¹_k` preserves finite colimits. -/
private theorem preservesFiniteColimits_affineLineConstantSheaf (k : Type u) [Field k]
    (Λ : Type) [Ring Λ] :
    PreservesFiniteColimits (affineLineConstantSheaf k Λ) :=
  have := (constantSheafAdj (Spec (.of k[X])).smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (isTerminalEtaleMkId (Spec (.of k[X])))).leftAdjoint_preservesColimits
  inferInstance

/-- A constant sheaf placed in degree zero is a bounded below complex. -/
private theorem plus_single_constantSheaf (k : Type u) [Field k] (Λ : Type) [Ring Λ]
    (M : ModuleCat.{u + 1} Λ) :
    CochainComplex.plus _ ((HomologicalComplex.single
      (EtaleModules.{u, 0} Λ (Spec (.of k[X]))) (ComplexShape.up ℤ) 0).obj
        ((affineLineConstantSheaf k Λ).obj M)) :=
  ⟨0, inferInstance⟩

/-- `Hⁱ_c(𝔸¹_k̄, -)` of constant sheaves is exact in the middle on a short exact sequence. -/
private theorem exact_compactSupportSheafCohomology_map_constantSheaf (k : Type u) [Field k]
    [Finite k] (Λ : Type) [Ring Λ] (j : CompactificationOf (Over.mk (affineLineStructureMap k)))
    (kbar : Type u) [Field kbar] [Algebra k kbar] (i : ℤ) {T : ShortComplex (ModuleCat.{u + 1} Λ)}
    (hT : T.ShortExact) :
    Function.Exact
      ((compactSupportSheafCohomology Λ (affineLineStructureMap k) j kbar i).map
        ((affineLineConstantSheaf k Λ).map T.f)).hom
      ((compactSupportSheafCohomology Λ (affineLineStructureMap k) j kbar i).map
        ((affineLineConstantSheaf k Λ).map T.g)).hom := by
  cases nonempty_fintype k
  have := preservesFiniteColimits_affineLineConstantSheaf k Λ
  exact exact_homology_compactSupportFrobeniusFunctor_map Λ (affineLineStructureMap k) j kbar
    ((hT.map_of_exact (affineLineConstantSheaf k Λ)).map_of_exact
      (HomologicalComplex.single (EtaleModules.{u, 0} Λ (Spec (.of k[X]))) (ComplexShape.up ℤ) 0))
    (plus_single_constantSheaf k Λ _) (plus_single_constantSheaf k Λ _)
    (plus_single_constantSheaf k Λ _) i

/-- **`Hⁱ_c` of constant sheaves vanishes in the middle** of a short exact sequence of modules
whose outer terms have vanishing `Hⁱ_c`. -/
private theorem subsingleton_compactSupportSheafCohomology_constantSheaf_of_shortExact
    (k : Type u) [Field k] [Finite k] (Λ : Type) [Ring Λ]
    (j : CompactificationOf (Over.mk (affineLineStructureMap k))) (kbar : Type u) [Field kbar]
    [Algebra k kbar] (i : ℤ) {T : ShortComplex (ModuleCat.{u + 1} Λ)} (hT : T.ShortExact)
    (h₁ : Subsingleton ((compactSupportSheafCohomology Λ (affineLineStructureMap k) j kbar i).obj
      ((affineLineConstantSheaf k Λ).obj T.X₁)))
    (h₃ : Subsingleton ((compactSupportSheafCohomology Λ (affineLineStructureMap k) j kbar i).obj
      ((affineLineConstantSheaf k Λ).obj T.X₃))) :
    Subsingleton ((compactSupportSheafCohomology Λ (affineLineStructureMap k) j kbar i).obj
      ((affineLineConstantSheaf k Λ).obj T.X₂)) := by
  have hex := exact_compactSupportSheafCohomology_map_constantSheaf k Λ j kbar i hT
  refine subsingleton_of_forall_eq 0 fun y => ?_
  obtain ⟨z, hz⟩ := (hex y).1 (@Subsingleton.elim _ h₃ _ _)
  rw [← hz, @Subsingleton.elim _ h₁ z 0, map_zero]

omit [Fintype k] in
/-- **A retract of coefficients is a retract on `Hⁱ_c`**: if `b ∘ a = id_M` then `Hⁱ_c(a)` is
injective. -/
theorem injective_compactSupportSheafCohomology_map_constantSheaf_of_retract (Λ : Type) [CommRing Λ]
    (j : CompactificationOf (Over.mk (affineLineStructureMap k))) (kbar : Type u) [Field kbar]
    [Algebra k kbar] (i : ℤ) {M N : ModuleCat.{u + 1} Λ} (a : M ⟶ N) (b : N ⟶ M)
    (hab : a ≫ b = 𝟙 M) :
    Function.Injective ((compactSupportSheafCohomology Λ (affineLineStructureMap k) j kbar i).map
      ((affineLineConstantSheaf k Λ).map a)).hom := by
  let H := compactSupportSheafCohomology Λ (affineLineStructureMap k) j kbar i
  have h : H.map ((affineLineConstantSheaf k Λ).map a) ≫
      H.map ((affineLineConstantSheaf k Λ).map b) = 𝟙 _ := by
    rw [← H.map_comp, ← (affineLineConstantSheaf k Λ).map_comp, hab,
      (affineLineConstantSheaf k Λ).map_id, H.map_id]
  exact Function.LeftInverse.injective (g := (H.map ((affineLineConstantSheaf k Λ).map b)).hom)
    fun z => LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) z

variable (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosed kbar] {ℓ : ℕ} [Fact ℓ.Prime]


omit [Fintype k] in
/-- **`Hⁱ_c(𝔸¹_k̄, M) = 0` for `i ≠ 2` and a finite `ℤ/ℓ`-module `M`**, by induction on `#M`: a
nonzero `M` is an extension of a smaller module by a line. -/
theorem subsingleton_compactSupportSheafCohomology_constantSheaf_affineLine_zmod [Finite k]
    (hℓ : IsUnit (ℓ : kbar)) (j : CompactificationOf (Over.mk (affineLineStructureMap k)))
    (i : ℤ) (hi : i ≠ 2) (M : ModuleCat.{u + 1} (ZMod ℓ)) [Finite M] :
    Subsingleton ((compactSupportSheafCohomology (ZMod ℓ) (affineLineStructureMap k) j kbar i).obj
      ((affineLineConstantSheaf k (ZMod ℓ)).obj M)) := by
  cases nonempty_fintype k
  have : LocallyOfFiniteType (affineLineStructureMap k) := locallyOfFiniteType_specPolynomial k
  let H := compactSupportSheafCohomology (ZMod ℓ) (affineLineStructureMap k) j kbar i
  have hunit : Subsingleton (H.obj ((affineLineConstantSheaf k (ZMod ℓ)).obj
      (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))) :=
    subsingleton_compactSupportSheafCohomology_unitSheaf_affineLine k kbar hℓ j i hi
  have : PreservesFiniteColimits (affineLineConstantSheaf k (ZMod ℓ)) :=
    have := (constantSheafAdj (Spec (.of k[X])).smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))
      (isTerminalEtaleMkId (Spec (.of k[X])))).leftAdjoint_preservesColimits
    inferInstance
  suffices h : ∀ (n : ℕ) (M : ModuleCat.{u + 1} (ZMod ℓ)) [Finite M], Nat.card M = n →
      Subsingleton (H.obj ((affineLineConstantSheaf k (ZMod ℓ)).obj M)) from h _ M rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ hn
  by_cases hM : Nontrivial M
  · obtain ⟨v, hv⟩ := exists_ne (0 : M)
    let : Fintype M := Fintype.ofFinite M
    let S := Submodule.span (ZMod ℓ) {v}
    let N₁ := ModuleCat.of (ZMod ℓ) S
    let N₂ := ModuleCat.of (ZMod ℓ) (M ⧸ S)
    have : Finite N₂ := inferInstanceAs (Finite (M ⧸ S))
    let eS : (ZMod ℓ) ≃ₗ[ZMod ℓ] S := LinearEquiv.toSpanNonzeroSingleton (ZMod ℓ) M v hv
    let e₁ : N₁ ≅ (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))) :=
      (ULift.moduleEquiv.trans eS).symm.toModuleIso
    have h₁ : Subsingleton (H.obj ((affineLineConstantSheaf k (ZMod ℓ)).obj N₁)) :=
      (H.mapIso ((affineLineConstantSheaf k (ZMod ℓ)).mapIso e₁)).toLinearEquiv.toEquiv.subsingleton
    have hcard : Nat.card N₂ < n := by
      rw [← hn]
      have hS : S ≠ ⊥ := mt Submodule.span_singleton_eq_bot.1 hv
      have := Submodule.card_eq_card_quotient_mul_card S
      change Nat.card (M ⧸ S) < Nat.card M
      have hS1 : 1 < Nat.card S := by
        have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hS
        exact Finite.one_lt_card
      have hpos : 0 < Nat.card (M ⧸ S) := Nat.card_pos
      nlinarith
    have h₃ : Subsingleton (H.obj ((affineLineConstantSheaf k (ZMod ℓ)).obj N₂)) :=
      ih _ hcard N₂ rfl
    let T := ModuleCat.shortComplexOfCompEqZero S.subtype S.mkQ (by ext; simp)
    exact subsingleton_compactSupportSheafCohomology_constantSheaf_of_shortExact k (ZMod ℓ) j
      kbar i (T := T) (ModuleCat.shortComplex_shortExact T (LinearMap.exact_subtype_mkQ S)
        S.injective_subtype S.mkQ_surjective) h₁ h₃
  · rw [not_nontrivial_iff_subsingleton] at hM
    exact (injective_compactSupportSheafCohomology_map_constantSheaf_of_retract k (ZMod ℓ) j
      kbar i (0 : M ⟶ (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))) 0 (by
        ext x
        exact Subsingleton.elim _ _)).subsingleton

omit [Fintype k] in
/-- **`H²_c(𝔸¹_k̄, M) ≠ 0` for a nonzero finite `ℤ/ℓ`-module `M`**: the line `ℤ/ℓ` is a retract
of `M`, and `H²_c(𝔸¹_k̄, ℤ/ℓ)` has `ℓ` elements. -/
theorem nontrivial_compactSupportSheafCohomology_two_constantSheaf_affineLine_zmod [Finite k]
    (hℓ : IsUnit (ℓ : kbar)) (j : CompactificationOf (Over.mk (affineLineStructureMap k)))
    (M : ModuleCat.{u + 1} (ZMod ℓ)) [Nontrivial M] :
    Nontrivial ((compactSupportSheafCohomology (ZMod ℓ) (affineLineStructureMap k) j kbar 2).obj
      ((affineLineConstantSheaf k (ZMod ℓ)).obj M)) := by
  cases nonempty_fintype k
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  let a₀ : ZMod ℓ →ₗ[ZMod ℓ] M := LinearMap.toSpanSingleton (ZMod ℓ) M v
  have ha₀ : LinearMap.ker a₀ = ⊥ := LinearMap.ker_eq_bot.2 (smul_left_injective (ZMod ℓ) hv)
  obtain ⟨b₀, hb₀⟩ := LinearMap.exists_leftInverse_of_injective a₀ ha₀
  let a : (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))) ⟶ M :=
    ModuleCat.ofHom (a₀.comp (ULift.moduleEquiv (R := ZMod ℓ)).toLinearMap)
  let b : M ⟶ (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))) :=
    ModuleCat.ofHom ((ULift.moduleEquiv (R := ZMod ℓ)).symm.toLinearMap.comp b₀)
  have hab : a ≫ b = 𝟙 _ := by
    ext x
    change b₀ (a₀ x.down) = x.down
    rw [← LinearMap.comp_apply, hb₀]
    rfl
  have hinj := injective_compactSupportSheafCohomology_map_constantSheaf_of_retract k (ZMod ℓ) j
    kbar 2 a b hab
  have hcard := natCard_compactSupportSheafCohomology_two_unitSheaf_affineLine k kbar (ℓ := ℓ) hℓ j
  have : Finite ((compactSupportSheafCohomology (ZMod ℓ) (affineLineStructureMap k) j kbar 2).obj
      ((affineLineConstantSheaf k (ZMod ℓ)).obj
        (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))) :=
    Nat.finite_of_card_ne_zero (ne_of_eq_of_ne hcard (Fact.out : ℓ.Prime).ne_zero)
  have : Nontrivial
      ((compactSupportSheafCohomology (ZMod ℓ) (affineLineStructureMap k) j kbar 2).obj
        ((affineLineConstantSheaf k (ZMod ℓ)).obj
          (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))) :=
    Finite.one_lt_card_iff_nontrivial.mp
      (lt_of_lt_of_eq (Fact.out : ℓ.Prime).one_lt hcard.symm)
  exact hinj.nontrivial

end Constant


/-! ### Modules killed by a prime: restriction of scalars to `ℤ/ℓ` -/

section Prime

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ]
  (kbar : Type u) [Field kbar] [Algebra k kbar]

omit [Fintype k] in
/-- **`Hⁱ_c(𝔸¹_k̄, W)` over `Λ` and over `ℤ/ℓ` have the same underlying group** for a finite group
`W` that is both a `Λ`-module and a `ℤ/ℓ`-module: restriction of scalars along `ℤ/m → Λ` and
`ℤ/m → ℤ/ℓ` (`m = #Λ · ℓ`) identifies both with `Hⁱ_c` of `W` over `ℤ/m`, through the lisse
sheaves of `W` with trivial action. -/
theorem nonempty_equiv_compactSupportSheafCohomology_constantSheaf_zmod [Finite k] (ℓ : ℕ)
    [Fact ℓ.Prime] (j : CompactificationOf (Over.mk (affineLineStructureMap k))) (i : ℤ)
    (W : Type (u + 1)) [AddCommGroup W] [Module Λ W] [Module (ZMod ℓ) W] [Finite W] :
    Nonempty ((compactSupportSheafCohomology Λ (affineLineStructureMap k) j kbar i).obj
        ((affineLineConstantSheaf k Λ).obj (ModuleCat.of Λ W)) ≃
      (compactSupportSheafCohomology (ZMod ℓ) (affineLineStructureMap k) j kbar i).obj
        ((affineLineConstantSheaf k (ZMod ℓ)).obj (ModuleCat.of (ZMod ℓ) W))) := by
  cases nonempty_fintype k
  have := small_single.{u} (Spec (.of k[X]))
  let B : BigEtaleSite.{u} := BigEtaleSite.ofSet {Spec (.of k[X])}
  let 𝕌 := specObject k[X] B (schemeSizeBelow_spec_polynomial k B)
  let x := affineLineOrigin k
  let G := EtaleFundamentalGroup (Spec (.of k[X])) x
  let : Fintype Λ := Fintype.ofFinite Λ
  let m := Fintype.card Λ * ℓ
  have : NeZero m := ⟨Nat.mul_ne_zero Fintype.card_ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
  let ρ₁ : ZMod m →+* Λ :=
    ZMod.castHom ((ringChar.dvd (Nat.cast_card_eq_zero Λ)).trans (dvd_mul_right _ ℓ)) Λ
  let ρ₂ : ZMod m →+* ZMod ℓ := ZMod.castHom (dvd_mul_left ℓ _) (ZMod ℓ)
  let P := characterTwistContinuousModule Λ (1 : G →* Λˣ) (isOpen_ker_one Λ) (ModuleCat.of Λ W)
  let V := characterTwistContinuousModule (ZMod ℓ) (1 : G →* (ZMod ℓ)ˣ) (isOpen_ker_one (ZMod ℓ))
    (ModuleCat.of (ZMod ℓ) W)
  obtain ⟨eP⟩ := nonempty_lisseEtaleSheaf_iso_constantSheaf_of_trivial B 𝕌 x Λ P fun g => by
    apply CategoryTheory.End.ext
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun v => ?_
    change (((1 : G →* Λˣ) g : Λˣ) : Λ) • (v : W) = v
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
  obtain ⟨eV⟩ := nonempty_lisseEtaleSheaf_iso_constantSheaf_of_trivial B 𝕌 x (ZMod ℓ) V fun g => by
    apply CategoryTheory.End.ext
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun v => ?_
    change (((1 : G →* (ZMod ℓ)ˣ) g : (ZMod ℓ)ˣ) : ZMod ℓ) • (v : W) = v
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
  let e : finiteTypeContinuousModuleRestrictScalars ρ₂ V ≅
      finiteTypeContinuousModuleRestrictScalars ρ₁ P :=
    finiteTypeContinuousModuleIsoOfLinearEquiv (ZMod m)
      { toFun := fun v => (v : W)
        invFun := fun v => (v : W)
        map_add' := fun _ _ => rfl
        map_smul' := fun c v => by
          change ρ₂ c • (@id W v) = ρ₁ c • (@id W v)
          rw [zmod_smul_eq_val_nsmul_of_ringHom ρ₂, zmod_smul_eq_val_nsmul_of_ringHom ρ₁]
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
      fun g v => by
        change (((1 : G →* (ZMod ℓ)ˣ) g : (ZMod ℓ)ˣ) : ZMod ℓ) • (@id W v) =
          (((1 : G →* Λˣ) g : Λˣ) : Λ) • (@id W v)
        rw [MonoidHom.one_apply, Units.val_one, one_smul, MonoidHom.one_apply, Units.val_one,
          one_smul]
  let eS : (etaleModuleRestrictScalars ρ₁ (Spec (.of k[X]))).obj
        ((affineLineConstantSheaf k Λ).obj (ModuleCat.of Λ W)) ≅
      (etaleModuleRestrictScalars ρ₂ (Spec (.of k[X]))).obj
        ((affineLineConstantSheaf k (ZMod ℓ)).obj (ModuleCat.of (ZMod ℓ) W)) :=
    (etaleModuleRestrictScalars ρ₁ (Spec (.of k[X]))).mapIso eP.symm ≪≫
      lisseEtaleSheafRestrictScalarsModuleIso B 𝕌 x ρ₁ P ≪≫
      (lisseEtaleSheaf B 𝕌 x (ZMod m)).mapIso e.symm ≪≫
      (lisseEtaleSheafRestrictScalarsModuleIso B 𝕌 x ρ₂ V).symm ≪≫
      (etaleModuleRestrictScalars ρ₂ (Spec (.of k[X]))).mapIso eV
  exact ⟨(compactSupportSheafCohomologyRestrictScalarsIso ρ₁ (affineLineStructureMap k) j kbar
      _ i).toLinearEquiv.toEquiv.trans
    (((compactSupportSheafCohomology (ZMod m) (affineLineStructureMap k) j kbar i).mapIso
      eS).toLinearEquiv.toEquiv.trans
      (compactSupportSheafCohomologyRestrictScalarsIso ρ₂ (affineLineStructureMap k) j kbar
        _ i).toLinearEquiv.toEquiv.symm)⟩

variable [IsAlgClosed kbar]

omit [Fintype k] in
/-- **`Hⁱ_c(𝔸¹_k̄, M) = 0` for `i ≠ 2`** for a finite `Λ`-module `M` killed by a prime `ℓ`
invertible in `k̄`. -/
theorem subsingleton_compactSupportSheafCohomology_constantSheaf_affineLine_of_prime (ℓ : ℕ)
    [Finite k] [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : kbar))
    (j : CompactificationOf (Over.mk (affineLineStructureMap k))) (i : ℤ) (hi : i ≠ 2)
    (M : ModuleCat.{u + 1} Λ) [Finite M] (hM : ∀ v : M, ℓ • v = 0) :
    Subsingleton ((compactSupportSheafCohomology Λ (affineLineStructureMap k) j kbar i).obj
      ((affineLineConstantSheaf k Λ).obj M)) := by
  cases nonempty_fintype k
  let : Module (ZMod ℓ) M := AddCommGroup.zmodModule hM
  obtain ⟨e⟩ := nonempty_equiv_compactSupportSheafCohomology_constantSheaf_zmod k Λ kbar ℓ j i M
  have := subsingleton_compactSupportSheafCohomology_constantSheaf_affineLine_zmod k kbar hℓ j i hi
    (ModuleCat.of (ZMod ℓ) M)
  exact e.subsingleton

omit [Fintype k] in
/-- **`H²_c(𝔸¹_k̄, M) ≠ 0`** for a nonzero finite `Λ`-module `M` killed by a prime `ℓ`
invertible in `k̄`. -/
theorem nontrivial_compactSupportSheafCohomology_two_constantSheaf_affineLine_of_prime (ℓ : ℕ)
    [Finite k] [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : kbar))
    (j : CompactificationOf (Over.mk (affineLineStructureMap k)))
    (M : ModuleCat.{u + 1} Λ) [Finite M] [Nontrivial M] (hM : ∀ v : M, ℓ • v = 0) :
    Nontrivial ((compactSupportSheafCohomology Λ (affineLineStructureMap k) j kbar 2).obj
      ((affineLineConstantSheaf k Λ).obj M)) := by
  cases nonempty_fintype k
  let : Module (ZMod ℓ) M := AddCommGroup.zmodModule hM
  obtain ⟨e⟩ := nonempty_equiv_compactSupportSheafCohomology_constantSheaf_zmod k Λ kbar ℓ j 2 M
  have : Nontrivial (ModuleCat.of (ZMod ℓ) M) := inferInstanceAs (Nontrivial M)
  have := nontrivial_compactSupportSheafCohomology_two_constantSheaf_affineLine_zmod k kbar hℓ j
    (ModuleCat.of (ZMod ℓ) M)
  exact e.nontrivial

end Prime

/-! ### Finite modules over a finite ring -/

section General

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ]
  (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosed kbar]

omit [IsAlgClosed kbar] in
/-- A prime not dividing `#k` is invertible in any extension field of `k`. -/
theorem isUnit_natCast_of_not_dvd_card (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ Fintype.card k) :
    IsUnit (p : kbar) := by
  obtain ⟨p₀, hchar⟩ := CharP.exists k
  have := hchar
  obtain ⟨n, hp₀, hn⟩ := FiniteField.card k p₀
  have hne : (p : k) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff k p₀] at h
    have hpp : p₀ = p := (Nat.prime_dvd_prime_iff_eq hp₀ (Fact.out : p.Prime)).1 h
    exact hp (hn ▸ hpp ▸ dvd_pow_self p₀ n.ne_zero)
  have := (isUnit_iff_ne_zero.2 hne).map (algebraMap k kbar)
  rwa [map_natCast] at this

/-- The short exact sequence `0 → pM → M → M/pM → 0` of a module and the multiples of `p`. -/
abbrev multiplesShortComplex (p : ℕ) (M : ModuleCat.{u + 1} Λ) :
    ShortComplex (ModuleCat.{u + 1} Λ) :=
  ModuleCat.shortComplexOfCompEqZero (LinearMap.range (p • LinearMap.id : M →ₗ[Λ] M)).subtype
    (LinearMap.range (p • LinearMap.id : M →ₗ[Λ] M)).mkQ (by ext; simp)

omit [Finite Λ] in
/-- The sequence `0 → pM → M → M/pM → 0` is short exact. -/
theorem multiplesShortComplex_shortExact (p : ℕ) (M : ModuleCat.{u + 1} Λ) :
    (multiplesShortComplex Λ p M).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (LinearMap.exact_subtype_mkQ _)
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)

/-- The quotient `M/pM` is killed by `p`. -/
private theorem nsmul_eq_zero_multiplesShortComplex_X₃ (Λ : Type) [CommRing Λ] (p : ℕ)
    (M : ModuleCat.{u + 1} Λ)
    (w : (multiplesShortComplex Λ p M).X₃) : p • w = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [← Submodule.Quotient.mk_smul]
  exact (Submodule.Quotient.mk_eq_zero _).2 ⟨y, rfl⟩

/-- A nonzero finite `Λ`-module has a prime `p ∤ #k` with `pM ≠ M`, when `#k` is invertible. -/
private theorem exists_prime_not_dvd_card_exists_not_mem_range_nsmul (k : Type u) [Fintype k]
    (Λ : Type) [CommRing Λ] (hq : IsUnit (Fintype.card k : Λ)) (M : ModuleCat.{u + 1} Λ) [Finite M]
    [Nontrivial M] :
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ Fintype.card k ∧
      ∃ x : M, x ∉ LinearMap.range (p • LinearMap.id : M →ₗ[Λ] M) := by
  let : Fintype M := Fintype.ofFinite M
  have hpp : (Nat.card M).minFac.Prime := Nat.minFac_prime fun h => by
    have := Finite.one_lt_card (α := M)
    omega
  have : Fact (Nat.card M).minFac.Prime := ⟨hpp⟩
  obtain ⟨v₀, hv₀⟩ := exists_prime_addOrderOf_dvd_card (G := M) (Nat.card M).minFac
    (by rw [← Nat.card_eq_fintype_card]; exact Nat.minFac_dvd _)
  have hv₀0 : v₀ ≠ 0 := fun h => by
    rw [h, addOrderOf_zero] at hv₀
    exact hpp.one_lt.ne hv₀
  have hpv₀ : (Nat.card M).minFac • v₀ = 0 := by rw [← hv₀]; exact addOrderOf_nsmul_eq_zero v₀
  refine ⟨_, hpp, fun ⟨c, hc⟩ => hv₀0 <| ?_, ?_⟩
  · refine (hq.smul_eq_zero).1 ?_
    rw [Nat.cast_smul_eq_nsmul, hc, mul_nsmul, hpv₀, nsmul_zero]
  · by_contra h
    push Not at h
    exact hv₀0 ((Finite.injective_iff_surjective.2 fun y => h y) (by
      change (Nat.card M).minFac • v₀ = (Nat.card M).minFac • 0
      rw [hpv₀, nsmul_zero]))

include kbar in
/-- **`Hⁱ_c(𝔸¹_k̄, M) = 0` for `i ≠ 2`** and every finite `Λ`-module `M`, `#k` invertible in `Λ`:
by induction on `#M`, through `0 → pM → M → M/pM → 0` for a prime `p ∣ #M`. -/
theorem subsingleton_compactSupportSheafCohomology_constantSheaf_affineLine
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk (affineLineStructureMap k)))
    (i : ℤ) (hi : i ≠ 2) (M : ModuleCat.{u + 1} Λ) [Finite M] :
    Subsingleton ((compactSupportSheafCohomology Λ (affineLineStructureMap k) j kbar i).obj
      ((affineLineConstantSheaf k Λ).obj M)) := by
  let H := compactSupportSheafCohomology Λ (affineLineStructureMap k) j kbar i
  let F := affineLineConstantSheaf k Λ
  have hprime : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ Fintype.card k → ∀ (N : ModuleCat.{u + 1} Λ)
      [Finite N], (∀ v : N, p • v = 0) → Subsingleton (H.obj (F.obj N)) :=
    fun p _ hpk N _ hN =>
      subsingleton_compactSupportSheafCohomology_constantSheaf_affineLine_of_prime
        k Λ kbar p (isUnit_natCast_of_not_dvd_card k kbar p hpk) j i hi N hN
  suffices h : ∀ (n : ℕ) (M : ModuleCat.{u + 1} Λ) [Finite M], Nat.card M = n →
      Subsingleton (H.obj (F.obj M)) from h _ M rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ hn
  by_cases hM : Nontrivial M
  · obtain ⟨p, hpp, hpk, x, hx⟩ :=
      exists_prime_not_dvd_card_exists_not_mem_range_nsmul k Λ hq M
    have : Fact p.Prime := ⟨hpp⟩
    let : Fintype M := Fintype.ofFinite M
    let S := LinearMap.range (p • LinearMap.id : M →ₗ[Λ] M)
    let T := multiplesShortComplex Λ p M
    have : Finite T.X₁ := inferInstanceAs (Finite S)
    have : Finite T.X₃ := inferInstanceAs (Finite (M ⧸ S))
    exact subsingleton_compactSupportSheafCohomology_constantSheaf_of_shortExact k Λ j kbar i
      (T := T) (multiplesShortComplex_shortExact Λ p M)
      (ih _ (hn ▸ Finite.card_subtype_lt hx) T.X₁ rfl)
      (hprime p hpk T.X₃ (nsmul_eq_zero_multiplesShortComplex_X₃ Λ p M))
  · rw [not_nontrivial_iff_subsingleton] at hM
    obtain ⟨p, hp1, hpp⟩ := Nat.exists_infinite_primes (Fintype.card k + 1)
    have : Fact p.Prime := ⟨hpp⟩
    exact hprime p (Nat.not_dvd_of_pos_of_lt Fintype.card_pos (by omega)) M
      fun _ => Subsingleton.elim _ _

include kbar in
/-- **`H²_c(𝔸¹_k̄, M) ≠ 0`** for every nonzero finite `Λ`-module `M`, `#k` invertible in `Λ`:
for a prime `p ∣ #M`, `M/pM ≠ 0` is killed by `p`, and `H²_c(M) ↠ H²_c(M/pM)` since
`H³_c(pM) = 0`. -/
theorem nontrivial_compactSupportSheafCohomology_two_constantSheaf_affineLine
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk (affineLineStructureMap k)))
    (M : ModuleCat.{u + 1} Λ) [Finite M] [Nontrivial M] :
    Nontrivial ((compactSupportSheafCohomology Λ (affineLineStructureMap k) j kbar 2).obj
      ((affineLineConstantSheaf k Λ).obj M)) := by
  have := preservesFiniteColimits_affineLineConstantSheaf k Λ
  obtain ⟨p, hpp, hpk, x, hx⟩ := exists_prime_not_dvd_card_exists_not_mem_range_nsmul k Λ hq M
  have : Fact p.Prime := ⟨hpp⟩
  let : Fintype M := Fintype.ofFinite M
  let S := LinearMap.range (p • LinearMap.id : M →ₗ[Λ] M)
  let T := multiplesShortComplex Λ p M
  have : Finite T.X₁ := inferInstanceAs (Finite S)
  have : Finite T.X₃ := inferInstanceAs (Finite (M ⧸ S))
  have : Nontrivial T.X₃ :=
    ⟨⟨Submodule.Quotient.mk x, 0, fun h => hx ((Submodule.Quotient.mk_eq_zero S).1 h)⟩⟩
  have h₃ := nontrivial_compactSupportSheafCohomology_two_constantSheaf_affineLine_of_prime k Λ
    kbar p (isUnit_natCast_of_not_dvd_card k kbar p hpk) j T.X₃
    (nsmul_eq_zero_multiplesShortComplex_X₃ Λ p M)
  have h₁ := subsingleton_compactSupportSheafCohomology_constantSheaf_affineLine k Λ kbar hq j
    (2 + 1) (by norm_num) T.X₁
  have hsurj := surjective_homology_compactSupportFrobeniusFunctor_map_g Λ
    (affineLineStructureMap k) j kbar
    (((multiplesShortComplex_shortExact Λ p M).map_of_exact
      (affineLineConstantSheaf k Λ)).map_of_exact
      (HomologicalComplex.single (EtaleModules.{u, 0} Λ (Spec (.of k[X]))) (ComplexShape.up ℤ) 0))
    (plus_single_constantSheaf k Λ _) (plus_single_constantSheaf k Λ _)
    (plus_single_constantSheaf k Λ _) 2 (@ModuleCat.isZero_of_subsingleton _ _ _ h₁)
  exact @Function.Surjective.nontrivial _ _ h₃ _ hsurj

end General

/-! ### `Rf_!(M_{𝔸¹})` on `Spec k` -/

section Final

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ]

/-- **`Hⁱ(Rf_!(M_{𝔸¹})) = 0` for `i ≠ 2`**, `f : 𝔸¹_k ⟶ Spec k` with any compactification, `M` a
finite module over a finite ring `Λ` in which `#k` is invertible. -/
theorem isZero_homology_derivedLowerShriek_constantSheaf_affineLine
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk (affineLineStructureMap k)))
    (M : ModuleCat.{u + 1} Λ) [Finite M] (i : ℤ) (hi : i ≠ 2) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((derivedLowerShriek.{u, 0} (affineLineStructureMap k) j Λ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj ((affineLineConstantSheaf k Λ).obj M)))) := by
  have : LocallyOfFiniteType (affineLineStructureMap k) := locallyOfFiniteType_specPolynomial k
  have := subsingleton_compactSupportSheafCohomology_constantSheaf_affineLine k Λ
    (AlgebraicClosure k) hq j i hi M
  exact (isZero_homology_iff_isZero_homology_derivedGlobalSections_inverseImage Λ k
    (AlgebraicClosure k) _ i).2 ((ModuleCat.isZero_of_subsingleton _).of_iso
      (derivedLowerShriekSingleStalkIso Λ (affineLineStructureMap k) j (AlgebraicClosure k) _ i))

/-- **`H²(Rf_!(M_{𝔸¹})) = 0` only for `M = 0`**, `f : 𝔸¹_k ⟶ Spec k` with any compactification,
`M` a finite module over a finite ring `Λ` in which `#k` is invertible. -/
theorem subsingleton_of_isZero_homology_two_derivedLowerShriek_constantSheaf_affineLine
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk (affineLineStructureMap k)))
    (M : ModuleCat.{u + 1} Λ) [Finite M]
    (h : IsZero ((DerivedCategory.Plus.homologyFunctor _ 2).obj
      ((derivedLowerShriek.{u, 0} (affineLineStructureMap k) j Λ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj ((affineLineConstantSheaf k Λ).obj M))))) :
    Subsingleton M := by
  have : LocallyOfFiniteType (affineLineStructureMap k) := locallyOfFiniteType_specPolynomial k
  by_contra hM
  rw [not_subsingleton_iff_nontrivial] at hM
  have hz := ((isZero_homology_iff_isZero_homology_derivedGlobalSections_inverseImage Λ k
    (AlgebraicClosure k) _ 2).1 h).of_iso
      (derivedLowerShriekSingleStalkIso Λ (affineLineStructureMap k) j
        (AlgebraicClosure k) _ 2).symm
  have := nontrivial_compactSupportSheafCohomology_two_constantSheaf_affineLine k Λ
    (AlgebraicClosure k) hq j M
  exact not_subsingleton _ (ModuleCat.subsingleton_of_isZero hz)

end Final

end Stacks.EtaleCohomology

end
