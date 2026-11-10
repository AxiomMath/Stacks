module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BoundedBelow
public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.TruncationTriangleCriterion
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.DerivedSections
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.DualityHomEquiv

/-!
# The relative dualizing complex of a modification of a surface lives in degrees `≥ -2`

Let `A` be a Noetherian normal local domain of dimension two, `ω_A` a finite `A`-module of
positive depth, and `f : X ⟶ Spec(A)` a modification with `X` normal. Then
`ω_X^• = f^×(ω_A[2]^~)` has no cohomology in degrees below `-2`. This is what makes
`ω_X = H^{-2}(ω_X^•)` of [Stacks, Tag 0B4R] corepresent `Hom(𝒪_X[2], ω_X^•)` in the proof of
[Stacks, Tag 0EA2].

The proof: `ω_X^•` is bounded below ([Stacks, Tag 0A9I]). If `b ≤ -3` were its lowest degree, the
identity of `𝒢 = H^b(ω_X^•)` would give a morphism `𝒢[-b] ⟶ ω_X^•`; by duality it is a morphism
`RΓ(X, 𝒢)[-b] ⟶ ω_A[2]` of `D(A)`. The source has cohomology in degrees `≤ b + 1 ≤ -2` only, and
its cohomology in degree `-2` is `H^{-2-b}(X, 𝒢)`, which is either zero or `H¹(X, 𝒢)`, a module
supported at the closed point. A finite module of positive depth admits no nonzero map from such a
module, so the morphism vanishes, hence `𝒢 = 0`.

## Main results

* `AlgebraicGeometry.DualizingDivisor.linearMap_eq_zero_of_one_le_depth`: a module killed off the
  closed point maps to zero in a finite module of positive depth.
* `AlgebraicGeometry.DualizingDivisor.isGE_twistedInverseImage`: `ω_X^•` lies in degrees `≥ -2`.

## References

* [Stacks Project, Tag 0A9I](https://stacks.math.columbia.edu/tag/0A9I)
* [Stacks Project, Tag 0EA2](https://stacks.math.columbia.edu/tag/0EA2)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Pretriangulated Stacks.Duality

universe u

namespace AlgebraicGeometry.DualizingDivisor

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- **A module supported at the closed point maps to zero in a module of positive depth.** If every
element of `M` is killed by an element outside each prime `𝔭 ≠ 𝔪`, then every `A`-linear map from
`M` to a finite module `N` of positive depth vanishes: a nonzero image `y` would make the maximal
ideal the only associated prime of `A·y ⊆ N`, contradicting `depth N ≥ 1`. -/
theorem linearMap_eq_zero_of_one_le_depth {M N : Type u} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hdepth : (1 : ℕ∞) ≤ Module.depth A (IsLocalRing.maximalIdeal A) N)
    (hM : ∀ (p : Ideal A) (_ : p.IsPrime), p ≠ IsLocalRing.maximalIdeal A →
      ∀ x : M, ∃ c : A, c ∉ p ∧ c • x = 0)
    (φ : M →ₗ[A] N) : φ = 0 := by
  ext x
  by_contra hne
  let S := Submodule.span A {φ x}
  have : Nontrivial S := ⟨⟨⟨φ x, Submodule.mem_span_singleton_self _⟩, 0, fun h => hne
    (by simpa using congrArg Subtype.val h)⟩⟩
  obtain ⟨q, hq⟩ := associatedPrimes.nonempty A S
  have hqm : q = IsLocalRing.maximalIdeal A := by
    by_contra hqne
    obtain ⟨c, hcq, hc⟩ := hM q hq.isPrime hqne x
    refine hcq (hq.annihilator_le (Submodule.mem_annihilator.2 fun z _ => ?_))
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 z.2
    refine Subtype.ext ?_
    change c • (z : N) = 0
    rw [← ha, smul_comm, ← map_smul, hc, map_zero, smul_zero]
  subst hqm
  have hN : IsLocalRing.maximalIdeal A ∈ associatedPrimes A N :=
    hq.map_of_injective (f := S.subtype) Subtype.val_injective
  rw [← Module.depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes] at hN
  rw [hN] at hdepth
  exact absurd hdepth (by decide)

/-- A morphism `K ⟶ ω_A[2]` vanishes when `K` lies in degrees `≤ -2` and `H^{-2}(K)` is supported
at the closed point, for `ω_A` finite of positive depth. -/
theorem eq_zero_of_isLE_of_homology_supported (ωA : ModuleCat.{u} A) [Module.Finite A ωA]
    (hdepth : (1 : ℕ∞) ≤ Module.depth A (IsLocalRing.maximalIdeal A) ωA)
    (K : DerivedCategory (ModuleCat.{u} A)) [K.IsLE (-2)]
    (hH : ∀ (p : Ideal A) (_ : p.IsPrime), p ≠ IsLocalRing.maximalIdeal A →
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).obj K,
        ∃ c : A, c ∉ p ∧ c • x = 0)
    (φ : K ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-2)).obj ωA) : φ = 0 := by
  -- the morphism factors through `τ^{≥ -2} K ≅ H^{-2}(K)[2]`
  let T := (DerivedCategory.TStructure.t.triangleLTGE (-2)).obj K
  have hφ₁ : T.mor₁ ≫ φ = 0 :=
    DerivedCategory.TStructure.t.zero_of_isLE_of_isGE _ (-3) (-2) (by omega)
      (DerivedCategory.TStructure.t.isLE_truncLT_obj _ _ _) inferInstance
  obtain ⟨ψ, hψ⟩ := Triangle.yoneda_exact₂ T
    (DerivedCategory.TStructure.t.triangleLTGE_distinguished (-2) K) φ hφ₁
  obtain ⟨ι⟩ := Stacks.PurityRamification.nonempty_iso_singleFunctor_truncGE K (-2)
  obtain ⟨χ, hχ⟩ := (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-2)).map_surjective
    (ι.inv ≫ ψ)
  have hχ0 : χ = 0 := by
    ext x
    exact LinearMap.congr_fun (linearMap_eq_zero_of_one_le_depth hdepth hH χ.hom) x
  have h₁ : ι.inv ≫ ψ = 0 := by rw [← hχ, hχ0, Functor.map_zero]
  rw [hψ, ← Iso.hom_inv_id_assoc ι ψ, h₁, comp_zero]
  exact comp_zero

variable [IsNormalDomain A]

section Concentration

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] [CompactSpace X]
  [QuasiSeparatedSpace X]

/-- `ω_X^• = f^×(ω_A[2]^~)` for a module `ω_A`, the dualizing complex of [Stacks, Tag 0B4R]
normalized with respect to `ω_A[2]`. -/
abbrev dualizingComplex (ωA : ModuleCat.{u} A) : quasiCoherentDerivedCategory X :=
  (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
    ((derivedTilde (CommRingCat.of A)).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) (-2)).obj ωA))

omit [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A] in
/-- The duality bijection is zero on the zero morphism. -/
theorem dualityHomEquiv_zero (F : quasiCoherentDerivedCategory X)
    (N : DerivedCategory (ModuleCat.{u} A)) :
    dualityHomEquiv f F N 0 = 0 := by
  have h := dualityHomEquiv_comp f N (0 : F ⟶ F) 0
  rw [zero_comp] at h
  rw [h, show (0 : F ⟶ F).hom = 0 from rfl, Functor.map_zero, zero_comp]

/-- A complex with quasi-coherent cohomology placed in a single degree. -/
def singleQuasiCoherent (G : X.Modules) [G.IsQuasicoherent] (b : ℤ) :
    quasiCoherentDerivedCategory X :=
  ⟨(DerivedCategory.singleFunctor X.Modules b).obj G, fun j => by
    have : (SheafOfModules.isQuasicoherent X.ringCatSheaf).ContainsZero :=
      AlgebraicGeometry.containsZero_isQuasicoherent X
    by_cases hj : j = b
    · subst hj
      exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules j).app G).symm
        ‹G.IsQuasicoherent›
    · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        ((DerivedCategory.homologyFunctorFactors X.Modules j).app
          ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) b).obj G)).symm
        ((SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isZero
          (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) b G j hj))⟩

/-- `RΓ(X, 𝒢[-b]) ≅ RΓ(X, 𝒢)[-b]`. -/
def derivedSectionsSingleIso (G : X.Modules) (b : ℤ) :
    (derivedGlobalSectionsOver f).obj ((DerivedCategory.singleFunctor X.Modules b).obj G) ≅
      (derivedSections f G)⟦-b⟧ :=
  (derivedGlobalSectionsOver f).mapIso
      (((DerivedCategory.singleFunctors X.Modules).shiftIso (-b) b 0 (by omega)).app G).symm ≪≫
    ((derivedGlobalSectionsOver f).commShiftIso (-b)).app _

variable (hdim : ringKrullDim A = 2) [IsNormal X] (hf : IsModification f)
include hdim hf

omit [IsProper f] [CompactSpace X] [QuasiSeparatedSpace X] in
/-- **The key step: a morphism `RΓ(X, 𝒢[-b]) ⟶ ω_A[2]` with `b ≤ -3` vanishes.** -/
theorem eq_zero_of_derivedSections_single (ωA : ModuleCat.{u} A) [Module.Finite A ωA]
    (hdepth : (1 : ℕ∞) ≤ Module.depth A (IsLocalRing.maximalIdeal A) ωA)
    (G : X.Modules) [G.IsQuasicoherent] (b : ℤ) (hb : b ≤ -3)
    (φ : (derivedGlobalSectionsOver f).obj ((DerivedCategory.singleFunctor X.Modules b).obj G) ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-2)).obj ωA) : φ = 0 := by
  let K' := (derivedGlobalSectionsOver f).obj ((DerivedCategory.singleFunctor X.Modules b).obj G)
  let e := derivedSectionsSingleIso f G b
  have : (derivedSections f G).IsLE 1 := isLE_derivedSections hdim f hf G
  have : ((derivedSections f G)⟦-b⟧).IsLE (1 + b) :=
    DerivedCategory.TStructure.t.isLE_shift _ 1 (-b) (1 + b)
  have : K'.IsLE (1 + b) := DerivedCategory.TStructure.t.isLE_of_iso e.symm _
  have : K'.IsLE (-2) := DerivedCategory.TStructure.t.isLE_of_le _ (1 + b) (-2)
  -- the cohomology of `K'` in degree `-2` is supported at the closed point
  have hH : ∀ (p : Ideal A) (_ : p.IsPrime), p ≠ IsLocalRing.maximalIdeal A →
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).obj K',
        ∃ c : A, c ∉ p ∧ c • x = 0 := by
    intro p hp hpm x
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = -2 - b := ⟨(-2 - b).toNat, by omega⟩
    let e' : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).obj K' ≅
        ((globalSectionsOver f).rightDerived m).obj G :=
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).mapIso e ≪≫
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shiftIso (-b) (-2) (m : ℤ)
          (by omega)).app _ ≪≫ homologyDerivedSectionsIso f G m
    let ε := e'.toLinearEquiv
    obtain ⟨c, hc, hcx⟩ : ∃ c : A, c ∉ p ∧ c • ε x = 0 := by
      rcases Nat.lt_or_ge 1 m with h | h
      · exact ⟨1, fun h1 => hp.ne_top ((Ideal.eq_top_iff_one p).2 h1),
          (ModuleCat.isZero_iff_subsingleton.mp
            (isZero_rightDerived_globalSectionsOver_of_one_lt hdim f hf G m h)).elim _ _⟩
      · obtain rfl : m = 1 := by omega
        exact exists_smul_eq_zero_rightDerived_one hdim f hf G p hpm (ε x)
    refine ⟨c, hc, ε.injective ?_⟩
    rw [map_smul, hcx, map_zero]
  exact eq_zero_of_isLE_of_homology_supported ωA hdepth K' hH φ

/-- **The lowest cohomology sheaf of `ω_X^•` in a degree `b ≤ -3` vanishes.** The identity of
`𝒢 = H^b(ω_X^•)` comes from a morphism `𝒢[-b] ⟶ ω_X^•`, whose dual `RΓ(X, 𝒢[-b]) ⟶ ω_A[2]`
vanishes by `eq_zero_of_derivedSections_single`. -/
theorem isZero_homology_dualizingComplex_of_isGE (ωA : ModuleCat.{u} A) [Module.Finite A ωA]
    (hdepth : (1 : ℕ∞) ≤ Module.depth A (IsLocalRing.maximalIdeal A) ωA) (b : ℤ) (hb : b ≤ -3)
    (hW : (dualizingComplex f ωA).obj.IsGE b) :
    IsZero ((DerivedCategory.homologyFunctor X.Modules b).obj (dualizingComplex f ωA).obj) := by
  let W := dualizingComplex f ωA
  let G := (DerivedCategory.homologyFunctor X.Modules b).obj W.obj
  have : G.IsQuasicoherent := W.2 b
  obtain ⟨ι, hι⟩ := (DerivedCategory.bijective_homologyFromSingle_of_isGE G W.obj b).2 (𝟙 G)
  let ι' : singleQuasiCoherent G b ⟶ W := ObjectProperty.homMk ι
  have h₀ : dualityHomEquiv f _ _ ι' = 0 :=
    eq_zero_of_derivedSections_single f hdim hf ωA hdepth G b hb _
  have h₁ : ι' = 0 :=
    (dualityHomEquiv f _ _).injective (h₀.trans (dualityHomEquiv_zero f _ _).symm)
  rw [show ι = 0 from congrArg (fun g => g.hom) h₁, map_zero] at hι
  exact (IsZero.iff_id_eq_zero G).2 hι.symm

/-- **`ω_X^•` lies in degrees `≥ -2`.** It is bounded below ([Stacks, Tag 0A9I]), and its lowest
cohomology sheaf cannot sit in a degree `≤ -3` by `isZero_homology_dualizingComplex_of_isGE`. -/
theorem isGE_dualizingComplex (ωA : ModuleCat.{u} A) [Module.Finite A ωA]
    (hdepth : (1 : ℕ∞) ≤ Module.depth A (IsLocalRing.maximalIdeal A) ωA) :
    (dualizingComplex f ωA).obj.IsGE (-2) := by
  obtain ⟨Nb, hNb⟩ := exists_isGE_twistedInverseImage_obj f
  have hN : ((derivedTilde (CommRingCat.of A)).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) (-2)).obj ωA)).obj.IsGE (-2) :=
    have : ((DerivedCategory.singleFunctor (Spec (CommRingCat.of A)).Modules (-2)).obj
        ((tilde.functor (CommRingCat.of A)).obj ωA)).IsGE (-2) := inferInstance
    DerivedCategory.TStructure.t.isGE_of_iso
      (X := (DerivedCategory.singleFunctor (Spec (CommRingCat.of A)).Modules (-2)).obj
        ((tilde.functor (CommRingCat.of A)).obj ωA))
      (((tilde.functor (CommRingCat.of A)).mapDerivedCategorySingleFunctor (-2)).app ωA).symm
      (-2)
  have h₀ := hNb _ (-2) hN
  suffices H : ∀ m : ℕ, (dualizingComplex f ωA).obj.IsGE (-2 - m) →
      (dualizingComplex f ωA).obj.IsGE (-2) from
    H Nb.toNat (DerivedCategory.TStructure.t.isGE_of_ge _ (-2 - Nb.toNat) (-2 - Nb) (by omega))
  intro m
  induction m with
  | zero => exact fun h => by simpa using h
  | succ m ih =>
    intro h
    apply ih
    rw [DerivedCategory.isGE_iff] at h ⊢
    intro i hi
    by_cases hi' : i < -2 - ((m + 1 : ℕ) : ℤ)
    · exact h i hi'
    · obtain rfl : i = -2 - ((m + 1 : ℕ) : ℤ) := by omega
      exact isZero_homology_dualizingComplex_of_isGE f hdim hf ωA hdepth _ (by omega)
        ((DerivedCategory.isGE_iff _ _).2 h)

end Concentration

end AlgebraicGeometry.DualizingDivisor

end
