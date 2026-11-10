module
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.CategoryTheory.Abelian.Projective.Horseshoe
public import StacksFrontier.Homology.DerivedIndexing.Basic

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.PrimeToTorsion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CurveConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CurveConstantCoefficientsUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.RestrictToDenseOpen
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstantSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.Scheme.SchemeStructure
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.InverseImage
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.FiniteCohomologyOfShortExact
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak

/-!
# Finiteness of the cohomology of torsion sheaves of modules on curves

Let `Λ` be a Noetherian ring, let `k` be an algebraically closed field and let `X` be a
separated scheme of finite type over `k` of dimension at most one. This file collects the
reductions of Stacks, Section 0GJB, in the model `Stacks.EtaleCohomology.EtaleModules Λ X` of
sheaves of `Λ`-modules on `X_étale`.

## Main results

* `Stacks.EtaleCohomology.TorsionModules.module_finite_cohomology_extensionByZero_constantSheaf`
  — Stacks 0GJF: `H^q(X, j_!M̲)` is a finite `Λ`-module for every open immersion `j : U ⟶ X`
  and every finite `Λ`-module `M` annihilated by an integer `n > 0`, if `n` is prime to the
  characteristic of `k` or `X` is proper.
* `Stacks.EtaleCohomology.TorsionModules.module_finite_cohomology_of_nsmul_id_eq_zero` — the first
  step of the proof of Stacks 0GJI: finiteness for sheaves of a weak Serre class annihilated by
  an integer prime to `p` reduces, through Lemma 0GJG, to those annihilated by a prime power.
* `Stacks.EtaleCohomology.TorsionModules.etaleModuleInverseImageConstantIso` — inverse image
  carries constant sheaves of `Λ`-modules to constant sheaves.

## Implementation notes

The source proves 0GJF from Lemmas 0GJE and 0GJC after enlarging `U` to a dense open. The proof
here uses instead the localization sequence `0 → j_!M̲_U → M̲_X → i_*M̲_Z → 0` of Tag 095L for
the reduced closed complement `i : Z ⟶ X` of `U`: the long exact cohomology sequence places
`H^q(X, j_!M̲)` between `H^{q-1}(X, i_*M̲_Z)` and `H^q(X, M̲_X)`. The latter is finite by
Lemma 0GJC on `X`, and the former by Lemma 0GJC on `Z` together with Lemma 0GJD for the finite
morphism `i`; `Z` is again separated of finite type over `k` of dimension at most one, and proper
if `X` is.

Two inputs are named arguments:

* `h03SC` is **Theorem 03SC**; it is consumed by Lemma 0GJC,
  `Stacks.EtaleCohomology.TorsionModules.module_finite_etaleCohomology_constantSheaf`.
* `h0GJD` is **Lemma 0GJD**: a finite morphism of such schemes preserves
  finiteness of cohomology under direct image.

Accordingly nothing in this file carries a `@[stacks]` attribute.

## References

* [Stacks Project, Tag 0GJF](https://stacks.math.columbia.edu/tag/0GJF)
* [Stacks Project, Tag 0GJC](https://stacks.math.columbia.edu/tag/0GJC)
* [Stacks Project, Tag 0GJD](https://stacks.math.columbia.edu/tag/0GJD)
* [Stacks Project, Tag 095L](https://stacks.math.columbia.edu/tag/095L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u r

attribute [-instance] Stacks.EtaleCohomology.TorsionModules.hasSheafify_smallEtaleTopology_moduleCat

namespace Stacks.EtaleCohomology.TorsionModules

variable (Λ : Type r) [CommRing Λ]

/-- **Inverse image carries constant sheaves of `Λ`-modules to constant sheaves**: both functors
are left adjoint to sections over the final object, which base change preserves. -/
def etaleModuleInverseImageConstantIso {X Y : Scheme.{u}} (i : Y ⟶ X) :
    constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ) ⋙
        etaleModuleInverseImage.{u, r} Λ i ≅
      constantSheaf Y.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ) :=
  Stacks.ConstantSheaf.constantSheafCompSheafPullbackIso (smallEtaleBaseChange i) _ _ _
    (etaleSiteTerminalIsTerminal X)
    ((etaleSiteTerminalIsTerminal X).isTerminalObj (smallEtaleBaseChange i)) (Iso.refl _)

variable [IsNoetherianRing Λ]

/-- **Stacks 0GJF**, granted Theorem 03SC as `h03SC` (it enters through Lemma 0GJC,
`module_finite_etaleCohomology_constantSheaf`) and Lemma 0GJD as `h0GJD`.

Let `Λ` be a Noetherian ring, let `M` be a finite `Λ`-module annihilated by an integer `n > 0`,
let `k` be an algebraically closed field, let `X` be a separated scheme of finite type over `k`
of dimension at most one and let `j : U ⟶ X` be an open immersion. If `n` is prime to the
characteristic of `k`, or if `X` is proper over `k`, then `H^q_étale(X, j_!M̲)` is a finite
`Λ`-module for every `q`.
-/
theorem module_finite_cohomology_extensionByZero_constantSheaf
    (h03SC : CurveTorsionCohomologyStatement.{u, r})
    (h0GJD : ∀ {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
      (πX : X ⟶ Spec (.of k)) (πY : Y ⟶ Spec (.of k))
      [IsSeparated πX] [LocallyOfFiniteType πX] [QuasiCompact πX]
      [IsSeparated πY] [LocallyOfFiniteType πY] [QuasiCompact πY],
      topologicalKrullDim X ≤ 1 → topologicalKrullDim Y ≤ 1 →
      ∀ (f : X ⟶ Y) [IsFinite f], f ≫ πY = πX → ∀ (F : EtaleModules.{u, r} Λ X) (q : ℕ),
        Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj F) →
        Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ Y).rightDerived q).obj
          ((etaleModuleDirectImage.{u, r} Λ f).obj F)))
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π] (hX : topologicalKrullDim X ≤ 1)
    (M : ModuleCat.{max (u + 1) r} Λ) [Module.Finite Λ M] (n : ℕ) (hn : 0 < n)
    (hM : ∀ m : M, n • m = 0) (h : n.Coprime (ringExpChar k) ∨ IsProper π)
    {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (q : ℕ) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj
      ((etaleModuleExtensionByZero.{u, r} Λ j).obj
        ((constantSheaf U.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M))) := by
  -- the reduced closed complement of `U`
  let Zc : TopologicalSpace.Closeds X :=
    ⟨(Set.range j.base)ᶜ, isClosed_compl_iff.2 j.isOpenEmbedding.isOpen_range⟩
  let S := Scheme.reducedInduced Zc
  let Z := S.toScheme
  let i : Z ⟶ X := S.ι
  have hij : Set.range j.base = (Set.range i.base)ᶜ := by
    rw [show Set.range i.base = (Zc : Set X) from S.range_ι]
    exact (compl_compl _).symm
  have hZ : topologicalKrullDim Z ≤ 1 :=
    (i.isClosedEmbedding.isInducing.topologicalKrullDim_le).trans hX
  have hZh : n.Coprime (ringExpChar k) ∨ IsProper (i ≫ π) :=
    h.imp id fun hp =>
      have : IsClosedImmersion i := inferInstanceAs (IsClosedImmersion S.ι)
      MorphismProperty.comp_mem @IsProper i π inferInstance hp
  -- the localization sequence of `M̲_X`
  let MX := (constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M
  obtain ⟨hz, hS⟩ := shortExact_etaleModuleExtensionByZero_directImage Λ i j hij MX
  set T := ShortComplex.mk ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit.app MX)
    ((etaleModuleInverseImageAdj.{u, r} Λ i).unit.app MX) hz with hT
  set D := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (etaleModuleGlobalSections.{u, r} Λ X) with hD
  -- finiteness of cohomology is invariant under isomorphism
  have hiso : ∀ {Y : Scheme.{u}} {A B : EtaleModules.{u, r} Λ Y} (e : A ≅ B) (m : ℕ),
      Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ Y).rightDerived m).obj A) →
      Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ Y).rightDerived m).obj B) :=
    fun e m _ => .equiv
      (((etaleModuleGlobalSections.{u, r} Λ _).rightDerived m).mapIso e).toLinearEquiv
  -- the middle term has finite cohomology
  have hB : ∀ m : ℕ, Module.Finite Λ ((D.functor m).obj T.X₂) := fun m =>
    module_finite_etaleCohomology_constantSheaf Λ h03SC π hX M n hn hM h m
  -- the right-hand term has finite cohomology
  have hC : ∀ m : ℕ, Module.Finite Λ ((D.functor m).obj T.X₃) := by
    intro m
    have := module_finite_etaleCohomology_constantSheaf Λ h03SC (i ≫ π) hZ M n hn hM hZh m
    exact h0GJD (i ≫ π) π hZ hX i rfl _ m
      (hiso ((etaleModuleInverseImageConstantIso Λ i).app M).symm m this)
  -- the left-hand term is `j_!M̲_U`
  have hA : Module.Finite Λ ((D.functor q).obj T.X₁) := by
    match q with
    | 0 => exact module_finite_of_mono Λ ((D.functor 0).map T.f) (D.mono_map_f hS) (hB 0)
    | (m + 1) => exact module_finite_of_exact Λ _ (D.exact_δ₂ hS m) (hC m) (hB (m + 1))
  have e : (etaleModuleExtensionByZero.{u, r} Λ j).obj
      ((constantSheaf U.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M) ≅ T.X₁ :=
    (etaleModuleExtensionByZero.{u, r} Λ j).mapIso
      (((etaleModuleInverseImageConstantIso Λ j).app M).symm ≪≫
        (etaleModuleInverseImageRestrictionIso.{u, r} Λ j).app MX)
  exact hiso e.symm q hA

/-- **Reduction to prime-power torsion** (first step of the proof of Stacks 0GJI). Let `C` be a
weak Serre class of sheaves of `Λ`-modules on `X_étale` (for instance the constructible ones).
If every sheaf in `C` annihilated by a power of a prime `ℓ` prime to `p` has finite cohomology,
then so does every sheaf in `C` annihilated by an integer `n > 0` prime to `p`.

Writing `n = ℓ^a m` with `ℓ` the smallest prime factor of `n` and `ℓ ∤ m`, the short exact
sequence `0 → ℱ[ℓ^a] → ℱ → ℱ/ℱ[ℓ^a] → 0` has its outer terms in `C`, annihilated by `ℓ^a` and
by `m < n` respectively, and Lemma 0GJG concludes by induction on `n`. -/
theorem module_finite_cohomology_of_nsmul_id_eq_zero {X : Scheme.{u}}
    (C : ObjectProperty (EtaleModules.{u, r} Λ X)) [C.IsWeakSerreClass] (p : ℕ)
    (hprime : ∀ G : EtaleModules.{u, r} Λ X, C G → ∀ ℓ a : ℕ, ℓ.Prime → ℓ.Coprime p →
      ℓ ^ a • 𝟙 G = 0 → ∀ q : ℕ,
        Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj G))
    (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p) (F : EtaleModules.{u, r} Λ X) (hF : C F)
    (hnF : n • 𝟙 F = 0) (q : ℕ) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj F) := by
  induction n using Nat.strong_induction_on generalizing F with
  | _ n ih =>
  by_cases h1 : n = 1
  · subst h1
    have hZ : IsZero F := by
      rw [IsZero.iff_id_eq_zero]
      simpa using hnF
    exact module_finite_of_isZero Λ
      (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).map_isZero hZ)
  -- the smallest prime factor of `n` and the decomposition `n = ℓ ^ a * m`
  set ℓ := n.minFac with hℓdef
  have hℓ : ℓ.Prime := Nat.minFac_prime h1
  have hℓn : ℓ ∣ n := Nat.minFac_dvd n
  set a := n.factorization ℓ with hadef
  set m := n / ℓ ^ a with hmdef
  have hnm : ℓ ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n ℓ
  have ha : 0 < a := hℓ.factorization_pos_of_dvd hn.ne' hℓn
  have hm : 0 < m := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hnm; omega
  have hmn : m < n := by
    rw [← hnm]
    exact lt_mul_of_one_lt_left hm (Nat.one_lt_pow ha.ne' hℓ.one_lt)
  have hℓp : ℓ.Coprime p := Nat.Coprime.coprime_dvd_left hℓn hnp
  have hmp : m.Coprime p := Nat.Coprime.coprime_dvd_left ⟨ℓ ^ a, by rw [← hnm, mul_comm]⟩ hnp
  -- the short exact sequence `0 → ℱ[ℓ^a] → ℱ → ℱ / ℱ[ℓ^a] → 0`
  let f : F ⟶ F := ℓ ^ a • 𝟙 F
  let S := ShortComplex.mk (kernel.ι f) (cokernel.π (kernel.ι f)) (cokernel.condition _)
  have hS : S.ShortExact := { exact := S.exact_of_g_is_cokernel (cokernelIsCokernel _) }
  have hK : ℓ ^ a • 𝟙 (kernel f) = 0 := by
    have h : (ℓ ^ a • 𝟙 (kernel f)) ≫ kernel.ι f = kernel.ι f ≫ f := by
      change _ = kernel.ι f ≫ (ℓ ^ a • 𝟙 F)
      rw [Preadditive.nsmul_comp, Category.id_comp, Preadditive.comp_nsmul, Category.comp_id]
    rw [← cancel_mono (kernel.ι f), h, kernel.condition, Limits.zero_comp]
  have hQ : m • 𝟙 (cokernel (kernel.ι f)) = 0 := by
    have h : cokernel.π (kernel.ι f) ≫ (m • 𝟙 (cokernel (kernel.ι f))) =
        (m • 𝟙 F) ≫ cokernel.π (kernel.ι f) := by
      rw [Preadditive.comp_nsmul, Category.comp_id, Preadditive.nsmul_comp, Category.id_comp]
    rw [← cancel_epi (cokernel.π (kernel.ι f)), h, Limits.comp_zero]
    have hfac : m • 𝟙 F = kernel.lift f (m • 𝟙 F) (by
        rw [Preadditive.nsmul_comp, Category.id_comp]
        change m • (ℓ ^ a • 𝟙 F) = 0
        rw [smul_smul, mul_comm, hnm, hnF]) ≫ kernel.ι f :=
      (kernel.lift_ι _ _ _).symm
    rw [hfac, Category.assoc, cokernel.condition, Limits.comp_zero]
  have hCK : C (kernel f) := C.prop_kernel f hF hF
  have hCQ : C (cokernel (kernel.ι f)) := C.prop_cokernel (kernel.ι f) hCK hF
  exact Stacks.Cohomology.module_finite_cohomology_of_shortExact X.smallEtaleTopology Λ S hS q
    (hprime _ hCK ℓ a hℓ hℓp hK q) (ih m hmn hm hmp _ hCQ hQ)

end Stacks.EtaleCohomology.TorsionModules

end
