module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassOfSection.Hyperplane
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassOfSection.RankOne
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.PullbackStable
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRank
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModuleFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Factorization
import all StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Factorization
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.FlagBundleUnconditional
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The section of the tautological subbundle over the hyperplane

Let `ℰ` be finite locally free of rank `r ≥ 2` on a scheme `X`, `π : P ⟶ X` its projective bundle
with tautological sequence `0 ⟶ ℰ' ⟶ π^*ℰ ⟶ 𝒪_P(1) ⟶ 0`, `s ∈ Γ(X, ℰ)`, and
`ι : Z(t) ⟶ P` the zero scheme of the image `t` of `π^*s` in `𝒪_P(1)`. On `Z(t)` the pulled-back
section `ι^*π^*s` maps to `ι^* t = 0`, so it comes from a unique section `s'` of `ι^*ℰ'`; the
sequence stays exact under every pullback because its quotient is invertible
(`Stacks.ProjectiveBundleSplitting.shortExact_map_pullback_of_epi_isInvertible`).

This file shows that the zero scheme of `s'`, a closed subscheme of `Z(t)` and hence of `P`, is
the inverse image `π⁻¹ Z(s)`. Both sides are characterized by which morphisms `g : T ⟶ P` factor
through them, and `g` factors through `π⁻¹ Z(s)` exactly when `g^*π^*s = 0`, which happens exactly
when `g` factors through `Z(t)` by some `h` with `h^*s' = 0`: the second step is the universal
property of the zero scheme ([Stacks, Tag 02OR]) together with injectivity of `ℰ' ⟶ π^*ℰ` after
every pullback. This is the identification `Z(s') = Z(π^*s)` of the proof of
[Stacks, Tag 0FA9].

## Main definitions

* `Stacks.Chow.bundleHyperplane` — the closed subscheme `Z(t) ⊆ P`.
* `Stacks.Chow.bundleRestrictedSection` — the section `s'` of `ι^*ℰ'`.

## Main results

* `Stacks.Chow.ker_zeroScheme_bundleRestrictedSection` — the zero scheme of `s'`, read in `P`,
  is `π⁻¹ Z(s)`.

## References

* [Stacks Project, Tag 0FA9](https://stacks.math.columbia.edu/tag/0FA9)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Tag 0AYP](https://stacks.math.columbia.edu/tag/0AYP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Chow

/-! ### Closed subschemes determined by their factorizations -/

/-- **Two ideal sheaves through which the same morphisms factor are equal.** -/
theorem idealSheafData_eq_of_forall_le_ker_iff {Y : Scheme.{u}} {I J : Y.IdealSheafData}
    (h : ∀ {T : Scheme.{u}} (g : T ⟶ Y), I ≤ g.ker ↔ J ≤ g.ker) : I = J := by
  refine le_antisymm ?_ ?_
  · simpa only [Scheme.IdealSheafData.ker_subschemeι] using
      (h J.subschemeι).mpr (by rw [Scheme.IdealSheafData.ker_subschemeι])
  · simpa only [Scheme.IdealSheafData.ker_subschemeι] using
      (h I.subschemeι).mp (by rw [Scheme.IdealSheafData.ker_subschemeι])

/-- A morphism factors through a closed immersion exactly when the kernel of the closed immersion
is below its kernel. -/
theorem ker_le_ker_iff_exists_comp_eq {Y Z T : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (g : T ⟶ Y) : i.ker ≤ g.ker ↔ ∃ h : T ⟶ Z, h ≫ i = g := by
  refine ⟨fun hle => ⟨IsClosedImmersion.lift i g hle, IsClosedImmersion.lift_fac i g hle⟩, ?_⟩
  rintro ⟨h, rfl⟩
  exact Scheme.Hom.le_ker_comp h i

/-- A morphism factors through the inverse image of a closed subscheme exactly when its composite
does through the closed subscheme. -/
theorem comap_le_ker_iff {X Y T : Scheme.{u}} (I : X.IdealSheafData) (π : Y ⟶ X) (g : T ⟶ Y) :
    I.comap π ≤ g.ker ↔ I ≤ (g ≫ π).ker := by
  rw [← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_ker]

/-! ### The tautological sequence and the hyperplane -/

variable {X : Scheme.{u}} (E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **The tautological sequence** `0 ⟶ ℰ' ⟶ π^*ℰ ⟶ 𝒪_P(1) ⟶ 0` of the projective bundle, its
first term the kernel `ℰ'` of the tautological quotient. -/
@[sga "5 VII 9.1", sga "6 VI 1.9" "partial"]
abbrev bundleTautologicalSequence : ShortComplex (bundle E).Modules :=
  ShortComplex.mk (kernel.ι (bundleTautological E)) (bundleTautological E) (kernel.condition _)

/-- The tautological sequence is short exact. -/
theorem shortExact_bundleTautologicalSequence : (bundleTautologicalSequence E).ShortExact :=
  have := epi_bundleTautological E
  { exact := ShortComplex.exact_kernel (bundleTautological E) }

/-- The tautological sequence stays short exact after every pullback, its quotient being
invertible. -/
theorem shortExact_pullback_bundleTautological {T : Scheme.{u}} (g : T ⟶ bundle E) :
    ((bundleTautologicalSequence E).map (Scheme.Modules.pullback g)).ShortExact :=
  Stacks.ProjectiveBundleSplitting.shortExact_map_pullback_of_epi_isInvertible g _
    (epi_bundleTautological E) (isInvertible_bundleTwist E)

/-- After every pullback the inclusion `ℰ' ⟶ π^*ℰ` is injective on global sections. -/
theorem injective_pullback_kernel_ι {T : Scheme.{u}} (g : T ⟶ bundle E) :
    Function.Injective (Scheme.Modules.Hom.app
      ((Scheme.Modules.pullback g).map ((bundleTautologicalSequence E).f)) ⊤) :=
  SheafOfModules.injective_of_mono_sections _ (shortExact_pullback_bundleTautological E g).mono_f
    (op ⊤)

/-- After two successive pullbacks the inclusion `ℰ' ⟶ π^*ℰ` is still injective on global
sections. -/
theorem injective_pullback_pullback_kernel_ι {T Y : Scheme.{u}} (h : T ⟶ Y) (i : Y ⟶ bundle E) :
    Function.Injective (Scheme.Modules.Hom.app ((Scheme.Modules.pullback h).map
      ((Scheme.Modules.pullback i).map ((bundleTautologicalSequence E).f))) ⊤) := by
  intro a b hab
  have hnat := (Scheme.Modules.pullbackComp h i).hom.naturality ((bundleTautologicalSequence E).f)
  have e1 := congrArg (fun ψ => Scheme.Modules.Hom.app ψ ⊤ a) hnat
  have e2 := congrArg (fun ψ => Scheme.Modules.Hom.app ψ ⊤ b) hnat
  simp only [Functor.comp_map, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at e1 e2
  have h3 : Scheme.Modules.Hom.app ((Scheme.Modules.pullback (h ≫ i)).map
      ((bundleTautologicalSequence E).f)) ⊤
        (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp h i).hom.app _) ⊤ a) =
      Scheme.Modules.Hom.app ((Scheme.Modules.pullback (h ≫ i)).map
      ((bundleTautologicalSequence E).f)) ⊤
        (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp h i).hom.app _) ⊤ b) := by
    rw [← e1, ← e2, hab]
  exact pullbackGlobalSections_injective_pullbackComp h i _ (injective_pullback_kernel_ι E _ h3)

/-- **The hyperplane `Z(t) ⊆ P`** cut out by the image `t` of `π^*s` in `𝒪_P(1)`. -/
abbrev bundleHyperplane (s : Γ(E, ⊤)) : (bundle E).IdealSheafData :=
  RegularSectionSequence.zeroScheme (bundle E) (bundleTwist E) (bundleHyperplaneSection E s)

/-- The section `ι^*π^*s` of the restriction of `π^*ℰ` to the hyperplane. -/
abbrev bundleHyperplaneRestriction (s : Γ(E, ⊤)) :
    Γ((Scheme.Modules.pullback (bundleHyperplane E s).subschemeι).obj
      ((Scheme.Modules.pullback (bundleProj E)).obj E), ⊤) :=
  pullbackGlobalSections (bundleHyperplane E s).subschemeι _
    (pullbackGlobalSections (bundleProj E) E s)

/-- `𝒪_P(1)` has rank one. -/
theorem isFiniteLocallyFreeOfRank_bundleTwist :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (bundleTwist E) 1 :=
  GenuineChern.isFiniteLocallyFreeOfRank_one_of_isInvertible _

/-- On the hyperplane, `ι^*π^*s` comes from the tautological subbundle. -/
theorem exists_bundleRestrictedSection (s : Γ(E, ⊤)) :
    ∃ s' : Γ((Scheme.Modules.pullback (bundleHyperplane E s).subschemeι).obj
        ((bundleTautologicalSequence E).X₁), ⊤),
      Scheme.Modules.Hom.app ((Scheme.Modules.pullback (bundleHyperplane E s).subschemeι).map
        ((bundleTautologicalSequence E).f)) ⊤ s' = bundleHyperplaneRestriction E s := by
  have := isFiniteLocallyFreeOfRank_bundleTwist E
  refine SheafOfModules.exists_of_shortExact_sections
    (shortExact_pullback_bundleTautological E (bundleHyperplane E s).subschemeι) (op ⊤) _ ?_
  show Scheme.Modules.Hom.app ((Scheme.Modules.pullback (bundleHyperplane E s).subschemeι).map
    (bundleTautological E)) ⊤ (bundleHyperplaneRestriction E s) = 0
  rw [bundleHyperplaneRestriction, ← AlgebraicGeometry.pullbackGlobalSections_natural]
  exact Stacks.RegularSectionSequence.pullbackGlobalSections_subschemeι_eq_zero
    (bundleTwist E) 1 (bundleHyperplaneSection E s)

/-- **The section `s'` of `ι^*ℰ'`** on the hyperplane whose image in `ι^*π^*ℰ` is `ι^*π^*s`. -/
def bundleRestrictedSection (s : Γ(E, ⊤)) :
    Γ((Scheme.Modules.pullback (bundleHyperplane E s).subschemeι).obj
      ((bundleTautologicalSequence E).X₁), ⊤) :=
  (exists_bundleRestrictedSection E s).choose

/-- The image of `s'` under `ι^*ℰ' → ι^*π^*ℰ` is `ι^*π^*s`. -/
theorem app_bundleRestrictedSection (s : Γ(E, ⊤)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullback (bundleHyperplane E s).subschemeι).map
      ((bundleTautologicalSequence E).f)) ⊤ (bundleRestrictedSection E s) =
        bundleHyperplaneRestriction E s :=
  (exists_bundleRestrictedSection E s).choose_spec

/-- **The zero scheme of `s'` is `π⁻¹ Z(s)`.** The zero scheme of the section `s'` of the
restriction of the tautological subbundle to the hyperplane `Z(t)`, viewed as a closed subscheme
of `P`, is the inverse image of the zero scheme of `s`. -/
theorem ker_zeroScheme_bundleRestrictedSection (m : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 1 + 1)]
    (s : Γ(E, ⊤)) :
    ((RegularSectionSequence.zeroScheme (bundleHyperplane E s).subscheme _
        (bundleRestrictedSection E s)).subschemeι ≫ (bundleHyperplane E s).subschemeι).ker =
      (RegularSectionSequence.zeroScheme X E s).comap (bundleProj E) := by
  have hK : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((bundleTautologicalSequence E).X₁) (m + 1) :=
    isFiniteLocallyFreeOfRank_kernel_bundleTautological E (m + 1) inferInstance
  have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback
    (bundleHyperplane E s).subschemeι ((bundleTautologicalSequence E).X₁) (m + 1)
  have := isFiniteLocallyFreeOfRank_bundleTwist E
  have key : ∀ {T : Scheme.{u}} (k : T ⟶ (bundleHyperplane E s).subscheme),
      pullbackGlobalSections k _ (bundleRestrictedSection E s) = 0 ↔
        pullbackGlobalSections (k ≫ (bundleHyperplane E s).subschemeι ≫ bundleProj E) E s = 0 :=
    fun {T} k => by
    rw [← Category.assoc, Stacks.Divisors.pullbackGlobalSections_comp_eq_zero_iff,
      Stacks.Divisors.pullbackGlobalSections_comp_eq_zero_iff]
    change _ ↔ pullbackGlobalSections k _ (bundleHyperplaneRestriction E s) = 0
    rw [← app_bundleRestrictedSection E s, AlgebraicGeometry.pullbackGlobalSections_natural]
    exact ⟨fun h => by rw [h, map_zero], fun h =>
      injective_pullback_pullback_kernel_ι E k (bundleHyperplane E s).subschemeι
        (h.trans (map_zero _).symm)⟩
  refine idealSheafData_eq_of_forall_le_ker_iff fun {T} g => ?_
  rw [ker_le_ker_iff_exists_comp_eq, comap_le_ker_iff,
    ← factorsThrough_ideal_iff_ideal_le_ker,
    ← Stacks.RegularSectionSequence.pullbackGlobalSections_eq_zero_iff_factorsThrough_zeroScheme
      E (m + 1 + 1) s]
  constructor
  · rintro ⟨h, rfl⟩
    rw [Category.assoc, Category.assoc, ← Category.assoc h, ← key,
      Stacks.Divisors.pullbackGlobalSections_comp_eq_zero_iff,
      Stacks.RegularSectionSequence.pullbackGlobalSections_subschemeι_eq_zero _ (m + 1), map_zero]
  · intro H0
    have Ht : pullbackGlobalSections g (bundleTwist E) (bundleHyperplaneSection E s) = 0 := by
      rw [bundleHyperplaneSection, AlgebraicGeometry.pullbackGlobalSections_natural,
        (Stacks.Divisors.pullbackGlobalSections_comp_eq_zero_iff _ _ _ _).mp H0, map_zero]
    obtain ⟨k, rfl⟩ :=
      (Stacks.RegularSectionSequence.pullbackGlobalSections_eq_zero_iff_factorsThrough_zeroScheme
        (bundleTwist E) 1 _ g).mp Ht
    rw [Category.assoc, ← key k] at H0
    exact
      ((Stacks.RegularSectionSequence.pullbackGlobalSections_eq_zero_iff_factorsThrough_zeroScheme
        _ (m + 1) _ k).mp H0).imp fun h hh => by rw [← Category.assoc, hh]

end Stacks.Chow

end
