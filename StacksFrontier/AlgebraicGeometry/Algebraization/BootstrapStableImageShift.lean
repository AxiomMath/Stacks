module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapIdealPowerSubmodule
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapUniformStableImage

/-!
# Rebasing the stable-image assertion of Tag 0EFX at the submodule `I^{m₀}M`

The stable-image assertion of [Stacks, Tag 0EFX] is based at an integer `m₀`: for `m ≥ m₀` the
image of `H^{s+1}_T(IᵏM) ⟶ H^{s+1}_T(IᵐM)` maps injectively into `H^{s+1}_T(I^{m₀}M)`. The engines
that derive parts (3) and (5) of [Stacks, Tag 0EFY] from it —
`Stacks.LocalCohomology.isMittagLefflerCategorical_localCohomologyAdicTower_of_stableImage` and
`Stacks.LocalCohomology.isIso_limitLift_localCohomologyAdicCone_of_stableImage` — need it based at
`0`, because their argument uses that the connecting map of `0 → I⁰M → M → M/I⁰M → 0` vanishes,
`M/I⁰M` being the zero module.

The two are the same statement read for different modules: based at `m₀` for `M`, the assertion is
based at `0` for the module `I^{m₀}M`, because `Iⁿ(I^{m₀}M) = I^{n+m₀}M` inside `M`
(`Stacks.Algebraization.map_subtype_pow_smul_top`). That identification of towers is what this
module supplies, and with it parts (3) and (5) hold at a general specialization-stable `T`, for
the tower of adic quotients of `I^{m₀}M` — which is the source's system `{I^{m₀}M/IⁿM}_{n ≥ m₀}`
along the cofinal shift `n ↦ n + m₀`, exactly as for the registrants at `T = {𝔪}`.

## Main definitions

* `Stacks.Algebraization.idealPowerShiftEquiv` — the isomorphism `Iⁿ(IʳM) ≅ I^{n+r}M`.

## Main results

* `Stacks.Algebraization.hasStableImageIdealPowerCohomology_idealPowerSubmodule` — the rebasing:
  the assertion based at `r` for `M` is the assertion based at `0` for `IʳM`.
* `Stacks.Algebraization.isMittagLefflerCategorical_localCohomologyAdicTower_idealPowerSubmodule`
  and `Stacks.Algebraization.isIso_limitLift_localCohomologyAdicCone_idealPowerSubmodule` — parts
  (3) and (5) of [Stacks, Tag 0EFY] at a general specialization-stable `T`, for every exponent
  past the base of the stable-image assertion.
* `Stacks.Algebraization.exists_forall_injective_and_isMittagLeffler_and_isIso_limitLift` —
  **parts (1), (3) and (5) of [Stacks, Tag 0EFY] at a general specialization-stable `T`, at one
  and the same `m₀`.**

## Implementation notes

The comparison carries a target index `p` together with a proof that `p = n + r`, rather than
being stated with the index `n + r` itself. The reason is `0 + r`: the shift of the base index of
the rebased assertion is `0 + r`, which is not the same term as `r`, and the tower is indexed by
terms. Carrying the index as a parameter lets the comparison be read at `r` directly.

## References

* [Stacks Project, Tag 0EFY](https://stacks.math.columbia.edu/tag/0EFY)
* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

variable {A : Type u} [CommRing A]

/-! ### The ideal-power tower of `IʳM` as the shifted tower of `M` -/

/-- **`Iⁿ(IʳM) ≅ I^{n+r}M`.** The inclusion `IʳM ⊆ M` restricts to an isomorphism of
`Iⁿ(IʳM)` onto its image, which is `I^{n+r}M` by
`Stacks.Algebraization.map_subtype_pow_smul_top`. The target index is carried as a parameter; see
the implementation notes. -/
def idealPowerShiftEquiv (I : Ideal A) (M : ModuleCat.{u} A) (r n p : ℕ) (hp : p = n + r) :
    ↥(I ^ n • (⊤ : Submodule A ↥(I ^ r • (⊤ : Submodule A M)))) ≃ₗ[A]
      ↥(I ^ p • (⊤ : Submodule A M)) :=
  (Submodule.equivMapOfInjective (I ^ r • (⊤ : Submodule A M)).subtype
      Subtype.val_injective (I ^ n • (⊤ : Submodule A ↥(I ^ r • (⊤ : Submodule A M))))).trans
    (LinearEquiv.ofEq _ _ (by rw [hp]; exact map_subtype_pow_smul_top I r n))

/-- The comparison `Iⁿ(IʳM) ≅ I^pM` commutes with the transition maps of the two towers: both
legs of the square send an element to the element of `M` it already was. -/
theorem idealPowerShiftEquiv_naturality (I : Ideal A) (M : ModuleCat.{u} A) (r : ℕ)
    {a b pa pb : ℕ} (hpa : pa = a + r) (hpb : pb = b + r) (hab : a ≤ b) (hab' : pa ≤ pb) :
    (idealPowerTower.{u, u} I (ModuleCat.of A ↥(I ^ r • (⊤ : Submodule A M)))).map
          (homOfLE hab).op ≫ (idealPowerShiftEquiv I M r a pa hpa).toModuleIso.hom =
      (idealPowerShiftEquiv I M r b pb hpb).toModuleIso.hom ≫
        (idealPowerTower.{u, u} I M).map (homOfLE hab').op := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- **The `a`-th term of the ideal-power tower of `IʳM` is the `p`-th term of the tower of `M`**,
for `p = a + r`. -/
def idealPowerTowerShiftIso (I : Ideal A) (M : ModuleCat.{u} A) (r a p : ℕ) (hp : p = a + r) :
    (idealPowerTower.{u, u} I (ModuleCat.of A ↥(I ^ r • (⊤ : Submodule A M)))).obj (op a) ≅
      (idealPowerTower.{u, u} I M).obj (op p) :=
  (idealPowerShiftEquiv I M r a p hp).toModuleIso

/-! ### Rebasing the stable-image assertion -/

/-- **The stable-image assertion based at `r` for `M` is the assertion based at `0` for `IʳM`.**
Both say that a class of `H^j_T(I^{k+r}M)` dying in `H^j_T(IʳM)` dies in `H^j_T(I^{m+r}M)` for
all large `k`; the first reads the tower of `M` from the index `r` on, the second reads the tower
of `IʳM` from `0` on, and `Iⁿ(IʳM) = I^{n+r}M` identifies them
(`Stacks.Algebraization.idealPowerTowerShiftIso`).

The engines that derive parts (3) and (5) of [Stacks, Tag 0EFY] need the base `0` form, which is
why the rebasing is needed and not only the `.mono` of
`Stacks.LocalCohomology.HasStableImageIdealPowerCohomology`, which raises the base. -/
theorem hasStableImageIdealPowerCohomology_idealPowerSubmodule
    (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : ModuleCat.{u} A) (j : ℤ) (r : ℕ)
    (h : HasStableImageIdealPowerCohomology.{u, u} T I M j r) :
    HasStableImageIdealPowerCohomology.{u, u} T I
      (ModuleCat.of A ↥(I ^ r • (⊤ : Submodule A M))) j 0 := by
  intro m _
  obtain ⟨c, hmc, hc⟩ := h (m + r) (Nat.le_add_left r m)
  have hmc' : m ≤ c := le_trans (Nat.le_add_right m r) hmc
  refine ⟨c, hmc', fun k hck x hx => ?_⟩
  have hmk : m ≤ k := hmc'.trans hck
  -- the comparison of the two towers, carried to local cohomology
  have hsq : ∀ {a b pa pb : ℕ} (hpa : pa = a + r) (hpb : pb = b + r) (hab : a ≤ b)
      (hab' : pa ≤ pb)
      (y : (localCohomologyWithSupportInModuleFunctor.{u, u} A T j).obj
        ((idealPowerTower.{u, u} I
          (ModuleCat.of A ↥(I ^ r • (⊤ : Submodule A M)))).obj (op b))),
      ((localCohomologyWithSupportInModuleFunctor.{u, u} A T j).map
          (idealPowerTowerShiftIso I M r a pa hpa).hom).hom
          (((localCohomologyWithSupportInModuleFunctor.{u, u} A T j).map
            ((idealPowerTower.{u, u} I (ModuleCat.of A
              ↥(I ^ r • (⊤ : Submodule A M)))).map (homOfLE hab).op)).hom y) =
        ((localCohomologyWithSupportInModuleFunctor.{u, u} A T j).map
            ((idealPowerTower.{u, u} I M).map (homOfLE hab').op)).hom
          (((localCohomologyWithSupportInModuleFunctor.{u, u} A T j).map
            (idealPowerTowerShiftIso I M r b pb hpb).hom).hom y) := by
    intro a b pa pb hpa hpb hab hab' y
    exact ConcreteCategory.congr_hom
      ((((localCohomologyWithSupportInModuleFunctor.{u, u} A T j).map_comp _ _).symm.trans
        (congrArg (localCohomologyWithSupportInModuleFunctor.{u, u} A T j).map
          (idealPowerShiftEquiv_naturality I M r hpa hpb hab hab'))).trans
        ((localCohomologyWithSupportInModuleFunctor.{u, u} A T j).map_comp _ _)) y
  have hinj : ∀ (a p : ℕ) (hp : p = a + r),
      Function.Injective ((localCohomologyWithSupportInModuleFunctor.{u, u} A T j).map
        (idealPowerTowerShiftIso I M r a p hp).hom).hom :=
    fun a p hp => (ModuleCat.mono_iff_injective _).1 inferInstance
  -- the hypothesis, transported: the class dies in `H^j_T(IʳM)`
  have hx' := (inverseSystem_transition_comp_apply.{u, u}
    (idealPowerTower.{u, u} I (ModuleCat.of A ↥(I ^ r • (⊤ : Submodule A M))) ⋙
      localCohomologyWithSupportInModuleFunctor.{u, u} A T j)
    (Nat.zero_le m) hmk x).symm.trans hx
  rw [Functor.comp_map] at hx'
  -- the conclusion, transported back
  refine hinj m (m + r) rfl ?_
  rw [map_zero]
  refine (hsq (rfl : m + r = m + r) (rfl : k + r = k + r) hmk (by omega) x).trans ?_
  refine hc (k + r) (by omega)
    (((localCohomologyWithSupportInModuleFunctor.{u, u} A T j).map
      (idealPowerTowerShiftIso I M r k (k + r) rfl).hom).hom x) ?_
  refine (inverseSystem_transition_comp_apply.{u, u}
    (idealPowerTower.{u, u} I M ⋙ localCohomologyWithSupportInModuleFunctor.{u, u} A T j)
    (Nat.le_add_left r m) (by omega) _).trans ?_
  rw [Functor.comp_map, ← hsq (show r = 0 + r by omega) (rfl : k + r = k + r) (Nat.zero_le k)
    (show r ≤ k + r by omega) x, hx', map_zero]

/-! ### Parts (3) and (5) of Tag 0EFY at a general specialization-stable locus -/

variable (S : BootstrapSituation.{u, u, u})

/-- **Stacks Project, Tag 0EFY, part (3)**, at a general specialization-stable `T`, for the
submodule `IʳM` with `r` past the base of the stable-image assertion. In Situation
[Stacks, Tag 0EFU] the inverse system `n ↦ H^i_T(IʳM/I^{n+r}M)` satisfies the Mittag-Leffler
condition for every `i ≤ s`.

The source indexes the system by `n ≥ r` and writes its terms `H^i_T(IʳM/IⁿM)`; the index here
runs over all of `ℕ`, which replaces `IⁿM` by `Iⁿ(IʳM) = I^{n+r}M`
(`Stacks.Algebraization.map_subtype_pow_smul_top`) and so gives the same family of modules and the
same transition maps along the cofinal shift `n ↦ n + r` — the same reading as the registrant at
`T = {𝔪}`,
`Stacks.LocalCohomology.isMittagLefflerCategorical_homologyAdicQuotientLocalCohomology_smul`.

In degrees `i < s` this is the pro-zero assertion of [Stacks, Tag 0EFX] in degree `i + 1` through
`Stacks.LocalCohomology.isMittagLefflerCategorical_localCohomologyAdicTower_of_proZero`; in degree
`i = s` it is the stable-image assertion through
`Stacks.LocalCohomology.isMittagLefflerCategorical_localCohomologyAdicTower_of_stableImage`,
rebased at `0` for the module `IʳM` by
`Stacks.Algebraization.hasStableImageIdealPowerCohomology_idealPowerSubmodule`. -/
theorem isMittagLefflerCategorical_localCohomologyAdicTower_idealPowerSubmodule (r : ℕ)
    (hstab : HasStableImageIdealPowerCohomology.{u, u} S.T S.I (ModuleCat.of S.A S.M)
      (S.s + 1) r)
    (i : ℤ) (hi : i ≤ S.s) :
    IsMittagLefflerCategorical (localCohomologyAdicTower.{u, u} S.A S.T S.I i
      (ModuleCat.of S.A ↥(S.I ^ r • (⊤ : Submodule S.A S.M)))) := by
  have hpro : ∀ a : ℤ, a ≤ S.s → IsProZeroIdealPowerCohomology.{u, u} S.T S.I
      (ModuleCat.of S.A ↥(S.I ^ r • (⊤ : Submodule S.A S.M))) a :=
    fun a ha => isProZeroIdealPowerCohomology (S.idealPowerSubmodule r) a ha
  rcases lt_or_eq_of_le hi with hlt | heq
  · exact isMittagLefflerCategorical_localCohomologyAdicTower_of_proZero.{u, u} S.T S.I
      (ModuleCat.of S.A ↥(S.I ^ r • (⊤ : Submodule S.A S.M))) i (hpro (i + 1) (by omega))
  · subst heq
    exact isMittagLefflerCategorical_localCohomologyAdicTower_of_stableImage.{u, u} S.T S.I
      (ModuleCat.of S.A ↥(S.I ^ r • (⊤ : Submodule S.A S.M))) S.s
      (hasStableImageIdealPowerCohomology_idealPowerSubmodule S.T S.I
        (ModuleCat.of S.A S.M) (S.s + 1) r hstab)

/-- **Stacks Project, Tag 0EFY, part (5)**, at a general specialization-stable `T`, for the
submodule `IʳM` with `r` past the base of the stable-image assertion. In Situation
[Stacks, Tag 0EFU] the comparison `H^s_T(IʳM) ⟶ lim_n H^s_T(IʳM/I^{n+r}M)` is an isomorphism.

As for part (3), the system is the source's `{IʳM/IⁿM}_{n ≥ r}` read along the cofinal shift
`n ↦ n + r`. The two inputs are the pro-zero assertion of [Stacks, Tag 0EFX] in degree `s` for the
module `IʳM`, the situation being stable under `M ↦ IᵏM`, and its stable-image assertion in degree
`s + 1` rebased at `0` for that module. -/
theorem isIso_limitLift_localCohomologyAdicCone_idealPowerSubmodule (r : ℕ)
    (hstab : HasStableImageIdealPowerCohomology.{u, u} S.T S.I (ModuleCat.of S.A S.M)
      (S.s + 1) r) :
    IsIso (limit.lift
      (localCohomologyAdicTower.{u, u} S.A S.T S.I S.s
        (ModuleCat.of S.A ↥(S.I ^ r • (⊤ : Submodule S.A S.M))))
      (localCohomologyAdicCone.{u, u} S.A S.T S.I S.s
        (ModuleCat.of S.A ↥(S.I ^ r • (⊤ : Submodule S.A S.M))))) :=
  isIso_limitLift_localCohomologyAdicCone_of_stableImage.{u, u} S.T S.I
    (ModuleCat.of S.A ↥(S.I ^ r • (⊤ : Submodule S.A S.M))) S.s
    (show IsProZeroIdealPowerCohomology.{u, u} S.T S.I
      (ModuleCat.of S.A ↥(S.I ^ r • (⊤ : Submodule S.A S.M))) S.s from
      isProZeroIdealPowerCohomology (S.idealPowerSubmodule r) S.s le_rfl)
    (hasStableImageIdealPowerCohomology_idealPowerSubmodule S.T S.I
      (ModuleCat.of S.A S.M) (S.s + 1) r hstab)

/-- **Stacks Project, Tag 0EFY, parts (1), (3) and (5)**, at a general specialization-stable `T`,
at one and the same `m₀`. In Situation [Stacks, Tag 0EFU] there is an integer `m₀` such that

* `H^i_T(M) ⟶ H^i_T(M/IⁿM)` is injective for every `i ≤ s` and every `n ≥ m₀` — part (1);
* `{H^i_T(I^{m₀}M/I^{n+m₀}M)}` satisfies the Mittag-Leffler condition for every `i ≤ s` — part
  (3), **at that `m₀`**; and
* `H^s_T(I^{m₀}M) ⟶ lim_n H^s_T(I^{m₀}M/I^{n+m₀}M)` is an isomorphism — part (5), **at that
  `m₀`**.

The last two items are the source's statements for the module `I^{m₀}M`: the `n`-th term of its
tower of adic quotients is `I^{m₀}M/I^{n+m₀}M`
(`Stacks.Algebraization.map_subtype_pow_smul_top`), so the tower is the source's system
`{I^{m₀}M/IⁿM}_{n ≥ m₀}` along the cofinal shift `n ↦ n + m₀` and the limits agree — the reading
the registrants at `T = {𝔪}` use as well.

Stating the three at a common `m₀` matters: `∃ m₀, part (5) at m₀` alone is satisfiable at
`m₀ = 0`, where part (5) degenerates into part (4) read in degree `s`. The `m₀` exhibited here is
a bound for part (1) and for the base of the stable-image assertion of [Stacks, Tag 0EFX]
simultaneously. Nothing beyond the data of Situation [Stacks, Tag 0EFU] is assumed. -/
@[stacks 0EFY "parts (1), (3) and (5) at a general specialization-stable T in Situation 0EFU, at \
one and the same m₀: the projections are injective from m₀ on, {Hⁱ_T(I^{m₀}M/IⁿM)} is \
Mittag-Leffler for i ≤ s, and Hˢ_T(I^{m₀}M) ⟶ lim Hˢ_T(I^{m₀}M/IⁿM) is an isomorphism"]
theorem exists_forall_injective_and_isMittagLeffler_and_isIso_limitLift :
    ∃ m₀ : ℕ,
      (∀ i ≤ S.s, ∀ n : ℕ, m₀ ≤ n →
        Function.Injective ((localCohomologyAdicCone.{u, u} S.A S.T S.I i
          (ModuleCat.of S.A S.M)).π.app (op n)).hom) ∧
      (∀ i ≤ S.s, IsMittagLefflerCategorical (localCohomologyAdicTower.{u, u} S.A S.T S.I i
        (ModuleCat.of S.A ↥(S.I ^ m₀ • (⊤ : Submodule S.A S.M))))) ∧
      IsIso (limit.lift
        (localCohomologyAdicTower.{u, u} S.A S.T S.I S.s
          (ModuleCat.of S.A ↥(S.I ^ m₀ • (⊤ : Submodule S.A S.M))))
        (localCohomologyAdicCone.{u, u} S.A S.T S.I S.s
          (ModuleCat.of S.A ↥(S.I ^ m₀ • (⊤ : Submodule S.A S.M))))) := by
  obtain ⟨m₁, hm₁⟩ := exists_forall_injective_localCohomologyAdicProjection S
  obtain ⟨m₂, hm₂⟩ := exists_hasStableImageIdealPowerCohomology S
  refine ⟨max m₁ m₂, fun i hi n hn => hm₁ i hi n ((le_max_left m₁ m₂).trans hn), ?_, ?_⟩
  · exact fun i hi => isMittagLefflerCategorical_localCohomologyAdicTower_idealPowerSubmodule S
      (max m₁ m₂) (hm₂.mono.{u, u} (le_max_right m₁ m₂)) i hi
  · exact isIso_limitLift_localCohomologyAdicCone_idealPowerSubmodule S (max m₁ m₂)
      (hm₂.mono.{u, u} (le_max_right m₁ m₂))

end Stacks.Algebraization

end
