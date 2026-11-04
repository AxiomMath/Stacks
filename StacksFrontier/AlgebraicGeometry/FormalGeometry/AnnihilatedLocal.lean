module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AnnihilatedAffineCriterion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Kernel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.RestrictOpen
public import StacksCore.Tactic.StacksAttribute

/-!
# Annihilation of the kernel and the cokernel is affine-local

Let `X` be a Noetherian scheme, let `𝓘, 𝓚 ⊆ 𝒪_X` be quasi-coherent sheaves of ideals and let
`α : (F_n) ⟶ (G_n)` be a morphism of `Coh(X, 𝓘)`. This file proves the equivalence of the three
conditions of Tag 0888:

1. there is an integer `t ≥ 1` such that `𝓚 ^ t` annihilates `Ker(α_n)` and `Coker(α_n)` for every
   `n`;
2. for every affine open `U ⊆ X` the modules `Ker(α_U)` and `Coker(α_U)` are annihilated by
   `K ^ t` for some `t ≥ 1`, where `α_U` is the map of finite modules over the completion which
   Tag 087W attaches to `α|_U` and `K = 𝓚(U)`;
3. the conclusion of (2) holds for the members of some finite affine open covering of `X`.

The equivalence of (1) and (2) over an affine scheme is
`Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_iff_affine`, which carries the
commutative-algebra content of the source. What is added here is that condition (1) is local: it
restricts along an open immersion because restriction is exact and preserves annihilation by a
power of the ideal sheaf, and it may be checked on a finite open covering because annihilation by
a *fixed* power of the ideal sheaf may be, the finiteness of the covering being what makes the
exponent uniform. Those two facts turn the affine equivalence into the equivalence of the three
conditions, (2) implying (3) because a Noetherian scheme is quasi-compact and its affine opens
form a basis.

## Main definitions

* `Stacks.Algebraization.IsAffineLocalKernelCokernelAnnihilated` — condition (2) of Tag 0888 at
  one affine open: the module condition for the system restricted to that open.

## Main results

* `Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_restrictFunctor_map` — condition (1)
  restricts along an open immersion.
* `Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_of_restrict` — condition (1) may be
  checked on a finite open covering.
* `Stacks.Algebraization.isAffineLocal_of_isKernelCokernelAnnihilatedByPower` and
  `Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_of_affineLocal_cover` — the two
  directions through the affine equivalence.
* `Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_tfae` — **Stacks Project, Tag 0888**:
  the three conditions are equivalent.

## Implementation notes

The affine open `U` is used through the open subscheme `U.toScheme`, whose affineness is the
property `U.2` rather than an instance; the statement of condition (2) therefore passes it
explicitly to `AlgebraicGeometry.isAffineOpen_top`. The ring `Γ(U.toScheme, ⊤)` is Noetherian
because `X` is locally Noetherian, through the isomorphism with `Γ(X, U)`.

Condition (3) quantifies over a finite index type together with a family of affine opens covering
`X`, rather than over a finite set of affine opens; this is the form in which
`TopologicalSpace.Opens.IsBasis.exists_iSup_eq_of_isCompact` produces a covering, and the form
`Stacks.Algebraization.idealPowerMultiple_eq_bot_of_restrict` consumes one.

## References

* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

/-! ### Condition (1) is local -/

/-- Restriction along an open immersion carries the kernel and cokernel of `f` to those of the
restricted morphism, so annihilation by a power of the ideal sheaf transfers between them. -/
private theorem idealPowerMultiple_restrict_kernel_cokernel_iff {X Y : Scheme.{u}}
    (g : Y ⟶ X) [IsOpenImmersion g] (𝒦 : X.IdealSheafData) (t : ℕ) {M N : X.Modules}
    (f : M ⟶ N) :
    (idealPowerMultiple (𝒦.comap g) t ((Scheme.Modules.restrictFunctor g).obj (kernel f)) = ⊥ ∧
      idealPowerMultiple (𝒦.comap g) t ((Scheme.Modules.restrictFunctor g).obj (cokernel f)) =
        ⊥) ↔
    (idealPowerMultiple (𝒦.comap g) t (kernel ((Scheme.Modules.restrictFunctor g).map f)) = ⊥ ∧
      idealPowerMultiple (𝒦.comap g) t (cokernel ((Scheme.Modules.restrictFunctor g).map f)) =
        ⊥) := by
  have hfl : PreservesFiniteLimits (Scheme.Modules.restrictFunctor g) :=
    AlgebraicGeometry.Modules.preservesFiniteLimits_restrictFunctor g
  have hpl : PreservesLimitsOfShape WalkingParallelPair (Scheme.Modules.restrictFunctor g) :=
    hfl.preservesFiniteLimits _
  have hpc : PreservesColimitsOfShape WalkingParallelPair
      (Scheme.Modules.restrictFunctor g) := inferInstance
  have hk := PreservesKernel.iso (Scheme.Modules.restrictFunctor g) f
  have hc := PreservesCokernel.iso (Scheme.Modules.restrictFunctor g) f
  exact ⟨fun h => ⟨idealPowerMultiple_eq_bot_of_iso _ hk.symm t h.1,
      idealPowerMultiple_eq_bot_of_iso _ hc.symm t h.2⟩,
    fun h => ⟨idealPowerMultiple_eq_bot_of_iso _ hk t h.1,
      idealPowerMultiple_eq_bot_of_iso _ hc t h.2⟩⟩

/-- **Condition (1) of Tag 0888 restricts along an open immersion.** Restriction is exact, so it
carries the levelwise kernels and cokernels of `α` to those of the restricted morphism, and it
preserves annihilation by a power of the ideal sheaf. -/
public theorem isKernelCokernelAnnihilatedByPower_restrictFunctor_map {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] (g : Y ⟶ X) [IsOpenImmersion g] (ℐ 𝒦 : X.IdealSheafData)
    {F G : Stacks.Coherent.CoherentAdicSystems ℐ} (α : F ⟶ G)
    (h : IsKernelCokernelAnnihilatedByPower 𝒦 α.hom) :
    IsKernelCokernelAnnihilatedByPower (𝒦.comap g)
      ((Stacks.Coherent.restrictFunctor ℐ g).map α).hom := by
  obtain ⟨t, ht, hkc⟩ := h
  exact ⟨t, ht, fun k => (idealPowerMultiple_restrict_kernel_cokernel_iff g 𝒦 t _).1
    ⟨idealPowerMultiple_restrict_eq_bot g 𝒦 t _ (hkc k).1,
      idealPowerMultiple_restrict_eq_bot g 𝒦 t _ (hkc k).2⟩⟩

/-- **Condition (1) of Tag 0888 may be checked on a finite open covering.** Annihilation by a
fixed power of the ideal sheaf is local on the base, and the covering being finite lets the
finitely many exponents be replaced by their maximum. -/
public theorem isKernelCokernelAnnihilatedByPower_of_restrict {X : Scheme.{u}}
    [IsLocallyNoetherian X] (ℐ 𝒦 : X.IdealSheafData)
    {F G : Stacks.Coherent.CoherentAdicSystems ℐ} (α : F ⟶ G)
    {J : Type u} [Finite J] (U : J → X.Opens) (hU : iSup U = ⊤)
    (h : ∀ j, IsKernelCokernelAnnihilatedByPower (𝒦.comap (U j).ι)
      ((Stacks.Coherent.restrictFunctor ℐ (U j).ι).map α).hom) :
    IsKernelCokernelAnnihilatedByPower 𝒦 α.hom := by
  obtain ⟨N, hN⟩ := Finite.exists_le fun j => (h j).choose
  have key := fun j k => (idealPowerMultiple_restrict_kernel_cokernel_iff (U j).ι 𝒦 (N + 1)
    (α.hom.app (op k))).2
    ⟨idealPowerMultiple_eq_bot_of_le ((h j).choose_spec.2 k).1 ((hN j).trans (Nat.le_succ N)),
      idealPowerMultiple_eq_bot_of_le ((h j).choose_spec.2 k).2 ((hN j).trans (Nat.le_succ N))⟩
  exact ⟨N + 1, Nat.succ_pos _, fun k =>
    ⟨idealPowerMultiple_eq_bot_of_restrict 𝒦 (N + 1) _ U hU fun j => (key j k).1,
      idealPowerMultiple_eq_bot_of_restrict 𝒦 (N + 1) _ U hU fun j => (key j k).2⟩⟩

/-! ### Condition (2) at one affine open -/

/-- **Tag 0888 (2), at one affine open.** The modules `Ker(α_U)` and `Coker(α_U)` attached by Tag
087W to the restriction of `α` to the affine open `U` are annihilated by a positive power of
`𝓚(U)`. -/
public def IsAffineLocalKernelCokernelAnnihilated {X : Scheme.{u}} [IsLocallyNoetherian X]
    (𝒦 : X.IdealSheafData) {ℐ : X.IdealSheafData}
    {F G : Stacks.Coherent.CoherentAdicSystems ℐ} (α : F ⟶ G) (U : X.affineOpens) : Prop :=
  IsAffineKernelCokernelAnnihilated
    ((𝒦.comap U.1.ι).ideal ⟨⊤, @isAffineOpen_top U.1.toScheme U.2⟩)
    ((Stacks.Coherent.restrictFunctor ℐ U.1.ι).map α)

/-- The ring of global sections of an affine open of a locally Noetherian scheme, read on the
open subscheme, is Noetherian. -/
public theorem isNoetherianRing_affineOpen_toScheme {X : Scheme.{u}} [IsLocallyNoetherian X]
    (U : X.affineOpens) : IsNoetherianRing Γ(U.1.toScheme, ⊤) := by
  have hNRX : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  exact isNoetherianRing_of_ringEquiv _
    (Scheme.restrictFunctorΓ.app (op U.1)).symm.commRingCatIsoToRingEquiv

/-- Over an affine open, condition (1) for the restricted morphism is condition (2). -/
private theorem isKernelCokernelAnnihilatedByPower_restrict_iff {X : Scheme.{u}}
    [IsLocallyNoetherian X] (ℐ 𝒦 : X.IdealSheafData)
    {F G : Stacks.Coherent.CoherentAdicSystems ℐ} (α : F ⟶ G) (U : X.affineOpens) :
    IsKernelCokernelAnnihilatedByPower (𝒦.comap U.1.ι)
      ((Stacks.Coherent.restrictFunctor ℐ U.1.ι).map α).hom ↔
    IsAffineLocalKernelCokernelAnnihilated 𝒦 α U := by
  have hAff : IsAffine U.1.toScheme := U.2
  have hNR : IsNoetherianRing Γ(U.1.toScheme, ⊤) := isNoetherianRing_affineOpen_toScheme U
  exact isKernelCokernelAnnihilatedByPower_iff_affine (ℐ.comap U.1.ι) (𝒦.comap U.1.ι)
    ((Stacks.Coherent.restrictFunctor ℐ U.1.ι).map α)

/-- **Tag 0888, (1) ⟹ (2).** -/
public theorem isAffineLocal_of_isKernelCokernelAnnihilatedByPower {X : Scheme.{u}}
    [IsLocallyNoetherian X] (ℐ 𝒦 : X.IdealSheafData)
    {F G : Stacks.Coherent.CoherentAdicSystems ℐ} (α : F ⟶ G)
    (h : IsKernelCokernelAnnihilatedByPower 𝒦 α.hom) (U : X.affineOpens) :
    IsAffineLocalKernelCokernelAnnihilated 𝒦 α U :=
  (isKernelCokernelAnnihilatedByPower_restrict_iff ℐ 𝒦 α U).1
    (isKernelCokernelAnnihilatedByPower_restrictFunctor_map U.1.ι ℐ 𝒦 α h)

/-- **Tag 0888, (3) ⟹ (1).** -/
public theorem isKernelCokernelAnnihilatedByPower_of_affineLocal_cover {X : Scheme.{u}}
    [IsLocallyNoetherian X] (ℐ 𝒦 : X.IdealSheafData)
    {F G : Stacks.Coherent.CoherentAdicSystems ℐ} (α : F ⟶ G)
    {J : Type u} [Finite J] (U : J → X.affineOpens) (hU : iSup (fun j => (U j).1) = ⊤)
    (h : ∀ j, IsAffineLocalKernelCokernelAnnihilated 𝒦 α (U j)) :
    IsKernelCokernelAnnihilatedByPower 𝒦 α.hom :=
  isKernelCokernelAnnihilatedByPower_of_restrict ℐ 𝒦 α (fun j => (U j).1) hU fun j =>
    (isKernelCokernelAnnihilatedByPower_restrict_iff ℐ 𝒦 α (U j)).2 (h j)

/-! ### The three conditions -/

/-- **Stacks Project, Tag 0888.** For a morphism `α` of `Coh(X, 𝓘)` on a Noetherian scheme `X` and
a quasi-coherent sheaf of ideals `𝓚`, the following are equivalent:

1. one positive power of `𝓚` annihilates every levelwise kernel `Ker(α_n)` and every levelwise
   cokernel `Coker(α_n)`;
2. for every affine open `U ⊆ X` one positive power of `𝓚(U)` annihilates `Ker(α_U)` and
   `Coker(α_U)`, where `α_U` is the map of finite modules over the completion attached to `α|_U`
   by Tag 087W;
3. the conclusion of (2) holds for the members of some finite affine open covering of `X`.

A morphism satisfying these conditions is the source's *map whose kernel and cokernel are
annihilated by a power of `𝓚`*. -/
@[stacks 0888 "the equivalence of (1), (2) and (3)"]
public theorem isKernelCokernelAnnihilatedByPower_tfae {X : Scheme.{u}} [IsNoetherian X]
    (ℐ 𝒦 : X.IdealSheafData) {F G : Stacks.Coherent.CoherentAdicSystems ℐ} (α : F ⟶ G) :
    List.TFAE
      [IsKernelCokernelAnnihilatedByPower 𝒦 α.hom,
        ∀ U : X.affineOpens, IsAffineLocalKernelCokernelAnnihilated 𝒦 α U,
        ∃ (J : Type u) (_ : Finite J) (U : J → X.affineOpens),
          iSup (fun j => (U j).1) = ⊤ ∧
            ∀ j, IsAffineLocalKernelCokernelAnnihilated 𝒦 α (U j)] := by
  tfae_have 1 → 2 := fun h => isAffineLocal_of_isKernelCokernelAnnihilatedByPower ℐ 𝒦 α h
  tfae_have 2 → 3 := by
    intro h
    have hbasis : TopologicalSpace.Opens.IsBasis (Set.range fun A : X.affineOpens => A.1) := by
      have heq : Set.range (fun A : X.affineOpens => A.1) = X.affineOpens := by
        ext W
        exact ⟨fun ⟨A, hA⟩ => hA ▸ A.property, fun hW => ⟨⟨W, hW⟩, rfl⟩⟩
      rw [heq]
      exact X.isBasis_affineOpens
    obtain ⟨κ, hκ, a, heq⟩ := hbasis.exists_iSup_eq_of_isCompact (⊤ : X.Opens) isCompact_univ
    exact ⟨κ, hκ, a, heq.symm, fun j => h (a j)⟩
  tfae_have 3 → 1 := by
    rintro ⟨J, hJ, U, hU, h⟩
    exact isKernelCokernelAnnihilatedByPower_of_affineLocal_cover ℐ 𝒦 α U hU h
  tfae_finish

end Stacks.Algebraization

end
