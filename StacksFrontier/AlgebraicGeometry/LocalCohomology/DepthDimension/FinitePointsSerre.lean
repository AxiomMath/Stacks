module

public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.Depth
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineLocalization
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexScheme
public import StacksFrontier.AlgebraicGeometry.Reflexive.ExtensionChain.Depth
public import StacksFrontier.RingTheory.Serre.FinitePointsDepthDimension
public import StacksCore.Tactic.StacksAttribute

/-!
# Finitely many points where the depth equals `k` and the support is bigger

Let `X` be a Noetherian scheme with a dualizing complex and let `F` be a coherent
`𝒪_X`-module satisfying Serre's condition `(Sₖ)`.  Then there are only finitely many points
`x ∈ X` with

`depth(F_x) = k` and `dim Supp(F_x) > k`.

This is [Stacks, Tag 0ECN].  The whole content is affine: a Noetherian scheme is covered by
finitely many affine opens, over an affine open `U` the stalk `F_x` is the localization of
`Γ(F, U)` at the prime of `x`, and a dualizing complex on `X` restricts on `U` to the associated
sheaf of a dualizing complex over `Γ(X, U)` (this is how `Stacks.Duality.IsDualizingComplex` is
defined, following [Stacks, Tag 0A87]).  So
`Module.finite_setOf_depth_eq_and_lt_supportDim_localization` applies to the `Γ(X, U)`-module
`Γ(F, U)` and gives finiteness inside `U`.

## Main results

* `AlgebraicGeometry.finite_setOf_depth_eq_and_lt_supportDim` — **[Stacks, Tag 0ECN]**.

## Implementation notes

The depth of a stalk is `Module.depth` along the maximal ideal of the local ring, and the
dimension of the support of a stalk is `Module.supportDim`, so the two conditions are read in
`ℕ∞` and in `WithBot ℕ∞` respectively.  The stalk module structure used is the one instance
search finds for a `Scheme.Modules`, which is the spelling of
`Stacks.AlgebraicGeometry.ReflexiveModules.min_supportDim_le_depth_of_sheafHasPropertySk`; it
equals the one `AlgebraicGeometry.SheafHasPropertySk` is stated with, though not definitionally,
and that lemma is the transport.

Serre's condition is `AlgebraicGeometry.SheafHasPropertySk`, the sheaf-level `(Sₖ)` of
[Stacks, Tag 0341]; the source's `k ≥ 0` is expressed by `k : ℕ`.

The derived category of `𝒪_X`-modules is an instance argument, as in
`Stacks.Duality.IsDualizingComplex`; only the existence of a dualizing complex over `Γ(X, U)`
for each affine open `U` is used, so the comparison isomorphism in the definition of
`Stacks.Duality.HasDualizingModelOn` is discarded.

## References

* [Stacks Project, Tag 0ECN](https://stacks.math.columbia.edu/tag/0ECN)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0341](https://stacks.math.columbia.edu/tag/0341)
* [Stacks Project, Tag 0EHS](https://stacks.math.columbia.edu/tag/0EHS)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u w

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Transport of depth and support dimension to an affine open -/

/-- **The depth and the support dimension of a stalk, read on an affine open.**  At a point `x`
of an affine open `U`, the germ map identifies the stalk `F_x` with the localization of
`Γ(F, U)` at the prime of `x`, semilinearly over the canonical isomorphism of the two local
rings; so the depth and the dimension of the support of `F_x` are those of that localization. -/
private lemma depth_and_supportDim_stalk_eq_localization [IsLocallyNoetherian X] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] {U : X.Opens} (hU : IsAffineOpen U) {x : X}
    (hx : x ∈ U) :
    Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (F.presheaf.stalk x) =
        Module.depth (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
          (IsLocalRing.maximalIdeal
            (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal))
          (LocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl Γ(F, U)) ∧
      Module.supportDim (X.presheaf.stalk x) (F.presheaf.stalk x) =
        Module.supportDim (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
          (LocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl Γ(F, U)) := by
  set p := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  have hprime : p.IsPrime := (hU.primeIdealOf ⟨x, hx⟩).isPrime
  have hfinM : Module.Finite Γ(X, U) Γ(F, U) := moduleFinite_sections_on_affine F U hU
  let T := X.presheaf.stalk x
  let N := F.presheaf.stalk x
  let S := Localization.AtPrime p
  let : Module Γ(X, U) N := affineStalkModule F U x hx
  let : Algebra Γ(X, U) T := (X.presheaf.germ U x hx).hom.toAlgebra
  let : IsScalarTower Γ(X, U) T N := IsScalarTower.of_algebraMap_smul fun r z => by
    show (X.presheaf.germ U x hx).hom r • z = r • z
    rfl
  let : IsLocalization.AtPrime T p := hU.isLocalization_stalk ⟨x, hx⟩
  let : IsLocalRing T := IsLocalization.AtPrime.isLocalRing T p
  let e : S ≃ₐ[Γ(X, U)] T := IsLocalization.algEquiv p.primeCompl S T
  let : Algebra S T := e.toAlgHom.toAlgebra
  let : Module S N := Module.compHom N (algebraMap S T)
  let : IsScalarTower S T N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hcomp (r : Γ(X, U)) : algebraMap S T (algebraMap Γ(X, U) S r) = algebraMap Γ(X, U) T r :=
    e.commutes r
  let : IsScalarTower Γ(X, U) S T := IsScalarTower.of_algebraMap_eq fun r => (hcomp r).symm
  let : IsScalarTower Γ(X, U) S N := IsScalarTower.of_algebraMap_smul fun r n => by
    rw [← algebraMap_smul T r n, ← hcomp]
    rfl
  have hlocM : IsLocalizedModule p.primeCompl (affineGerm F U x hx) :=
    affineGerm_isLocalized F U hU x hx
  let eM' : LocalizedModule p.primeCompl Γ(F, U) ≃ₗ[S] N :=
    (IsLocalizedModule.linearEquiv p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl Γ(F, U))
      (affineGerm F U x hx)).extendScalarsOfIsLocalization p.primeCompl S
  have hdepthM : Module.depth S (IsLocalRing.maximalIdeal S)
      (LocalizedModule p.primeCompl Γ(F, U)) = Module.depth S (IsLocalRing.maximalIdeal S) N :=
    Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal S) eM'
  have hdimM : Module.supportDim S (LocalizedModule p.primeCompl Γ(F, U)) =
      Module.supportDim S N := Module.supportDim_eq_of_equiv eM'
  have hmax : Ideal.map (algebraMap S T) (IsLocalRing.maximalIdeal S) =
      IsLocalRing.maximalIdeal T := by
    show Ideal.map e.toRingHom (IsLocalRing.maximalIdeal S) = IsLocalRing.maximalIdeal T
    exact IsLocalRing.map_ringEquiv_maximalIdeal e.toRingEquiv
  have hdepthST := Module.depth_eq_depth_map_algebraMap
    (A := S) (B := T) e.surjective (IsLocalRing.maximalIdeal S) N
  rw [hmax] at hdepthST
  have hfinS : Module.Finite S N := Module.Finite.of_surjective eM'.toLinearMap eM'.surjective
  have hfinT : Module.Finite T N := Module.Finite.of_surjective
    ({ toFun := id
       map_smul' := fun _ _ => rfl
       map_add' := fun _ _ => rfl } : N →ₛₗ[e.toRingHom] N) fun n => ⟨n, rfl⟩
  have hdimST : Module.supportDim S N = Module.supportDim T N :=
    Module.supportDim_eq_of_ringEquiv e.toRingEquiv N rfl
  refine ⟨?_, ?_⟩
  · show Module.depth T (IsLocalRing.maximalIdeal T) N =
      Module.depth S (IsLocalRing.maximalIdeal S) (LocalizedModule p.primeCompl Γ(F, U))
    rw [← hdepthST, ← hdepthM]
  · show Module.supportDim T N =
      Module.supportDim S (LocalizedModule p.primeCompl Γ(F, U))
    rw [← hdimST, ← hdimM]

/-! ### Finiteness on an affine open, and globally -/

/-- The exceptional set of [Stacks, Tag 0ECN] inside an affine open is finite: the dualizing
complex on `X` provides a dualizing complex over `Γ(X, U)`, Serre's condition for `F` gives
Serre's condition for `Γ(F, U)`, and the affine statement
`Module.finite_setOf_depth_eq_and_lt_supportDim_localization` applies. -/
private lemma finite_setOf_depth_eq_and_lt_supportDim_inter_affine [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} X.Modules] {K : DerivedCategory X.Modules}
    (hK : Stacks.Duality.IsDualizingComplex K) (F : X.Modules) [F.IsCoherent] (k : ℕ)
    (hF : SheafHasPropertySk X F k) (U : X.Opens) (hU : IsAffineOpen U) :
    ({x : X |
        Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
            (F.presheaf.stalk x) = (k : ℕ∞) ∧
          (k : WithBot ℕ∞) < Module.supportDim (X.presheaf.stalk x) (F.presheaf.stalk x)} ∩
      (U : Set X)).Finite := by
  obtain ⟨_, _⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  have hnoeth : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hfinM : Module.Finite Γ(X, U) Γ(F, U) := moduleFinite_sections_on_affine F U hU
  obtain ⟨ω, hω, -⟩ := hK U hU
  have hring := Module.finite_setOf_depth_eq_and_lt_supportDim_localization ω hω k Γ(F, U)
    fun q => by
      have hqU : hU.fromSpec q ∈ U := (hU.isoSpec.inv q).2
      have hqEq : hU.primeIdealOf ⟨hU.fromSpec q, hqU⟩ = q :=
        hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf ⟨hU.fromSpec q, hqU⟩)
      obtain ⟨hdep, hdim⟩ := depth_and_supportDim_stalk_eq_localization F hU hqU
      have hpoint := min_supportDim_le_depth_of_sheafHasPropertySk F k hF (hU.fromSpec q)
      rwa [hdep, hdim, hqEq] at hpoint
  refine (hring.image hU.fromSpec).subset ?_
  rintro x ⟨hxE, hxU⟩
  refine ⟨hU.primeIdealOf ⟨x, hxU⟩, ?_, hU.fromSpec_primeIdealOf ⟨x, hxU⟩⟩
  obtain ⟨hdep, hdim⟩ := depth_and_supportDim_stalk_eq_localization F hU hxU
  exact ⟨hdep ▸ hxE.1, hdim ▸ hxE.2⟩

/-- **Stacks Project, Tag 0ECN.**  Let `X` be a Noetherian scheme with a dualizing complex `K`,
let `F` be a coherent `𝒪_X`-module and let `k ≥ 0` be an integer.  If `F` satisfies Serre's
condition `(Sₖ)`, then there are only finitely many points `x ∈ X` with

`depth(F_x) = k` and `dim Supp(F_x) > k`. -/
@[stacks 0ECN]
public theorem finite_setOf_depth_eq_and_lt_supportDim (X : Scheme.{u}) [IsNoetherian X]
    [HasDerivedCategory.{w} X.Modules] {K : DerivedCategory X.Modules}
    (hK : Stacks.Duality.IsDualizingComplex K) (F : X.Modules) [F.IsCoherent] (k : ℕ)
    (hF : SheafHasPropertySk X F k) :
    {x : X |
        Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
            (F.presheaf.stalk x) = (k : ℕ∞) ∧
          (k : WithBot ℕ∞) <
            Module.supportDim (X.presheaf.stalk x) (F.presheaf.stalk x)}.Finite := by
  classical
  set E : Set X := {x : X |
      Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (F.presheaf.stalk x) = (k : ℕ∞) ∧
        (k : WithBot ℕ∞) < Module.supportDim (X.presheaf.stalk x) (F.presheaf.stalk x)}
  obtain ⟨Us, hUs, hUs_finite, hUs_sup⟩ :=
    X.isBasis_affineOpens.exists_finite_of_isCompact (U := (⊤ : X.Opens))
      (by simpa using isCompact_univ (X := X))
  have : Fintype Us := hUs_finite.fintype
  have hfin (i : Us) : (E ∩ (i.1 : Set X)).Finite :=
    finite_setOf_depth_eq_and_lt_supportDim_inter_affine hK F k hF i.1 (hUs i.2)
  refine (Set.finite_iUnion hfin).subset fun x hx => ?_
  have hxtop : x ∈ ((⊤ : X.Opens) : Set X) := trivial
  rw [hUs_sup, sSup_eq_iSup] at hxtop
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxtop
  obtain ⟨hiUs, hxi⟩ := Opens.mem_iSup.mp hi
  exact Set.mem_iUnion.mpr ⟨⟨i, hiUs⟩, ⟨hx, hxi⟩⟩

end AlgebraicGeometry

end
