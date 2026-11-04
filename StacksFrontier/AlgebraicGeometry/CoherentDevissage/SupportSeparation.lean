module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.Sections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.IdealPowerMultiple
import all StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.RelativeFinitePresentation.Operations

/-!
# Separating the support of a coherent module into two closed pieces

[Stacks, Tag 01YD] says that a coherent module `F` on a Noetherian scheme whose support is a
union `Z ∪ Z'` of two closed sets sits in a short exact sequence

`0 ⟶ G' ⟶ F ⟶ G ⟶ 0`

of coherent modules with `Supp G' ⊆ Z'` and `Supp G ⊆ Z`.

The witnesses are the ones the source uses. Let `I` and `J` be the vanishing ideal sheaves of
`Z` and `Z'`, so that `Supp F ⊆ V(I) ∪ V(J) = V(IJ)`; [Stacks, Tag 01Y9] supplies an `n` with
`(IJ) ^ n F = 0`, and the sequence is

`0 ⟶ I ^ n F ⟶ F ⟶ F / I ^ n F ⟶ 0`.

For the two support claims it is enough, again by [Stacks, Tag 01Y9], to annihilate each outer
term by a power of the relevant ideal, and both computations are affine-local because the
sections of `I ^ n F` over an affine open `U` are exactly `I(U) ^ n Γ(F, U)`
(`Stacks.Algebraization.idealPowerMultiple_toSubmodule_obj_affine`):

* `J ^ n` kills `I ^ n F`, because `J(U) ^ n (I(U) ^ n Γ(F, U)) = ((IJ)(U)) ^ n Γ(F, U) = 0`;
* `I ^ n` kills `F / I ^ n F`, because over an affine open the quotient map is surjective on
  sections and `I(U) ^ n Γ(F, U)` is exactly the submodule being quotiented out.

This is why the argument needs no restriction to the open complement of `Z'`, which is how the
source phrases the second step: the uniform exponent that [Stacks, Tag 01Y9] already produces on
`X` does the work on every affine open at once.

## Main results

* `Stacks.AlgebraicGeometry.CoherentDevissage.idealPowerMultiple_eq_bot_of_forall_smul_eq_zero`:
  the affine-local pointwise criterion for `I ^ n M = 0`.
* `Stacks.AlgebraicGeometry.CoherentDevissage.idealPowerMultiple_toSheafOfModules_eq_bot_of_mul`:
  if `(IJ) ^ n F` vanishes then `J ^ n` annihilates `I ^ n F`.
* `Stacks.AlgebraicGeometry.CoherentDevissage.idealPowerMultiple_cokernel_eq_bot`: `I ^ n`
  annihilates `F / I ^ n F`, for `F` quasi-coherent.
* `Stacks.AlgebraicGeometry.CoherentDevissage.exists_submodule_supp_subset_of_supp_eq_union`:
  [Stacks, Tag 01YD] with the sub-object exhibited as a submodule of `F`, which is the form the
  filtration of [Stacks, Tag 01YF] consumes.
* `Stacks.AlgebraicGeometry.CoherentDevissage.exists_shortExact_coherent_of_supp_eq_union`:
  [Stacks, Tag 01YD] as a short exact sequence.

## Implementation notes

**`_root_.SheafOfModules.IsCoherent` is written out throughout**, for the reason recorded in
`DevissageFiltration.lean`: inside the `Stacks.` namespace the unqualified spelling resolves to
`Stacks.SheafOfModules.IsCoherent`, a different constant, once that declaration is in the import
closure — which it is here, through `CoherentSubquotients.Basic`. The predicate used is the one
[Stacks, Tag 01Y9] and the dévissage engine are stated with.

**Three consequences of `AlgebraicGeometry.Scheme.Modules` being a plain `def`**: instance search does not see
through it to `SheafOfModules X.ringCatSheaf`, where the relevant instances live.

* `Mono N.ι` is **not** synthesized for a submodule `N` of an `X.Modules`. It is obtained by
  reflecting the monomorphism along the forgetful functor, which is also why it appears in the
  conclusion of `exists_submodule_supp_subset_of_supp_eq_union` rather than being left to the
  consumer. For the same reason `Epi (cokernel.π N.ι)` is obtained from
  `CategoryTheory.Limits.epi_of_isColimit_cofork`.
* `Submodule.smul_le` re-synthesizes `Module Γ(X, U) Γ(M, U)`, which fails when `M` is
  `N.toSheafOfModules` rather than a variable of type `X.Modules`. That is the whole reason
  `idealPowerMultiple_eq_bot_of_forall_smul_eq_zero` exists as a separate lemma about a variable
  `M : X.Modules`: inside it the synthesis succeeds, and at the call sites the instance arrives
  by substitution instead.
* Anything proved by `rw` about `N.toSheafOfModules` must first bind it at type `X.Modules` with
  `set`; `rw` builds its motive at `implicit` transparency and reports an application type
  mismatch between `TopCat.Sheaf RingCat ↑X.toPresheafedSpace` and
  `Sheaf (Opens.grothendieckTopology ↥X) RingCat` for the one term `X.ringCatSheaf`.

## References

* [Stacks Project, Tag 01YD](https://stacks.math.columbia.edu/tag/01YD)
* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Algebraization

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.AlgebraicGeometry.HigherDirectImageCoherent

variable {X : Scheme.{u}}

/-! ### Annihilating a quasi-coherent module by a power of an ideal sheaf -/

/-- **The affine-local pointwise criterion for `I ^ n M = 0`.** For `M` quasi-coherent it is
enough that every section of `I(U) ^ n` annihilate every section of `M` over every affine open
`U`.

`M` must be a variable of type `X.Modules`, not a term like `N.toSheafOfModules`: see the
implementation notes. -/
public theorem idealPowerMultiple_eq_bot_of_forall_smul_eq_zero (I : X.IdealSheafData) (n : ℕ)
    (M : X.Modules) [M.IsQuasicoherent]
    (h : ∀ U : X.affineOpens, ∀ a ∈ I.ideal U ^ n, ∀ m : Γ(M, U.1), a • m = 0) :
    idealPowerMultiple I n M = ⊥ := by
  refine (Stacks.IdealPowerSupport.idealPowerMultiple_eq_bot_iff I n M).2 fun U => ?_
  refine le_antisymm (Submodule.smul_le.2 fun a ha m _ => ?_) bot_le
  exact (Submodule.mem_bot _).2 (h U a ha m)

/-- The cokernel projection of a morphism of modules over a scheme is an epimorphism. -/
private instance epi_cokernel_π {F G : X.Modules} (f : G ⟶ F) : Epi (cokernel.π f) :=
  Limits.epi_of_isColimit_cofork (colimit.isColimit _)

/-- The cokernel of a morphism of quasi-coherent modules is quasi-coherent. -/
private instance isQuasicoherent_cokernel_of_isQuasicoherent {F G : X.Modules} (f : G ⟶ F)
    [G.IsQuasicoherent] [F.IsQuasicoherent] : (cokernel f).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel f

/-- The submodule `I ^ n F` of a quasi-coherent module `F` is quasi-coherent. -/
private instance isQuasicoherent_idealPowerMultiple_toSheafOfModules (I : X.IdealSheafData)
    (n : ℕ) (F : X.Modules) [F.IsQuasicoherent] :
    (idealPowerMultiple I n F).toSheafOfModules.IsQuasicoherent :=
  idealPowerMultiple_isQuasicoherent I n F

/-- **A power of `J` annihilates `I ^ n F` as soon as `(IJ) ^ n F` vanishes.** Over an affine
open the sections of `I ^ n F` are `I(U) ^ n Γ(F, U)`, and multiplying by `J(U) ^ n` lands in
`(I(U) J(U)) ^ n Γ(F, U) = ((IJ)(U)) ^ n Γ(F, U)`, which is zero. -/
public theorem idealPowerMultiple_toSheafOfModules_eq_bot_of_mul (I J : X.IdealSheafData) (n : ℕ)
    (F : X.Modules) [F.IsQuasicoherent] (hn : idealPowerMultiple (I * J) n F = ⊥) :
    idealPowerMultiple J n (idealPowerMultiple I n F).toSheafOfModules = ⊥ := by
  refine idealPowerMultiple_eq_bot_of_forall_smul_eq_zero J n
    (idealPowerMultiple I n F).toSheafOfModules fun U a ha m => ?_
  have hUbot := (Stacks.IdealPowerSupport.idealPowerMultiple_eq_bot_iff (I * J) n F).1 hn U
  -- the sections of `I ^ n F` over `U` are `I(U) ^ n Γ(F, U)`
  let mv : Γ(F, U.1) := m.val
  have hmem : mv ∈ I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) :=
    (idealPowerMultiple_toSubmodule_obj_affine I n F U).le m.property
  have hkey : a • mv = 0 := by
    refine Submodule.smul_induction_on hmem (fun c hc x _ => ?_) fun x y hx hy => ?_
    · have hprod : a * c ∈ ((I * J).ideal U) ^ n := by
        rw [show (I * J).ideal U = I.ideal U * J.ideal U from rfl, mul_pow, mul_comm a c]
        exact Ideal.mul_mem_mul hc ha
      have hz : (a * c) • x ∈ ((I * J).ideal U) ^ n • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) :=
        Submodule.smul_mem_smul hprod Submodule.mem_top
      rw [hUbot, Submodule.mem_bot] at hz
      rwa [smul_smul]
    · rw [smul_add, hx, hy, add_zero]
  exact Subtype.ext hkey

/-- **`I ^ n` annihilates `F / I ^ n F`.** Over an affine open the quotient map is surjective on
sections, because both modules are quasi-coherent, and a lift of a section multiplied by
`I(U) ^ n` lies in the sections of `I ^ n F` over `U`, hence dies in the quotient. -/
public theorem idealPowerMultiple_cokernel_eq_bot (I : X.IdealSheafData) (n : ℕ)
    (F : X.Modules) [F.IsQuasicoherent] :
    idealPowerMultiple I n (cokernel (idealPowerMultiple I n F).ι) = ⊥ := by
  set N : F.Submodule := idealPowerMultiple I n F with hN
  set G' : X.Modules := N.toSheafOfModules
  set f : G' ⟶ F := N.ι
  set G : X.Modules := cokernel f
  set g : F ⟶ G := cokernel.π f
  refine idealPowerMultiple_eq_bot_of_forall_smul_eq_zero I n G fun U a ha s => ?_
  obtain ⟨m, hm⟩ := AlgebraicGeometry.epi_app_of_isAffineOpen g U.1 U.2 s
  have hmem : a • m ∈ N.toSubmodule.obj (op U.1) := by
    rw [hN, idealPowerMultiple_toSubmodule_obj_affine I n F U]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  have hfz : Scheme.Modules.Hom.app f U.1 ⟨a • m, hmem⟩ = a • m := rfl
  have hcomp0 : Scheme.Modules.Hom.app (f ≫ g) U.1 ⟨a • m, hmem⟩ = 0 := by
    rw [cokernel.condition f]
    rfl
  have hcomp : Scheme.Modules.Hom.app g U.1 (a • m) = 0 := by
    rw [← hfz]
    simp only [Scheme.Modules.Hom.comp_app] at hcomp0
    exact hcomp0
  rwa [← hm, ← Scheme.Modules.Hom.app_smul]

/-! ### [Stacks, Tag 01YD] -/

/-- **[Stacks, Tag 01YD], with the sub-object exhibited as a submodule of `F`.** If the support
of a coherent module `F` on a Noetherian scheme is the union of two closed sets `Z` and `Z'`,
then `F` has a coherent submodule supported in `Z'` whose quotient is coherent and supported in
`Z`. The submodule is `I ^ n F`, for `I` the vanishing ideal of `Z` and `n` large enough that
`(I · J) ^ n F = 0`, where `J` is the vanishing ideal of `Z'`.

`Mono N.ι` is part of the conclusion because it is not synthesized: see the implementation notes
of this file. -/
public theorem exists_submodule_supp_subset_of_supp_eq_union
    (X : Scheme.{u}) [IsNoetherian X] (F : X.Modules) [_root_.SheafOfModules.IsCoherent F]
    (Z Z' : Set X) (hZ : IsClosed Z) (hZ' : IsClosed Z')
    (hF : SheafOfModules.supp F = Z ∪ Z') :
    ∃ N : F.Submodule,
      Mono (C := X.Modules) N.ι ∧
      _root_.SheafOfModules.IsCoherent N.toSheafOfModules ∧
      _root_.SheafOfModules.IsCoherent (cokernel N.ι) ∧
      SheafOfModules.supp N.toSheafOfModules ⊆ Z' ∧
      SheafOfModules.supp (cokernel N.ι) ⊆ Z := by
  classical
  have _hFqc : F.IsQuasicoherent :=
    @_root_.isQuasicoherent_of_isCoherent _ _ _ F inferInstance
  set I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZ⟩
  set J : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨Z', hZ'⟩
  have hIsupp : ((I.support : Closeds X) : Set X) = Z :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal ⟨Z, hZ⟩
  have hJsupp : ((J.support : Closeds X) : Set X) = Z' :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal ⟨Z', hZ'⟩
  have hIJ : SheafOfModules.supp F ⊆ (((I * J).support : Closeds X) : Set X) := by
    rw [Scheme.IdealSheafData.support_mul, Closeds.coe_sup, hIsupp, hJsupp, hF]
  obtain ⟨n, hn⟩ :=
    (Stacks.IdealPowerSupport.exists_idealPowerMultiple_eq_bot_iff_supp_subset F (I * J)).2 hIJ
  set N : F.Submodule := idealPowerMultiple I n F with hN
  set G' : X.Modules := N.toSheafOfModules
  set f : G' ⟶ F := N.ι
  set G : X.Modules := cokernel f
  have hmono : Mono f :=
    (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map
      (inferInstanceAs (Mono N.toSubmodule.ι))
  have hG'coh : _root_.SheafOfModules.IsCoherent G' :=
    Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono (F := F) (G := G') f
  have hGcoh : _root_.SheafOfModules.IsCoherent G :=
    Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_epi (F := F) (G := G)
      (cokernel.π f)
  refine ⟨N, hmono, hG'coh, hGcoh, ?_, ?_⟩
  · have h := (Stacks.IdealPowerSupport.exists_idealPowerMultiple_eq_bot_iff_supp_subset
      G' J).1 ⟨n, idealPowerMultiple_toSheafOfModules_eq_bot_of_mul I J n F hn⟩
    rwa [hJsupp] at h
  · have h := (Stacks.IdealPowerSupport.exists_idealPowerMultiple_eq_bot_iff_supp_subset
      G I).1 ⟨n, idealPowerMultiple_cokernel_eq_bot I n F⟩
    rwa [hIsupp] at h

/-- **[Stacks, Tag 01YD].** A coherent module whose support is a union of two closed sets is an
extension of coherent modules supported on those sets: there is a short exact sequence
`0 ⟶ G' ⟶ F ⟶ G ⟶ 0` of coherent modules with `Supp G' ⊆ Z'` and `Supp G ⊆ Z`, and `F` is
literally its middle term. -/
@[stacks 01YD]
public theorem exists_shortExact_coherent_of_supp_eq_union
    (X : Scheme.{u}) [IsNoetherian X] (F : X.Modules) [_root_.SheafOfModules.IsCoherent F]
    (Z Z' : Set X) (hZ : IsClosed Z) (hZ' : IsClosed Z')
    (hF : SheafOfModules.supp F = Z ∪ Z') :
    ∃ (G' G : X.Modules) (f : G' ⟶ F) (g : F ⟶ G) (w : f ≫ g = 0),
      (ShortComplex.mk f g w).ShortExact ∧
        _root_.SheafOfModules.IsCoherent G' ∧ _root_.SheafOfModules.IsCoherent G ∧
        SheafOfModules.supp G' ⊆ Z' ∧ SheafOfModules.supp G ⊆ Z := by
  obtain ⟨N, hmono, hG'coh, hGcoh, hG'supp, hGsupp⟩ :=
    exists_submodule_supp_subset_of_supp_eq_union X F Z Z' hZ hZ' hF
  exact ⟨N.toSheafOfModules, cokernel N.ι, N.ι, cokernel.π N.ι, cokernel.condition N.ι,
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel N.ι) hmono
      (epi_cokernel_π N.ι),
    hG'coh, hGcoh, hG'supp, hGsupp⟩

end Stacks.AlgebraicGeometry.HigherDirectImageCoherent

end

end
