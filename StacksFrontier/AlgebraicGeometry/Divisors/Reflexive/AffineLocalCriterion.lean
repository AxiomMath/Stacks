module

public import StacksFrontier.Algebra.Module.Reflexive.Localization
public import StacksFrontier.AlgebraicGeometry.AssociatedPointPrime.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.ReflexiveEquivalence.StalkDescent

/-!
# Reflexivity of a coherent module is affine-local

On an integral locally Noetherian scheme a coherent module is reflexive exactly when its module
of sections over every affine open is a reflexive module over the ring of functions there.

## Main results

* `Module.isReflexive_congr_ringEquiv`: reflexivity is insensitive to replacing the base ring by
  an isomorphic one acting through the isomorphism.
* `AlgebraicGeometry.isReflexive_localizedModule_iff_isReflexive_stalk`: at a point of an affine
  open, the localization of the sections is reflexive exactly when the stalk is.
* `AlgebraicGeometry.isReflexive_sections_iff_forall_isReflexive_stalk`: the sections over an
  affine open are reflexive exactly when every stalk at a point of that open is.
* `AlgebraicGeometry.isReflexive_iff_sections_isReflexive`: the affine-local criterion.

## References

* [Stacks Project, Tag 0AY0](https://stacks.math.columbia.edu/tag/0AY0)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.AssociatedPointPrime
open Stacks.AlgebraicGeometry.ReflexiveEquivalence
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

/-- Reflexivity of a module is unchanged when the base ring is replaced by an isomorphic one
acting through the isomorphism. -/
theorem Module.isReflexive_congr_ringEquiv {R S N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup N] [Module R N] [Module S N] (e : R ≃+* S)
    (hsmul : ∀ (r : R) (n : N), r • n = e r • n) :
    Module.IsReflexive R N ↔ Module.IsReflexive S N := by
  have hsymm (s : S) (n : N) : s • n = e.symm s • n := by
    rw [hsmul (e.symm s) n, e.apply_symm_apply]
  have : RingHomInvPair (e : R →+* S) (e.symm : S →+* R) := RingHomInvPair.of_ringEquiv e
  have : RingHomInvPair (e.symm : S →+* R) (e : R →+* S) := RingHomInvPair.of_ringEquiv_symm e
  have : RingHomInvPair (e.symm : S →+* R) (e.symm.symm : R →+* S) :=
    RingHomInvPair.of_ringEquiv e.symm
  have : RingHomInvPair (e.symm.symm : R →+* S) (e.symm : S →+* R) :=
    RingHomInvPair.of_ringEquiv_symm e.symm
  exact ⟨fun _ => isReflexive_of_semilinearEquiv e
      { toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
        map_add' := fun _ _ => rfl, map_smul' := hsmul },
    fun _ => isReflexive_of_semilinearEquiv e.symm
      { toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
        map_add' := fun _ _ => rfl, map_smul' := hsymm }⟩

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- At a point `x` of an affine open `U`, the localization of `Γ(F, U)` at the prime of `x` is a
reflexive module over the localization of `Γ(X, U)` there exactly when the stalk `F_x` is a
reflexive `𝒪_{X,x}`-module. -/
theorem isReflexive_localizedModule_iff_isReflexive_stalk
    (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)
    {x : X} (hx : x ∈ U) :
    Module.IsReflexive (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
        (LocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl Γ(F, U)) ↔
      Module.IsReflexive (X.presheaf.stalk x) (F.presheaf.stalk x) := by
  set p := (hU.primeIdealOf ⟨x, hx⟩).asIdeal with hp
  have hprime : p.IsPrime := (hU.primeIdealOf ⟨x, hx⟩).isPrime
  let : Module Γ(X, U) ↑(F.presheaf.stalk x) := sectionsStalkModule F hx
  let : Algebra Γ(X, U) ↑(X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  have hlocR : IsLocalization.AtPrime ↑(X.presheaf.stalk x) p :=
    hU.isLocalization_stalk ⟨x, hx⟩
  have hlocM : IsLocalizedModule p.primeCompl (germₗ F hx) := isLocalizedModule_germₗ F hU hx
  let e : Localization.AtPrime p ≃ₐ[Γ(X, U)] ↑(X.presheaf.stalk x) :=
    IsLocalization.algEquiv p.primeCompl _ _
  have he (r : Γ(X, U)) : e (algebraMap Γ(X, U) (Localization.AtPrime p) r) =
      (X.presheaf.germ U x hx) r := by
    simpa only [RingHom.algebraMap_toAlgebra] using e.commutes r
  let : Algebra (Localization.AtPrime p) ↑(X.presheaf.stalk x) :=
    e.toRingEquiv.toRingHom.toAlgebra
  let : Module (Localization.AtPrime p) ↑(F.presheaf.stalk x) :=
    Module.compHom _ e.toRingEquiv.toRingHom
  have hsmulA (a : Localization.AtPrime p) (n : ↑(F.presheaf.stalk x)) : a • n = e a • n := rfl
  let : IsScalarTower Γ(X, U) (Localization.AtPrime p) ↑(F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun r n => by
      rw [hsmulA, he r]
      rfl
  let eLoc : LocalizedModule p.primeCompl Γ(F, U) ≃ₗ[Localization.AtPrime p]
      ↑(F.presheaf.stalk x) :=
    (IsLocalizedModule.iso p.primeCompl (germₗ F hx)).extendScalarsOfIsLocalization
      p.primeCompl (Localization.AtPrime p)
  have hmod : Module.IsReflexive (Localization.AtPrime p)
      (LocalizedModule p.primeCompl Γ(F, U)) ↔
      Module.IsReflexive (Localization.AtPrime p) ↑(F.presheaf.stalk x) :=
    ⟨fun _ => Module.equiv eLoc, fun _ => Module.equiv eLoc.symm⟩
  exact hmod.trans (Module.isReflexive_congr_ringEquiv e.toRingEquiv hsmulA)

/-- The sections of a coherent module over an affine open of a locally Noetherian scheme form a
reflexive module exactly when the stalk at every point of that open is reflexive. -/
theorem isReflexive_sections_iff_forall_isReflexive_stalk [IsLocallyNoetherian X]
    (F : X.Modules) [_root_.SheafOfModules.IsCoherent F] {U : X.Opens} (hU : IsAffineOpen U) :
    Module.IsReflexive Γ(X, U) Γ(F, U) ↔
      ∀ x : X, x ∈ U → Module.IsReflexive (X.presheaf.stalk x) (F.presheaf.stalk x) := by
  let : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
  let : F.IsFiniteType := _root_.IsCoherent.toIsFiniteType F
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : Module.Finite Γ(X, U) Γ(F, U) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F hU
  have hlocal : Module.IsReflexive Γ(X, U) Γ(F, U) ↔
      ∀ (q : Ideal Γ(X, U)) [q.IsPrime],
        Module.IsReflexive (Localization.AtPrime q) (LocalizedModule q.primeCompl Γ(F, U)) :=
    (reflexive_tfae Γ(X, U) Γ(F, U)).out 1 2
  refine ⟨fun h x hx => (isReflexive_localizedModule_iff_isReflexive_stalk F hU hx).mp
    (hlocal.mp h (hU.primeIdealOf ⟨x, hx⟩).asIdeal), fun h => hlocal.mpr fun q hq => ?_⟩
  let y : PrimeSpectrum Γ(X, U) := ⟨q, hq⟩
  have hy : hU.fromSpec y ∈ U := (hU.isoSpec.inv y).2
  have hq' : hU.primeIdealOf ⟨hU.fromSpec y, hy⟩ = y :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf ⟨hU.fromSpec y, hy⟩)
  have hmain := (isReflexive_localizedModule_iff_isReflexive_stalk F hU hy).mpr
    (h (hU.fromSpec y) hy)
  rwa [hq'] at hmain

/-- A coherent module on an integral locally Noetherian scheme is reflexive if and only if its
module of sections over every affine open is reflexive. -/
@[stacks 0AY0]
theorem isReflexive_iff_sections_isReflexive (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] (F : X.Modules) [_root_.SheafOfModules.IsCoherent F] :
    IsReflexive F ↔ ∀ (U : X.Opens), IsAffineOpen U → Module.IsReflexive Γ(X, U) Γ(F, U) := by
  let : F.IsFinitePresentation := _root_.isFinitePresentation_of_isCoherent F
  let : _root_.SheafOfModules.IsCoherent (dualSheaf F) := isCoherent_dualSheaf F
  let : (dualSheaf F).IsFinitePresentation := _root_.isFinitePresentation_of_isCoherent _
  refine ⟨fun hF U hU => (isReflexive_sections_iff_forall_isReflexive_stalk F hU).mpr
    fun x _ => isReflexive_stalk_of_isReflexive F hF x,
    fun hsections => isReflexive_of_forall_isReflexive_stalk F fun x => ?_⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (a := x) (Set.mem_univ x) isOpen_univ
  exact (isReflexive_sections_iff_forall_isReflexive_stalk F hU).mp (hsections U hU) x hxU

end AlgebraicGeometry

end
