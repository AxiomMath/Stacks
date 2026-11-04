module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenPushforward
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.AffineTarget
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Module
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf

/-!
# A quasi-coherent module on an affine scheme has the rank of its global sections

Let `T` be an affine scheme and `ℳ` a quasi-coherent `𝒪_T`-module.  If the global sections
`Γ(T, ℳ)` form a finite locally free `Γ(T, 𝒪_T)`-module of rank `r`, then `ℳ` is a finite
locally free `𝒪_T`-module of rank `r`.  On the spectrum of a ring this is the comparison of
`ℳ` with the module associated to its global sections, which preserves the rank
(`tilde_isFiniteLocallyFreeOfRank_iff`); an arbitrary affine scheme is carried to the spectrum of
its ring of global functions by the isomorphism `T ≅ Spec Γ(T, 𝒪_T)`, along which the direct
image of `ℳ` has the same global sections.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_of_spec`: the statement on the
  spectrum of a ring.
* `AlgebraicGeometry.Scheme.Modules.globalSectionsLinearEquivIsoSpec`: the global sections of
  the direct image along `T ≅ Spec Γ(T, 𝒪_T)` are the global sections of `ℳ`.
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_of_isAffine`: **the statement on
  an affine scheme.**
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- On the spectrum of a ring, a quasi-coherent module whose global sections are finite locally
free of rank `r` is finite locally free of rank `r`. -/
theorem isFiniteLocallyFreeOfRank_of_spec (R : CommRingCat.{u}) (M : (Spec R).Modules)
    [hqc : M.IsQuasicoherent] (r : ℕ)
    (h : Module.IsFiniteLocallyFreeOfRank R (moduleSpecΓFunctor.obj M) r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r := by
  have : IsIso (fromTildeΓ (R := R) M) := (isQuasicoherent_iff_isIso_fromTildeΓ M).mp hqc
  exact (isFiniteLocallyFreeOfRank_iff M r).mp <| IsFiniteLocallyFreeOfRank.of_iso
    (asIso (fromTildeΓ (R := R) M))
    ((tilde_isFiniteLocallyFreeOfRank_iff ↑R ↑(moduleSpecΓFunctor.obj M) r).mpr h)

/-- The global sections of the direct image of a module along the isomorphism
`T ≅ Spec Γ(T, 𝒪_T)` of an affine scheme are the global sections of the module, linearly over
`Γ(T, 𝒪_T)`. -/
def globalSectionsLinearEquivIsoSpec {T : Scheme.{u}} [IsAffine T] (M : T.Modules) :
    Γ(M, ⊤) ≃ₗ[Γ(T, ⊤)]
      (moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward T.isoSpec.hom).obj M)) where
  toFun m := m
  invFun m := m
  map_add' _ _ := rfl
  map_smul' r m := by
    change r • m = (T.isoSpec.hom.appTop.hom ((Scheme.ΓSpecIso Γ(T, ⊤)).inv.hom r)) • m
    have : T.isoSpec.hom.appTop.hom ((Scheme.ΓSpecIso Γ(T, ⊤)).inv.hom r) = r := by
      rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
      exact congrArg (fun φ => φ.hom r) (Iso.inv_hom_id (Scheme.ΓSpecIso Γ(T, ⊤)))
    rw [this]
  left_inv _ := rfl
  right_inv _ := rfl

/-- **A quasi-coherent module on an affine scheme whose global sections are finite locally free
of rank `r` is finite locally free of rank `r`.** -/
theorem isFiniteLocallyFreeOfRank_of_isAffine {T : Scheme.{u}} [IsAffine T] (M : T.Modules)
    [M.IsQuasicoherent] {r : ℕ} (h : Module.IsFiniteLocallyFreeOfRank Γ(T, ⊤) Γ(M, ⊤) r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r :=
  SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    (@asIso _ _ _ _ _ (isIso_pullbackPushforwardAdjunction_counit_app_of_isOpenImmersion
      T.isoSpec.hom M))
    (@AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ T.isoSpec.hom
      ((Scheme.Modules.pushforward T.isoSpec.hom).obj M) r
      (isFiniteLocallyFreeOfRank_of_spec Γ(T, ⊤) ((Scheme.Modules.pushforward T.isoSpec.hom).obj M)
        r (h.of_linearEquiv (globalSectionsLinearEquivIsoSpec M))))

end AlgebraicGeometry.Scheme.Modules

end
