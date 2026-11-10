module

public import StacksFrontier.AlgebraicGeometry.Divisors.ReflexiveEquivalence.StalkDescent
public import StacksFrontier.AlgebraicGeometry.Modules.Stalk
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# The rank of a stalk of a module associated with a module over an affine open

Let `V` be an affine open of a scheme `Y` and `F` an `𝒪_Y`-module whose restriction to `V` is
the sheaf associated with a `Γ(Y, V)`-module `N` (transported along `V ≅ Spec Γ(Y, V)`).  Then
at a point `y ∈ V` corresponding to the prime `p` of `Γ(Y, V)`, the rank of the stalk `F_y` over
the local ring `𝒪_{Y, y}` is the rank of the localization `N_p` over `Γ(Y, V)_p`.

## Main results

* `AlgebraicGeometry.finrank_stalk_eq_finrank_localizedModule`.
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.AlgebraicGeometry.ReflexiveEquivalence

universe u

namespace AlgebraicGeometry

/-- **Ranks are invariant under semilinear equivalences over ring isomorphisms.** -/
theorem finrank_eq_of_semilinearEquiv {R S : Type*} {M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] {τ : R →+* S} {τ' : S →+* R}
    [RingHomInvPair τ τ'] [RingHomInvPair τ' τ] (hτ : Function.Bijective τ)
    (e : M ≃ₛₗ[τ] N) :
    Module.finrank R M = Module.finrank S N := by
  have h := _root_.lift_rank_eq_of_equiv_equiv (fun r => τ r) e.toAddEquiv hτ
    fun r m => e.map_smulₛₗ r m
  have h' := congrArg Cardinal.toNat h
  simp only [Cardinal.toNat_lift] at h'
  exact h'

/-- Ranks are invariant under semilinear equivalences over a ring equivalence. -/
private theorem finrank_eq_of_ringEquiv {R S : Type*} {M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] (eR : R ≃+* S)
    (e : ∀ [RingHomInvPair (eR : R →+* S) (eR.symm : S →+* R)]
      [RingHomInvPair (eR.symm : S →+* R) (eR : R →+* S)], M ≃ₛₗ[(eR : R →+* S)] N) :
    Module.finrank R M = Module.finrank S N :=
  haveI := RingHomInvPair.of_ringEquiv eR
  haveI := RingHomInvPair.of_ringEquiv_symm eR
  finrank_eq_of_semilinearEquiv (τ' := (eR.symm : S →+* R)) eR.bijective e

/-- The rank of the stalk of `F|_W` at `w` is the rank of the stalk of `F` at `j w`, for an open
immersion `j : W ⟶ X`. -/
theorem finrank_restrict_stalk {X W : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) (w : W) :
    Module.finrank (W.presheaf.stalk w) ((F.restrict j).presheaf.stalk w) =
      Module.finrank (X.presheaf.stalk (j w)) (F.presheaf.stalk (j w)) :=
  finrank_eq_of_ringEquiv (openImmersionStalkRingEquiv j w)
    (restrictStalkSemilinearEquiv j F w)

/-- The rank of the stalk at `p` of the sheaf associated with an `A`-module `N` on `Spec A` is the
rank of the localization `N_p` over `A_p`. -/
theorem finrank_tilde_stalk {A : CommRingCat.{u}} (N : ModuleCat.{u} A) (p : PrimeSpectrum A) :
    letI := Scheme.Modules.moduleStalkPresheaf (tilde N) p
    Module.finrank ((Spec A).presheaf.stalk p) ((tilde N).presheaf.stalk p) =
      Module.finrank (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl N) := by
  let _inst := Scheme.Modules.moduleStalkPresheaf (tilde N) p
  let eR : (Spec A).presheaf.stalk p ≃+* Localization.AtPrime p.asIdeal :=
    (StructureSheaf.stalkIso A p).symm.toRingEquiv
  let : Module (Localization.AtPrime p.asIdeal) ((tilde N).presheaf.stalk p) :=
    Module.compHom _ eR.symm.toRingHom
  have _htower : IsScalarTower A (Localization.AtPrime p.asIdeal)
      ((tilde N).presheaf.stalk p) :=
    .of_algebraMap_smul fun r m => by
      change eR.symm (algebraMap A _ r) • m = r • m
      have hr : eR.symm (algebraMap A _ r) = (StructureSheaf.toStalk A p).hom r :=
        (StructureSheaf.stalkIso A p).commutes r
      rw [hr]
      rfl
  let eLoc : LocalizedModule p.asIdeal.primeCompl N
      ≃ₗ[Localization.AtPrime p.asIdeal] (tilde N).presheaf.stalk p :=
    LinearEquiv.extendScalarsOfIsLocalization p.asIdeal.primeCompl _
      (IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N) (tilde.toStalk N p).hom)
  rw [finrank_eq_of_ringEquiv eR
    { AddEquiv.refl _ with
      map_smul' := fun a z => by change a • z = eR.symm (eR a) • z; simp }, eLoc.finrank_eq]

/-- **The rank of a stalk of a module associated with a module over an affine open.**  If the
restriction of `F` to the affine open `V` is the sheaf associated with the `Γ(Y, V)`-module `N`,
then at `y ∈ V`, with prime `p` of `Γ(Y, V)`, the rank of `F_y` over `𝒪_{Y, y}` is the rank of
`N_p` over `Γ(Y, V)_p`. -/
theorem finrank_stalk_eq_finrank_localizedModule {Y : Scheme.{u}} (V : Y.affineOpens)
    (F : Y.Modules) (N : ModuleCat.{u} Γ(Y, V))
    (e : F.restrict V.1.ι ≅
      (tilde.functor Γ(Y, V) ⋙ Scheme.Modules.restrictFunctor V.2.isoSpec.hom).obj N)
    (y : V.1.toScheme) :
    Module.finrank (Y.presheaf.stalk (V.1.ι y)) (F.presheaf.stalk (V.1.ι y)) =
      Module.finrank (Localization.AtPrime (V.2.primeIdealOf y).asIdeal)
        (LocalizedModule (V.2.primeIdealOf y).asIdeal.primeCompl N) := by
  rw [← finrank_restrict_stalk V.1.ι F y, (stalkLinearEquivOfIso e y).finrank_eq]
  exact (finrank_restrict_stalk V.2.isoSpec.hom (tilde N) y).trans (finrank_tilde_stalk N _)

end AlgebraicGeometry

end
