module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankDecomposition
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Restriction
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Transport

/-!
# The rank of a finite locally free module whose pullback is free

Let `E` be a finite locally free module on a scheme `X` and let `q : T ⟶ X` be a morphism of
schemes such that `q^*E` is free on a finite index type `J`. Then `E` has rank `#J` at every
point of the image of `q`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.restrictIsoFreeOfOverIso`: a module free on the slice site over
  an open is free after restriction to that open.
* `AlgebraicGeometry.Scheme.Modules.restrictPullbackIsoFree`: the pullback of a module free over
  `V` is free over the preimage of `V`.
* `AlgebraicGeometry.Scheme.Modules.trivializationOfRestrictIso`: the trivialisation given by an
  isomorphism of a restriction with a free module.

## Main results

* `AlgebraicGeometry.Scheme.Modules.mem_rankStratum_of_pullback_iso_free_of_finite`: if `q^*E`
  is free on a finite type `J`, then `q` maps into the locus where `E` has rank `#J`.
* `AlgebraicGeometry.Scheme.Modules.mem_rankStratum_of_pullback_iso_free`: the same statement
  for the standard free module of rank `m`.
* `AlgebraicGeometry.Scheme.Modules.mem_rankStratum_zero_of_pullback_iso_free_pempty`: if `q^*E`
  is zero, in the sense of being free on the empty type, then `q` maps into the locus where `E`
  has rank `0`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace LocallyFreeRank

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The restriction of a sheaf of modules to an open on which it is free on the slice site is
free on the same index type. -/
def restrictIsoFreeOfOverIso {X : Scheme.{u}} (E : X.Modules) (V : X.Opens) (I : Type u)
    (e : SheafOfModules.free.{u} I ≅ (toRingSheafModule E).over V) :
    (restrictFunctor V.ι).obj E ≅ SheafOfModules.free.{u} I :=
  letI := hasSheafify_overOpens V
  letI := wEqualsLocallyBijective_overOpens V
  restrictIsoFreeOfGeneratingSections E V
    (SheafOfModules.GeneratingSections.equivOfIso e (SheafOfModules.free.generatingSections I))
    (isIso_equivOfIso_free_generatingSections_π I e)

/-- If `E` is free on `I` over an open `V`, then the pullback of `E` along `q` is free on `I`
over the preimage of `V`. -/
def restrictPullbackIsoFree {X T : Scheme.{u}} (E : X.Modules) (q : T ⟶ X) (V : X.Opens)
    (I : Type u) (eV : (restrictFunctor V.ι).obj E ≅ SheafOfModules.free.{u} I) :
    (restrictFunctor (q ⁻¹ᵁ V).ι).obj ((pullback q).obj E) ≅ SheafOfModules.free.{u} I :=
  (restrictFunctorIsoPullback (q ⁻¹ᵁ V).ι).app _ ≪≫
    (pullbackComp (q ⁻¹ᵁ V).ι q).app E ≪≫
    (pullbackCongr (morphismRestrict_ι q V).symm).app E ≪≫
    (pullbackComp (q ∣_ V) V.ι).symm.app E ≪≫
    (pullback (q ∣_ V)).mapIso ((restrictFunctorIsoPullback V.ι).symm.app E ≪≫ eV) ≪≫
    pullbackFreeIso (q ∣_ V) I

/-- An isomorphism between the restriction of a sheaf of modules to an open and a free sheaf of
modules is a trivialisation of it on that open. -/
def trivializationOfRestrictIso {T : Scheme.{u}} (F : T.Modules) (W : T.Opens) (I : Type u)
    (e : (restrictFunctor W.ι).obj F ≅ SheafOfModules.free.{u} I) :
    Trivialization T.toTopCat (toRingSheaf T.toTopCat T.sheaf) F W :=
  ⟨I, (overFunctorEquiv W).app F ≪≫ e⟩

/-- If the pullback of a finite
locally free module `E` along `q : T ⟶ X` is free on a finite type `J`, then `E` has rank `#J`
at every point of the image of `q`. -/
theorem mem_rankStratum_of_pullback_iso_free_of_finite {X T : Scheme.{u}} (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (q : T ⟶ X)
    (J : Type u) [Finite J] (e : (pullback q).obj E ≅ SheafOfModules.free.{u} J) (t : T) :
    q t ∈ rankStratum E (Nat.card J) := by
  obtain ⟨V, hV, -, I, ⟨eI⟩, ⟨eV⟩⟩ :=
    exists_free_nbhd_of_mem_rankStratum E _ (q t) ((mem_rankStratum E).2 rfl)
  have ht : t ∈ q ⁻¹ᵁ V := hV
  have hcard : Nat.card I = Nat.card J := congrArg Cardinal.toNat <|
    Trivialization.rank_eq_of_mem T.toTopCat T.sheaf (scheme_stalksNontrivial T)
      ((pullback q).obj E) t ht ht
      (trivializationOfRestrictIso _ _ I
        (restrictPullbackIsoFree E q V I (restrictIsoFreeOfOverIso E V I eV)))
      (trivializationOfRestrictIso _ _ J
        ((restrictFunctor (q ⁻¹ᵁ V).ι).mapIso e ≪≫ (restrictFreeIso (q ⁻¹ᵁ V).ι J).symm))
  rw [Nat.card_congr eI, Nat.card_fin] at hcard
  exact (mem_rankStratum E).2 hcard

/-- If the pullback of a finite locally free module `E` along `q : T ⟶ X` is the free module of
rank `m`, then `E` has rank `m` at every point of the image of `q`. -/
theorem mem_rankStratum_of_pullback_iso_free {X T : Scheme.{u}} (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (q : T ⟶ X) {m : ℕ}
    (e : (Scheme.Modules.pullback q).obj E ≅ SheafOfModules.free (ULift.{u} (Fin m))) (t : T) :
    q t ∈ rankStratum E m := by
  simpa using mem_rankStratum_of_pullback_iso_free_of_finite E q _ e t

/-- If the pullback of a finite locally free module `E` along `q : T ⟶ X` is free on the empty
type, then `E` has rank `0` at every point of the image of `q`. -/
theorem mem_rankStratum_zero_of_pullback_iso_free_pempty {X T : Scheme.{u}} (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (q : T ⟶ X)
    (e : (Scheme.Modules.pullback q).obj E ≅ SheafOfModules.free PEmpty.{u + 1}) (t : T) :
    q t ∈ rankStratum E 0 := by
  simpa using mem_rankStratum_of_pullback_iso_free_of_finite E q _ e t

end AlgebraicGeometry.Scheme.Modules
