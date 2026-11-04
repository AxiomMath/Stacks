module

public import StacksFrontier.Algebra.Module.Reflexive
public import StacksFrontier.Algebra.Module.TorsionFree
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.Depth
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineLocalization
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TorsionFree
public import StacksFrontier.AlgebraicGeometry.Divisors.OrderOfVanishingInvertible
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.AffineLocalCriterion
public import StacksFrontier.AlgebraicGeometry.Divisors.ReflexiveEquivalence.StalkDescent
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.DepthCoherence.ReflexiveExtension
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeTFAE
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.NormalDepthTwo
public import StacksFrontier.AlgebraicGeometry.Properties.Serre
public import StacksFrontier.AlgebraicGeometry.Reflexive.Basic
public import StacksFrontier.AlgebraicGeometry.Reflexive.ExtensionChain.Depth
public import StacksFrontier.AlgebraicGeometry.ReflexiveOpenEquivalence.Pushforward
public import StacksFrontier.AlgebraicGeometry.StalkFiniteType.RingCatStalk
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
public import StacksFrontier.RingTheory.Serre.Defs
public import StacksFrontier.Topology.Dimension.Codimension
public import StacksFrontier.Topology.Dimension.SpecializingSurjection
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksCore.Tactic.StacksAttribute

/-!
# Reflexive coherent modules on a normal scheme

On an integral locally Noetherian normal scheme a coherent module is reflexive exactly when it
is torsion free and satisfies Serre's condition `(S₂)`, and exactly when it is the direct image
of a finite locally free module from an open subscheme whose complement has codimension at
least two.

## Main results

* `AlgebraicGeometry.isReflexive_isTorsionFree_propertyS2_extension_tfae`: the three-way
  equivalence.

## Implementation notes

The codimension condition is stated at every point of the complement rather than on the
irreducible components of the complement, as the source does.  The two are equivalent: a point
`x` of the complement lies in some component `Z` of it, and then `closure {x} ⊆ Z`, so the
component bound gives the pointwise one; conversely the space of a scheme is sober, so a
component of the complement is the closure of a single point of the complement, and the
pointwise bound gives the component bound.

Equality of `F` with the direct image of its restriction is asserted of the *canonical* map, the
unit of the restriction–direct-image adjunction `Scheme.Modules.pullbackPushforwardAdjunction`,
which is stronger than the existence of some isomorphism.

## References

* [Stacks Project, Tag 0AY6](https://stacks.math.columbia.edu/tag/0AY6)
* [Stacks Project, Tag 0AY0](https://stacks.math.columbia.edu/tag/0AY0)
* [Stacks Project, Tag 0AVB](https://stacks.math.columbia.edu/tag/0AVB)
* [Stacks Project, Tag 0345](https://stacks.math.columbia.edu/tag/0345)
* [Stacks Project, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ)
* [Stacks Project, Tag 0B8J](https://stacks.math.columbia.edu/tag/0B8J)
* [Stacks Project, Tag 0AUW](https://stacks.math.columbia.edu/tag/0AUW)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ReflexiveEquivalence
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Serre's condition on the sections over an affine open -/

/-- Serre's condition `(Sₖ)` for a module transports along a surjective ring isomorphism. -/
private lemma module_serreSk_congr_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) (M : Type*) [AddCommGroup M] [Module A M]
    [Module B M] [Algebra A B] [IsScalarTower A B M]
    (hsurj : Function.Surjective (algebraMap A B)) (hAlg : algebraMap A B = e.toRingHom)
    (hmax : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal B) [Module.Finite A M] [Module.Finite B M] (k : ℕ) :
    (min (k : WithBot ℕ∞) (Module.supportDim A M) ≤
        (Module.depth A (IsLocalRing.maximalIdeal A) M : WithBot ℕ∞)) ↔
      min (k : WithBot ℕ∞) (Module.supportDim B M) ≤
        (Module.depth B (IsLocalRing.maximalIdeal B) M : WithBot ℕ∞) := by
  rw [Module.supportDim_eq_of_ringEquiv e M hAlg,
    Module.depth_eq_depth_map_algebraMap hsurj (IsLocalRing.maximalIdeal A) M, hmax]

/-- On an affine open, Serre's condition `(Sₖ)` for the localization of the module of sections at
the prime of `x` is Serre's condition for the stalk at `x`: the germ map presents the stalk as
that localization. -/
private lemma affine_stalk_serre_iff [IsLocallyNoetherian X] (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] (U : X.Opens) (hU : IsAffineOpen U) (x : X)
    (hx : x ∈ U) (k : ℕ) :
    (min (k : WithBot ℕ∞) (Module.supportDim
          (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
          (LocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl Γ(F, U))) ≤
        (Module.depth (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
          (IsLocalRing.maximalIdeal
            (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal))
          (LocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl Γ(F, U)) :
            WithBot ℕ∞)) ↔
      min (k : WithBot ℕ∞)
          (Module.supportDim (X.presheaf.stalk x) (F.presheaf.stalk x)) ≤
        (Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (F.presheaf.stalk x) : WithBot ℕ∞) := by
  set p := (hU.primeIdealOf ⟨x, hx⟩).asIdeal with hp
  have hqc : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
  have hft : F.IsFiniteType := _root_.IsCoherent.toIsFiniteType F
  have hfinM : Module.Finite Γ(X, U) Γ(F, U) := moduleFinite_sections_on_affine F U hU
  let : Module Γ(X, U) (F.presheaf.stalk x) := affineStalkModule F U x hx
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  let : IsLocalization.AtPrime (X.presheaf.stalk x) p := hU.isLocalization_stalk ⟨x, hx⟩
  let : IsLocalRing (X.presheaf.stalk x) := IsLocalization.AtPrime.isLocalRing _ p
  let e : Localization.AtPrime p ≃ₐ[Γ(X, U)] X.presheaf.stalk x :=
    IsLocalization.algEquiv p.primeCompl _ _
  let : Algebra (Localization.AtPrime p) (X.presheaf.stalk x) := e.toAlgHom.toAlgebra
  let : Module (Localization.AtPrime p) (F.presheaf.stalk x) :=
    Module.compHom _ (algebraMap (Localization.AtPrime p) (X.presheaf.stalk x))
  let : IsScalarTower (Localization.AtPrime p) (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hcomp (r : Γ(X, U)) :
      algebraMap (Localization.AtPrime p) (X.presheaf.stalk x)
          (algebraMap Γ(X, U) (Localization.AtPrime p) r) =
        algebraMap Γ(X, U) (X.presheaf.stalk x) r := by
    show e (algebraMap Γ(X, U) (Localization.AtPrime p) r) = _
    exact e.commutes r
  let : IsScalarTower Γ(X, U) (Localization.AtPrime p) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun r t => by
      show algebraMap (Localization.AtPrime p) (X.presheaf.stalk x)
          (algebraMap Γ(X, U) (Localization.AtPrime p) r) * t =
        algebraMap Γ(X, U) (X.presheaf.stalk x) r * t
      rw [hcomp]
  let : IsScalarTower Γ(X, U) (Localization.AtPrime p) (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun r n => by
      show algebraMap (Localization.AtPrime p) (X.presheaf.stalk x)
          (algebraMap Γ(X, U) (Localization.AtPrime p) r) • n =
        algebraMap Γ(X, U) (X.presheaf.stalk x) r • n
      rw [hcomp]
  have hloc : IsLocalizedModule p.primeCompl (affineGerm F U x hx) :=
    affineGerm_isLocalized F U hU x hx
  let eM : LocalizedModule p.primeCompl Γ(F, U) ≃ₗ[Γ(X, U)] F.presheaf.stalk x :=
    IsLocalizedModule.linearEquiv p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl Γ(F, U)) (affineGerm F U x hx)
  let eM' : LocalizedModule p.primeCompl Γ(F, U) ≃ₗ[Localization.AtPrime p]
      F.presheaf.stalk x :=
    eM.extendScalarsOfIsLocalization p.primeCompl (Localization.AtPrime p)
  have hdepth : Module.depth (Localization.AtPrime p) (IsLocalRing.maximalIdeal _)
      (LocalizedModule p.primeCompl Γ(F, U)) =
      Module.depth (Localization.AtPrime p) (IsLocalRing.maximalIdeal _)
        (F.presheaf.stalk x) :=
    Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal _) eM'
  have hdim : Module.supportDim (Localization.AtPrime p)
      (LocalizedModule p.primeCompl Γ(F, U)) =
      Module.supportDim (Localization.AtPrime p) (F.presheaf.stalk x) :=
    Module.supportDim_eq_of_equiv eM'
  have halg : algebraMap (Localization.AtPrime p) (X.presheaf.stalk x) = e.toRingHom := rfl
  have hmax : Ideal.map (algebraMap (Localization.AtPrime p) (X.presheaf.stalk x))
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    IsLocalRing.map_ringEquiv_maximalIdeal e.toRingEquiv
  have hsurj : Function.Surjective
      (algebraMap (Localization.AtPrime p) (X.presheaf.stalk x)) := e.surjective
  have hfinS : Module.Finite (Localization.AtPrime p) (F.presheaf.stalk x) :=
    Module.Finite.of_surjective eM'.toLinearMap eM'.surjective
  have hfinT : Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    Module.Finite.of_surjective
      ({ toFun := id
         map_smul' := fun _ _ => rfl
         map_add' := fun _ _ => rfl } :
        F.presheaf.stalk x →ₛₗ[e.toRingHom] F.presheaf.stalk x) fun n => ⟨n, rfl⟩
  calc
    min (k : WithBot ℕ∞) (Module.supportDim (Localization.AtPrime p)
          (LocalizedModule p.primeCompl Γ(F, U))) ≤
        (Module.depth (Localization.AtPrime p) (IsLocalRing.maximalIdeal _)
          (LocalizedModule p.primeCompl Γ(F, U)) : WithBot ℕ∞) ↔
      min (k : WithBot ℕ∞)
          (Module.supportDim (Localization.AtPrime p) (F.presheaf.stalk x)) ≤
        (Module.depth (Localization.AtPrime p) (IsLocalRing.maximalIdeal _)
          (F.presheaf.stalk x) : WithBot ℕ∞) := by rw [hdim, hdepth]
    _ ↔ _ := module_serreSk_congr_of_ringEquiv e.toRingEquiv (F.presheaf.stalk x) hsurj halg
      hmax k

/-- Passage from the `WithBot ℕ∞`-valued form of Serre's inequality, in which the empty support
has dimension `⊥`, to the `ℕ∞`-valued form in which it is truncated to `0`. -/
private lemma min_unbotD_le_of_min_le {k : ℕ} {sd : WithBot ℕ∞} {dp : ℕ∞}
    (h : min (k : WithBot ℕ∞) sd ≤ (dp : WithBot ℕ∞)) :
    min (k : ℕ∞) (sd.unbotD 0) ≤ dp := by
  cases sd with
  | bot => simp
  | coe d =>
    rw [WithBot.unbotD_coe]
    refine WithBot.coe_le_coe.mp ?_
    rw [WithBot.coe_min]
    simpa using h

/-- **Serre's condition is affine-local.**  If a coherent module on a locally Noetherian scheme
satisfies `(Sₖ)`, then its module of sections over an affine open satisfies `(Sₖ)`. -/
@[ega "IV 5.7.2" "special case"]
private lemma propertySkModule_sections_of_sheafHasPropertySk [IsLocallyNoetherian X]
    (F : X.Modules) [_root_.SheafOfModules.IsCoherent F] (k : ℕ)
    (hF : SheafHasPropertySk X F k) (U : X.Opens) (hU : IsAffineOpen U)
    [IsNoetherianRing Γ(X, U)] [Module.Finite Γ(X, U) Γ(F, U)] :
    PropertySkModule Γ(X, U) Γ(F, U) k := by
  intro q hq
  let y : PrimeSpectrum Γ(X, U) := ⟨q, hq⟩
  have hyU : hU.fromSpec y ∈ U := (hU.isoSpec.inv y).2
  have hyEq : hU.primeIdealOf ⟨hU.fromSpec y, hyU⟩ = y :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf ⟨hU.fromSpec y, hyU⟩)
  have hpoint := min_supportDim_le_depth_of_sheafHasPropertySk F k hF (hU.fromSpec y)
  have hlocal := (affine_stalk_serre_iff F U hU (hU.fromSpec y) hyU k).mpr hpoint
  rw [hyEq] at hlocal
  have hlocal' : min (k : WithBot ℕ∞) (Module.supportDim (Localization.AtPrime q)
        (LocalizedModule.AtPrime q Γ(F, U))) ≤
      (Module.depth (Localization.AtPrime q)
        (IsLocalRing.maximalIdeal (Localization.AtPrime q))
        (LocalizedModule.AtPrime q Γ(F, U)) : WithBot ℕ∞) := hlocal
  have hdimEq : moduleSupportDim (Localization.AtPrime q)
      (LocalizedModule.AtPrime q Γ(F, U)) =
      Module.supportDim (Localization.AtPrime q) (LocalizedModule.AtPrime q Γ(F, U)) :=
    moduleSupportDim_eq_Module_supportDim
  by_cases hn : Nontrivial (LocalizedModule.AtPrime q Γ(F, U))
  · have hdepthEq : moduleDepth (Localization.AtPrime q)
        (LocalizedModule.AtPrime q Γ(F, U)) =
        Module.depth (Localization.AtPrime q)
          (IsLocalRing.maximalIdeal (Localization.AtPrime q))
          (LocalizedModule.AtPrime q Γ(F, U)) := moduleDepth_eq_depth
    rw [hdimEq, hdepthEq]
    exact min_unbotD_le_of_min_le hlocal'
  · have : Subsingleton (LocalizedModule.AtPrime q Γ(F, U)) :=
      not_nontrivial_iff_subsingleton.mp hn
    rw [hdimEq, Module.supportDim_eq_bot_of_subsingleton]
    simp

/-! ### Codimension of a point and the depth of its local ring -/

/-- **[Stacks, Tag 02IZ].**  The Krull dimension of the local ring at a point is the
codimension of the closure of that point. -/
private lemma ringKrullDim_stalk_eq_codimension (X : Scheme.{u}) (x : X) :
    ringKrullDim (X.presheaf.stalk x) =
      (codimension (IrreducibleCloseds.closureSingleton x) : WithBot ℕ∞) := by
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight,
    coheight_eq_codimension_closureSingleton]

/-- On a locally Noetherian normal scheme the local ring at a point whose closure has
codimension at least two has depth at least two. -/
private lemma two_le_depth_stalk_of_two_le_codimension [IsLocallyNoetherian X] [IsNormal X]
    (x : X) (hx : (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x)) :
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) :=
  two_le_depth_stalk_of_two_le_coheight x
    (by rwa [coheight_eq_codimension_closureSingleton])

/-! ### The free locus -/

/-- The set of points having an open neighbourhood on which every stalk of `F` is a free
module over the corresponding local ring. -/
private def freeLocus (F : X.Modules) : Set X :=
  {x | ∃ W : X.Opens, x ∈ W ∧
    ∀ y : X, y ∈ W → Module.Free (X.presheaf.stalk y) (F.presheaf.stalk y)}

/-- The free locus is open. -/
private lemma isOpen_freeLocus (F : X.Modules) : IsOpen (freeLocus F) := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨W, hxW, hW⟩
  exact ⟨W, fun y hy => ⟨W, hy, hW⟩, W.isOpen, hxW⟩

/-- At a point of the free locus the stalk is free. -/
private lemma free_stalk_of_mem_freeLocus (F : X.Modules) {x : X} (hx : x ∈ freeLocus F) :
    Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x) :=
  hx.elim fun _ h => h.2 x h.1

/-- **[Stacks, Tag 0B8J].**  A coherent module with free stalk at `x` is free on a
neighbourhood of `x`, so `x` lies in the free locus. -/
private lemma mem_freeLocus_of_free_stalk [IsLocallyNoetherian X] (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] (x : X)
    (hfree : Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x)) :
    x ∈ freeLocus F := by
  have : F.IsFinitePresentation := _root_.isFinitePresentation_of_isCoherent F
  have : Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent F x
  let b := Module.Free.chooseBasis (X.presheaf.stalk x) (F.presheaf.stalk x)
  have : Finite (Module.Free.ChooseBasisIndex (X.presheaf.stalk x) (F.presheaf.stalk x)) :=
    Module.Finite.finite_basis b
  obtain ⟨W, hxW, ⟨e⟩⟩ := Stacks.StalkFiniteType.exists_over_iso_free_of_stalk_basis F x b
  refine ⟨W, hxW, fun y hy => ?_⟩
  let G : (F.over W).GeneratingSections :=
    { I := Module.Free.ChooseBasisIndex (X.presheaf.stalk x) (F.presheaf.stalk x)
      s := (F.over W).freeHomEquiv e.inv
      epi := by
        rw [Equiv.symm_apply_apply]
        infer_instance }
  have : IsIso G.π := by
    show IsIso ((F.over W).freeHomEquiv.symm ((F.over W).freeHomEquiv e.inv))
    rw [Equiv.symm_apply_apply]
    infer_instance
  obtain ⟨ey⟩ := Stacks.StalkFreeBridge.nonempty_stalkLinearEquiv W F G hy
  exact Module.Free.of_equiv ey.symm

/-- **[Stacks, Tag 0AUW].**  A finite reflexive module over a regular local ring of dimension
at most one is free. -/
private lemma free_of_isReflexive_of_ringKrullDim_le_one {R M : Type*} [CommRing R]
    [IsRegularLocalRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsReflexive R M] (hdim : ringKrullDim R ≤ 1) : Module.Free R M := by
  have : IsDomain R := IsRegularLocalRing.isDomain R
  have htf : Module.IsTorsionFree R M :=
    (isTorsionFree_of_isReflexive_and_dualEval_isTorsion_and_injective_iff
      (R := R) (M := M)).1 inferInstance
  by_cases hField : IsField R
  · let : Field R := hField.toField
    infer_instance
  · have hone : (1 : WithBot ℕ∞) ≤ ringKrullDim R := by
      show (1 : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum R)
      rw [Order.one_le_krullDim_iff]
      refine ⟨⟨⊥, Ideal.isPrime_bot⟩,
        ⟨IsLocalRing.maximalIdeal R, (IsLocalRing.maximalIdeal.isMaximal R).isPrime⟩, ?_⟩
      show (⊥ : Ideal R) < IsLocalRing.maximalIdeal R
      exact bot_lt_iff_ne_bot.mpr fun h =>
        hField (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)
    have hdvr := ((isDiscreteValuationRing_tfae R).out 3 1).mp
      (⟨inferInstance, le_antisymm hdim hone⟩ :
        IsRegularLocalRing R ∧ ringKrullDim R = 1)
    obtain ⟨_, hDVR⟩ := hdvr
    let : IsDiscreteValuationRing R := hDVR
    let : IsPrincipalIdealRing R := IsDiscreteValuationRing.toIsPrincipalIdealRing
    exact Module.free_iff_isTorsionFree.mpr htf

/-! ### The criterion -/

/-- Let `X` be an integral locally Noetherian normal scheme and let `F` be a coherent
`𝒪_X`-module. The following are equivalent:

1. `F` is reflexive;
2. `F` is torsion free and satisfies Serre's condition `(S₂)`;
3. there is an open subscheme `j : U → X` whose complement has codimension at least two at
   every point, such that `j^*F` is finite locally free and the canonical map `F → j_*j^*F` is
   an isomorphism. -/
@[stacks 0AY6]
theorem isReflexive_isTorsionFree_propertyS2_extension_tfae (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] :
    List.TFAE [
      IsReflexive F,
      IsTorsionFree F ∧ SheafHasPropertySk X F 2,
      ∃ U : X.Opens,
        (∀ x : X, x ∉ U →
          (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x)) ∧
        SheafOfModules.IsFiniteLocallyFree (F.restrict U.ι) ∧
        IsIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F)] := by
  have hqc : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
  have hft : F.IsFiniteType := _root_.IsCoherent.toIsFiniteType F
  have hfp : F.IsFinitePresentation := _root_.isFinitePresentation_of_isCoherent F
  have hdfp : (dualSheaf F).IsFinitePresentation := isFinitePresentation_dualSheaf F
  have hres (U : X.Opens) : IsLocallyNoetherian U.toScheme ∧
      _root_.SheafOfModules.IsCoherent (F.restrict U.ι) ∧
      (F.restrict U.ι).IsFinitePresentation := by
    have hUN := isLocallyNoetherian_of_isOpenImmersion U.ι
    have hGcoh := isCoherent_restrict U F
    exact ⟨hUN, hGcoh, _root_.isFinitePresentation_of_isCoherent _⟩
  tfae_have 1 → 2 := fun hF =>
    ⟨isTorsionFree_of_isReflexive_of_isLocallyNoetherian F hF,
      sheafHasPropertySk_two_of_isReflexive F hF
        ((isNormal_iff_hasPropertySk_two_and_isRegularInCodimension_one X).mp
          inferInstance).1⟩
  tfae_have 2 → 1 := by
    rintro ⟨hTF, hS2⟩
    refine (isReflexive_iff_sections_isReflexive X F).2 fun U hU => ?_
    by_cases hne : Nonempty U
    · have : IsDomain Γ(X, U) := IsIntegral.component_integral U
      have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
      have : IsIntegrallyClosed Γ(X, U) :=
        (isNormal_iff_forall_affineOpen_normal X).mp inferInstance ⟨U, hU⟩ hne
      have : Module.Finite Γ(X, U) Γ(F, U) := moduleFinite_sections_on_affine F U hU
      have hinput : Module.IsTorsionFree Γ(X, U) Γ(F, U) ∧
          PropertySkModule Γ(X, U) Γ(F, U) 2 :=
        ⟨(isTorsionFree_iff_forall_isAffineOpen F).mp hTF U hU,
          propertySkModule_sections_of_sheafHasPropertySk F 2 hS2 U hU⟩
      exact ((isReflexive_isTorsionFree_propertyS2_intersection_tfae
        (R := Γ(X, U)) (M := Γ(F, U))).out 2 1).mp hinput
    · have : Subsingleton Γ(F, U) := ⟨fun s t =>
        TopCat.Presheaf.IsSheaf.section_ext F.isSheaf fun z hz => (hne ⟨⟨z, hz⟩⟩).elim⟩
      have : Module.Finite Γ(X, U) Γ(F, U) := moduleFinite_sections_on_affine F U hU
      have : Module.Free Γ(X, U) Γ(F, U) := Module.Free.of_subsingleton _ _
      infer_instance
  tfae_have 1 → 3 := by
    intro hF
    have hcodim : ∀ x : X, x ∉ (⟨freeLocus F, isOpen_freeLocus F⟩ : X.Opens) →
        (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x) := by
      intro x hx
      by_contra hnot
      have hdim : ringKrullDim (X.presheaf.stalk x) ≤ (1 : WithBot ℕ∞) := by
        refine withBot_lt_two_le_one ?_
        rw [ringKrullDim_stalk_eq_codimension]
        by_contra hge
        exact hnot (WithBot.coe_le_coe.mp (le_of_not_gt hge))
      have : IsRegularLocalRing (X.presheaf.stalk x) :=
        ((isNormal_iff_hasPropertySk_two_and_isRegularInCodimension_one X).mp
          inferInstance).2 x hdim
      have : Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) :=
        AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent F x
      have : Module.IsReflexive (X.presheaf.stalk x) (F.presheaf.stalk x) :=
        isReflexive_stalk_of_isReflexive F hF x
      exact hx (mem_freeLocus_of_free_stalk F x
        (free_of_isReflexive_of_ringKrullDim_le_one hdim))
    set U : X.Opens := ⟨freeLocus F, isOpen_freeLocus F⟩ with hUdef
    obtain ⟨hUN, hGcoh, hGfp⟩ := hres U
    refine ⟨U, hcodim, ?_, ?_⟩
    · have htfae := (Stacks.FiniteLocallyFree.ModuleTFAE.finiteLocallyFree_tfae
        (F.restrict U.ι)).out 2 4
      refine htfae.mp ⟨hGfp, fun y => ?_⟩
      have h1 : RingHomInvPair
          (openImmersionStalkRingEquiv U.ι y :
            U.toScheme.presheaf.stalk y →+* X.presheaf.stalk (U.ι y))
          ((openImmersionStalkRingEquiv U.ι y).symm :
            X.presheaf.stalk (U.ι y) →+* U.toScheme.presheaf.stalk y) :=
        RingHomInvPair.of_ringEquiv _
      have h2 : RingHomInvPair
          ((openImmersionStalkRingEquiv U.ι y).symm :
            X.presheaf.stalk (U.ι y) →+* U.toScheme.presheaf.stalk y)
          (openImmersionStalkRingEquiv U.ι y :
            U.toScheme.presheaf.stalk y →+* X.presheaf.stalk (U.ι y)) :=
        RingHomInvPair.of_ringEquiv_symm _
      have : Module.Free (X.presheaf.stalk (U.ι y)) (F.presheaf.stalk (U.ι y)) :=
        free_stalk_of_mem_freeLocus F y.2
      exact Module.Free.of_equiv (restrictStalkSemilinearEquiv U.ι F y).symm
    · exact Stacks.FundamentalGroup.DepthCoherence.isIso_unit_of_isReflexive U F hF
        fun x hx => two_le_depth_stalk_of_two_le_codimension x (hcodim x hx)
  tfae_have 3 → 1 := by
    rintro ⟨U, hcodim, hflf, hunit⟩
    have hdepth : ∀ x : X, x ∉ (U : Set X) →
        (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) :=
      fun x hx => two_le_depth_stalk_of_two_le_codimension x (hcodim x hx)
    obtain ⟨hUN, hGcoh, hGfp⟩ := hres U
    have hGdfp : (dualSheaf (F.restrict U.ι)).IsFinitePresentation :=
      isFinitePresentation_dualSheaf _
    have htfae := (Stacks.FiniteLocallyFree.ModuleTFAE.finiteLocallyFree_tfae
      (F.restrict U.ι)).out 4 2
    have hGstalkFree := (htfae.mp hflf).2
    have hGrefl : IsReflexive (F.restrict U.ι) := by
      refine isReflexive_of_forall_isReflexive_stalk _ fun y => ?_
      have : Module.Free (U.toScheme.presheaf.stalk y) ((F.restrict U.ι).presheaf.stalk y) :=
        hGstalkFree y
      have : Module.Finite (U.toScheme.presheaf.stalk y)
          ((F.restrict U.ι).presheaf.stalk y) :=
        AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent (F.restrict U.ι) y
      infer_instance
    obtain ⟨hPcoh, hPrefl⟩ :=
      isCoherent_and_isReflexive_pushforward X U hdepth (F.restrict U.ι) hGcoh hGrefl
    have : _root_.SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward U.ι).obj (F.restrict U.ι)) := hPcoh
    let eF : F ≅ (Scheme.Modules.pushforward U.ι).obj (F.restrict U.ι) :=
      asIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F) ≪≫
        (Scheme.Modules.pushforward U.ι).mapIso
          ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app F).symm
    exact Stacks.AlgebraicGeometry.ReflexiveModules.isReflexive_of_iso eF.symm hPrefl
  tfae_finish

end AlgebraicGeometry

end

