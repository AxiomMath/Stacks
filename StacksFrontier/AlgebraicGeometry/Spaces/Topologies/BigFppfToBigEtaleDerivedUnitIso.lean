module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToBigEtaleDerivedUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationConvergenceUniformBoundUnconditional
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedLimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationTowerConvergenceUnconditional
public import StacksFrontier.AlgebraicGeometry.Cohomology.TruncationTowerAnyModel
public import StacksFrontier.Algebra.Homology.DerivedCategory.AdjunctionUnitTruncations
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.ModuleHigherVanishing
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived

/-!
# When the derived unit of the fppf-to-big-étale comparison is an isomorphism

Let `X` be an algebraic space, `ε_X : ((Spaces/X)_fppf, 𝒪) ⟶ ((Spaces/X)_étale, 𝒪)` the
change-of-topology morphism, and `B` a family of objects of the big fppf site of `X` which covers
every object for the étale topology. Call a module `𝓖` on `(Spaces/X)_étale` *good* if the unit
`𝓖 ⟶ ε_{X,*}ε_X^*𝓖` is an isomorphism and `𝓖`, resp. `ε_X^*𝓖`, has no higher cohomology on the
members of `B`. Then the derived unit `M ⟶ Rε_{X,*}Lε_X^*M` is an isomorphism at every object `M`
all of whose cohomology sheaves are good.

This is the formal half of the proof of Stacks 0DGR: there `M = Lπ_X^*K` and the goodness of the
cohomology sheaves is Stacks 0DGQ, read étale locally on `X`.

## Main definitions

* `AlgebraicGeometry.BigFppfSpaceSite.FppfToBigEtaleGood`: the goodness condition.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.isIso_fppfToBigEtale_derivedAdjunction_unit_app`.

## Implementation notes

The argument is `Stacks.DerivedCategory.AdjunctionUnitTruncations.isIso_unit_app`: `Lε_X^*` is
t-exact, `Rε_{X,*}` preserves derived limits, the unit is invertible at a good module in degree
zero (Stacks 0DGP for the coarsening `ε_X`), and objects with good cohomology, and their images
under `Lε_X^*`, are derived limits of their truncation towers (Stacks 0D6P).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackOnRingedTopoi

universe u

namespace AlgebraicGeometry.BigFppfSpaceSite

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

attribute [local instance 5000] SheafOfModules.instAbelian

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : T.schemeSite = E.fppfSite) (X : T.Spaces)

/-- The change-of-topology morphism `ε_X`, as a morphism of ringed topoi at the universe of the
sites. -/
abbrev epsilonHom :
    RingedToposSiteHom (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (bigFppfRingedSite T X))
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (E.bigEtaleRingedSite (etaleSpace T E h X))) :=
  (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom

/-- Sheaves of modules on the big étale ringed site of an algebraic space have enough
injectives. -/
theorem _root_.AlgebraicGeometry.BigEtaleSpaceSite.enoughInjectives_modules (X' : E.Spaces) :
    EnoughInjectives (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (E.bigEtaleRingedSite X')).O)) :=
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{u + 1, u + 1, u + 1, u + 1} _

attribute [local instance] BigEtaleSpaceSite.enoughInjectives_modules
  enoughInjectives_bigFppfModules

/-- **Good modules on the big étale site of `X`**, relative to a family `B` of objects of the big
fppf site of `X`: the unit `𝓖 ⟶ ε_{X,*}ε_X^*𝓖` is an isomorphism, and `𝓖`, resp. `ε_X^*𝓖`, has no
higher cohomology on the members of `B`. -/
def FppfToBigEtaleGood (B : Set (Over X)) :
    ObjectProperty (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
        (E.bigEtaleRingedSite (etaleSpace T E h X))).O)) :=
  fun G ↦
    IsIso ((epsilonHom T E h X).pullbackPushforwardAdjunctionTopos.unit.app G) ∧
    (∀ V : Over (etaleSpace T E h X), B ((fppfToBigEtaleRingedHom T E h X).u.obj V) →
      ∀ p : ℕ, 0 < p → IsZero (Stacks.Cohomology.moduleCohomology.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
            (E.bigEtaleRingedSite (etaleSpace T E h X))).O) V p G)) ∧
    (∀ V : Over X, B V → ∀ p : ℕ, 0 < p →
      IsZero (Stacks.Cohomology.moduleCohomology.{u + 1, u + 1, u + 1, u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (bigFppfRingedSite T X)).O) V p
      ((epsilonHom T E h X).pullbackTopos.obj G)))

/-- The good modules form a property closed under isomorphisms. -/
instance (B : Set (Over X)) : (FppfToBigEtaleGood T E h X B).IsClosedUnderIsomorphisms where
  of_iso {G G'} e hG := by
    obtain ⟨h₁, h₂, h₃⟩ := hG
    refine ⟨?_, fun V hV p hp ↦
        Stacks.Cohomology.isZero_moduleCohomology_of_iso.{u + 1, u + 1, u + 1, u + 1} _ V p e.symm
          (h₂ V hV p hp),
      fun V hV p hp ↦ Stacks.Cohomology.isZero_moduleCohomology_of_iso.{u + 1, u + 1, u + 1, u + 1}
        _ V p ((epsilonHom T E h X).pullbackTopos.mapIso e).symm (h₃ V hV p hp)⟩
    exact (NatTrans.isIso_app_iff_of_iso _ e).1 h₁

/-- A zero module has no higher cohomology. -/
theorem isZero_moduleCohomology_of_isZero {C : Type*} [Category C] {J : GrothendieckTopology C}
    {O : Sheaf J RingCat} [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
    [EnoughInjectives (SheafOfModules O)] {F : SheafOfModules O} (hF : IsZero F) (U : C) (p : ℕ)
    (hp : 0 < p) : IsZero (Stacks.Cohomology.moduleCohomology O U p F) := by
  have hEv : (SheafOfModules.evaluation O (.op U)).Additive := by
    dsimp [SheafOfModules.evaluation]; infer_instance
  have := hF.injective
  obtain ⟨p, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  unfold Stacks.Cohomology.moduleCohomology
  exact Functor.isZero_rightDerived_obj_injective_succ (SheafOfModules.evaluation O (.op U)) p F

/-- The derived category of modules on the big étale site of `X` has countable products. -/
instance hasProductsOfShape_derivedCategory_bigEtaleModules :
    HasProductsOfShape ℕ (DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
          (E.bigEtaleRingedSite (etaleSpace T E h X))).O))) :=
  Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules.{
    _, u + 1, u + 1, u + 1, u + 1} _

/-- The derived category of modules on the big fppf site of `X` has countable products. -/
instance hasProductsOfShape_derivedCategory_bigFppfModules :
    HasProductsOfShape ℕ (DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (bigFppfRingedSite T X)).O))) :=
  Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules.{
    _, u + 1, u + 1, u + 1, u + 1} _

open Stacks.DerivedCategory.AdjunctionUnitTruncations in
/-- **An object of `D((Spaces/X)_étale)` with good cohomology is the derived limit of its
truncations** (Stacks 0D6P with the family `B`). -/
theorem isDerivedLimit_truncGETower_of_homologyIn_good (B : Set (Over X))
    (hB : ∀ U : Over (etaleSpace T E h X), ∃ 𝒰 : PreZeroHypercover.{u + 1} U,
      𝒰.sieve₀ ∈ E.bigEtaleTopology (etaleSpace T E h X) U ∧
        ∀ i, B ((fppfToBigEtaleRingedHom T E h X).u.obj (𝒰.X i)))
    (M : DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
        (E.bigEtaleRingedSite (etaleSpace T E h X))).O)))
    (hM : HomologyIn (FppfToBigEtaleGood T E h X B) M) :
    IsDerivedLimit (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
          (E.bigEtaleRingedSite (etaleSpace T E h X))).O)) M) M :=
  isDerivedLimit_truncGETower_of_forall_isIso M fun L c q hL hc ↦
    Stacks.Cohomology.UniformBound.isIso_to_isDerivedLimit_truncGETower_of_vanishing_uniform.{
      u + 1, u + 1, u + 1, u + 1}
      _ M 0 le_rfl {V | B ((fppfToBigEtaleRingedHom T E h X).u.obj V)} hB
      (fun V hV p hp q _ ↦ (hM q).elim (fun hG ↦ hG.2.1 V hV p (by exact_mod_cast hp))
        (fun hZ ↦ isZero_moduleCohomology_of_isZero hZ V p (by exact_mod_cast hp))) L c q hL hc

open Stacks.DerivedCategory.AdjunctionUnitTruncations in
/-- **`Lε_X^* M` is the derived limit of its truncations** when `M` has good cohomology
(Stacks 0D6P on the big fppf site with the family `B`). -/
theorem isDerivedLimit_truncGETower_derivedPullback_of_homologyIn_good (B : Set (Over X))
    (hB : ∀ U : Over X, ∃ 𝒰 : PreZeroHypercover.{u + 1} U,
      𝒰.sieve₀ ∈ BigFppfSpaceOver.topology T X U ∧ ∀ i, B (𝒰.X i))
    (M : DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
        (E.bigEtaleRingedSite (etaleSpace T E h X))).O)))
    (hM : HomologyIn (FppfToBigEtaleGood T E h X B) M) :
    IsDerivedLimit (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (bigFppfRingedSite T X)).O))
        ((derivedPullback (epsilonHom T E h X)).obj M))
      ((derivedPullback (epsilonHom T E h X)).obj M) :=
  isDerivedLimit_truncGETower_of_forall_isIso _ fun L c q hL hc ↦
    Stacks.Cohomology.UniformBound.isIso_to_isDerivedLimit_truncGETower_of_vanishing_uniform.{
      u + 1, u + 1, u + 1, u + 1}
      _ _ 0 le_rfl B hB
      (fun V hV p hp q _ ↦
        Stacks.Cohomology.isZero_moduleCohomology_of_iso.{u + 1, u + 1, u + 1, u + 1} _ V p
        (Stacks.Cohomology.CohomologicalDescent.derivedPullbackHomologyObjIso
          (epsilonHom T E h X) M q)
        ((hM q).elim (fun hG ↦ hG.2.2 V hV p (by exact_mod_cast hp))
          (fun hZ ↦ isZero_moduleCohomology_of_isZero
            ((epsilonHom T E h X).pullbackTopos.map_isZero hZ) V p (by exact_mod_cast hp))))
      L c q hL hc

/-- **The higher direct images along `ε_X` of `ε_X^*𝓖` vanish for a good module `𝓖`**: the
fppf cohomology of `ε_X^*𝓖` vanishes on the members of `B`, which cover every object for the
étale topology. -/
theorem isZero_rightDerived_fppfToBigEtale_pushforward_pullback_of_good (B : Set (Over X))
    (hB : ∀ U : Over (etaleSpace T E h X), ∃ 𝒰 : PreZeroHypercover.{u + 1} U,
      𝒰.sieve₀ ∈ E.bigEtaleTopology (etaleSpace T E h X) U ∧
        ∀ i, B ((fppfToBigEtaleRingedHom T E h X).u.obj (𝒰.X i)))
    (G : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (E.bigEtaleRingedSite (etaleSpace T E h X))).O))
    (hG : FppfToBigEtaleGood T E h X B G) (p : ℕ) (hp : 0 < p) :
    IsZero ((((epsilonHom T E h X).pushforwardTopos).rightDerived p).obj
      ((epsilonHom T E h X).pullbackTopos.obj G)) := by
  refine Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve.{
    u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
    (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.u _ _
    (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.fSharpRing p _ (fun V ↦ ?_)
  obtain ⟨𝒰, h𝒰, hB𝒰⟩ := hB V
  refine ⟨fun W _ ↦ B ((fppfToBigEtaleRingedHom T E h X).u.obj W),
    E.bigEtaleTopology (etaleSpace T E h X) |>.superset_covering ?_ h𝒰,
    fun W g hW ↦ hG.2.2 _ hW p hp⟩
  rw [PreZeroHypercover.sieve₀, Sieve.generate_le_iff]
  rintro W g ⟨i⟩
  exact Sieve.le_generate _ _ _ (hB𝒰 i)

open Stacks.DerivedCategory.AdjunctionUnitTruncations
  Stacks.Cohomology.DerivedPushforwardOnRingedTopoi in
/-- **Stacks 0DGR, the formal half: the derived unit of `ε_X` is invertible at every object with
good cohomology.** Let `B` be a family of objects of `(Spaces/X)_fppf` covering every object for
the fppf topology and, through `ε_X`, every object of `(Spaces/X)_étale` for the étale topology.
Then `M ⟶ Rε_{X,*}Lε_X^*M` is an isomorphism for every `M` all of whose cohomology sheaves are
good for `B` or zero. -/
theorem isIso_fppfToBigEtale_derivedAdjunction_unit_app (B : Set (Over X))
    (hBet : ∀ U : Over (etaleSpace T E h X), ∃ 𝒰 : PreZeroHypercover.{u + 1} U,
      𝒰.sieve₀ ∈ E.bigEtaleTopology (etaleSpace T E h X) U ∧
        ∀ i, B ((fppfToBigEtaleRingedHom T E h X).u.obj (𝒰.X i)))
    (hBfppf : ∀ U : Over X, ∃ 𝒰 : PreZeroHypercover.{u + 1} U,
      𝒰.sieve₀ ∈ BigFppfSpaceOver.topology T X U ∧ ∀ i, B (𝒰.X i))
    (M : DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
        (E.bigEtaleRingedSite (etaleSpace T E h X))).O)))
    (hM : HomologyIn (FppfToBigEtaleGood T E h X B) M) :
    IsIso ((Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedAdjunction (epsilonHom T E h X)
      (fppfToBigEtaleRingedHom T E h X).isMorphismOfSites).unit.app M) := by
  let adj := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedAdjunction (epsilonHom T E h X)
    (fppfToBigEtaleRingedHom T E h X).isMorphismOfSites
  let := Stacks.Sheaves.RingedToposDerivedPullback.derivedPullback_commShift (epsilonHom T E h X)
  have : (derivedPullback (epsilonHom T E h X)).IsTriangulated :=
    Stacks.Cohomology.DerivedPullbackOnRingedTopoi.isTriangulated_derivedPullback
      (epsilonHom T E h X) (fppfToBigEtaleRingedHom T E h X).isMorphismOfSites
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedPushforward.{u + 1} (epsilonHom T E h X))
    (derivedPushforwardUnit.{u + 1} (epsilonHom T E h X))
    (HomotopyCategory.quasiIso (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (bigFppfRingedSite T X)).O))
      (ComplexShape.up ℤ)) ℤ
  have _ := SheafOfModules.isGrothendieckAbelianU.{u + 1, u + 1, u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (bigFppfRingedSite T X)).O)
  have : (derivedPushforward.{u + 1} (epsilonHom T E h X)).IsTriangulated :=
    Stacks.Injectives.rightDerivedFunctor_isTriangulated (epsilonHom T E h X).pushforwardTopos
      (derivedPushforward.{u + 1} (epsilonHom T E h X))
      (derivedPushforwardUnit.{u + 1} (epsilonHom T E h X))
  have hη0 : ∀ G, FppfToBigEtaleGood T E h X B G →
      IsIso (adj.unit.app ((DerivedCategory.singleFunctor _ 0).obj G)) := by
    intro G hG
    refine (isIso_unit_app_iff_of_adjunction
      (derivedPullbackPushforwardAdjunctionOfExact (epsilonHom T E h X)) adj _).1
      (isIso_derivedUnit_app_singleFunctor_obj_of_isZero (epsilonHom T E h X) G hG.1
        (fun p hp ↦ ?_))
    refine IsZero.of_iso (isZero_rightDerived_fppfToBigEtale_pushforward_pullback_of_good
      T E h X B hBet G hG p hp) ?_
    refine (DerivedCategory.homologyFunctor _ (p : ℤ)).mapIso
      ((derivedPushforward.{u + 1} (epsilonHom T E h X)).mapIso
        (Stacks.Cohomology.CohomologicalDescent.derivedPullbackSingleFunctorObjIso
          (epsilonHom T E h X) G)) ≪≫ ?_
    exact (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
      (epsilonHom T E h X).pushforwardTopos
      (derivedPushforward.{u + 1} (epsilonHom T E h X))
      (derivedPushforwardUnit.{u + 1} (epsilonHom T E h X))
      (fun K ↦ ⟨_, (Stacks.Injectives.kInjectiveResolutionInclusion _).app K,
        inferInstance, inferInstance⟩) p).app _
  refine isIso_unit_app adj (FppfToBigEtaleGood T E h X B) (fun G hG n ↦ ?_)
    (fun K n hK ↦ Stacks.Cohomology.CohomologicalDescent.isLE_derivedPullback_obj
      (epsilonHom T E h X) K n hK)
    (fun K n hK ↦ Stacks.Cohomology.CohomologicalDescent.isGE_derivedPullback_obj
      (epsilonHom T E h X) K n hK)
    (fun K hK ↦ isDerivedLimit_truncGETower_of_homologyIn_good T E h X B hBet K hK)
    (fun K hK ↦
      isDerivedLimit_truncGETower_derivedPullback_of_homologyIn_good T E h X B hBfppf K hK)
    M hM
  have := hη0 G hG
  exact isIso_unit_app_singleFunctor_obj adj G n

end AlgebraicGeometry.BigFppfSpaceSite

end
