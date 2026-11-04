module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.ProperSpecialization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.LocalAcyclicity.SmoothMorphisms
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionStalkCriterion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.TorsionCohomologySingle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.LocallyConstantCoefficientsUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.SmallEtaleConstantSheafPullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The specialization map of a smooth proper morphism

Let `f : X ⟶ S` be a smooth proper morphism of schemes and `F` a locally constant abelian sheaf
on `X_étale` whose stalks are torsion groups of order prime to the residue characteristics. Then
every specialization map `sp : (Rf_*F)_s ⟶ (Rf_*F)_t` is an isomorphism (Tag 0GKD).

## Main results

* `AlgebraicGeometry.isLocallyAcyclic_of_isUniversallyLocallyAcyclic`: a universally locally
  acyclic morphism is locally acyclic.
* `AlgebraicGeometry.isIso_specializationMap_of_smooth_of_isProper`: for `f` smooth and proper
  and `F` locally constant with torsion stalks of order prime to the residue characteristics,
  every specialization map of `Rf_*F` is an isomorphism, given the statements of Tags 095T and
  03Q9 and the inputs of the smooth base change theorem as hypotheses.

## References

* [Stacks Project, Tag 0GKD](https://stacks.math.columbia.edu/tag/0GKD)
* [Stacks Project, Tag 0GJQ](https://stacks.math.columbia.edu/tag/0GJQ)
* [Stacks Project, Tag 0GJR](https://stacks.math.columbia.edu/tag/0GJR)
* [Stacks Project, Tag 0GJW](https://stacks.math.columbia.edu/tag/0GJW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable (B : BigEtaleSite.{u})

/-- **A universally locally acyclic morphism is locally acyclic**, inside any big étale site `B`
containing `X` and `S`. -/
theorem isLocallyAcyclic_of_isUniversallyLocallyAcyclic {X S : Scheme.{u}} (hX : B.Contains X)
    (hS : B.Contains S) (f : X ⟶ S)
    (h : IsUniversallyLocallyAcyclic f) :
    IsLocallyAcyclic B hX hS f := by
  have hP : B.Contains (pullback f (𝟙 S)) := Scheme.size_pullback_lt _ _ hX hS
  let e : X ⟶ pullback f (𝟙 S) := pullback.lift (𝟙 X) f (by simp)
  have he : IsIso e := ⟨⟨pullback.fst f (𝟙 S), pullback.lift_fst _ _ _, by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp, pullback.condition,
        Category.comp_id]⟩⟩
  have sq : IsPullback e f (pullback.snd f (𝟙 S)) (𝟙 S) :=
    IsPullback.of_horiz_isIso ⟨by rw [pullback.lift_snd, Category.comp_id]⟩
  intro x n hn hcop
  have h₁ := h S (𝟙 S) B hP hS (x.map e) n hn hcop
  have h₂ := isLocallyAcyclicAt_of_isIntegralHom B hP hS hS hX sq
    (smallEtaleConstantZModComplex (pullback f (𝟙 S)) n) h₁
  let iso : (smallEtaleDerivedPullbackAb e).obj
      (smallEtaleConstantZModComplex (pullback f (𝟙 S)) n) ≅ smallEtaleConstantZModComplex X n :=
    ((smallEtalePullbackAb e).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        ((smallEtalePullbackAbConstantSheafIso e).app _)
  intro t
  exact (NatTrans.isIso_app_iff_of_iso _ iso).1 (h₂ t)

/-- **Specialization maps of a smooth proper morphism are isomorphisms.** Let `f : X ⟶ S` be a
morphism of schemes of a big étale site and `F` an abelian sheaf on `X_étale`. Assume

1. `f` is smooth and proper,
2. `F` is locally constant, and
3. for every geometric point `x` of `X` the stalk `F_x` is a torsion group all of whose elements
   have order prime to the characteristic of the residue field of `x`.

Then for every geometric point `s` of `S` and every geometric point `t` of `Spec 𝒪^{sh}_{S,s}`
the specialization map `sp : (Rf_*F)_s ⟶ (Rf_*F)_t` is an isomorphism; the stalk at `t` is taken
at its image in `S`, as the source does.

The hypotheses `h095T` and `h03Q9` are the statements of Stacks 095T and 03Q9, and `h0EYS`,
`h0EZR`, `h0EZS`, `h0F08`, `h03SC2`, `h03SC6`, `h0BMA` and `h0EYD` are the inputs of the smooth
base change theorem (Tag 0EYU). -/
@[sga "4 XVI 2.3" "special case"]
theorem isIso_specializationMap_of_smooth_of_isProper
    (h095T : ∀ ⦃X S : Scheme.{u}⦄ (f : X ⟶ S) [IsProper f],
      CohomologyCommutesWithBaseChange.{u, 0} f)
    (h03Q9 : DerivedPushforwardStalkFormula B)
    (h0EYS : SmoothBaseChange.FlatReducedFibresBaseChange.{u})
    (h0EZR : SmoothBaseChange.EtaleLocalHigherBaseChange.{u})
    (h0EZS : SmoothBaseChange.HigherBaseChangePaste.{u})
    (h0F08 : SmoothBaseChange.FirstFailureNormalization.{u})
    (h03SC2 : SmoothBaseChange.AffineCurveCohomologyVanishing.{u})
    (h03SC6 : SmoothBaseChange.CurveCohomologyAlgClosedInvariance.{u})
    (h0BMA : PurityAtRegularLocalRings.{u})
    (h0EYD : ∀ S : Stacks.FundamentalGroup.CodimensionOnePullbackSetup.{u},
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne S.U.ι S.f →
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (pullback.fst S.g S.U.ι)
        S.pulledBackCover)
    {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S) (f : X ⟶ S) [Smooth f]
    [IsProper f] (F : Sheaf X.smallEtaleTopology Ab.{u + 1})
    (hFlc : Stacks.ConstantSheaf.IsLocallyConstant X.smallEtaleTopology F)
    (hFtors : ∀ (x : GeometricPoint X) (a : (smallEtaleStalkAb x.hom).obj F),
      ∃ n : ℕ, 0 < n ∧
        (ringChar x.residueField = 0 ∨ Nat.Coprime n (ringChar x.residueField)) ∧ n • a = 0)
    (s : GeometricPoint S) (t : GeometricPoint (strictHenselization B S hS s)) :
    IsIso ((smallEtaleDerivedSpecializationStalkAbAt B S hS s t).app
      ((smallEtaleDerivedPushforwardAb f).obj
        ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj F))) := by
  have hla := isLocallyAcyclicRelative_of_isLocallyConstant_unconditional B hX hS f F hFlc hFtors
    (isLocallyAcyclic_of_isUniversallyLocallyAcyclic B hX hS f
      (SmoothBaseChange.isUniversallyLocallyAcyclic_of_smooth h0EYS h0EZR h0EZS h0F08 h03SC2
        h03SC6 h0BMA h0EYD f))
  have hKt := Stacks.Torsion.torsionCohomologyProperty_singleFunctor _ F
    (torsionSheafProperty_of_forall_smallEtaleStalkAb F fun x g => by
      obtain ⟨n, hn, -, h⟩ := hFtors x g
      exact ⟨n, hn, h⟩)
  exact (isIso_specializationMap_and_cospecializationMap_of_isProper B hS f s t h095T h03Q9 hX _
    0 inferInstance hla hKt).1

end AlgebraicGeometry

end
