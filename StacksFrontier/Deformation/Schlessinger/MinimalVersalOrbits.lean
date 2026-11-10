module

public import StacksFrontier.Deformation.FormalObject.VersalCriterion
public import StacksFrontier.Deformation.Schlessinger.MiniversalSeparable

/-!
# The differential of a versal formal object on derivation orbits

Let `p : F ⥤ 𝒞_Λ` be a predeformation category, let `ξ` be a formal object of `p` over the
complete local algebra `R = ξ.base` with augmentation `q : R → k`, and let
`dξ : Der_Λ(R, k) → T p` be its differential. The group `Der_Λ(k, k)` acts on both sides: on the
source a derivation `δ` of `k` acts by adding `δ ∘ q`, and on the target by the twisting
automorphisms of the dual numbers.

For an arbitrary versal formal object:

* `dξ` is surjective;
* `dξ` is equivariant: `dξ (D + δ ∘ q)` is the image of `dξ D` under the action of `δ`;
* consequently two derivations differing by some `δ ∘ q` have tangent vectors in the same
  `Der_Λ(k, k)`-orbit.

For a predeformation category satisfying (S2), `dξ` is additive: two derivations with the same
differential have a difference whose differential is that of the zero derivation.

## Main definitions

* `Deformation.residueCompDerivation`: the derivation `δ ∘ q` of `R` attached to a derivation
  `δ` of the residue field.

## Main results

* `Deformation.derivationToTangent_surjective`: the differential of a versal formal object is
  surjective.
* `Deformation.derivationToTangent_add_residueCompDerivation`: equivariance of the
  differential.
* `Deformation.derivationToTangent_sub_eq_derivationToTangent_zero`: additivity of the
  differential, under (S2).
* `Deformation.exists_derivationDifferentialGraph_of_versal`,
  `Deformation.exists_derivationDifferentialGraph_derivationAction` and
  `Deformation.exists_derivationAction_eq_of_sub_residueCompDerivation`: the same three facts
  for the graph `Deformation.derivationDifferentialGraph` of the differential.

## References

* [Stacks Project, Tag 06T6](https://stacks.math.columbia.edu/tag/06T6)
* [Stacks Project, Tag 06IH](https://stacks.math.columbia.edu/tag/06IH)
* [Stacks Project, Tag 06IJ](https://stacks.math.columbia.edu/tag/06IJ)
* [Stacks Project, Tag 06IU](https://stacks.math.columbia.edu/tag/06IU)
* [Stacks Project, Tag 06SU](https://stacks.math.columbia.edu/tag/06SU)
* [Stacks Project, Tag 06SW](https://stacks.math.columbia.edu/tag/06SW)
-/

@[expose] public section

open CategoryTheory IsLocalRing

namespace Deformation

universe u v w uF vF

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]

/-- The differential of a versal formal object is surjective: every tangent vector of the
predeformation category is the image of a derivation of the underlying complete local
algebra. -/
public theorem derivationToTangent_surjective
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p)
    (hS1 : SchlessingerConditionS1 p) (hS2 : SchlessingerConditionS2 p)
    (ξ : FormalObject p) (hξ : IsVersal hp.cofibered ξ)
    (P : ChosenPushforwards p) :
    Function.Surjective (derivationToTangent hp.cofibered ξ P) := by
  classical
  let : Algebra ξ.base k := (residueHom ξ.base).toRingHom.toAlgebra
  let hsource := categoryOfElements_projection_isCofibered (restrictedCoyoneda ξ.base)
  let 𝓢 := BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda ξ.base))
  intro y
  obtain ⟨z, hz⟩ := ((isVersal_iff_differential_surjective_and_base_lifts
    (BasedCategory.ofFunctor p) hp hS1 hS2 ξ P).mp hξ).1 y
  obtain ⟨⟨@⟨A', α⟩, hA⟩, hx⟩ := classOf_surjective 𝓢 hsource (artinianDualNumbers Λ k) z
  change A' = artinianDualNumbers Λ k at hA
  cases hA
  refine ⟨tangentSpaceDerivationsLinearEquiv ξ.base α, ?_⟩
  change mapIsomorphismClasses hsource hp.cofibered
      (associatedMorphism hp.cofibered ξ P).toBasedFunctor
      (artinianDualNumbers Λ k)
      (classOf 𝓢 hsource ⟨Functor.elementsMk _ (artinianDualNumbers Λ k)
        ((tangentSpaceDerivationsLinearEquiv ξ.base).symm
          (tangentSpaceDerivationsLinearEquiv ξ.base α)), rfl⟩) = y
  rw [LinearEquiv.symm_apply_apply]
  rwa [← hx] at hz

/-- The `Λ`-derivation `δ ∘ q` of a complete local algebra `R` with residue field `k`
obtained from a `Λ`-derivation `δ` of `k` by composing with the augmentation `q : R → k`.
Its image is the subspace of derivations of `R` that vanish on the maximal ideal. -/
public noncomputable def residueCompDerivation (R : CompleteLocalAlgCat.{u, max v w, w} Λ k)
    (δ : Derivation Λ k k) :
    letI : Algebra R k := (residueHom R).toRingHom.toAlgebra
    Derivation Λ R k := by
  letI : Algebra R k := (residueHom R).toRingHom.toAlgebra
  refine { toLinearMap := δ.toLinearMap.comp (residueHom R).toLinearMap
           map_one_eq_zero' := ?_, leibniz' := ?_ }
  · change δ (residueHom R 1) = 0
    rw [map_one, δ.map_one_eq_zero]
  · intro a b
    change δ (residueHom R (a * b)) =
      a • δ (residueHom R b) + b • δ (residueHom R a)
    rw [map_mul, δ.leibniz, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def,
      Algebra.smul_def]
    rfl

/-- The derivation `δ ∘ q` is the composite of the augmentation with `δ`. -/
public theorem residueCompDerivation_apply (R : CompleteLocalAlgCat.{u, max v w, w} Λ k)
    (δ : Derivation Λ k k) (r : R) :
    letI : Algebra R k := (residueHom R).toRingHom.toAlgebra
    residueCompDerivation R δ r = δ (residueHom R r) := rfl

/-- The first coordinate of a square-zero point of `R` is the augmentation of `R`. -/
public theorem dualNumberPoint_fst (R : CompleteLocalAlgCat.{u, max v w, w} Λ k)
    (α : tangentSpaceArtinian Λ k (restrictedCoyoneda R)) (r : R) :
    (α.hom r).fst = residueHom R r := α.residue_comm r

/-- Twisting a square-zero point of `R` by the automorphism of the dual numbers attached to
a derivation `δ` of `k` adds `δ ∘ q` to the corresponding derivation of `R`. -/
public theorem tangentSpaceDerivationsLinearEquiv_map_dualNumbersTwistHom
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p) (R : CompleteLocalAlgCat.{u, max v w, w} Λ k)
    (δ : Derivation Λ k k) (α : tangentSpaceArtinian Λ k (restrictedCoyoneda R)) :
    letI : Algebra R k := (residueHom R).toRingHom.toAlgebra
    tangentSpaceDerivationsLinearEquiv R
        ((restrictedCoyoneda R).map (dualNumbersTwistHom.{u, v, w} p hp δ) α) =
      tangentSpaceDerivationsLinearEquiv R α + residueCompDerivation R δ := by
  let : Algebra R k := (residueHom R).toRingHom.toAlgebra
  refine Derivation.ext fun r ↦ ?_
  have hsplit : α.hom r =
      TrivSqZeroExt.inl (residueHom R r) + TrivSqZeroExt.inr (α.hom r).snd := by
    rw [← dualNumberPoint_fst R α r]
    exact (TrivSqZeroExt.inl_fst_add_inr_snd_eq (α.hom r)).symm
  have hgen := dualNumbersTwistHom_apply_ulift p hp δ (residueHom R r) (α.hom r).snd
  rw [← hsplit] at hgen
  have hmap : ((restrictedCoyoneda R).map
      (dualNumbersTwistHom.{u, v, w} p hp δ) α).hom r =
      TrivSqZeroExt.inl (residueHom R r) +
        TrivSqZeroExt.inr ((α.hom r).snd + ULift.up (δ (residueHom R r))) := hgen
  rw [tangentSpaceDerivationsLinearEquiv_apply, hmap, Derivation.add_apply,
    tangentSpaceDerivationsLinearEquiv_apply, residueCompDerivation_apply]
  exact zero_add _

/-- Translating a derivation of the base of a formal
object by `δ ∘ q` translates its differential by the action of `δ` on the tangent space. -/
public theorem derivationToTangent_add_residueCompDerivation
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p)
    (ξ : FormalObject p) (P : ChosenPushforwards p) (δ : Derivation Λ k k)
    (D : letI : Algebra ξ.base k := (residueHom ξ.base).toRingHom.toAlgebra
      Derivation Λ ξ.base k) :
    derivationToTangent hp.cofibered ξ P (D + residueCompDerivation ξ.base δ) =
      (derivationAction.{u, v, w} p hp).action
        (δ, derivationToTangent hp.cofibered ξ P D) := by
  let : Algebra ξ.base k := (residueHom ξ.base).toRingHom.toAlgebra
  let hsource := categoryOfElements_projection_isCofibered (restrictedCoyoneda ξ.base)
  let 𝓢 := BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda ξ.base))
  let e := tangentSpaceDerivationsLinearEquiv ξ.base
  let twist := dualNumbersTwistHom.{u, v, w} p hp δ
  let α : tangentSpaceArtinian Λ k (restrictedCoyoneda ξ.base) := e.symm D
  let α' := (restrictedCoyoneda ξ.base).map twist α
  let x : 𝓢.p.Fiber (artinianDualNumbers.{u, w, v} Λ k) :=
    ⟨Functor.elementsMk _ (artinianDualNumbers.{u, w, v} Λ k) α, rfl⟩
  let y : 𝓢.p.Fiber (artinianDualNumbers.{u, w, v} Λ k) :=
    ⟨Functor.elementsMk _ (artinianDualNumbers.{u, w, v} Λ k) α', rfl⟩
  let m : x.1 ⟶ y.1 := ⟨twist, rfl⟩
  let hm : 𝓢.p.IsHomLift twist m := IsHomLift.map 𝓢.p m
  have hα' : α' = e.symm (D + residueCompDerivation ξ.base δ) := by
    apply e.injective
    rw [e.apply_symm_apply, ← show e α = D from e.apply_symm_apply D]
    exact tangentSpaceDerivationsLinearEquiv_map_dualNumbersTwistHom p hp ξ.base δ α
  have hmc : (isomorphismClasses 𝓢 hsource).map twist (classOf 𝓢 hsource x) =
      classOf 𝓢 hsource y := map_classOf 𝓢 hsource twist x y m
  have hnat := mapIsomorphismClasses_naturality hsource hp.cofibered
    (associatedMorphism hp.cofibered ξ P).toBasedFunctor twist (classOf 𝓢 hsource x)
  rw [hmc] at hnat
  change mapIsomorphismClasses hsource hp.cofibered
      (associatedMorphism hp.cofibered ξ P).toBasedFunctor
      (artinianDualNumbers.{u, w, v} Λ k) (classOf 𝓢 hsource y) =
    (isomorphismClasses (BasedCategory.ofFunctor p) hp.cofibered).map twist
      (mapIsomorphismClasses hsource hp.cofibered
        (associatedMorphism hp.cofibered ξ P).toBasedFunctor
        (artinianDualNumbers.{u, w, v} Λ k) (classOf 𝓢 hsource x)) at hnat
  change mapIsomorphismClasses hsource hp.cofibered
      (associatedMorphism hp.cofibered ξ P).toBasedFunctor
      (artinianDualNumbers.{u, w, v} Λ k)
      (classOf 𝓢 hsource ⟨Functor.elementsMk _ (artinianDualNumbers.{u, w, v} Λ k)
        (e.symm (D + residueCompDerivation ξ.base δ)), rfl⟩) = _
  rwa [← hα']

/-- For a predeformation category satisfying (S2), two derivations of the base of a formal object
with the same differential have a difference whose differential is that of the zero derivation.
-/
public theorem derivationToTangent_sub_eq_derivationToTangent_zero
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p) (hS2 : SchlessingerConditionS2 p)
    (ξ : FormalObject p) (P : ChosenPushforwards p)
    (X Y : letI : Algebra ξ.base k := (residueHom ξ.base).toRingHom.toAlgebra
      Derivation Λ ξ.base k)
    (h : derivationToTangent hp.cofibered ξ P X =
      derivationToTangent hp.cofibered ξ P Y) :
    derivationToTangent hp.cofibered ξ P (X - Y) =
      derivationToTangent hp.cofibered ξ P 0 := by
  let : Algebra ξ.base k := (residueHom ξ.base).toRingHom.toAlgebra
  let 𝓕 := BasedCategory.ofFunctor p
  let hAssoc := schlessingerConditionS2_of_isIsomorphismClasses 𝓕 hp.cofibered hS2 (Or.inl hp)
  let L := associatedTangentSpaceModuleStructure 𝓕 hp hAssoc
  let f := linearMapOfPointNaturality ξ.base L.functor
    (pointToModule hp.cofibered ξ P L) (pointToModule_naturality hp.cofibered ξ P L)
  let E := tangentSpaceDerivationsLinearEquiv ξ.base
  let V : FGModuleCat.{max v w} k := FGModuleCat.of k (ULift.{v} k)
  have hpt : ∀ a b : tangentSpaceArtinian Λ k (restrictedCoyoneda ξ.base),
      pointToModule hp.cofibered ξ P L V a = pointToModule hp.cofibered ξ P L V b ↔
        pointClass hp.cofibered ξ P (artinianDualNumbers.{u, w, v} Λ k) a =
          pointClass hp.cofibered ξ P (artinianDualNumbers.{u, w, v} Λ k) b := by
    intro a b
    change (eqToHom L.forget_comp.symm).app V
        (pointClass hp.cofibered ξ P (artinianDualNumbers.{u, w, v} Λ k) a) =
      (eqToHom L.forget_comp.symm).app V
        (pointClass hp.cofibered ξ P (artinianDualNumbers.{u, w, v} Λ k) b) ↔ _
    rw [eqToHom_app_apply_cast, eqToHom_app_apply_cast]
    exact cast_inj _
  have hfXY : f (E.symm X) = f (E.symm Y) := by
    refine (hpt _ _).mpr ?_
    rw [← derivationToTangent_eq_pointClass hp.cofibered ξ P X,
      ← derivationToTangent_eq_pointClass hp.cofibered ξ P Y]
    exact h
  have hzero : f (E.symm X - E.symm Y) = f 0 := by
    rw [map_sub, hfXY, sub_self, map_zero]
  rw [derivationToTangent_eq_pointClass hp.cofibered ξ P (X - Y),
    derivationToTangent_eq_pointClass hp.cofibered ξ P 0, map_sub, map_zero]
  exact (hpt _ _).mp hzero

/-- For a versal formal object every tangent vector
of the predeformation category is related by the graph of the differential to a derivation of
the underlying complete local algebra. -/
public theorem exists_derivationDifferentialGraph_of_versal
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p)
    (hS1 : SchlessingerConditionS1 p) (hS2 : SchlessingerConditionS2 p)
    (ξ : FormalObject p) (hξ : IsVersal hp.cofibered ξ)
    (y : predeformationTangentSpace.{u, v, w} p hp) :
    ∃ D : Derivations ξ.base k, derivationDifferentialGraph.{u, v, w} p hp ξ D y := by
  let P : ChosenPushforwards p := chosenPushforwardsOfCofibered p hp.cofibered
  obtain ⟨d, rfl⟩ := derivationToTangent_surjective p hp hS1 hS2 ξ hξ P y
  exact ⟨standardToDerivation ξ d, derivationToTangent_graph hp ξ P d⟩

/-- Acting on a tangent vector by a derivation `δ` of
the residue field corresponds, on the side of derivations of the base, to adding `δ ∘ q`. -/
public theorem exists_derivationDifferentialGraph_derivationAction
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p) (ξ : FormalObject p)
    (D : Derivations ξ.base k) (δ : Derivation Λ k k)
    (y : predeformationTangentSpace.{u, v, w} p hp)
    (hy : derivationDifferentialGraph.{u, v, w} p hp ξ D y) :
    ∃ E : Derivations ξ.base k,
      (∀ r : ξ.base, E r = D r + δ (residueHom ξ.base r)) ∧
        derivationDifferentialGraph.{u, v, w} p hp ξ E
          ((derivationAction.{u, v, w} p hp).action (δ, y)) := by
  let : Algebra ξ.base k := (residueHom ξ.base).toRingHom.toAlgebra
  let P : ChosenPushforwards p := chosenPushforwardsOfCofibered p hp.cofibered
  let D' := derivationToStandard ξ D
  refine ⟨standardToDerivation ξ (D' + residueCompDerivation ξ.base δ), ?_, ?_⟩
  · intro r
    rw [standardToDerivation_apply, Derivation.add_apply, residueCompDerivation_apply,
      derivationToStandard_apply]
  · have hgraph := derivationToTangent_graph hp ξ P (D' + residueCompDerivation ξ.base δ)
    rw [derivationToTangent_add_residueCompDerivation p hp ξ P δ D'] at hgraph
    rwa [derivationDifferentialGraph_eq_derivationToTangent hp ξ P D y hy]

/-- If two derivations of the base
differ by `δ ∘ q`, their tangent vectors lie in the same `Der_Λ(k, k)`-orbit. -/
public theorem exists_derivationAction_eq_of_sub_residueCompDerivation
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p) (ξ : FormalObject p)
    (D E : Derivations ξ.base k)
    (y z : predeformationTangentSpace.{u, v, w} p hp)
    (hy : derivationDifferentialGraph.{u, v, w} p hp ξ D y)
    (hz : derivationDifferentialGraph.{u, v, w} p hp ξ E z)
    (h : ∃ δ : Derivation Λ k k, ∀ r : ξ.base, E r = D r + δ (residueHom ξ.base r)) :
    ∃ δ : Derivation Λ k k, z = (derivationAction.{u, v, w} p hp).action (δ, y) := by
  obtain ⟨δ, hδ⟩ := h
  obtain ⟨E', hE', hgraph⟩ :=
    exists_derivationDifferentialGraph_derivationAction p hp ξ D δ y hy
  have hEE : E = E' := by
    let : Module Λ k := Module.compHom k (algebraMap Λ k)
    let : Module ξ.base k := Module.compHom k (residueHom ξ.base).toRingHom
    refine Derivation.ext fun r ↦ ?_
    rw [hδ r, hE' r]
  subst hEE
  exact ⟨δ, (existsUnique_derivationDifferentialGraph hp ξ E).unique hz hgraph⟩

end Deformation

end
