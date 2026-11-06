module

public import StacksFrontier.Deformation.Schlessinger.MiniversalSeparable
public import StacksFrontier.Deformation.FormalObject.VersalCriterion

/-!
# The differential of a formal object on derivation orbits

Let `ξ` be a formal object of a predeformation category, with differential presented as the
relation `Deformation.derivationDifferentialGraph` between `Λ`-derivations of `ξ.base` and tangent
vectors. This file proves that the differential is surjective when `ξ` is versal, that it is
equivariant for the translation action of `Der_Λ(k, k)`, that derivations differing by an element
of `Der_Λ(k, k)` name tangent vectors in the same orbit, and that the differential is additive.

## Main results

* `Deformation.exists_derivationDifferentialGraph_of_isVersal`: for a versal formal object every
  tangent vector is related to some derivation.
* `Deformation.exists_derivationDifferentialGraph_action`: the differential is equivariant for
  the action of `Der_Λ(k, k)`.
* `Deformation.eq_action_of_eq_add`: derivations differing by a residue-field derivation `δ` name
  tangent vectors differing by the translation by `δ`.
* `Deformation.derivationToTangent_sub_eq_zero_of_eq`: if two derivations name the same tangent
  vector, their difference names the same tangent vector as the zero derivation.

## References

* [Stacks Project, Tag 06T6](https://stacks.math.columbia.edu/tag/06T6)
* [Stacks Project, Tag 06T8](https://stacks.math.columbia.edu/tag/06T8)
* [Stacks Project, Tag 06IJ](https://stacks.math.columbia.edu/tag/06IJ)
* [Stacks Project, Tag 06IU](https://stacks.math.columbia.edu/tag/06IU)
* [Stacks Project, Tag 06SW](https://stacks.math.columbia.edu/tag/06SW)
-/

@[expose] public section

open CategoryTheory

namespace Deformation

section

universe u v w uF vF

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ Deformation.ArtinianLocalAlgCat.{u, max v w, w} Λ k}

/-- The standard derivation of a dual-number point of `ξ.base` is its square-zero component. -/
private theorem standardToDerivation_apply_snd
    (ξ : FormalObject p)
    (α : (restrictedCoyoneda ξ.base).obj (artinianDualNumbers.{u, w, v} Λ k))
    (r : ξ.base) :
    letI : Algebra ξ.base k := (residueHom ξ.base).toRingHom.toAlgebra
    standardToDerivation ξ ((tangentSpaceDerivationsLinearEquiv ξ.base) α) r =
      (α.hom r).snd.down :=
  (standardToDerivation_apply ξ _ r).trans (tangentSpaceDerivationsLinearEquiv_apply ξ.base α r)

/-- Every tangent vector of a predeformation category carrying a versal formal object `ξ` is
related to some derivation of `ξ.base` by the graph of the differential of `ξ`. -/
public theorem exists_derivationDifferentialGraph_of_isVersal
    (hp : IsPredeformationCategory p)
    (hS2 : SchlessingerConditionS2 p)
    (ξ : FormalObject p)
    (hξ : IsVersal hp.cofibered ξ)
    (y : predeformationTangentSpace.{u, v, w} p hp) :
    ∃ D : Derivations ξ.base k,
      derivationDifferentialGraph.{u, v, w} p hp ξ D y := by
  let P : ChosenPushforwards p := chosenPushforwardsOfCofibered p hp.cofibered
  have hS1 := schlessingerConditionS1_of_versal p hp ξ hξ
  have hsurj := (isVersal_iff_differential_surjective_and_base_lifts
    (BasedCategory.ofFunctor p) hp hS1 hS2 ξ P).mp hξ
  obtain ⟨z, hz⟩ := hsurj.1 y
  obtain ⟨x, hx⟩ := classOf_surjective
    (BasedCategory.ofFunctor (CategoryOfElements.π (restrictedCoyoneda ξ.base)))
    (categoryOfElements_projection_isCofibered (restrictedCoyoneda ξ.base))
    (artinianDualNumbers.{u, w, v} Λ k) z
  rcases x with ⟨⟨α⟩, hA⟩
  cases hA
  let : Algebra ξ.base k := (residueHom ξ.base).toRingHom.toAlgebra
  refine ⟨standardToDerivation ξ ((tangentSpaceDerivationsLinearEquiv ξ.base) α), ?_⟩
  exact ⟨P, α, fun r => (standardToDerivation_apply_snd ξ α r).symm,
    hx ▸ hz⟩

/-- The first coordinate of a dual-number point of `ξ.base` is its residue. -/
public theorem restrictedCoyoneda_hom_fst
    (ξ : FormalObject p)
    (α : (restrictedCoyoneda ξ.base).obj (artinianDualNumbers.{u, w, v} Λ k))
    (r : ξ.base) : (α.hom r).fst = residueHom ξ.base r :=
  α.residue_comm r

/-- Twisting a square-zero point of `ξ.base` by a residue-field derivation `δ` adds
`δ ∘ residueHom` to its square-zero component. -/
public theorem twist_squareZeroPoint_snd
    (hp : IsPredeformationCategory p)
    (ξ : FormalObject p) (δ : Derivation Λ k k)
    (α : (restrictedCoyoneda ξ.base).obj (artinianDualNumbers.{u, w, v} Λ k))
    (r : ξ.base) :
    (((restrictedCoyoneda ξ.base).map
        (dualNumbersTwistHom.{u, v, w} p hp δ) α).hom r).snd.down =
      (α.hom r).snd.down + δ (residueHom ξ.base r) := by
  have key : (dualNumbersTwistHom.{u, v, w} p hp δ).hom (α.hom r) =
      TrivSqZeroExt.inl (α.hom r).fst +
        TrivSqZeroExt.inr ((α.hom r).snd + ULift.up (δ (α.hom r).fst)) := by
    conv_lhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq (α.hom r)]
    exact dualNumbersTwistHom_apply_ulift p hp δ (α.hom r).fst (α.hom r).snd
  rw [show ((restrictedCoyoneda ξ.base).map (dualNumbersTwistHom.{u, v, w} p hp δ) α).hom r =
    (dualNumbersTwistHom.{u, v, w} p hp δ).hom (α.hom r) from rfl, key,
    restrictedCoyoneda_hom_fst ξ α r]
  show ((TrivSqZeroExt.snd (TrivSqZeroExt.inl (residueHom ξ.base r) +
      TrivSqZeroExt.inr ((α.hom r).snd + ULift.up (δ (residueHom ξ.base r))) :
        TrivSqZeroExt k (ULift.{v} k))).down)
    = (α.hom r).snd.down + δ (residueHom ξ.base r)
  simp

/-- If `D` is related to the tangent vector `y` by the graph of the differential of `ξ`, then
`D + δ ∘ residueHom` is related to the translate of `y` by `δ`. -/
public theorem exists_derivationDifferentialGraph_action
    (hp : IsPredeformationCategory p)
    (ξ : FormalObject p)
    (D : Derivations ξ.base k) (δ : Derivation Λ k k)
    (y : predeformationTangentSpace.{u, v, w} p hp)
    (hy : derivationDifferentialGraph.{u, v, w} p hp ξ D y) :
    ∃ E : Derivations ξ.base k,
      (∀ r : ξ.base, E r = D r + δ (residueHom ξ.base r)) ∧
        derivationDifferentialGraph.{u, v, w} p hp ξ E
          ((derivationAction.{u, v, w} p hp).action (δ, y)) := by
  obtain ⟨P, α, hα, hmap⟩ := hy
  let tw := dualNumbersTwistHom.{u, v, w} p hp δ
  let α' := (restrictedCoyoneda ξ.base).map tw α
  let : Algebra ξ.base k := (residueHom ξ.base).toRingHom.toAlgebra
  refine ⟨standardToDerivation ξ ((tangentSpaceDerivationsLinearEquiv ξ.base) α'),
    ?_, ⟨P, α', ?_, ?_⟩⟩
  · intro r
    rw [← hα r, ← twist_squareZeroPoint_snd hp ξ δ α r]
    exact standardToDerivation_apply_snd ξ α' r
  · exact fun r => (standardToDerivation_apply_snd ξ α' r).symm
  · let 𝓑 :=
      BasedCategory.ofFunctor (CategoryOfElements.π (restrictedCoyoneda ξ.base))
    let h𝓑 := categoryOfElements_projection_isCofibered (restrictedCoyoneda ξ.base)
    let φ := (associatedMorphism hp.cofibered ξ P).toBasedFunctor
    let dual := artinianDualNumbers.{u, w, v} Λ k
    let xα : 𝓑.p.Fiber dual := ⟨(restrictedCoyoneda ξ.base).elementsMk dual α, rfl⟩
    let xα' : 𝓑.p.Fiber dual := ⟨(restrictedCoyoneda ξ.base).elementsMk dual α', rfl⟩
    let a : xα.1 ⟶ xα'.1 := ⟨tw, rfl⟩
    have ha : 𝓑.p.IsHomLift tw a :=
      CategoryTheory.IsHomLift.of_fac 𝓑.p tw a rfl rfl rfl
    have hstep : (isomorphismClasses 𝓑 h𝓑).map tw (classOf 𝓑 h𝓑 xα) =
        classOf 𝓑 h𝓑 xα' := map_classOf 𝓑 h𝓑 tw xα xα' a
    rw [← hstep, mapIsomorphismClasses_naturality h𝓑 hp.cofibered φ tw
      (classOf 𝓑 h𝓑 xα)]
    exact congrArg _ hmap

/-- Two `Deformation.Derivations` of `ξ.base` that agree pointwise are equal. -/
public theorem derivations_ext
    (ξ : FormalObject p) {D E : Derivations ξ.base k}
    (h : ∀ r : ξ.base, D r = E r) : D = E := by
  let : Module Λ k := Module.compHom k (algebraMap Λ k)
  let : Module ξ.base k :=
    Module.compHom k (residueHom ξ.base).toRingHom
  exact Derivation.ext h

/-- If `E` differs from `D` by a residue-field derivation, then the tangent vectors they name
differ by the corresponding translation. -/
public theorem eq_action_of_eq_add
    (hp : IsPredeformationCategory p)
    (ξ : FormalObject p)
    (D E : Derivations ξ.base k)
    (y z : predeformationTangentSpace.{u, v, w} p hp)
    (hy : derivationDifferentialGraph.{u, v, w} p hp ξ D y)
    (hz : derivationDifferentialGraph.{u, v, w} p hp ξ E z)
    (hδ : ∃ δ : Derivation Λ k k, ∀ r : ξ.base, E r = D r + δ (residueHom ξ.base r)) :
    ∃ δ : Derivation Λ k k,
      z = (derivationAction.{u, v, w} p hp).action (δ, y) := by
  obtain ⟨δ, hδ⟩ := hδ
  obtain ⟨E', hE', hgraph⟩ :=
    exists_derivationDifferentialGraph_action.{u, v, w} hp ξ D δ y hy
  have hEE' : E = E' := derivations_ext ξ fun r => (hδ r).trans (hE' r).symm
  subst hEE'
  obtain ⟨_, _, huniq⟩ := existsUnique_derivationDifferentialGraph.{u, v, w} hp ξ E
  exact ⟨δ, (huniq z hz).trans (huniq _ hgraph).symm⟩

/-- If two derivations of `ξ.base` name the same tangent vector, their difference names the same
tangent vector as the zero derivation. -/
public theorem derivationToTangent_sub_eq_zero_of_eq
    (hp : IsPredeformationCategory p)
    (hS2 : SchlessingerConditionS2 p)
    (ξ : FormalObject p) (P : ChosenPushforwards p)
    (d e : (letI : Algebra ξ.base k :=
      (residueHom ξ.base).toRingHom.toAlgebra
      Derivation Λ ξ.base k))
    (h : derivationToTangent hp.cofibered ξ P d =
      derivationToTangent hp.cofibered ξ P e) :
    derivationToTangent hp.cofibered ξ P (d - e) =
      derivationToTangent hp.cofibered ξ P 0 := by
  let : Algebra ξ.base k := (residueHom ξ.base).toRingHom.toAlgebra
  let 𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, max v w, w} Λ k) :=
    BasedCategory.ofFunctor p
  let hAssoc := schlessingerConditionS2_of_isIsomorphismClasses.{u, v, w}
    𝓕 hp.cofibered hS2 (Or.inl hp)
  let L := associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 hp hAssoc
  let V : FGModuleCat.{max v w} k := FGModuleCat.of k (ULift.{v} k)
  let f := linearMapOfPointNaturality.{u, v, w} ξ.base L.functor
    (pointToModule.{u, v, w} hp.cofibered ξ P L)
    (pointToModule_naturality.{u, v, w} hp.cofibered ξ P L)
  let E := tangentSpaceDerivationsLinearEquiv.{u, v, w} ξ.base
  let Φ := fun z : (isomorphismClasses 𝓕 hp.cofibered).obj
    (artinianDualNumbers.{u, w, v} Λ k) => (eqToHom L.forget_comp.symm).app V z
  have hΦ : ∀ z, (eqToHom L.forget_comp).app V (Φ z) = z := by
    intro z
    show ((eqToHom L.forget_comp.symm ≫ eqToHom L.forget_comp).app V) z = z
    simp
  have key : ∀ d' : Derivation Λ ξ.base k,
      f (E.symm d') = Φ (derivationToTangent hp.cofibered ξ P d') := by
    intro d'
    rw [derivationToTangent_eq_pointClass hp.cofibered ξ P d']
    rfl
  have hsub : f (E.symm (d - e)) = f (E.symm 0) := by
    rw [map_sub, map_sub, map_zero, map_zero, key, key, h, sub_self]
  rw [key, key] at hsub
  exact (hΦ _).symm.trans ((congrArg ((eqToHom L.forget_comp).app V) hsub).trans (hΦ _))

end

end Deformation

end
