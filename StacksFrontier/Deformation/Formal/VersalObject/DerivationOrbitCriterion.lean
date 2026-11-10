module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Formal.VersalObject.IsomorphismClasses
public import StacksFrontier.Deformation.Formal.VersalObject.MinimalUniqueness
public import StacksFrontier.Deformation.FormalObject.AssociatedMorphismMap
public import StacksFrontier.Deformation.FormalObject.DerivationOrbits
public import StacksFrontier.Deformation.MinimalVersal
public import StacksFrontier.Deformation.RestrictedRepresentable
public import StacksFrontier.Deformation.Schlessinger.MiniversalSeparable
public import StacksFrontier.Deformation.TangentSpace.BijectiveDifferential
public import StacksFrontier.Deformation.TangentSpace.Derivations

/-!
# Minimality from bijectivity of the differential on derivation orbits

A versal formal object of a predeformation category whose differential is bijective on
derivation orbits is a minimal versal formal object; consequently any two such formal objects
are isomorphic.

## Main results

* `Deformation.isMinimalVersal_of_hasBijectiveDifferentialOnDerivationOrbits`: a versal formal
  object whose differential is bijective on derivation orbits is minimal versal.
* `Deformation.isomorphic_of_hasBijectiveDifferentialOnDerivationOrbits`: any two such versal
  formal objects are isomorphic.

## References

* [Stacks Project, Tag 06IR](https://stacks.math.columbia.edu/tag/06IR)
* [Stacks Project, Tag 06T6](https://stacks.math.columbia.edu/tag/06T6)
-/

@[expose] public section

open CategoryTheory IsLocalRing

namespace Deformation

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  Deformation.restrictedRepresentable

universe u v w uF vF

section

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The two augmentations of a complete local algebra to its residue field induce the same
algebra structure on the residue field. -/
private theorem residueAlgebra_eq (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    (residueAlgHom R).toRingHom.toAlgebra = (residueHom R).toRingHom.toAlgebra :=
  congrArg (fun φ : R →ₐ[Λ] k ↦ φ.toRingHom.toAlgebra) (residueAlgHom_eq_residueHom R)

/-- A residue-field-valued derivation, read as a derivation for the algebra structure induced
by `Deformation.residueHom`. -/
private noncomputable def residueDerivationToStandard
    {R : CompleteLocalAlgCat.{u, v, w} Λ k} (D : ResidueDerivation R) :
    letI : Algebra R k := (residueHom R).toRingHom.toAlgebra
    Derivation Λ R k :=
  cast (derivation_type_eq
    (congrArg (fun i : Algebra R k ↦ @Algebra.toModule R k _ _ i) (residueAlgebra_eq R)) rfl) D

/-- `Deformation.residueDerivationToStandard D` has the same values as `D`. -/
private theorem residueDerivationToStandard_apply
    {R : CompleteLocalAlgCat.{u, v, w} Λ k} (D : ResidueDerivation R) (r : R) :
    residueDerivationToStandard D r = D r :=
  derivation_cast_apply
    (congrArg (fun i : Algebra R k ↦ @Algebra.toModule R k _ _ i) (residueAlgebra_eq R)) rfl D r

/-- The point of `R` with values in the dual numbers attached to a residue-field-valued
derivation of `R`, together with its two components: the residue map, and the derivation. -/
private noncomputable def derivationPointWithApply
    {R : CompleteLocalAlgCat.{u, max v w, w} Λ k} (D : ResidueDerivation R) :
    {α : (restrictedCoyoneda R).obj (artinianDualNumbers.{u, w, v} Λ k) //
      (∀ r : R, (α.hom r).fst = residueHom R r) ∧ ∀ r : R, (α.hom r).snd.down = D r} := by
  letI : Algebra R k := (residueHom R).toRingHom.toAlgebra
  refine ⟨(tangentSpaceDerivationsLinearEquiv.{u, v, w} R).symm
    (residueDerivationToStandard D), fun r ↦ ?_, fun r ↦ ?_⟩
  · exact ((tangentSpaceDerivationsLinearEquiv.{u, v, w} R).symm
      (residueDerivationToStandard D)).residue_comm r
  · exact (tangentSpaceDerivationsLinearEquiv_apply.{u, v, w} R _ r).symm.trans <| by
      rw [LinearEquiv.apply_symm_apply, residueDerivationToStandard_apply]

/-- The point of `R` with values in the dual numbers attached to a residue-field-valued
derivation of `R`. -/
private noncomputable def derivationPoint
    {R : CompleteLocalAlgCat.{u, max v w, w} Λ k} (D : ResidueDerivation R) :
    (restrictedCoyoneda R).obj (artinianDualNumbers.{u, w, v} Λ k) :=
  (derivationPointWithApply.{u, v, w} D).1

/-- The residue component of `Deformation.derivationPoint D` is the residue map of `R`. -/
private theorem derivationPoint_fst
    {R : CompleteLocalAlgCat.{u, max v w, w} Λ k} (D : ResidueDerivation R) (r : R) :
    ((derivationPoint.{u, v, w} D).hom r).fst = residueHom R r :=
  (derivationPointWithApply.{u, v, w} D).2.1 r

/-- The square-zero component of `Deformation.derivationPoint D` is `D`. -/
private theorem derivationPoint_snd
    {R : CompleteLocalAlgCat.{u, max v w, w} Λ k} (D : ResidueDerivation R) (r : R) :
    ((derivationPoint.{u, v, w} D).hom r).snd.down = D r :=
  (derivationPointWithApply.{u, v, w} D).2.2 r

/-- Two derivations restricting to the same derivation along a morphism give the same point
after precomposition with that morphism. -/
private theorem derivationPoint_precomp_eq
    {R S : CompleteLocalAlgCat.{u, max v w, w} Λ k} (f : R ⟶ S)
    (D E : ResidueDerivation S)
    (h : ResidueDerivation.comap f D = ResidueDerivation.comap f E) :
    (restrictedCoyonedaMap f).app (artinianDualNumbers.{u, w, v} Λ k) (derivationPoint D) =
      (restrictedCoyonedaMap f).app (artinianDualNumbers.{u, w, v} Λ k)
        (derivationPoint E) := by
  refine CompleteLocalAlgCat.Hom.ext (AlgHom.ext fun r ↦ ?_)
  change (derivationPoint.{u, v, w} D).hom (f.hom r) =
    (derivationPoint.{u, v, w} E).hom (f.hom r)
  refine TrivSqZeroExt.ext ?_ (ULift.ext ?_)
  · rw [derivationPoint_fst, derivationPoint_fst]
  · rw [derivationPoint_snd, derivationPoint_snd]
    simpa only [ResidueDerivation.comap_apply] using
      congrArg (fun d : ResidueDerivation R ↦ d r) h

end

section

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}

/-- A residue-field-valued derivation of the base of a formal object, read as a
`Deformation.Derivations`. -/
private noncomputable def residueDerivationToDerivations
    (ξ : FormalObject p) (D : ResidueDerivation ξ.base) : Derivations ξ.base k :=
  standardToDerivation ξ (residueDerivationToStandard D)

/-- `Deformation.residueDerivationToDerivations ξ D` has the same values as `D`. -/
private theorem residueDerivationToDerivations_apply
    (ξ : FormalObject p) (D : ResidueDerivation ξ.base) (r : ξ.base) :
    residueDerivationToDerivations ξ D r = D r :=
  (standardToDerivation_apply ξ (residueDerivationToStandard D) r).trans
    (residueDerivationToStandard_apply D r)

/-- A versal formal object of a predeformation category whose
differential is bijective on derivation orbits is a minimal versal formal object. -/
@[stacks 06IR "minimality"]
public theorem isMinimalVersal_of_hasBijectiveDifferentialOnDerivationOrbits
    (hp : IsPredeformationCategory p) (ξ : FormalObject p) (hξ : IsVersal hp.cofibered ξ)
    (hd : HasBijectiveDifferentialOnDerivationOrbits.{u, v, w} p hp ξ) :
    IsMinimalVersal hp.cofibered ξ := by
  refine ⟨hξ, fun ξ' f ↦ surjective_of_residueDerivation_comap_injective f.base
    fun D E hDE ↦ ?_⟩
  let push := chosenPushforwardsOfCofibered p hp.cofibered
  let dual := artinianDualNumbers.{u, w, v} Λ k
  let src := restrictedRepresentable ξ.base
  let hsrc := categoryOfElements_projection_isCofibered (restrictedCoyoneda ξ.base)
  let X := associatedMorphism hp.cofibered ξ' push
  let Y := associatedMorphism hp.cofibered ξ push
  let y (D' : ResidueDerivation ξ.base) := mapIsomorphismClasses hsrc hp.cofibered
    Y.toBasedFunctor dual (classOf src hsrc ⟨Functor.elementsMk _ dual (derivationPoint D'), rfl⟩)
  have hGraph (D' : ResidueDerivation ξ.base) : derivationDifferentialGraph.{u, v, w} p hp ξ
      (residueDerivationToDerivations ξ D') (y D') :=
    ⟨push, derivationPoint D', fun r ↦ (derivationPoint_snd D' r).trans
      (residueDerivationToDerivations_apply ξ D' r).symm, rfl⟩
  have hclasses : y D = y E := by
    let src' := restrictedRepresentable ξ'.base
    let hsrc' := categoryOfElements_projection_isCofibered (restrictedCoyoneda ξ'.base)
    let f' := restrictedRepresentableMap f.base
    have hβ : (restrictedCoyonedaMap f.base).app dual (derivationPoint D) =
        (restrictedCoyonedaMap f.base).app dual (derivationPoint E) :=
      derivationPoint_precomp_eq f.base D E hDE
    obtain ⟨τ, _⟩ := associatedMorphism_map hp.cofibered f push
    have hstep (α : (restrictedCoyoneda ξ.base).obj dual) :
        mapIsomorphismClasses hsrc hp.cofibered Y.toBasedFunctor dual
            (classOf src hsrc ⟨Functor.elementsMk _ dual α, rfl⟩) =
          mapIsomorphismClasses hsrc' hp.cofibered X.toBasedFunctor dual
            (classOf src' hsrc'
              ⟨Functor.elementsMk _ dual ((restrictedCoyonedaMap f.base).app dual α), rfl⟩) := by
      have hiso := congrFun (mapIsomorphismClasses_eq_of_iso hsrc hp.cofibered
        (BasedFunctor.comp f' X.toBasedFunctor) Y.toBasedFunctor τ dual)
        (classOf src hsrc ⟨Functor.elementsMk _ dual α, rfl⟩)
      rw [← hiso, mapIsomorphismClasses_comp hsrc hsrc' hp.cofibered f' X.toBasedFunctor dual]
      exact congrArg (mapIsomorphismClasses hsrc' hp.cofibered X.toBasedFunctor dual)
        (mapIsomorphismClasses_classOf hsrc hsrc' f' ⟨Functor.elementsMk _ dual α, rfl⟩)
    exact (hstep _).trans (hβ ▸ (hstep _).symm)
  obtain ⟨δ, hOrbit⟩ := (hd.2.2.2 (residueDerivationToDerivations ξ D)
    (residueDerivationToDerivations ξ E) (y D) (y E) (hGraph D) (hGraph E)).mp
    ⟨0, by rw [(derivationAction.{u, v, w} p hp).zero_action, hclasses]⟩
  have hδ : δ = 0 := by
    refine Derivation.ext fun a ↦ ?_
    obtain ⟨r, hr⟩ := ξ'.base.residueEquiv.surjective a
    obtain ⟨s, hs⟩ := residue_surjective r
    have hsum : D (f.base.hom s) + δ (residueHom ξ.base (f.base.hom s)) =
        D (f.base.hom s) := by
      calc
        _ = E (f.base.hom s) := by
          simpa only [residueDerivationToDerivations_apply] using (hOrbit _).symm
        _ = D (f.base.hom s) := by
          simpa only [ResidueDerivation.comap_apply] using
            congrArg (fun q : ResidueDerivation ξ'.base ↦ q s) hDE.symm
    have hq : residueHom ξ.base (f.base.hom s) = a := by
      change ξ.base.residueEquiv (residue ξ.base (f.base.hom s)) = a
      rw [f.base.residue_comm s, hs, hr]
    simpa only [hq, Derivation.zero_apply] using add_eq_left.mp hsum
  let : Algebra ξ.base k := (residueAlgHom ξ.base).toRingHom.toAlgebra
  refine Derivation.ext fun r ↦ ?_
  simpa only [residueDerivationToDerivations_apply, hδ, Derivation.zero_apply, add_zero] using
    (hOrbit r).symm

/-- Any two versal formal objects whose differentials are bijective on derivation orbits are
isomorphic. -/
@[stacks 06IR "uniqueness", sga "7 VI 1.20" "uniqueness"]
public theorem isomorphic_of_hasBijectiveDifferentialOnDerivationOrbits
    (hp : IsPredeformationCategory p) (ξ η : FormalObject p)
    (hξ : IsVersal hp.cofibered ξ) (hη : IsVersal hp.cofibered η)
    (hdξ : HasBijectiveDifferentialOnDerivationOrbits.{u, v, w} p hp ξ)
    (hdη : HasBijectiveDifferentialOnDerivationOrbits.{u, v, w} p hp η) :
    Nonempty (ξ ≅ η) :=
  isomorphic_of_isMinimalVersal hp ξ η
    (isMinimalVersal_of_hasBijectiveDifferentialOnDerivationOrbits hp ξ hξ hdξ)
    (isMinimalVersal_of_hasBijectiveDifferentialOnDerivationOrbits hp η hη hdη)

end

end Deformation

end
