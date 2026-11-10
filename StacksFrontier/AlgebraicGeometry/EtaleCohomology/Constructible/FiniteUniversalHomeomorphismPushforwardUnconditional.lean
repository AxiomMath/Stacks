module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointDomination
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.BasicUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SurjectiveMorphismStalkDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.EtaleStalkFunctor
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteUniversalHomeomorphismPushforward
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteUniversalHomeomorphismPushforward

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteEtalePushforwardConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteEtalePushforwardConstructibleUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Topologies.EtaleUniversalHomeomorphism
public import StacksCore.Tactic.StacksAttribute

/-!
# Pullback along a finite universal homeomorphism of big étale sites

Let `p : T ⟶ S` be a finite morphism of a big étale site which is a universal homeomorphism. The
unit of the adjunction `p⁻¹ ⊣ p_*` on sheaves of sets on the small étale sites is an isomorphism;
together with the counit this makes `p⁻¹` and `p_*` inverse equivalences of the small étale topoi.

## Main results

* `AlgebraicGeometry.isIso_of_isIso_smallInverseImage_of_surjective`: inverse image along a
  surjective morphism reflects isomorphisms of sheaves of sets.
* `AlgebraicGeometry.isIso_unit_smallPullbackAdjunction_of_universalHomeomorphism`: the unit of
  `p⁻¹ ⊣ p_*` is an isomorphism for a finite universal homeomorphism `p`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section Counit

variable (B : BigEtaleSite.{u}) {T S : B.Scheme} (p : T ⟶ S)

/-- **Inverse image along a surjective morphism reflects isomorphisms of sheaves of sets.** Let
`f : X ⟶ Y` be a morphism of a big étale site which is surjective and let `α` be a map of sheaves
of sets on `Y_étale`. If `f⁻¹α` is an isomorphism then so is `α`. -/
public theorem isIso_of_isIso_smallInverseImage_of_surjective {X Y : B.Scheme} (f : X ⟶ Y)
    (hf : Function.Surjective (B.inclusion.map f).base)
    {F G : Sheaf (SmallEtale.topology B Y.1 Y.property) (Type (u + 1))} (α : F ⟶ G)
    [IsIso ((B.smallInverseImage f (Type (u + 1))).map α)] : IsIso α := by
  refine isIso_of_bijective_etaleStalkMap_univ.{u, 0} B Y.1 Y.property α fun s => ?_
  obtain ⟨x, hx⟩ := exists_geometricPoint_map_hom_base_eq_of_surjective (B.inclusion.map f) hf s
  rw [← isIso_iff_bijective]
  refine (NatIso.isIso_map_iff (Functor.isoWhiskerLeft (sheafToPresheaf _ _)
    (etaleStalkPresheafFunctorIsoOfEqBase B Y.1 Y.property hx (Type (u + 1)))) α).1 ?_
  refine (NatIso.isIso_map_iff (smallEtalePullbackStalkIsoUniv.{u, 0} B f x) α).1 ?_
  change IsIso ((etaleStalkFunctor.{u, u + 1} B X.1 X.property x).map
    ((B.smallInverseImage f (Type (u + 1))).map α))
  infer_instance

/-- **The unit of `p⁻¹ ⊣ p_*` is an isomorphism for a finite universal homeomorphism.** Let
`p : T ⟶ S` be a finite morphism of a big étale site which is a universal homeomorphism and let
`𝒢` be a sheaf of sets on the small étale site of `S`. Then `𝒢 ⟶ p_*p⁻¹𝒢` is an isomorphism. -/
public theorem isIso_unit_smallPullbackAdjunction_of_universalHomeomorphism
    [IsFinite (B.inclusion.map p)] [UniversalHomeomorphism (B.inclusion.map p)]
    (G : Sheaf (SmallEtale.topology B S.1 S.property) (Type (u + 1))) :
    IsIso ((B.smallPullbackAdjunction p (Type (u + 1))).unit.app G) := by
  have := isIso_counit_smallPullbackAdjunction_of_universalHomeomorphism B p
    ((B.smallInverseImage p (Type (u + 1))).obj G)
  have h := (B.smallPullbackAdjunction p (Type (u + 1))).left_triangle_components G
  have : IsIso ((B.smallInverseImage p (Type (u + 1))).map
      ((B.smallPullbackAdjunction p (Type (u + 1))).unit.app G)) :=
    isIso_of_comp_hom_eq_id _ h
  exact isIso_of_isIso_smallInverseImage_of_surjective B p
    (Stacks.Etale.surjective_of_universalHomeomorphism (B.inclusion.map p)).surj _

end Counit

section Constructible

variable (B : BigEtaleSite.{u}) {T S : B.Scheme} (p : T ⟶ S)

end Constructible

end AlgebraicGeometry

end
