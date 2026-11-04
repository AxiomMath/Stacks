module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleAdicPointLift
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveEtaleLocal
import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveComposition

/-!
# Joint rig-surjectivity of a jointly surjective representable étale family

Let `{vⱼ : Vⱼ ⟶ V}` be a family of morphisms of formal algebraic spaces over `S` which are
representable by algebraic spaces and étale and which is jointly surjective on points. Then the
family is jointly rig-surjective: every adic morphism `p : Spf R ⟶ V` out of the formal
spectrum of a complete discrete valuation ring lifts, after an extension `R ⊂ R'` of complete
discrete valuation rings, to an adic morphism `Spf R' ⟶ Vⱼ` into one member of the family.

This is **Stacks 0AQU** for the family, together with the factorization of an adic point of the
coproduct `∐ Vⱼ` through one summand which the proof of Stacks 0AQV takes for granted. The
member is chosen first: the formal spectrum of `R` has the point of its residue field, joint
surjectivity catches its image in one `Vⱼ`, and the pair of points is a point of the fibre
product `Spf R ×_V Vⱼ`. From a point of that fibre product,
`AlgebraicGeometry.FormalSpace.exists_lift_of_pointsULift_pullback_of_isRepresentableEtale`
builds the lift directly, without knowing that the fibre product is a formal algebraic space,
and the lift is adic by this library's Stacks 0AQ0.

## Main results

* `isJointlyRigSurjective_of_isRepresentableEtale_of_isJointlySurjective`: a jointly surjective
  family of representable étale morphisms of formal algebraic spaces is jointly rig-surjective.

## References

* [Stacks Project, Tag 0AQQ](https://stacks.math.columbia.edu/tag/0AQQ)
* [Stacks Project, Tag 0AQU](https://stacks.math.columbia.edu/tag/0AQU)
* [Stacks Project, Tag 0AQV](https://stacks.math.columbia.edu/tag/0AQV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u v

attribute [local instance] sheaf_hasColimits

/-- **A jointly surjective family of representable étale morphisms of formal algebraic spaces
is jointly rig-surjective.** Every adic morphism `p : Spf R ⟶ V` out of the formal spectrum of
a complete discrete valuation ring lifts, over an extension `R ⊂ R'` of complete discrete
valuation rings, to an adic morphism into one member of the family.

The residue field of `R` gives a point of `Spf R`; joint surjectivity catches its image in a
member `vⱼ`, so the fibre product `Spf R ×_V Vⱼ` has a point, and
`AlgebraicGeometry.FormalSpace.exists_lift_of_pointsULift_pullback_of_isRepresentableEtale`
turns that point into the lift. The lift is adic by this library's Stacks 0AQ0, through
`isRepresentableByAlgebraicSpacesULift_of_comp_eq_formalSpectrumMap_comp`. -/
theorem isJointlyRigSurjective_of_isRepresentableEtale_of_isJointlySurjective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {V : FppfSheaf B S hS}
    {J : Type v} (Vj : J → FppfSheaf B S hS) (v : ∀ j, Vj j ⟶ V)
    (hVj : ∀ j, IsFormalAlgebraicSpace B S hS (Vj j))
    (hv : ∀ j, IsRepresentableEtale B S hS (v j))
    (hcover : IsJointlySurjective B S hS Vj v) :
    IsJointlyRigSurjective B S hS Vj v := by
  classical
  intro R _ _ _ _ _ _ hRadic hRcomplete hRweak D p hp
  have hRcard := mk_lt_cutoff_of_quotientSystem hRadic hRcomplete D
  -- the point of `Spf R` given by its residue field
  have hmR : TopologicalRing.IsWeakIdealOfDefinition (IsLocalRing.maximalIdeal R) :=
    TopologicalRing.isWeakIdealOfDefinition_of_isAdic hRadic
  have zpt : Space.pointsULift.{u + 1} B S hS (formalSpectrum D).obj :=
    Space.FieldValuedPointULift.class B S hS (formalSpectrum D).obj
      { carrier := R ⧸ IsLocalRing.maximalIdeal R
        field := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
        contained := D.inSite ⟨IsLocalRing.maximalIdeal R, hmR⟩
        toBase := D.overS ⟨IsLocalRing.maximalIdeal R, hmR⟩
        value := Sheaf.sectionEquiv (C := BigFppfOver B S hS)
          (X := (BigAffineFppf.inclusion B S hS).obj
            (D.stage ⟨IsLocalRing.maximalIdeal R, hmR⟩))
          (F := formalSpectrum D) (BigFppfOver.topology B S hS)
          (formalSpectrumInclusion D ⟨IsLocalRing.maximalIdeal R, hmR⟩) }
  -- the member of the family which catches its image in `V`, and a point of the fibre product
  obtain ⟨j, xpt, hxpt⟩ :=
    hcover (Space.pointsMapULift.{u + 1} B S hS (formalSpectrum D).obj p.hom zpt)
  have hsq : IsPullback (pullback.fst p (v j)) (pullback.snd p (v j)) p (v j) :=
    IsPullback.of_hasPullback p (v j)
  obtain ⟨zZ, -, -⟩ := Space.exists_point_of_isPullbackULift B S hS
    (hsq.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))) zpt xpt hxpt.symm
  -- the lift through `vⱼ`
  obtain ⟨R', hR'ring, hR'dom, hR'dvr, hR'alg, hR'ext, hR'top, hR'topring, hR'lin, hR'adic,
    hR'complete, D', e, y, he, hy⟩ :=
    exists_lift_of_pointsULift_pullback_of_isRepresentableEtale (v j) (hv j) hRadic hRweak hRcard
      D p zZ
  let : CommRing R' := hR'ring
  let : IsDomain R' := hR'dom
  let : IsDiscreteValuationRing R' := hR'dvr
  let : Algebra R R' := hR'alg
  let : IsDiscreteValuationRing.IsExtension R R' := hR'ext
  let : TopologicalSpace R' := hR'top
  let : IsTopologicalRing R' := hR'topring
  let : IsLinearTopology R' R' := hR'lin
  -- the lift is adic
  have hR'weak : TopologicalRing.IsWeaklyAdmissible R' :=
    TopologicalRing.isWeaklyAdmissible_of_isAdic hR'adic hR'complete
  have hyadic : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS y.hom :=
    isRepresentableByAlgebraicSpacesULift_of_comp_eq_formalSpectrumMap_comp B S hS hRadic
      hR'adic hR'complete hRweak hR'weak (v j) (hVj j) e he hp hy
  exact ⟨R', hR'ring, hR'dom, hR'dvr, hR'alg, hR'ext, hR'top, hR'topring, hR'lin, hR'adic,
    hR'complete, D', e, j, y, he, hyadic, hy⟩

end AlgebraicGeometry.FormalSpace

end
