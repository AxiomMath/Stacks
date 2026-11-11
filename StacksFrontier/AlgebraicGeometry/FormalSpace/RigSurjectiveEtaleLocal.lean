module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Surjective
import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatComposition
import StacksFrontier.RingTheory.DiscreteValuationRing.EppCondition
import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissibleAdic

/-!
# Rig-surjectivity along a jointly rig-surjective étale cover, with explicit inputs

Let `S` be a scheme contained in a big fppf site `B`, let `f : X ⟶ Y` be a morphism of fppf
sheaves over `S` which is locally of finite type, and let `{gᵢ : Yᵢ ⟶ Y}` be a family of
representable étale morphisms which is jointly surjective on points. This file defines joint
rig-surjectivity and joint surjectivity of such a family, and proves that `f` is rig-surjective
if and only if every base change `fᵢ : X ×_Y Yᵢ ⟶ Yᵢ` is, given two general inputs as explicit
arguments (see below).

**Stacks 0AQV** itself, with both inputs proved, is
`AlgebraicGeometry.FormalSpace.isRigSurjective_iff_forall_pullback_snd_of_isRepresentableEtale`
in `StacksFrontier.AlgebraicGeometry.FormalSpace.JointlyRigSurjectiveEtale`.

The forward direction is stability of rig-surjectivity under base change, which is
Stacks 0AQS. For the converse an adic point `Spf R ⟶ Y` out of a complete discrete valuation
ring is first lifted, after an extension `R ⊂ R'` of complete discrete valuation rings, to an
adic point of one member `Yᵢ` of the family, and then lifted through `fᵢ` after a further
extension `R' ⊂ R''`; the projection `X ×_Y Yᵢ ⟶ X` turns that into a lift through `f` and the
two extensions compose to the single extension the definition asks for.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsJointlyRigSurjective`: a family of morphisms is *jointly
  rig-surjective* when every adic point of the common target out of a complete discrete
  valuation ring lifts, after an extension of complete discrete valuation rings, to an adic
  point of one member of the family. This is the content of Stacks 0AQU for the coproduct of
  the family, together with the factorization of a point of the coproduct through a summand.

## Main results

* `AlgebraicGeometry.FormalSpace.isRigSurjective_iff_forall_pullback_snd`: the equivalence
  above, with the two inputs as arguments.

## Implementation notes

Joint surjectivity of `{gᵢ}` is expressed as surjectivity of the map from the disjoint union of
the point sets of the sources onto the point set of the target, which is the pointwise form of
surjectivity of `∐ gᵢ` because `AlgebraicGeometry.FormalSpace.IsSurjective` is surjectivity on
points of `StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedPoints`. Writing it this way avoids
the coproduct of fppf sheaves, which is not needed anywhere else in the statement.

The base change `fᵢ` is `CategoryTheory.Limits.pullback.snd f (g i)`, the projection of
`X ×_Y Yᵢ` to `Yᵢ`.

The locally Noetherian hypotheses on `X`, `Y` and the `Yᵢ` are omitted, exactly as in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveBaseChange`: they enter Definition
0AQQ only through the identification of adicness with representability, and
`AlgebraicGeometry.FormalSpace.IsRigSurjective` already takes adicness in the representable
form.

### The two explicit inputs

`hetaleFiniteType` is the assertion that a morphism of fppf sheaves which is representable by
algebraic spaces and étale is locally of finite type (Stacks 0AJG read through
Definition 0AM4); the library proves it as
`AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteType.of_isRepresentableEtale`.

`h0AQU` is the assertion that a family of representable étale morphisms whose disjoint union is
surjective on points is jointly rig-surjective: Stacks 0AQU applied to `∐ gᵢ`, together with
the factorization of an adic point of a coproduct through a summand. The library proves it, for
families of formal algebraic spaces, as
`isJointlyRigSurjective_of_isRepresentableEtale_of_isJointlySurjective`.

## References

* [Stacks Project, Tag 0AJG](https://stacks.math.columbia.edu/tag/0AJG)
* [Stacks Project, Tag 0AQQ](https://stacks.math.columbia.edu/tag/0AQQ)
* [Stacks Project, Tag 0AQS](https://stacks.math.columbia.edu/tag/0AQS)
* [Stacks Project, Tag 0AQU](https://stacks.math.columbia.edu/tag/0AQU)
* [Stacks Project, Tag 0AQV](https://stacks.math.columbia.edu/tag/0AQV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u v

/-- A family of morphisms `v j : V j ⟶ V` of formal algebraic spaces over `S` is *jointly
rig-surjective* when every adic morphism to `V` out of the formal spectrum of a complete
discrete valuation ring `R` lifts to some member of the family along the formal spectrum of an
extension `R ⊂ R'` of complete discrete valuation rings, by an adic morphism. For a single
morphism this is Definition 0AQQ; for a family it is Definition 0AQQ for `∐ v j` together with
the factorization of an adic point of the coproduct through one summand. -/
abbrev IsJointlyRigSurjective (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V : FppfSheaf B S hS} {J : Type v} (Vj : J → FppfSheaf B S hS)
    (v : ∀ j, Vj j ⟶ V) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R],
    IsAdic (IsLocalRing.maximalIdeal R) → IsAdicComplete (IsLocalRing.maximalIdeal R) R →
      ∀ (hR : TopologicalRing.IsWeaklyAdmissible R) (D : QuotientSystem B S hS R)
        (p : formalSpectrum D ⟶ V),
        Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS p.hom →
          ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
            (_ : Algebra R R') (_ : IsDiscreteValuationRing.IsExtension R R')
            (_ : TopologicalSpace R') (_ : IsTopologicalRing R') (_ : IsLinearTopology R' R'),
            IsAdic (IsLocalRing.maximalIdeal R') ∧
              IsAdicComplete (IsLocalRing.maximalIdeal R') R' ∧
                ∃ (D' : QuotientSystem B S hS R') (e : ContinuousHom D D') (j : J)
                  (y : formalSpectrum D' ⟶ Vj j),
                  e.toRingHom = algebraMap R R' ∧
                    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS y.hom ∧
                      y ≫ v j = formalSpectrumMap hR e ≫ p

/-- A family of morphisms of fppf sheaves is *jointly surjective on points* when every point of
the common target is the image of a point of one of the sources. This is the pointwise form of
surjectivity of the coproduct morphism `∐ v j ⟶ V`, surjectivity of a morphism of formal
algebraic spaces being surjectivity on points. It is
`AlgebraicGeometry.Space.IsJointlySurjective` for presheaves taking values in `Type (u + 1)`,
and stands to it as `AlgebraicGeometry.FormalSpace.IsSurjective` stands to
`AlgebraicGeometry.Space.IsSurjective`. -/
abbrev IsJointlySurjective (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V : FppfSheaf B S hS} {J : Type v} (Vj : J → FppfSheaf B S hS)
    (v : ∀ j, Vj j ⟶ V) : Prop :=
  ∀ q : Space.pointsULift.{u + 1} B S hS V.obj,
    ∃ (j : J) (x : Space.pointsULift.{u + 1} B S hS (Vj j).obj),
      Space.pointsMapULift.{u + 1} B S hS (Vj j).obj (v j).hom x = q

/-- **Rig-surjectivity is étale local on the target, from explicit inputs.** Let `f : X ⟶ Y` be a
morphism of fppf sheaves over `S` which is locally of finite type and let `{gᵢ : Yᵢ ⟶ Y}` be a
family of representable étale morphisms which is jointly surjective on points. Given that
representable étale morphisms are locally of finite type (`hetaleFiniteType`) and that jointly
surjective families of representable étale morphisms are jointly rig-surjective (`h0AQU`), `f`
is rig-surjective exactly when each base change `X ×_Y Yᵢ ⟶ Yᵢ` is rig-surjective.

The forward direction is Stacks 0AQS. For the converse an adic point of `Y` out of a complete
discrete valuation ring is lifted to one `Yᵢ` over an extension of complete discrete valuation
rings, using that the family is jointly rig-surjective, and then lifted through that base
change over a further extension; the projection to `X` makes the result a lift through `f`, and
the two extensions compose to one.

Both inputs are proved in the library
(`AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteType.of_isRepresentableEtale` and, when the
`Yᵢ` are formal algebraic spaces,
`isJointlyRigSurjective_of_isRepresentableEtale_of_isJointlySurjective`);
**Stacks 0AQV** with them discharged is
`AlgebraicGeometry.FormalSpace.isRigSurjective_iff_forall_pullback_snd_of_isRepresentableEtale`. -/
theorem isRigSurjective_iff_forall_pullback_snd (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {I : Type v} {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (Yi : I → FppfSheaf B S hS) (g : ∀ i, Yi i ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f)
    (hg : ∀ i, IsRepresentableEtale B S hS (g i))
    (hcover : IsJointlySurjective B S hS Yi g)
    (hetaleFiniteType : ∀ {U V : FppfSheaf B S hS} (w : U ⟶ V),
      IsRepresentableEtale B S hS w → IsLocallyOfFiniteType B S hS w)
    (h0AQU : ∀ {V : FppfSheaf B S hS} {J : Type v} (Vj : J → FppfSheaf B S hS)
      (v : ∀ j, Vj j ⟶ V), (∀ j, IsRepresentableEtale B S hS (v j)) →
      IsJointlySurjective B S hS Vj v → IsJointlyRigSurjective B S hS Vj v) :
    IsRigSurjective B S hS f ↔ ∀ i, IsRigSurjective B S hS (pullback.snd f (g i)) := by
  constructor
  · intro hsf i
    exact (IsRigSurjective.of_isPullback B S hS (IsPullback.of_hasPullback f (g i)).flip hf
      (hetaleFiniteType (g i) (hg i)) hsf).2
  · intro hfi R _ _ _ _ _ _ hRadic hRcomplete hRweak D p hp
    obtain ⟨R', hR'ring, hR'dom, hR'dvr, hR'alg, hR'ext, hR'top, hR'topring, hR'lin, hR'adic,
      hR'complete, D', e, i, y, he, hyrep, hy⟩ :=
      h0AQU Yi g hg hcover R hRadic hRcomplete hRweak D p hp
    let : CommRing R' := hR'ring
    let : IsDomain R' := hR'dom
    let : IsDiscreteValuationRing R' := hR'dvr
    let : Algebra R R' := hR'alg
    let : IsDiscreteValuationRing.IsExtension R R' := hR'ext
    let : TopologicalSpace R' := hR'top
    let : IsTopologicalRing R' := hR'topring
    let : IsLinearTopology R' R' := hR'lin
    have hR'weak : TopologicalRing.IsWeaklyAdmissible R' :=
      TopologicalRing.isWeaklyAdmissible_of_isAdic hR'adic hR'complete
    obtain ⟨R'', hR''ring, hR''dom, hR''dvr, hR''alg, hR''ext, hR''top, hR''topring, hR''lin,
      hR''adic, hR''complete, D'', e', x, he', hx⟩ :=
      hfi i R' hR'adic hR'complete hR'weak D' y hyrep
    let : CommRing R'' := hR''ring
    let : IsDomain R'' := hR''dom
    let : IsDiscreteValuationRing R'' := hR''dvr
    let : Algebra R' R'' := hR''alg
    let : IsDiscreteValuationRing.IsExtension R' R'' := hR''ext
    let : TopologicalSpace R'' := hR''top
    let : IsTopologicalRing R'' := hR''topring
    let : IsLinearTopology R'' R'' := hR''lin
    let : Algebra R R'' := ((algebraMap R' R'').comp (algebraMap R R')).toAlgebra
    have halg : (algebraMap R R'' : R →+* R'') = (algebraMap R' R'').comp (algebraMap R R') :=
      RingHom.algebraMap_toAlgebra _
    let : IsScalarTower R R' R'' := IsScalarTower.of_algebraMap_eq fun z => by rw [halg]; rfl
    refine ⟨R'', inferInstance, inferInstance, inferInstance, inferInstance,
      IsDiscreteValuationRing.IsExtension.trans R R' R'', inferInstance, inferInstance,
      inferInstance, hR''adic, hR''complete, D'',
      ContinuousHom.comp hR'weak hRweak e' e, x ≫ pullback.fst f (g i), ?_, ?_⟩
    · rw [ContinuousHom.comp_toRingHom, he', he, halg]
    · calc (x ≫ pullback.fst f (g i)) ≫ f
          = x ≫ pullback.fst f (g i) ≫ f := Category.assoc _ _ _
        _ = x ≫ pullback.snd f (g i) ≫ g i := by rw [pullback.condition]
        _ = (x ≫ pullback.snd f (g i)) ≫ g i := (Category.assoc _ _ _).symm
        _ = (formalSpectrumMap hR'weak e' ≫ y) ≫ g i := by rw [hx]
        _ = formalSpectrumMap hR'weak e' ≫ y ≫ g i := Category.assoc _ _ _
        _ = formalSpectrumMap hR'weak e' ≫ formalSpectrumMap hRweak e ≫ p := by rw [hy]
        _ = (formalSpectrumMap hR'weak e' ≫ formalSpectrumMap hRweak e) ≫ p :=
          (Category.assoc _ _ _).symm
        _ = formalSpectrumMap hRweak (ContinuousHom.comp hR'weak hRweak e' e) ≫ p := by
          rw [formalSpectrumMap_comp_eq hR'weak hRweak e' e]

end AlgebraicGeometry.FormalSpace

end
