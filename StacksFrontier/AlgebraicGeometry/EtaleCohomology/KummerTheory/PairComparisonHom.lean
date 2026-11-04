module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerTransportTrivialization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.PairComparisonMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.TrivializationTorsorAdditivity
public import StacksFrontier.AlgebraicGeometry.Picard.BaseAssociatedModuleRightUnitor

/-!
# The comparison map of Tag 040Q is a homomorphism

`AlgebraicGeometry.basePairCohomologyClass` carries the isomorphism class of a pair `(ℒ, α)` on a
scheme `S` to the class in `H¹((Sch/S)_τ, μ_n)` of the torsor of trivializations of the
transported pair.  Its source is an abelian group under the tensor product of pairs
(`AlgebraicGeometry.instAddCommGroupPairClasses`) and its target is an abelian group, being an
`Ext¹`.  This file shows the map is a homomorphism between them.

The content is that the transport to the big `τ`-site carries the tensor product of pairs to the
tensor product of pairs — `Stacks.SheafOfModules.TensorPowerTransport.transportTriv_tensor` at the
associated-module functor of Descent, Proposition 03DX — together with the additivity of the
class of the torsor of trivializations in the pair,
`AlgebraicGeometry.trivializationTorsor_class_add`.

## Main definitions

* `AlgebraicGeometry.basePairCohomologyClassHom`: **the comparison map of Tag 040Q as a
  homomorphism of abelian groups** `PairClasses S n →+ H¹((Sch/S)_τ, μ_n)`.

## Main results

* `AlgebraicGeometry.basePairTriv_tensor`: **the transported trivialization of a tensor product
  of pairs is the tensor product of the two transported trivializations**, on the big `τ`-site of
  `S`.  This is part (4) of the second construction of Tag 040Q, and the first use the four
  coherences of `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso'` have had.
* `AlgebraicGeometry.basePairClass_tensor`: **a tensor product of pairs has the torsor of
  trivializations of the tensor product of the two transported pairs.**
* `AlgebraicGeometry.basePairCohomologyClass_add`: the comparison map is additive, read on
  classes of pairs.

## Implementation notes

The scheme enters `Stacks.SheafOfModules.TensorPowerTransport.transportTriv_tensor` as
`Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite`, which is the ringed site
`AlgebraicGeometry.tensorPair` is written over, so the trivialization of a tensor product of
pairs is the `Stacks.Cohomology.Torsors.Generators.tensorTriv` the generic statement asks for
with no transport.  The four coherences are stated over `S.presheaf` and
`AlgebraicGeometry.SmallEtale.zariskiStructureIsSheaf`, while that ringed site presents them as
`(schemeRingedSite S).O.obj` and
`(Stacks.SheafOfModules.Tensor.ringSheaf (schemeRingedSite S).O).2`; the first pair is the same
term and the second is a second proof of one proposition, so by proof irrelevance no transport
appears and the instantiation is an application.

Four retypings are re-enabled rather than restated: the invertibility of a sheaf of modules on a
scheme at the `schemeRingedSite` spelling, the invertibility of a transported pair sheaf at the
two spellings `AlgebraicGeometry.basePairSheaf` and `(baseAssociatedModule _).obj _`, and the two
sheafification instances of the big `τ`-site at the `(schemeFunctionsRingedSite _ _ _).J`
spelling that `AlgebraicGeometry.trivializationTorsor` asks for.  All are `local instance`s where
they are declared, except `AlgebraicGeometry.basePairSheaf_isInvertible`, which is a theorem.

The invertibility of the transported *tensor product* is supplied by a `letI` in the statement
rather than by instance search: the module there is
`(baseAssociatedModule _).obj (tensorSheaf S.presheaf (ringSheafCond S) _ _)`, and
`AlgebraicGeometry.basePairSheaf` does not unfold to it at instance transparency — the pair whose
sheaf it is, `AlgebraicGeometry.tensorPair`, is reached only through a structure projection of a
plain definition.  That `letI` has to be written at the `S.presheaf` spelling and not as
`tensorSheafOfModules (schemeRingedSite S)`: the latter reaches `S.presheaf` only by unfolding
`Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite`, which is a plain definition, so a
local instance stated that way is not matched either.

## References

* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.AlgebraicGeometry.ReflexiveModules (schemeRingedSite)
open Stacks.Cohomology.Torsors (torsorSetoid torsorIsoClassesEquivH1)
open Stacks.Cohomology.Torsors.Generators (tpow powerMap tensorTriv tensorSheafOfModules
  LocalRoots)
open Stacks.SheafOfModules (IsInvertible)
open Stacks.SheafOfModules.TensorPowerTransport (transportTriv_tensor)

universe w u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (τ : SiteKind) (n : ℕ)

-- The invertibility of a sheaf of modules on a scheme retyped for the ringed site of the scheme,
-- the invertibility of a transported pair sheaf at its two spellings, and the two sheafification
-- retypings of the big `τ`-site at the spelling `AlgebraicGeometry.trivializationTorsor` asks
-- for.  Each is declared elsewhere, so the attribute is re-enabled here rather than any of them
-- repeated.
attribute [local instance] isInvertible_schemeRingedSite basePairSheaf_isInvertible
  basePairSheafObj_isInvertible baseSchemeFunctions_hasWeakSheafify
  baseSchemeFunctions_wEqualsLocallyBijective

/-- **The transported trivialization of a tensor product of pairs is the tensor product of the
two transported trivializations**, on the big `τ`-site of `S`.

This is part (4) of the second construction of Tag 040Q: it is
`Stacks.SheafOfModules.TensorPowerTransport.transportTriv_tensor` at the associated-module functor
of Descent, Proposition 03DX, whose four coherences are
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso'_natural`,
`_associator`, `_braiding` and `_rightUnitor`. -/
@[stacks 040Q "the transport to the big tau-site carries the tensor product of pairs to the \
tensor product of pairs"]
public theorem basePairTriv_tensor (P Q : TrivializedPower S n) :
    letI := basePairSheaf_isInvertible B S hS τ n P
    letI := basePairSheaf_isInvertible B S hS τ n Q
    letI : IsInvertible (BigFppfOver.baseRingedSite B S hS τ).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O).2
        ((BigFppfOver.baseAssociatedModule B S hS τ).obj
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨S.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf
              (forget₂ CommRingCat RingCat) (ringSheafCond S)⟩).obj P.sheaf).obj Q.sheaf))) :=
      basePairSheaf_isInvertible B S hS τ n (tensorPair S n P Q)
    letI : IsInvertible (BigFppfOver.baseRingedSite B S hS τ).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O).2
        (tensorSheafOfModules (BigFppfOver.baseRingedSite B S hS τ)
          ((BigFppfOver.baseAssociatedModule B S hS τ).obj P.sheaf)
          ((BigFppfOver.baseAssociatedModule B S hS τ).obj Q.sheaf)) :=
      Stacks.SheafOfModules.isInvertible_tensorSheaf
        (BigFppfOver.baseRingedSite B S hS τ).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O).2
        (basePairSheaf B S hS τ n P) (basePairSheaf B S hS τ n Q)
    powerMap (BigFppfOver.baseRingedSite B S hS τ)
          (BigFppfOver.baseAssociatedModuleTensorIso' B S hS τ P.sheaf Q.sheaf) n ≪≫
        tensorTriv (BigFppfOver.baseRingedSite B S hS τ) (basePairSheaf B S hS τ n P)
          (basePairSheaf B S hS τ n Q) n (basePairTriv B S hS τ n P)
          (basePairTriv B S hS τ n Q) =
      basePairTriv B S hS τ n (tensorPair S n P Q) :=
  let := P.invertible
  let := Q.invertible
  transportTriv_tensor (schemeRingedSite S) (BigFppfOver.baseRingedSite B S hS τ)
    (BigFppfOver.baseAssociatedModule B S hS τ)
    (BigFppfOver.baseAssociatedModulePicardUnitIso B S hS τ)
    (BigFppfOver.baseAssociatedModuleTensorIso' B S hS τ)
    (BigFppfOver.baseAssociatedModuleTensorIso'_natural B S hS τ)
    (BigFppfOver.baseAssociatedModuleTensorIso'_associator B S hS τ)
    (BigFppfOver.baseAssociatedModuleTensorIso'_braiding B S hS τ)
    (BigFppfOver.baseAssociatedModuleTensorIso'_rightUnitor B S hS τ)
    P.sheaf Q.sheaf n P.trivialization Q.trivialization

variable [HasSheafify (BigFppfOver.baseOverTopology B S hS τ) AddCommGrpCat.{u}]
  [HasExt.{w} (Sheaf (BigFppfOver.baseOverTopology B S hS τ) AddCommGrpCat.{u})]

omit [HasSheafify (BigFppfOver.baseOverTopology B S hS τ) AddCommGrpCat.{u}]
  [HasExt.{w} (Sheaf (BigFppfOver.baseOverTopology B S hS τ) AddCommGrpCat.{u})] in
/-- **A tensor product of pairs has the torsor of trivializations of the tensor product of the
two transported pairs.**  This is
`AlgebraicGeometry.trivializationTorsor_class_eq_of_iso'` fed the object-level tensor comparison
of the associated-module functor and `AlgebraicGeometry.basePairTriv_tensor`. -/
@[stacks 040Q "the torsor of trivializations of a tensor product of pairs"]
public theorem basePairClass_tensor (hroot : LocalRoots (BigFppfOver.baseRingedSite B S hS τ) n)
    (P Q : TrivializedPower S n) :
    Quotient.mk
          (torsorSetoid (rootsOfUnitySheaf (BigFppfOver.baseOverTopology B S hS τ)
            (BigFppfOver.toScheme B S hS) (unitsPresheaf_isSheaf_base B S hS τ) n))
          (trivializationTorsor (BigFppfOver.baseOverTopology B S hS τ)
            (BigFppfOver.toScheme B S hS) (BigFppfOver.baseRingedSite B S hS τ).O.property
            (unitsPresheaf_isSheaf_base B S hS τ) n
            (baseRingedSite_isLocallyRinged B S hS τ) hroot
            (basePairSheaf B S hS τ n (tensorPair S n P Q))
            (basePairSheaf_isInvertible B S hS τ n (tensorPair S n P Q))
            (basePairTriv B S hS τ n (tensorPair S n P Q))) =
      Quotient.mk
        (torsorSetoid (rootsOfUnitySheaf (BigFppfOver.baseOverTopology B S hS τ)
          (BigFppfOver.toScheme B S hS) (unitsPresheaf_isSheaf_base B S hS τ) n))
        (trivializationTorsor (BigFppfOver.baseOverTopology B S hS τ)
          (BigFppfOver.toScheme B S hS) (BigFppfOver.baseRingedSite B S hS τ).O.property
          (unitsPresheaf_isSheaf_base B S hS τ) n
          (baseRingedSite_isLocallyRinged B S hS τ) hroot
          (tensorSheafOfModules (BigFppfOver.baseRingedSite B S hS τ)
            (basePairSheaf B S hS τ n P) (basePairSheaf B S hS τ n Q))
          (Stacks.SheafOfModules.isInvertible_tensorSheaf
            (BigFppfOver.baseRingedSite B S hS τ).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O).2
            (basePairSheaf B S hS τ n P) (basePairSheaf B S hS τ n Q))
          (tensorTriv (BigFppfOver.baseRingedSite B S hS τ) (basePairSheaf B S hS τ n P)
            (basePairSheaf B S hS τ n Q) n (basePairTriv B S hS τ n P)
            (basePairTriv B S hS τ n Q))) :=
  trivializationTorsor_class_eq_of_iso' (BigFppfOver.baseOverTopology B S hS τ)
    (BigFppfOver.toScheme B S hS) (BigFppfOver.baseRingedSite B S hS τ).O.property
    (unitsPresheaf_isSheaf_base B S hS τ) n (baseRingedSite_isLocallyRinged B S hS τ) hroot
    (basePairSheaf B S hS τ n (tensorPair S n P Q))
    (tensorSheafOfModules (BigFppfOver.baseRingedSite B S hS τ)
      (basePairSheaf B S hS τ n P) (basePairSheaf B S hS τ n Q))
    (basePairSheaf_isInvertible B S hS τ n (tensorPair S n P Q))
    (Stacks.SheafOfModules.isInvertible_tensorSheaf
      (BigFppfOver.baseRingedSite B S hS τ).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O).2
      (basePairSheaf B S hS τ n P) (basePairSheaf B S hS τ n Q))
    (basePairTriv B S hS τ n (tensorPair S n P Q))
    (tensorTriv (BigFppfOver.baseRingedSite B S hS τ) (basePairSheaf B S hS τ n P)
      (basePairSheaf B S hS τ n Q) n (basePairTriv B S hS τ n P) (basePairTriv B S hS τ n Q))
    (BigFppfOver.baseAssociatedModuleTensorIso' B S hS τ P.sheaf Q.sheaf)
    (basePairTriv_tensor B S hS τ n P Q)

/-- **The comparison map of Tag 040Q is additive**, read on classes of pairs: the class of a
tensor product of pairs is the sum of the two classes. -/
@[stacks 040Q "the comparison map is additive on classes of pairs"]
public theorem basePairCohomologyClass_add
    (hroot : LocalRoots (BigFppfOver.baseRingedSite B S hS τ) n) (P Q : TrivializedPower S n) :
    basePairCohomologyClass B S hS τ n hroot (pairClass P + pairClass Q) =
      basePairCohomologyClass B S hS τ n hroot (pairClass P) +
        basePairCohomologyClass B S hS τ n hroot (pairClass Q) :=
  (congrArg (torsorIsoClassesEquivH1 _) (basePairClass_tensor B S hS τ n hroot P Q)).trans
    (trivializationTorsor_class_add (BigFppfOver.baseOverTopology B S hS τ)
      (BigFppfOver.toScheme B S hS) (BigFppfOver.baseRingedSite B S hS τ).O.property
      (unitsPresheaf_isSheaf_base B S hS τ) n (baseRingedSite_isLocallyRinged B S hS τ) hroot
      (basePairSheaf B S hS τ n P) (basePairSheaf B S hS τ n Q)
      (basePairSheaf_isInvertible B S hS τ n P) (basePairSheaf_isInvertible B S hS τ n Q)
      (basePairTriv B S hS τ n P) (basePairTriv B S hS τ n Q)).symm

/-- **The comparison map of Tag 040Q as a homomorphism of abelian groups**,
`PairClasses S n →+ H¹((Sch/S)_τ, μ_n)`.  The addition of the source is the tensor product of
pairs and that of the target is the addition of `Ext¹`; additivity is
`AlgebraicGeometry.basePairCohomologyClass_add`, and the vanishing at the zero class follows from
it, the two groups being groups.

This is the map `Stacks.Kummer.bijective_of_comparison` consumes. -/
@[stacks 040Q "the comparison map from the isomorphism classes of pairs to H^1 of the roots of \
unity as a homomorphism of abelian groups; injectivity and surjectivity are not proved here"]
public def basePairCohomologyClassHom
    (hroot : LocalRoots (BigFppfOver.baseRingedSite B S hS τ) n) :
    PairClasses S n →+
      Sheaf.H (rootsOfUnitySheaf (BigFppfOver.baseOverTopology B S hS τ)
        (BigFppfOver.toScheme B S hS) (unitsPresheaf_isSheaf_base B S hS τ) n) 1 :=
  AddMonoidHom.mk' (basePairCohomologyClass B S hS τ n hroot) fun x y =>
    Quotient.inductionOn₂ x y fun P Q => basePairCohomologyClass_add B S hS τ n hroot P Q

/-- The comparison homomorphism of Tag 040Q has the comparison map of
`AlgebraicGeometry.basePairCohomologyClass` underneath it. -/
public theorem basePairCohomologyClassHom_apply
    (hroot : LocalRoots (BigFppfOver.baseRingedSite B S hS τ) n) (x : PairClasses S n) :
    basePairCohomologyClassHom B S hS τ n hroot x =
      basePairCohomologyClass B S hS τ n hroot x := rfl

end AlgebraicGeometry

end
