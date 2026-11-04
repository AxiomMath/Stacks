module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceCriteria
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.MorphismOfAffines
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSitePostcomposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteFormalAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.GeneralReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactFiniteRefinement
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFlatPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticTransfer
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpacesEtaleIdentification
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedCoproductEtale
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FiniteCoproducts
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedQuasiCompactPoints
public import StacksFrontier.CategoryTheory.Sites.LocallySurjectiveBaseChange
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfSchemeThickenings
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceCriteriaReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticDescentRepresentable

/-!
# Criteria for quasi-compactness of formal algebraic spaces

For a formal algebraic space `X` over `S` with a reduction `Xred`, the following are equivalent:
`Xred` is a quasi-compact algebraic space; `X` admits an atlas indexed by a finite type; `X` is
quasi-compact. On an algebraic space, the quasi-compactness of formal algebraic spaces agrees
with the quasi-compactness of algebraic spaces.

## Main results

* `hasFiniteFormalAtlas_of_isQuasiCompactSpaceULift_of_isReduction`: a formal algebraic space
  whose reduction is a quasi-compact algebraic space has a finite formal atlas.
* `IsQuasiCompactSpace.isQuasiCompactSpaceULift_reduction_space`: the reduction of a
  quasi-compact formal algebraic space is a quasi-compact algebraic space.
* `tfae_isQuasiCompactSpace_of_isReduction_unconditional`: the three conditions are equivalent
  at an arbitrary reduction.
* `tfae_isQuasiCompactSpace_of_isFormalAlgebraicSpace`: the three conditions are equivalent at
  the reduction `reduction`.
* `quasiCompactSpaceAgreesOnAlgebraicSpaces`: an algebraic space is a quasi-compact formal
  algebraic space exactly when it is a quasi-compact algebraic space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The implication (1) ⇒ (2) -/

/-- Let `X` be a formal algebraic space over `S` and let `i : Xred ⟶ X` be a reduction of `X`
whose source is a quasi-compact algebraic space. Then `X` has a finite formal atlas.

Finitely many members of the atlas as in Definition 0AIM which `X` carries are already jointly
surjective on points, by
`AlgebraicGeometry.FormalSpace.exists_finite_jointly_surjective_of_isQuasiCompactSpaceULift`;
what remains is that such a finite subfamily is itself an atlas as in Definition 0AIM, that is
that its induced morphism out of the coproduct is a surjection of sheaves. That morphism is
representable by algebraic spaces and étale by
`AlgebraicGeometry.FormalSpace.coproductsRepresentableEtale'`, hence flat and locally of finite
presentation; joint surjectivity on points is surjectivity on points of it, which for a morphism
representable by algebraic spaces is surjectivity in the sense of Stacks 03XZ by
`AlgebraicGeometry.FormalSpace.hasPropertyULift_isSurjectiveULift_iff`; and Stacks 05VM turns a
representable surjective flat cover into a surjection of sheaves. -/
@[stacks 0AJ9 "the implication (1) ⇒ (2)"]
theorem hasFiniteFormalAtlas_of_isQuasiCompactSpaceULift_of_isReduction
    {X Xred : FppfSheaf B S hS} {i : Xred ⟶ X} (hX : IsFormalAlgebraicSpace B S hS X)
    (hi : IsReduction B S hS X Xred i)
    (h : Space.IsQuasiCompactSpaceULift.{u + 1} B S hS Xred.obj) :
    HasFiniteFormalAtlas' B S hS X := by
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨hset, I, Xi, f, haffine, hetale, hsurjective⟩ := hX
  obtain ⟨t, ht⟩ := exists_finite_jointly_surjective_of_isQuasiCompactSpaceULift B S hS hi h
    hetale hsurjective
  refine ⟨hset, {j : I // j ∈ t}, fun j ↦ Xi j.1, fun j ↦ f j.1, inferInstance,
    fun j ↦ haffine j.1, fun j ↦ hetale j.1, ?_⟩
  obtain ⟨hrep, hetale'⟩ := coproductsRepresentableEtale' B S hS {j : I // j ∈ t}
    (fun j ↦ Xi j.1) X (fun j ↦ f j.1) inferInstance fun j ↦ hetale j.1
  refine isLocallySurjective_of_surjective_flat B S hS _ hrep ?_
    (hasPropertyULift_flat_of_isEtale B S hS _ hrep hetale')
    (hasPropertyULift_locallyOfFinitePresentation_of_isEtale B S hS _ hrep hetale')
  refine (hasPropertyULift_isSurjectiveULift_iff
    (Sigma.desc fun j : {j : I // j ∈ t} ↦ f j.1).hom hrep).mpr fun p ↦ ?_
  obtain ⟨j, hjt, z, hz⟩ := ht p
  have hι : (Sigma.ι (fun j : {j : I // j ∈ t} ↦ Xi j.1) ⟨j, hjt⟩).hom ≫
      (Sigma.desc fun j : {j : I // j ∈ t} ↦ f j.1).hom = (f j).hom := by
    have hcomp : (Sigma.ι (fun j : {j : I // j ∈ t} ↦ Xi j.1) ⟨j, hjt⟩ ≫
        Sigma.desc fun j : {j : I // j ∈ t} ↦ f j.1).hom = (f j).hom := by
      rw [Sigma.ι_desc]
    exact hcomp
  refine ⟨Space.pointsMapULift.{u + 1} B S hS (Xi j).obj
    (Sigma.ι (fun j : {j : I // j ∈ t} ↦ Xi j.1) ⟨j, hjt⟩).hom z, ?_⟩
  refine ((Space.pointsMapULift_comp_apply B S hS
    (Sigma.ι (fun j : {j : I // j ∈ t} ↦ Xi j.1) ⟨j, hjt⟩).hom
    (Sigma.desc fun j : {j : I // j ∈ t} ↦ f j.1).hom z).symm.trans ?_)
  rw [hι]
  exact hz

/-- The reduction `reduction` of a quasi-compact formal algebraic space over `S` is a
quasi-compact algebraic space.

This is `AlgebraicGeometry.FormalSpace.IsQuasiCompactSpace.isQuasiCompactSpaceULift_of_isReduction`
read at the reduction `AlgebraicGeometry.FormalSpace.reduction` that Stacks 0AIN produces, the
formal algebraic space being the source's own hypothesis on `X` and being implied by condition
(3). Condition (1) of the source names the reduction of `X`, so the statement mentions it; any
other reduction is canonically isomorphic to this one by
`AlgebraicGeometry.FormalSpace.Reduction.iso`, and the general statement applies to it directly,
so nothing depends on the choice. -/
@[stacks 0AJ9 "the implication (3) ⇒ (1)"]
theorem IsQuasiCompactSpace.isQuasiCompactSpaceULift_reduction_space {X : FppfSheaf B S hS}
    (h : IsQuasiCompactSpace B S hS X) :
    Space.IsQuasiCompactSpaceULift.{u + 1} B S hS
      (liftSheaf B S hS
        (reduction B S hS X (IsQuasiCompactSpace.isFormalAlgebraicSpace B S hS h)).space).obj :=
  IsQuasiCompactSpace.isQuasiCompactSpaceULift_of_isReduction B S hS
    (reduction B S hS X (IsQuasiCompactSpace.isFormalAlgebraicSpace B S hS h)).isReduction h

/-- Let `X` be a formal algebraic space over `S` and let `i : Xred ⟶ X` be a reduction of `X`.
The following are equivalent:

1. `Xred` is a quasi-compact algebraic space,
2. `X` admits an atlas as in Definition 0AIM indexed by a finite type,
3. `X` receives a morphism from an affine formal algebraic space which is representable by
   algebraic spaces, étale and a surjection of sheaves. -/
theorem tfae_isQuasiCompactSpace_of_isReduction_unconditional
    {X Xred : FppfSheaf B S hS} {i : Xred ⟶ X}
    (hX : IsFormalAlgebraicSpace B S hS X) (hi : IsReduction B S hS X Xred i) :
    [Space.IsQuasiCompactSpaceULift.{u + 1} B S hS Xred.obj,
      HasFiniteFormalAtlas' B S hS X,
      IsQuasiCompactSpace B S hS X].TFAE := by
  tfae_have 1 → 2 :=
    hasFiniteFormalAtlas_of_isQuasiCompactSpaceULift_of_isReduction B S hS hX hi
  tfae_have 2 → 3 := HasFiniteFormalAtlas.isQuasiCompactSpace' B S hS
  tfae_have 3 → 1 := IsQuasiCompactSpace.isQuasiCompactSpaceULift_of_isReduction B S hS hi
  tfae_finish

/-- Let `X` be a formal algebraic space over `S`. The following are equivalent:

1. the reduction `reduction` of `X` is a quasi-compact algebraic space,
2. `X` admits an atlas as in Definition 0AIM indexed by a finite type,
3. `X` receives a morphism from an affine formal algebraic space which is representable by
   algebraic spaces, étale and a surjection of sheaves.

Condition (1) is read at the reduction `AlgebraicGeometry.FormalSpace.reduction` that
Stacks 0AIN produces; by `AlgebraicGeometry.FormalSpace.Reduction.iso` any two reductions of
`X` are canonically isomorphic, so the condition does not depend on the choice, and
`AlgebraicGeometry.FormalSpace.tfae_isQuasiCompactSpace_of_isReduction_unconditional` is the same
equivalence at an arbitrary reduction. -/
@[stacks 0AJ9 "the equivalence of the three conditions"]
theorem tfae_isQuasiCompactSpace_of_isFormalAlgebraicSpace
    {X : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X) :
    [Space.IsQuasiCompactSpaceULift.{u + 1} B S hS
        (liftSheaf B S hS (reduction B S hS X hX).space).obj,
      HasFiniteFormalAtlas' B S hS X,
      IsQuasiCompactSpace B S hS X].TFAE :=
  tfae_isQuasiCompactSpace_of_isReduction_unconditional B S hS hX
    (reduction B S hS X hX).isReduction

/-! ### Comparison with the quasi-compactness of Stacks 03E3 -/

/-- `QuasiCompactSpaceAgreesOnAlgebraicSpaces` holds: an fppf sheaf which is an algebraic space
over `S` is a quasi-compact formal algebraic space over `S` exactly when it is a quasi-compact
algebraic space over `S` in the sense of Stacks 03E3, quasi-compactness of the formal algebraic
space being taken in the form of condition (3) of Stacks 0AJ9.

For the forward implication the reduction of the sheaf is a quasi-compact algebraic space by the
implication (3) ⇒ (1) of Stacks 0AJ9, and the inclusion of a reduction is bijective — in
particular surjective — on points, so Stacks 040W, part (1) makes the sheaf itself quasi-compact.

For the converse Stacks 03H6 supplies an *affine* surjective étale chart `U` of the algebraic
space. The sheaf it represents is an affine formal algebraic space by the constant presentation,
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_sheafifiedYoneda'`; the chart is
representable by algebraic spaces because a scheme-valued point of an algebraic space is (see
`SetTheoreticDescent.isRepresentableByAlgebraicSpacesULift_point_of_isAlgebraicSpace`),
and it is étale after every represented base change, étaleness of a morphism out of a
representable being the same as étaleness after every represented base change; being also
surjective on points, flat and locally of finite presentation, it is a surjection of sheaves by
Stacks 05VM. That single chart is an atlas as in Definition 0AIM over a one-point index type, so
the set-theoretic condition of Stacks 0AIS comes from
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_countable_atlas`, and condition
(3) of Stacks 0AJ9 holds. -/
theorem quasiCompactSpaceAgreesOnAlgebraicSpaces :
    QuasiCompactSpaceAgreesOnAlgebraicSpaces B S hS := by
  let : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  intro W hW
  refine ⟨fun h => ?_, fun h => ?_⟩
  · -- the reduction is quasi-compact and is surjective on points
    exact Space.isQuasiCompactSpaceULift_of_isSurjectiveULift B S hS
      (reduction B S hS W
        (IsQuasiCompactSpace.isFormalAlgebraicSpace B S hS h)).isReduction.algebraic hW
      (reduction B S hS W (IsQuasiCompactSpace.isFormalAlgebraicSpace B S hS h)).inclusion.hom
      (reduction B S hS W (IsQuasiCompactSpace.isFormalAlgebraicSpace B S hS
        h)).isReduction.bijective_pointsMapULift.2
      (IsQuasiCompactSpace.isQuasiCompactSpaceULift_reduction_space B S hS h)
  · -- Stacks 03H6 supplies an affine surjective étale chart, which is the atlas of condition (3)
    obtain ⟨U, a, hUaff, hsurj, hetale⟩ :=
      Space.exists_affine_chart_of_isQuasiCompactSpaceULift.{u + 1} B S hS hW h
    let Z : FppfSheaf B S hS := yonedaSheaf B S hS U
    let c : Z ⟶ W := ObjectProperty.homMk a
    have hZaff : IsAffineFormalAlgebraicSpace B S hS Z :=
      isAffineFormalAlgebraicSpace_of_iso B S hS
        ((Sheaf.sheafifiedYonedaIsoUliftYoneda' (BigFppfOver.topology B S hS)).app U)
        (isAffineFormalAlgebraicSpace_sheafifiedYoneda' B S hS U hUaff)
    have hcrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS c.hom :=
      SetTheoreticDescent.isRepresentableByAlgebraicSpacesULift_point_of_isAlgebraicSpace
        B S hS hW a
    have hrel := (Space.isEtaleULift_iff_relative_etale.{u + 1} B S hS a).mp hetale
    have hcet : Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) c.hom hcrep :=
      fun _ ξ _ φ hφ => Space.relative_comp B S hS hφ
        (Space.relative_of_isPullback B S hS (IsPullback.of_hasPullback ξ a) hrel)
    have hcsurj : Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsSurjectiveULift.{u + 1} B S hS g.hom) c.hom hcrep :=
      (hasPropertyULift_isSurjectiveULift_iff c.hom hcrep).mpr
        (Space.surjective_pointsMapULift_of_relative_surjective.{u + 1} B S hS hW a hsurj)
    have hls : Sheaf.IsLocallySurjective c :=
      isLocallySurjective_of_surjective_flat B S hS c.hom hcrep hcsurj
        (hasPropertyULift_flat_of_isEtale B S hS c.hom hcrep hcet)
        (hasPropertyULift_locallyOfFinitePresentation_of_isEtale B S hS c.hom hcrep hcet)
    have hone : Sheaf.IsLocallySurjective (Sigma.desc (fun _ : PUnit.{u + 2} ↦ c)) := by
      have hc : Epi c := (Sheaf.isLocallySurjective_iff_epi c).mp hls
      have hcomp : Epi (Sigma.ι (fun _ : PUnit.{u + 2} ↦ Z) PUnit.unit ≫
          Sigma.desc (fun _ : PUnit.{u + 2} ↦ c)) := by
        rw [Sigma.ι_desc]
        exact hc
      exact (Sheaf.isLocallySurjective_iff_epi _).mpr
        (epi_of_epi (Sigma.ι (fun _ : PUnit.{u + 2} ↦ Z) PUnit.unit) _)
    exact ⟨satisfiesSetTheoreticCondition_of_countable_atlas B S hS W
      (fun _ : PUnit.{u + 2} ↦ Z) (fun _ ↦ c) ⟨fun _ ↦ hZaff, fun _ ↦ ⟨hcrep, hcet⟩, hone⟩,
      Z, c, hZaff, ⟨hcrep, hcet⟩, hls⟩

/-! ### Stacks 0AJA, the definition

A formal algebraic space is *quasi-compact* when the equivalent conditions of Stacks 0AJ9 hold.
This notion is `AlgebraicGeometry.FormalSpace.IsQuasiCompactSpace`, condition (3) of that lemma;
its equivalence with conditions (1) and (2), which is what makes the choice of condition
immaterial and so makes this a definition rather than a choice, is `tfae_isQuasiCompactSpace`. -/

add_to_stacks 0AJA "the definition, realized by condition (3) of Stacks 0AJ9, \
`AlgebraicGeometry.FormalSpace.IsQuasiCompactSpace`; the equivalence with conditions (1) and \
(2) that makes the choice of condition immaterial is `tfae_isQuasiCompactSpace`, which is \
unconditional"
  AlgebraicGeometry.FormalSpace.IsQuasiCompactSpace

end AlgebraicGeometry.FormalSpace

end
