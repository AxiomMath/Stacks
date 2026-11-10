module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasChartRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasJointSurjectivity
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTargetRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Surjective

/-!
# The discussion of Definition 0AIM

Let `S` be a scheme contained in a big fppf site `B`. Section 87.11 of the Stacks project
(**Stacks 0AIL**, "Formal algebraic spaces") introduces Definition 0AIM and follows it with an
unlabelled discussion making three assertions:

1. *Sanity check:* an affine formal algebraic space is a formal algebraic space.
2. In the situation of the definition, the morphisms `Xᵢ ⟶ X` are representable (by schemes),
   by Lemma 0AIG.
3. By Bootstrap, Lemma 04S1, one could, instead of asking `∐ Xᵢ ⟶ X` to be surjective as a map
   of sheaves, require it to be surjective.

This file proves all three, and records with them the remark that an affine formal algebraic
space is quasi-compact, its own identity being a surjective representable étale chart.

## Main results

* `AlgebraicGeometry.FormalSpace.isQuasiCompactSpace_of_isAffineFormalAlgebraicSpace`: an affine
  formal algebraic space is a quasi-compact formal algebraic space.
* `AlgebraicGeometry.FormalSpace.isSurjectiveOnSchemeBaseChanges_sigmaDesc_of_isLocallySurjective`:
  for a family as in Definition 0AIM, if `∐ Xᵢ ⟶ X` is a surjection of sheaves, then it is
  surjective.
* `AlgebraicGeometry.FormalSpace.isLocallySurjective_sigmaDesc_of_isSurjectiveOnSchemeBaseChanges`:
  for a family as in Definition 0AIM, if `∐ Xᵢ ⟶ X` is surjective, then it is a surjection of
  sheaves.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_iff_surjective_atlas`: the
  reformulation of Definition 0AIM with surjectivity in place of surjectivity as a map of
  sheaves.
* `AlgebraicGeometry.FormalSpace.formalAlgebraicSpaces_discussion`: **Stacks 0AIL**, the
  three assertions of the discussion together.

## Implementation notes

*Surjective* is the notion of this library for morphisms of fppf sheaves:
`AlgebraicGeometry.FormalSpace.IsSurjectiveOnSchemeBaseChanges` asks every base change along a
scheme of the site mapping to the target to be surjective, which for a representable morphism
is exactly surjectivity in the sense of Bootstrap, Section 046E (the base changes being the
schemes `T ×_X ∐ Xᵢ ⟶ T`). The source justifies this phrasing by saying that `∐ Xᵢ ⟶ X` is
representable. In this library an atlas is indexed by a type of `Type (u + 1)`, and the morphism
out of the coproduct of such a family is not representable by objects of the site in general:
the base change of `∐_{i ∈ I} X ⟶ X` (every member the identity of an affine formal algebraic
space `X`) along a point `h_T ⟶ X` is `I` copies of `T`, which has more points than a scheme of
the site once `I` is large enough. The condition of base changes along schemes is meaningful
without representability, and it is the one used here; the representability of the individual
members, which the source also asserts, is assertion (2).

The forward implication of (3) is the base change of a surjection of sheaves, which is
surjective on points. The backward implication is the content of Bootstrap, Lemma 04S1: a point
of `X` lifts to a point of `∐ Xᵢ`, hence of some `Xᵢ`, and a family of representable étale
morphisms out of affine formal algebraic spaces which is jointly surjective on points is a
surjection of sheaves out of the coproduct
(`AlgebraicGeometry.FormalSpace.isLocallySurjective_sigmaDesc_of_jointly_surjective_points`).

## References

* [Stacks Project, Tag 0AIL](https://stacks.math.columbia.edu/tag/0AIL)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIG](https://stacks.math.columbia.edu/tag/0AIG)
* [Stacks Project, Tag 04S1](https://stacks.math.columbia.edu/tag/04S1)
* [Stacks Project, Tag 0AJ9](https://stacks.math.columbia.edu/tag/0AJ9)
* [Stacks Project, Tag 0AJA](https://stacks.math.columbia.edu/tag/0AJA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An affine formal algebraic space over `S` is a quasi-compact formal algebraic space over
`S`: its identity is a morphism from an affine formal algebraic space which is representable
by algebraic spaces, étale and a surjection of sheaves. -/
theorem isQuasiCompactSpace_of_isAffineFormalAlgebraicSpace {X : FppfSheaf B S hS}
    (hX : IsAffineFormalAlgebraicSpace B S hS X) : IsQuasiCompactSpace B S hS X :=
  ⟨hX.1, X, 𝟙 X, hX, isRepresentableEtale_id B S hS X, inferInstance⟩

/-- **A surjection of sheaves out of a coproduct is surjective.** If `∐ Xᵢ ⟶ X` is a surjection
of fppf sheaves then every base change of it along a scheme of the site mapping to `X` is
surjective: it is surjective on points, and surjectivity on points is stable under base
change. -/
theorem isSurjectiveOnSchemeBaseChanges_sigmaDesc_of_isLocallySurjective {X : FppfSheaf B S hS}
    {I : Type (u + 1)} {Xi : I → FppfSheaf B S hS} (f : ∀ i, Xi i ⟶ X)
    (hf : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc f)) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    IsSurjectiveOnSchemeBaseChanges B S hS (Sigma.desc f) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  exact fun _ _ _ _ _ sq ↦
    IsSurjective.of_isPullback B S hS sq (isSurjective_of_isLocallySurjective B S hS hf)

/-- **Bootstrap, Lemma 04S1, for a family as in Definition 0AIM.** Let `fᵢ : Xᵢ ⟶ X` be a family
of morphisms of fppf sheaves whose sources are affine formal algebraic spaces and which are
representable by algebraic spaces and étale. If `∐ Xᵢ ⟶ X` is surjective, that is, each of its
base changes along a scheme of the site mapping to `X` is surjective, then it is a surjection
of sheaves.

A point of `X` is the image of a point of `∐ Xᵢ`, and every point of the coproduct is the image
of a point of one summand, because the identity of the coproduct is the morphism induced by the
coproduct inclusions. So the family is jointly surjective on points, and a family of
representable étale morphisms out of affine formal algebraic spaces which is jointly surjective
on points induces a surjection of sheaves out of the coproduct. -/
theorem isLocallySurjective_sigmaDesc_of_isSurjectiveOnSchemeBaseChanges
    {X : FppfSheaf B S hS} {I : Type (u + 1)} {Xi : I → FppfSheaf B S hS} (f : ∀ i, Xi i ⟶ X)
    (haffine : ∀ i, IsAffineFormalAlgebraicSpace B S hS (Xi i))
    (hetale : ∀ i, IsRepresentableEtale B S hS (f i))
    (hf : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      IsSurjectiveOnSchemeBaseChanges B S hS (Sigma.desc f)) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    Sheaf.IsLocallySurjective (Sigma.desc f) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have hsurj : IsSurjective B S hS (Sigma.desc f) :=
    isSurjective_of_isSurjectiveOnAffineBaseChanges B S hS _ fun T _ g W p q sq ↦ hf T g W p q sq
  have hid : Sigma.desc (fun i ↦ Sigma.ι Xi i) = 𝟙 (∐ Xi) :=
    Sigma.hom_ext _ _ fun i ↦ by rw [Sigma.ι_comp_desc, Category.comp_id]
  have hιsurj : Sheaf.IsLocallySurjective (Sigma.desc (fun i ↦ Sigma.ι Xi i)) := by
    rw [hid]
    infer_instance
  refine isLocallySurjective_sigmaDesc_of_jointly_surjective_points B S hS f haffine hetale
    fun x ↦ ?_
  obtain ⟨z, rfl⟩ := hsurj x
  obtain ⟨i, w, rfl⟩ := exists_pointsMapULift_eq_of_isLocallySurjective_sigmaDesc B S hS
    (fun i ↦ Sigma.ι Xi i) hιsurj z
  refine ⟨i, w, ?_⟩
  have hcomp : (f i).hom = (Sigma.ι Xi i).hom ≫ (Sigma.desc f).hom :=
    congrArg (fun k : Xi i ⟶ X ↦ k.hom) (Sigma.ι_comp_desc f i).symm
  rw [hcomp, Space.pointsMapULift_comp]
  rfl

/-- **Definition 0AIM with surjectivity in place of surjectivity as a map of sheaves.** An fppf
sheaf on the big fppf site of `S` is a formal algebraic space exactly when it satisfies the
set-theoretic condition of Stacks 0AIS and admits a family of maps `fᵢ : Xᵢ ⟶ X` whose sources
are affine formal algebraic spaces, each representable by algebraic spaces and étale, such that
`∐ Xᵢ ⟶ X` is surjective: each of its base changes along a scheme of the site mapping to `X` is
surjective. -/
theorem isFormalAlgebraicSpace_iff_surjective_atlas (X : FppfSheaf B S hS) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    IsFormalAlgebraicSpace B S hS X ↔
      SatisfiesSetTheoreticCondition B S hS X ∧
        ∃ (I : Type (u + 1)) (Xi : I → FppfSheaf B S hS) (f : ∀ i, Xi i ⟶ X),
          (∀ i, IsAffineFormalAlgebraicSpace B S hS (Xi i)) ∧
          (∀ i, ∃ hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f i).hom,
            Space.HasPropertyULift.{u + 1} B S hS
              (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (f i).hom hfi) ∧
          IsSurjectiveOnSchemeBaseChanges B S hS (Sigma.desc f) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  exact ⟨fun ⟨hset, I, Xi, f, haffine, hetale, hsurj⟩ ↦ ⟨hset, I, Xi, f, haffine, hetale,
      isSurjectiveOnSchemeBaseChanges_sigmaDesc_of_isLocallySurjective B S hS f hsurj⟩,
    fun ⟨hset, I, Xi, f, haffine, hetale, hsurj⟩ ↦ ⟨hset, I, Xi, f, haffine, hetale,
      isLocallySurjective_sigmaDesc_of_isSurjectiveOnSchemeBaseChanges B S hS f haffine hetale
        hsurj⟩⟩

/-- **Stacks 0AIL**, the discussion following Definition 0AIM in Section 87.11, "Formal algebraic
spaces". Over a scheme `S` contained in a big fppf site:

1. *(sanity check)* every affine formal algebraic space is a formal algebraic space;
2. in the situation of Definition 0AIM — a family of maps `fᵢ : Xᵢ ⟶ X` of fppf sheaves whose
   sources are affine formal algebraic spaces and which are representable by algebraic spaces
   and étale — every `fᵢ` is representable by schemes, that is, by objects of the site
   (Lemma 0AIG);
3. *(Bootstrap, Lemma 04S1)* Definition 0AIM is unchanged if the requirement that `∐ Xᵢ ⟶ X` be
   surjective as a map of sheaves is replaced by the requirement that it be surjective, meaning
   that each of its base changes along a scheme of the site mapping to `X` is surjective.

The last conjunct records that an affine formal algebraic space is moreover a quasi-compact
formal algebraic space (Definition 0AJA, through condition (3) of Lemma 0AJ9), its identity being
a surjective representable étale chart. -/
@[stacks 0AIL "the unnumbered discussion of Definition 0AIM in the section: an affine formal \
algebraic space is a formal algebraic space; the members of a family as in Definition 0AIM are \
representable by schemes; surjectivity of the map from the coproduct as a map of sheaves may be \
replaced by surjectivity (Bootstrap, Lemma 04S1). Also records that an affine formal algebraic \
space is quasi-compact"]
theorem formalAlgebraicSpaces_discussion :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    (∀ X : FppfSheaf B S hS,
      IsAffineFormalAlgebraicSpace B S hS X → IsFormalAlgebraicSpace B S hS X) ∧
    (∀ (X : FppfSheaf B S hS) (I : Type (u + 1)) (Xi : I → FppfSheaf B S hS)
      (f : ∀ i, Xi i ⟶ X), (∀ i, IsAffineFormalAlgebraicSpace B S hS (Xi i)) →
      (∀ i, ∃ hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f i).hom,
        Space.HasPropertyULift.{u + 1} B S hS
          (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (f i).hom hfi) →
      ∀ i, uliftYoneda.{u + 1}.relativelyRepresentable (f i).hom) ∧
    (∀ X : FppfSheaf B S hS,
      IsFormalAlgebraicSpace B S hS X ↔
        SatisfiesSetTheoreticCondition B S hS X ∧
          ∃ (I : Type (u + 1)) (Xi : I → FppfSheaf B S hS) (f : ∀ i, Xi i ⟶ X),
            (∀ i, IsAffineFormalAlgebraicSpace B S hS (Xi i)) ∧
            (∀ i, ∃ hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f i).hom,
              Space.HasPropertyULift.{u + 1} B S hS
                (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (f i).hom hfi) ∧
            IsSurjectiveOnSchemeBaseChanges B S hS (Sigma.desc f)) ∧
    (∀ X : FppfSheaf B S hS,
      IsAffineFormalAlgebraicSpace B S hS X → IsQuasiCompactSpace B S hS X) :=
  ⟨fun _ hX ↦ isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hX,
    fun _ _ _ f haffine hetale i ↦ relativelyRepresentable_of_isEtale_of_isAffineFormal B S hS
      (f i) (haffine i) (hetale i).1 (hetale i).2,
    isFormalAlgebraicSpace_iff_surjective_atlas B S hS,
    fun _ hX ↦ isQuasiCompactSpace_of_isAffineFormalAlgebraicSpace B S hS hX⟩

end AlgebraicGeometry.FormalSpace

end
