module

public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.ProjectionChain
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Comparison

/-!
# One step of the chain of projections, as a projection of the smaller projective space

Let `W ≤ V` be a submodule and let `P ≤ W` be a submodule of it. The image `P.map W.subtype` of
`P` in `V` is a submodule of `V` contained in `W`, and the projection of `𝐏(V)` away from it is
the projection away from `W` followed by the projection of `𝐏(W)` away from `P`:

`𝐏(V) ⇢ 𝐏(W) ⇢ 𝐏(P)`

the target of the composite being `𝐏(P)` rather than `𝐏(P.map W.subtype)`, which the
identification of `P` with its image in `V` repairs.

This is the step the proof of Stacks 0B0E runs its induction along, in the form the induction
consumes: the centre of the next projection is a point `p` of the *current* projective space
`𝐏(W)`, so the next submodule of `V` is the image in `V` of the hyperplane
`pointSubmodule k ↥W p` of `W`, and what has to be known is that projecting away from that image
is the same as projecting away from `W` and then away from `p`.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.mapSubtypeEquiv`: the identification of a submodule
  of a submodule with its image in the ambient module.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.gradedSymAlgMap_subtype_comp_subtype`: the
  factorization on symmetric algebras, which is where the identification enters.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.mapDomain_comp_subtype_eq`: the projection away from
  `P.map W.subtype` and the composite of the two projections are defined on the same open.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_comp_eq_projection_map_subtype`: the
  factorization of the morphisms of schemes, for a scheme mapping into both domains of
  definition.

## Implementation notes

**Why the identification is needed at all.** The target of the second projection is `𝐏(P)` for
`P` a submodule of `W`, while the target of the projection away from `P.map W.subtype` is
`𝐏(P.map W.subtype)`. The two modules are different types, carrying the same vector space, and
`Submodule.equivMapOfInjective` identifies them; the isomorphism of projective spaces it induces
is `AlgebraicGeometry.ProjectiveSpaceOfModule.mapOfLinearEquiv` of
`StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.ProjectionChain`, and the conclusion of
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_comp_eq_projection_map_subtype` carries it.

**Why `exists_projection_eq_comp` is not used.** That lemma factors the projection away from a
submodule `W'` of `V` through the projection away from a larger submodule `W`, with second factor
the morphism induced by `AlgebraicGeometry.ProjectiveSpaceOfModule.chainSymAlgMap`. Identifying
that second factor with a projection of `𝐏(W)` means identifying
`Submodule.comap W.subtype W'` with a submodule of `W` given in advance, which is an equality of
submodules standing between two different types. Taking the submodule `P` of `W` as the datum and
`P.map W.subtype` as what is derived avoids it: the factorization of graded homomorphisms is then
`SymPow.gradedSymAlgMap_comp` applied to `W.subtype ∘ₗ P.subtype`, with the identification
appearing only in degree one.

**The two factorizations.** The homomorphism `Sym(P) ⟶ Sym(V)` induced by the composite inclusion
`P ⟶ W ⟶ V` factors in two ways: through `Sym(W)`, whose morphism is the projection away from
`W`, and through `Sym(P.map W.subtype)`, whose morphism is the projection away from
`P.map W.subtype`. Tag 01MZ, in the form
`Stacks.AlgebraicGeometry.RelativeProjMapComp.mapHom_comp_of_eq`, reads a morphism off each, and
the two are composed. The second factorization has an isomorphism for its inner factor, which is
why its domain of definition is everything
(`Stacks.AlgebraicGeometry.ProjShared.mapDomain_eq_top_of_irrelevant_le_map`) and why its outer
domain of definition is the whole domain of definition of the composite
(`AlgebraicGeometry.ProjectiveSpaceOfModule.mapDomain_comp_subtype_eq`); the morphism it
contributes is `Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop` of the isomorphism, which
`Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop_eq_map` identifies with `Proj.map`, hence with
`mapOfLinearEquiv`.

## References

* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
* [Stacks Project, Tag 0B1N](https://stacks.math.columbia.edu/tag/0B1N)
* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.RelativeProj

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- **A submodule of a submodule, identified with its image in the ambient module.** For
`P ≤ W ≤ V` the inclusion of `W` in `V` carries `P` isomorphically onto `P.map W.subtype`. -/
public def mapSubtypeEquiv (W : Submodule k V) (P : Submodule k ↥W) :
    ↥P ≃ₗ[k] ↥(P.map W.subtype) :=
  Submodule.equivMapOfInjective W.subtype (Submodule.injective_subtype W) P

/-- The composite inclusion `P ⟶ W ⟶ V` is the inclusion of the image of `P` in `V`, preceded by
the identification of `P` with that image. -/
public theorem subtype_comp_subtype_eq (W : Submodule k V) (P : Submodule k ↥W) :
    W.subtype ∘ₗ P.subtype =
      (P.map W.subtype).subtype ∘ₗ (mapSubtypeEquiv k V W P).toLinearMap := by
  ext x
  exact (Submodule.coe_equivMapOfInjective_apply W.subtype
    (Submodule.injective_subtype W) P x).symm

/-- **The factorization on symmetric algebras.** The graded homomorphism induced by the composite
inclusion `P ⟶ W ⟶ V` is both the one of the inclusion of `W` after the one of the inclusion of
`P`, and the one of the inclusion of `P.map W.subtype` after the isomorphism identifying `P` with
that image. -/
public theorem gradedSymAlgMap_subtype_comp_subtype (W : Submodule k V) (P : Submodule k ↥W) :
    (SymPow.gradedSymAlgMap W.subtype).comp (SymPow.gradedSymAlgMap P.subtype) =
      (SymPow.gradedSymAlgMap (P.map W.subtype).subtype).comp
        (SymPow.gradedSymAlgMap (mapSubtypeEquiv k V W P).toLinearMap) := by
  rw [← SymPow.gradedSymAlgMap_comp, ← SymPow.gradedSymAlgMap_comp,
    subtype_comp_subtype_eq k V W P]

/-- The isomorphism identifying `P` with its image in `V` induces a graded homomorphism which is
defined everywhere. -/
public theorem mapDomain_mapSubtypeEquiv_eq_top (W : Submodule k V) (P : Submodule k ↥W) :
    mapDomain (fun n => SymPow.symmetricPower n k ↥P)
        (fun n => SymPow.symmetricPower n k ↥(P.map W.subtype))
        (SymPow.gradedSymAlgMap (mapSubtypeEquiv k V W P).toLinearMap) = ⊤ :=
  mapDomain_eq_top_of_irrelevant_le_map _ _ _
    (irrelevant_le_map_gradedSymAlgMap_of_surjective (mapSubtypeEquiv k V W P).surjective)

/-- **The composite of the two projections is defined exactly where the projection away from the
image is.** The graded homomorphism of the composite inclusion `P ⟶ W ⟶ V` has the same domain of
definition as the one of the inclusion of `P.map W.subtype`, because the two differ by an
isomorphism, which is defined everywhere. -/
public theorem mapDomain_comp_subtype_eq (W : Submodule k V) (P : Submodule k ↥W) :
    mapDomain (fun n => SymPow.symmetricPower n k ↥P)
        (fun n => SymPow.symmetricPower n k V)
        ((SymPow.gradedSymAlgMap (P.map W.subtype).subtype).comp
          (SymPow.gradedSymAlgMap (mapSubtypeEquiv k V W P).toLinearMap)) =
      projectionDomain k V (P.map W.subtype) := by
  rw [Stacks.AlgebraicGeometry.ProjTwistChain.mapDomain_comp,
    mapDomain_mapSubtypeEquiv_eq_top]
  simp

/-- **One step of the chain of projections of Stacks 0B0E.** Let `P ≤ W ≤ V` and let `X` be a
scheme mapping into the domain of definition of the projection away from `W` and into that of the
projection away from the image of `P` in `V`, compatibly with the two inclusions into `𝐏(V)`.
Then `X` maps into the domain of definition of the projection of `𝐏(W)` away from `P`, over the
projection of `X` away from `W`, and the projection of `X` away from `P.map W.subtype` is the
projection away from `P` of that, followed by the isomorphism `𝐏(P) ≅ 𝐏(P.map W.subtype)`. -/
public theorem exists_comp_eq_projection_map_subtype (W : Submodule k V) (P : Submodule k ↥W)
    {X : Scheme.{u}} (jW : X ⟶ (projectionDomain k V W).toScheme)
    (j : X ⟶ (projectionDomain k V (P.map W.subtype)).toScheme)
    (hj : j ≫ (projectionDomain k V (P.map W.subtype)).ι =
      jW ≫ (projectionDomain k V W).ι) :
    ∃ jP : X ⟶ (projectionDomain k ↥W P).toScheme,
      jP ≫ (projectionDomain k ↥W P).ι = jW ≫ projection k V W ∧
        j ≫ projection k V (P.map W.subtype) =
          jP ≫ projection k ↥W P ≫ (mapOfLinearEquiv (mapSubtypeEquiv k V W P)).inv := by
  have heq := gradedSymAlgMap_subtype_comp_subtype k V W P
  have hdom := mapDomain_mapSubtypeEquiv_eq_top k V W P
  have hU := (congrArg (mapDomain (fun n => SymPow.symmetricPower n k ↥P)
    (fun n => SymPow.symmetricPower n k V)) heq).trans (mapDomain_comp_subtype_eq k V W P)
  obtain ⟨q, hq, hqmap⟩ :=
    Stacks.AlgebraicGeometry.RelativeProjMapComp.mapHom_comp_of_eq _ _ _
      (SymPow.gradedSymAlgMap P.subtype) (SymPow.gradedSymAlgMap W.subtype) rfl
      (mapDomain_comp_le _ _ _ (SymPow.gradedSymAlgMap P.subtype)
        (SymPow.gradedSymAlgMap W.subtype))
  obtain ⟨q', hq', hqmap'⟩ :=
    Stacks.AlgebraicGeometry.RelativeProjMapComp.mapHom_comp_of_eq _ _ _
      (SymPow.gradedSymAlgMap (mapSubtypeEquiv k V W P).toLinearMap)
      (SymPow.gradedSymAlgMap (P.map W.subtype).subtype) heq
      (Stacks.AlgebraicGeometry.RelativeProjMapComp.mapDomain_comp_le_of_eq _ _ _ _ _ heq)
  have hjmid : (j ≫ ((projectiveSpaceOfModule k V).isoOfEq hU).inv) ≫
      (mapDomain (fun n => SymPow.symmetricPower n k ↥P)
        (fun n => SymPow.symmetricPower n k V)
        ((SymPow.gradedSymAlgMap W.subtype).comp (SymPow.gradedSymAlgMap P.subtype))).ι =
      j ≫ (projectionDomain k V (P.map W.subtype)).ι := by
    rw [Category.assoc, Scheme.isoOfEq_inv_ι]
  have hjW : (j ≫ ((projectiveSpaceOfModule k V).isoOfEq hU).inv) ≫
      (projectiveSpaceOfModule k V).homOfLE
        (mapDomain_comp_le _ _ _ (SymPow.gradedSymAlgMap P.subtype)
          (SymPow.gradedSymAlgMap W.subtype)) = jW := by
    rw [← cancel_mono (projectionDomain k V W).ι, Category.assoc, Scheme.homOfLE_ι, hjmid, hj]
  have hjW' : (j ≫ ((projectiveSpaceOfModule k V).isoOfEq hU).inv) ≫
      (projectiveSpaceOfModule k V).homOfLE
        (Stacks.AlgebraicGeometry.RelativeProjMapComp.mapDomain_comp_le_of_eq _ _ _
          (SymPow.gradedSymAlgMap (mapSubtypeEquiv k V W P).toLinearMap)
          (SymPow.gradedSymAlgMap (P.map W.subtype).subtype) heq) = j := by
    rw [← cancel_mono (projectionDomain k V (P.map W.subtype)).ι, Category.assoc,
      Scheme.homOfLE_ι, hjmid]
  have hsplit := topIso_inv_isoOfEq_hom_ι _ _
    (SymPow.gradedSymAlgMap (mapSubtypeEquiv k V W P).toLinearMap) hdom
  have hsplit' : (mapDomain _ _
        (SymPow.gradedSymAlgMap (mapSubtypeEquiv k V W P).toLinearMap)).ι ≫
      (Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ hdom.symm).hom = 𝟙 _ := by
    rw [← cancel_mono (mapDomain _ _
      (SymPow.gradedSymAlgMap (mapSubtypeEquiv k V W P).toLinearMap)).ι]
    simp only [Category.assoc]
    rw [hsplit]
    simp
  have hmap : mapHomOfTop _ _ _ hdom = (mapOfLinearEquiv (mapSubtypeEquiv k V W P)).hom :=
    mapHomOfTop_eq_map _ _ _
      (irrelevant_le_map_gradedSymAlgMap_of_surjective (mapSubtypeEquiv k V W P).surjective) hdom
  have hitop : (mapDomain _ _
        (SymPow.gradedSymAlgMap (mapSubtypeEquiv k V W P).toLinearMap)).ι ≫
      mapHomOfTop _ _ _ hdom =
      Stacks.AlgebraicGeometry.ProjTwistChain.mapHom _ _
        (SymPow.gradedSymAlgMap (mapSubtypeEquiv k V W P).toLinearMap) := by
    have h := congrArg (fun g => g ≫ Stacks.AlgebraicGeometry.ProjTwistChain.mapHom _ _
      (SymPow.gradedSymAlgMap (mapSubtypeEquiv k V W P).toLinearMap)) hsplit'
    simpa [mapHomOfTop] using h
  refine ⟨(j ≫ ((projectiveSpaceOfModule k V).isoOfEq hU).inv) ≫ q, ?_, ?_⟩
  · rw [Category.assoc, hq, ← Category.assoc, hjW]
    rfl
  · have hLW : (j ≫ ((projectiveSpaceOfModule k V).isoOfEq hU).inv) ≫ q' ≫
          (mapDomain _ _ (SymPow.gradedSymAlgMap (mapSubtypeEquiv k V W P).toLinearMap)).ι =
        j ≫ projection k V (P.map W.subtype) := by
      rw [hq', ← Category.assoc, hjW']
      rfl
    have key : j ≫ projection k V (P.map W.subtype) ≫
        (mapOfLinearEquiv (mapSubtypeEquiv k V W P)).hom =
        ((j ≫ ((projectiveSpaceOfModule k V).isoOfEq hU).inv) ≫ q) ≫ projection k ↥W P := by
      rw [← hmap]
      have h1 : j ≫ projection k V (P.map W.subtype) ≫ mapHomOfTop _ _ _ hdom =
          ((j ≫ ((projectiveSpaceOfModule k V).isoOfEq hU).inv) ≫ q' ≫
            (mapDomain _ _ (SymPow.gradedSymAlgMap (mapSubtypeEquiv k V W P).toLinearMap)).ι) ≫
            mapHomOfTop _ _ _ hdom := by
        rw [hLW, Category.assoc]
      rw [h1]
      simp only [Category.assoc]
      rw [hitop, ← hqmap', hqmap]
      rfl
    have hpost := congrArg (fun g => g ≫ (mapOfLinearEquiv (mapSubtypeEquiv k V W P)).inv) key
    simpa [Category.assoc] using hpost

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
