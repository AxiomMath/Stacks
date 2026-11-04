module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.FieldTheory.AlgebraicClosure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointStalkMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.EtaleStalkFunctor

/-!
# Domination of geometric points over a common point, and independence of the étale stalk

Two geometric points of a scheme `S` with the same image in `S` are both dominated by a third
geometric point: the fibre product of their sources over `S` has a point over that common
image, and an algebraic closure of its residue field receives both.  Since a morphism of
geometric points induces an isomorphism of étale stalk functors, the étale stalk functor at a
geometric point therefore depends only on the point of `S` beneath it, up to a canonical
isomorphism.

## Main definitions

* `AlgebraicGeometry.etaleStalkPresheafFunctorIsoOfEqBase` — the isomorphism of étale stalk
  functors at two geometric points with the same image in `S`.

## Main results

* `AlgebraicGeometry.GeometricPoint.exists_dominating` — two geometric points with the same
  image in `S` are dominated by a third.
* `AlgebraicGeometry.etaleStalkPresheafFunctorIsoOfEqBase_naturality` — naturality of that
  isomorphism in the presheaf.

## References

* [Stacks Project, Tag 04FN](https://stacks.math.columbia.edu/tag/04FN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

namespace GeometricPoint

/-- Two geometric points of `S` lying over the same point of `S` are both dominated by a
third: take an algebraic closure of the residue field at a point of the fibre product of
their sources over `S`, which is nonempty exactly because the two points have the same
image. -/
public theorem exists_dominating {S : Scheme.{u}} {p q : GeometricPoint S}
    (h : p.hom default = q.hom default) :
    ∃ r : GeometricPoint S,
      Nonempty (GeometricPoint.Hom r p) ∧ Nonempty (GeometricPoint.Hom r q) := by
  let P := pullback p.hom q.hom
  obtain ⟨t, ht₁, ht₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := p.hom) (g := q.hom) (default : Spec (.of p.residueField))
    (default : Spec (.of q.residueField)) h
  let K := AlgebraicClosure (P.residueField t)
  let : Field K := inferInstance
  let : IsAlgClosed K := inferInstance
  let v : Spec (.of K) ⟶ P :=
    Spec.map (CommRingCat.ofHom (algebraMap (P.residueField t) K)) ≫ P.fromSpecResidueField t
  let r : GeometricPoint S :=
    ⟨K, v ≫ pullback.fst p.hom q.hom ≫ p.hom⟩
  refine ⟨r, ⟨⟨v ≫ pullback.fst p.hom q.hom, rfl⟩⟩, ?_⟩
  refine ⟨⟨v ≫ pullback.snd p.hom q.hom, ?_⟩⟩
  simpa only [Category.assoc] using
    congrArg (fun f => v ≫ f) pullback.condition.symm

end GeometricPoint

/-- The étale stalk functors at two geometric points of `S` with the same image in `S` are
isomorphic, by comparing both with the stalk functor at a common dominating geometric
point. -/
public noncomputable def etaleStalkPresheafFunctorIsoOfEqBase (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {p q : GeometricPoint S}
    (h : p.hom default = q.hom default) (A : Type v) [Category.{w} A]
    [HasColimitsOfSize.{u, u} A] :
    etaleStalkPresheafFunctor B S hS p A ≅ etaleStalkPresheafFunctor B S hS q A := by
  let a : GeometricPoint.Hom (GeometricPoint.exists_dominating h).choose p :=
    (GeometricPoint.exists_dominating h).choose_spec.1.some
  let b : GeometricPoint.Hom (GeometricPoint.exists_dominating h).choose q :=
    (GeometricPoint.exists_dominating h).choose_spec.2.some
  let : IsIso (geometricPointStalkMap B S hS a A) := geometricPointStalkMap_isIso B S hS a A
  let : IsIso (geometricPointStalkMap B S hS b A) := geometricPointStalkMap_isIso B S hS b A
  exact asIso (geometricPointStalkMap B S hS a A) ≪≫
    (asIso (geometricPointStalkMap B S hS b A)).symm

/-- The isomorphism of étale stalk functors at two geometric points with the same image in `S`
is natural in the presheaf. -/
public theorem etaleStalkPresheafFunctorIsoOfEqBase_naturality (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {p q : GeometricPoint S}
    (h : p.hom default = q.hom default) (A : Type v) [Category.{w} A]
    [HasColimitsOfSize.{u, u} A] {P Q : (SmallEtale B S hS)ᵒᵖ ⥤ A} (α : P ⟶ Q) :
    (etaleStalkPresheafFunctorIsoOfEqBase B S hS h A).hom.app P ≫
        (etaleStalkPresheafFunctor B S hS q A).map α =
      (etaleStalkPresheafFunctor B S hS p A).map α ≫
        (etaleStalkPresheafFunctorIsoOfEqBase B S hS h A).hom.app Q :=
  ((etaleStalkPresheafFunctorIsoOfEqBase B S hS h A).hom.naturality α).symm

end AlgebraicGeometry

end
