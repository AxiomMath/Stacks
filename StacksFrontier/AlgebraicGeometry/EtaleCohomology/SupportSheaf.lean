module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.FieldTheory.AlgebraicClosure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointStalkMap
public import StacksCore.Tactic.StacksAttribute

/-!
# The support of an abelian sheaf on the small étale site

The support of an abelian sheaf on the small étale site of a scheme is the set of points of
the scheme at which some geometric stalk above the point is nonzero.  Since any two geometric
points above a common point of the scheme are dominated by a third, this is the same as the
set of points at which *every* geometric stalk above the point is nonzero.

The coefficient category of the sheaf lives in a universe independent of the universe of the
schemes, so a geometric stalk — a colimit over a category of étale neighborhoods whose objects
live one universe higher — need not exist for the sheaf itself.  The support is therefore
defined using the stalk of the sheaf composed with the universe lift of abelian groups, which
always exists because the neighborhood category has a small cofinal subcategory.  Lifting is
harmless: `AlgebraicGeometry.isZero_etaleStalk_ulift_iff` says that whenever the unlifted
stalk exists, the two vanish together.

## Main definitions

* `AlgebraicGeometry.supportSheaf` — the support of an abelian sheaf on the small étale site.

## Main results

* `AlgebraicGeometry.isZero_etaleStalk_ulift_iff` — lifting the coefficients does not change
  vanishing of a geometric stalk that already exists.
* `AlgebraicGeometry.mem_supportSheaf_iff_exists` — the defining existential criterion for
  membership in the support.
* `AlgebraicGeometry.mem_supportSheaf_iff` — nonvanishing of the geometric stalk is
  independent of the choice of geometric point above the given point, so the support may be
  tested at any one of them.

## References

* [Stacks Project, Tag 04FS](https://stacks.math.columbia.edu/tag/04FS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v

namespace AlgebraicGeometry

open CategoryTheory.Limits

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})

/-- Lifting the values does not change vanishing of an existing geometric stalk. -/
public theorem isZero_etaleStalk_ulift_iff (p : GeometricPoint S)
    [HasColimit ((CategoryOfElements.π (geometricPointFiber B S hS p)).op ⋙
      F.obj)] :
    IsZero (etaleStalk B S hS p (F.obj ⋙ AddCommGrpCat.uliftFunctor.{u, v})) ↔
      IsZero (etaleStalk B S hS p F.obj) := by
  let U := AddCommGrpCat.uliftFunctor.{u, v}
  let e := preservesColimitIso U
    ((CategoryOfElements.π (geometricPointFiber B S hS p)).op ⋙ F.obj) ≪≫
    HasColimit.isoOfNatIso (Functor.associator _ _ _)
  show IsZero (colimit _) ↔ IsZero (colimit _)
  rw [← e.isZero_iff, IsZero.iff_id_eq_zero, ← U.map_id, U.map_eq_zero_iff,
    ← IsZero.iff_id_eq_zero]

/-- The points of a scheme at which a geometric stalk of an abelian étale
sheaf is nonzero. -/
@[stacks 04FS "support_sheaf"]
public def supportSheaf : Set S :=
  { x | ∃ p : GeometricPoint S,
      GeometricPoint.LiesOver p x ∧
        ¬ IsZero (etaleStalk B S hS p
          (F.obj ⋙ AddCommGrpCat.uliftFunctor.{u, v})) }

/-- The defining criterion for membership in the support. -/
@[simp]
public theorem mem_supportSheaf_iff_exists (x : S) :
    x ∈ supportSheaf B S hS F ↔
      ∃ p : GeometricPoint S,
        GeometricPoint.LiesOver p x ∧
          ¬ IsZero (etaleStalk B S hS p
            (F.obj ⋙ AddCommGrpCat.uliftFunctor.{u, v})) :=
  Iff.rfl

/-- Two geometric points of `S` lying over the same point of `S` are both dominated by a
third: take an algebraic closure of the residue field at a point of the fibre product of
their sources over `S`, which is nonempty exactly because the two points have the same
image. -/
private theorem exists_common_geometric_point {p q : GeometricPoint S}
    (h : p.hom default = q.hom default) :
    ∃ r : GeometricPoint S,
      Nonempty (GeometricPoint.Hom r p) ∧
        Nonempty (GeometricPoint.Hom r q) := by
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
  refine ⟨r, ⟨⟨v ≫ pullback.fst p.hom q.hom, rfl⟩⟩, ⟨⟨v ≫ pullback.snd p.hom q.hom, ?_⟩⟩⟩
  simpa only [Category.assoc] using
    congrArg (fun f => v ≫ f) pullback.condition.symm

/-- Nonvanishing of the geometric stalk at two geometric points over the same point of `S`
agree, because both stalks are isomorphic to the stalk at a common dominating point. -/
private theorem geometricStalk_nonzero_iff {p q : GeometricPoint S}
    (h : p.hom default = q.hom default) :
    ¬ IsZero (etaleStalk B S hS p (F.obj ⋙ AddCommGrpCat.uliftFunctor.{u, v})) ↔
      ¬ IsZero (etaleStalk B S hS q (F.obj ⋙ AddCommGrpCat.uliftFunctor.{u, v})) := by
  obtain ⟨r, ⟨a⟩, ⟨b⟩⟩ := exists_common_geometric_point (S := S) h
  have key : ∀ {p r : GeometricPoint S} (a : GeometricPoint.Hom r p),
      IsZero (etaleStalk B S hS p (F.obj ⋙ AddCommGrpCat.uliftFunctor.{u, v})) ↔
        IsZero (etaleStalk B S hS r (F.obj ⋙ AddCommGrpCat.uliftFunctor.{u, v})) := by
    intro p r a
    have := geometricPointStalkMap_isIso B S hS a AddCommGrpCat.{max u v}
    exact ((asIso (geometricPointStalkMap B S hS a AddCommGrpCat.{max u v})).app _).isZero_iff
  exact (key a).not.trans (key b).not.symm

/-- Nonvanishing of a stalk is independent of the geometric point above `x`. -/
@[stacks 04FS "support_sheaf", sga "4 VIII 6.6" "support of a sheaf"]
public theorem mem_supportSheaf_iff (p : GeometricPoint S) (x : S)
    (hp : GeometricPoint.LiesOver p x) :
    x ∈ supportSheaf B S hS F ↔
      ¬ IsZero (etaleStalk B S hS p
        (F.obj ⋙ AddCommGrpCat.uliftFunctor.{u, v})) := by
  rw [mem_supportSheaf_iff_exists]
  refine ⟨fun ⟨q, hq, hq_nonzero⟩ => ?_, fun h => ⟨p, hp, h⟩⟩
  exact (geometricStalk_nonzero_iff (B := B) (S := S) (hS := hS) (F := F)
    (p := q) (q := p) (hq.trans hp.symm)).mp hq_nonzero

end AlgebraicGeometry
