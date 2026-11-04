module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.SheafStalk
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits

/-!
# Global sections of an étale sheaf over a field

Let `K` be a field and let `sbar` be a geometric point of `Spec K`, with absolute Galois group
`G` the Galois group of the separable closure of the residue field at its image inside the
algebraically closed field of `sbar`. The spectrum of `K` is the final object of its own small
étale site, so a global section of a sheaf of sets is a section over that object; its germ at
`sbar` is fixed by `G`, and taking germs is a bijection from the global sections onto the
`G`-fixed elements of the stalk, functorially in the sheaf.

## Main results

* `AlgebraicGeometry.bijective_etaleGlobalSectionGerm` — taking the germ at a geometric point is
  a bijection from the global sections of a sheaf onto the Galois-fixed elements of its stalk.
* `AlgebraicGeometry.etaleGlobalSectionsEquivGaloisFixedPoints` — that bijection as an
  equivalence.
* `AlgebraicGeometry.etaleGlobalSectionGerm_map` — the bijection is functorial in the sheaf.

## References

* [Stacks Project, Tag 04JM](https://stacks.math.columbia.edu/tag/04JM)
* [Stacks Project, Tag 03QT](https://stacks.math.columbia.edu/tag/03QT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

attribute [local instance] GeometricPoint.residueFieldAlgebra

variable (B : BigEtaleSite.{u}) (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (sbar : GeometricPoint (Spec (.of K)))

/-- A geometric point of the spectrum of a field, viewed as a lift of itself to the final object
of the small étale site. -/
def finalGeometricPointLift :
    (geometricPointFiber B (Spec (.of K)) hK sbar).obj
      (SmallEtale.final B (Spec (.of K)) hK) :=
  ⟨sbar.hom, by simp [SmallEtale.final]⟩

/-- A lift of a geometric point to the final object of the small étale site is the point
itself. -/
theorem eq_finalGeometricPointLift
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj
      (SmallEtale.final B (Spec (.of K)) hK)) :
    p = finalGeometricPointLift B K hK sbar :=
  Subtype.ext (by simpa [SmallEtale.final, finalGeometricPointLift] using p.2)

/-- A geometric point of the spectrum of a field has at most one lift to the final object of the
small étale site. -/
instance subsingleton_geometricPointFiber_final :
    Subsingleton ((geometricPointFiber B (Spec (.of K)) hK sbar).obj
      (SmallEtale.final B (Spec (.of K)) hK)) :=
  ⟨fun p q ↦ (eq_finalGeometricPointLift B K hK sbar p).trans
    (eq_finalGeometricPointLift B K hK sbar q).symm⟩

/-- The final object of the small étale site, pointed by the unique lift of the geometric
point. -/
def finalPointedNeighborhood : (geometricPointFiber B (Spec (.of K)) hK sbar).Elements :=
  ⟨SmallEtale.final B (Spec (.of K)) hK, finalGeometricPointLift B K hK sbar⟩

/-- The germ at a geometric point of a global section of a sheaf of sets on the small étale site
of the spectrum of a field. -/
def etaleGlobalSectionGerm (F : smallEtaleTopos.{u, max u v} B (Spec (.of K)) hK)
    (t : ((sheafToPresheaf _ _).obj F).obj (op (SmallEtale.final B (Spec (.of K)) hK))) :
    (etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).obj F :=
  etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F
    (finalPointedNeighborhood B K hK sbar) t

/-- The elements of the étale stalk of a sheaf at a geometric point of the spectrum of a field
which are fixed by the absolute Galois group at that point. -/
abbrev etaleStalkGaloisFixedPoints
    (F : smallEtaleTopos.{u, max u v} B (Spec (.of K)) hK) :=
  { x : (etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).obj F //
    ∀ σ : GeometricPoint.absoluteGaloisGroup sbar,
      ConcreteCategory.hom (etaleStalkSmul.{u, v} B K hK sbar F σ) x = x }

/-- The germ of a global section is fixed by the absolute Galois group. -/
theorem etaleStalkSmul_etaleGlobalSectionGerm
    (F : smallEtaleTopos.{u, max u v} B (Spec (.of K)) hK)
    (σ : GeometricPoint.absoluteGaloisGroup sbar)
    (t : ((sheafToPresheaf _ _).obj F).obj (op (SmallEtale.final B (Spec (.of K)) hK))) :
    ConcreteCategory.hom (etaleStalkSmul.{u, v} B K hK sbar F σ)
        (etaleGlobalSectionGerm.{u, v} B K hK sbar F t) =
      etaleGlobalSectionGerm.{u, v} B K hK sbar F t :=
  (etaleStalkSmul_germ.{u, v} B K hK sbar F σ
      (finalPointedNeighborhood B K hK sbar) t).trans
    (congrArg (fun p ↦ etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F
      ⟨SmallEtale.final B (Spec (.of K)) hK, p⟩ t) (Subsingleton.elim _ _))

/-- For a geometric point of the spectrum of a field, taking the germ at that point is a bijection
from the global sections of a sheaf of sets on the small étale site onto the elements of its stalk
fixed by the absolute Galois group. -/
@[stacks 04JM]
theorem bijective_etaleGlobalSectionGerm
    (F : smallEtaleTopos.{u, max u v} B (Spec (.of K)) hK) :
    Function.Bijective
      (fun t : ((sheafToPresheaf _ _).obj F).obj
          (op (SmallEtale.final B (Spec (.of K)) hK)) ↦
        (⟨etaleGlobalSectionGerm.{u, v} B K hK sbar F t,
            fun σ ↦ etaleStalkSmul_etaleGlobalSectionGerm.{u, v} B K hK sbar F σ t⟩ :
          etaleStalkGaloisFixedPoints.{u, v} B K hK sbar F)) := by
  refine ⟨fun t t' h ↦ eq_of_etaleStalkGerm_eq.{u, v} B K hK sbar F _ t t' fun p ↦ ?_,
    fun x ↦ ?_⟩
  · obtain rfl := Subsingleton.elim p (finalGeometricPointLift B K hK sbar)
    exact congrArg Subtype.val h
  · obtain ⟨t, ht⟩ := exists_section_etaleStalkGerm.{u, v} B K hK sbar F
      (SmallEtale.final B (Spec (.of K)) hK) (fun _ ↦ x.1) (fun σ _ ↦ (x.2 σ).symm)
    exact ⟨t, Subtype.ext (ht (finalGeometricPointLift B K hK sbar))⟩

/-- The bijection between the global sections of a sheaf of sets on the small étale site of the
spectrum of a field and the Galois-fixed elements of its stalk at a geometric point. -/
@[stacks 04JM "the functorial bijection"]
def etaleGlobalSectionsEquivGaloisFixedPoints
    (F : smallEtaleTopos.{u, max u v} B (Spec (.of K)) hK) :
    ((sheafToPresheaf _ _).obj F).obj (op (SmallEtale.final B (Spec (.of K)) hK)) ≃
      etaleStalkGaloisFixedPoints.{u, v} B K hK sbar F :=
  Equiv.ofBijective _ (bijective_etaleGlobalSectionGerm.{u, v} B K hK sbar F)

/-- The bijection `etaleGlobalSectionsEquivGaloisFixedPoints` sends a global section to its
germ. -/
@[simp]
theorem etaleGlobalSectionsEquivGaloisFixedPoints_apply_coe
    (F : smallEtaleTopos.{u, max u v} B (Spec (.of K)) hK)
    (t : ((sheafToPresheaf _ _).obj F).obj (op (SmallEtale.final B (Spec (.of K)) hK))) :
    (etaleGlobalSectionsEquivGaloisFixedPoints.{u, v} B K hK sbar F t).1 =
      etaleGlobalSectionGerm.{u, v} B K hK sbar F t :=
  rfl

/-- The bijection between global sections and Galois-fixed stalk elements is functorial: a
morphism of sheaves carries the germ of a global section to the germ of its image. -/
@[stacks 04JM "functoriality in the sheaf"]
theorem etaleGlobalSectionGerm_map
    {F F' : smallEtaleTopos.{u, max u v} B (Spec (.of K)) hK} (φ : F ⟶ F')
    (t : ((sheafToPresheaf _ _).obj F).obj (op (SmallEtale.final B (Spec (.of K)) hK))) :
    etaleGlobalSectionGerm.{u, v} B K hK sbar F'
        (ConcreteCategory.hom (((sheafToPresheaf _ _).map φ).app
          (op (SmallEtale.final B (Spec (.of K)) hK))) t) =
      ConcreteCategory.hom ((etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).map φ)
        (etaleGlobalSectionGerm.{u, v} B K hK sbar F t) :=
  (etaleStalkFunctor_map_germ.{u, v} B K hK sbar φ _
    (finalGeometricPointLift B K hK sbar) t).symm

end AlgebraicGeometry

end
