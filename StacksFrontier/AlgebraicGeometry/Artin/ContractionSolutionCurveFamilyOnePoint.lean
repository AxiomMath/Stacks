module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionCurveFamilyPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical

/-!
# The completion along a single point has at most one point

Let `X` be an fppf sheaf on the big fppf site of `S` and let `t ∈ |X|`. The completion
`X_{/\{t\}}` of `X` along the single point `t` has at most one point in the sense of
`AlgebraicGeometry.FormalSpace.HasAtMostOnePoint`: its sections over spectra of fields are the
field-valued points of `X` representing `t`, and any two of them have a common field-valued
extension because they define the same point of `|X|`.

The main application is to the completion of the spectrum of a local ring along its closed
point.

## Main results

* `AlgebraicGeometry.FormalSpace.hasAtMostOnePoint_completionSheaf_of_subsingleton`: the
  completion of an fppf sheaf along a set with at most one point has at most one point.
* `AlgebraicGeometry.FormalSpace.hasAtMostOnePoint_completionSheaf_singleton`: the completion
  of an fppf sheaf along a single point has at most one point.
* `AlgebraicGeometry.FormalSpace.hasAtMostOnePoint_completionSheaf_yoneda_singleton`: the
  same for a representable sheaf.
* `AlgebraicGeometry.FormalSpace.hasAtMostOnePoint_completionSheaf_closedPoint`: the
  completion of an object of the site isomorphic to `Spec A`, `A` local, along the closed point
  has at most one point.

## References

* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The completion `X_{/T}` of an fppf sheaf `X` along a set `T ⊆ |X|` with at most one element
has at most one point: a section over the spectrum of a field is a field-valued point of `X`
lying over a point of `T`, and two field-valued points with the same class have a common
field-valued extension. -/
theorem hasAtMostOnePoint_completionSheaf_of_subsingleton {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X) {T : Set (Space.points B S hS X)}
    (hT : T.Subsingleton) :
    HasAtMostOnePoint (Space.completionSheaf B S hS X T) := by
  intro K₁ K₂ _ _ h₁ h₂ p₁ p₂ w₁ w₂
  let e := Space.completionSheafIsoSubfunctor B S hS hX T
  let P₁ : Space.FieldValuedPoint B S hS X := ⟨K₁, h₁, p₁, (e.hom.app _ w₁).1.down⟩
  let P₂ : Space.FieldValuedPoint B S hS X := ⟨K₂, h₂, p₂, (e.hom.app _ w₂).1.down⟩
  have hP₁ : P₁.class B S hS X ∈ T :=
    (Space.hasImageIn_iff_class_mem B S hS X T P₁).1 (e.hom.app _ w₁).2
  have hP₂ : P₂.class B S hS X ∈ T :=
    (Space.hasImageIn_iff_class_mem B S hS X T P₂).1 (e.hom.app _ w₂).2
  obtain ⟨r, ⟨f₁, hf₁⟩, ⟨f₂, hf₂⟩⟩ :=
    (Space.FieldValuedPoint.class_eq_class_iff B S hS X P₁ P₂).1 (hT hP₁ hP₂)
  refine ⟨r.carrier, inferInstance, r.contained, r.toBase, f₁, f₂, ?_⟩
  have key : ∀ (P : Space.FieldValuedPoint B S hS X)
      (w : (Space.completionSheaf B S hS X T).obj.obj (op P.siteObject))
      (_ : P.value = (e.hom.app _ w).1.down) (f : r.siteObject ⟶ P.siteObject),
      (e.hom.app _ ((Space.completionSheaf B S hS X T).obj.map f.op w)).1.down =
        X.map f.op P.value := by
    intro P w hw f
    rw [NatTrans.naturality_apply e.hom f.op, hw]
    rfl
  apply (mono_iff_injective (e.hom.app _)).1 inferInstance
  apply Subtype.ext
  apply ULift.ext
  exact (key P₁ w₁ rfl f₁).trans (hf₁.trans (hf₂.symm.trans (key P₂ w₂ rfl f₂).symm))

/-- The completion `X_{/\{t\}}` of an fppf sheaf `X` along a single point `t ∈ |X|` has at most
one point. -/
theorem hasAtMostOnePoint_completionSheaf_singleton {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X) (t : Space.points B S hS X) :
    HasAtMostOnePoint (Space.completionSheaf B S hS X {t}) :=
  hasAtMostOnePoint_completionSheaf_of_subsingleton hX Set.subsingleton_singleton

/-- The completion of the presheaf represented by an object `P` of the big fppf site of `S`
along a single point of `|h_P|` has at most one point. -/
theorem hasAtMostOnePoint_completionSheaf_yoneda_singleton (P : BigFppfOver B S hS)
    (t : Space.points B S hS (yoneda.obj P)) :
    HasAtMostOnePoint (Space.completionSheaf B S hS (yoneda.obj P) {t}) :=
  hasAtMostOnePoint_completionSheaf_singleton (BigFppfOver.isSheaf_yoneda_obj B S hS P) t

/-- Let `P` be an object of the big fppf site of `S` whose underlying scheme is isomorphic to
`Spec A` for a local ring `A`. The completion of `h_P` along the point of `|h_P|` corresponding
to the closed point of `Spec A` has at most one point. -/
theorem hasAtMostOnePoint_completionSheaf_closedPoint (P : BigFppfOver B S hS)
    {A : Type u} [CommRing A] [IsLocalRing A]
    (eA : (BigFppfOver.toScheme B S hS).obj P ≅ Spec (.of A)) :
    HasAtMostOnePoint (Space.completionSheaf B S hS (yoneda.obj P)
      {(Space.schemePointsHomeomorph B S hS P).symm (eA.inv (IsLocalRing.closedPoint A))}) :=
  hasAtMostOnePoint_completionSheaf_yoneda_singleton P _

end AlgebraicGeometry.FormalSpace

end
