module

public import Mathlib.CategoryTheory.Sites.Sieves.Presheaf
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Recompletion
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The subfunctor of sections with point-set image in a set of points is an fppf sheaf

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an fppf sheaf of `Type (u + 1)`
over `S` and let `T` be a set of points of `X`. The sections of `X` over an object of the site
whose point-set image lies in `T` form the subfunctor
`AlgebraicGeometry.Space.completionSubfunctorULift` of `X`, whose fppf sheafification is the
completion of `X` along `T`. This file proves that the subfunctor is itself an fppf sheaf, for
every `X` and every `T`.

A subfunctor of a sheaf is a sheaf exactly when a section of the ambient sheaf whose
restrictions along a covering sieve all lie in the subfunctor lies in the subfunctor. Here that
is the statement that every field-valued point of the base object is, up to a field extension,
the image of a field-valued point of a member of the sieve: an fppf covering sieve is surjective
on the points of Stacks 03BU, so the point of `X` cut out of the section by a field-valued point
of the base object is also cut out at a member of the sieve, where it lies in `T`.

## Main results

* `AlgebraicGeometry.Space.class_restrict_eq_of_hasCommonExtension`: the point of `X` cut out of
  a section by a field-valued point of the base object depends only on the class of that
  field-valued point.
* `AlgebraicGeometry.Space.isLocallySurjective_sieveFunctorInclusion`: the presheaf induced by a
  covering sieve maps locally surjectively onto the represented presheaf.
* `AlgebraicGeometry.Space.isSheaf_completionSubfunctorULift`: the subfunctor of sections with
  point-set image in `T` is an fppf sheaf.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The point of `X` cut out of a section `x` over `U` by a field-valued point of `U` depends
only on the class of that field-valued point: a common field-valued extension of two
field-valued points of `U` restricts `x` to a common extension of the two points cut out. -/
theorem class_restrict_eq_of_hasCommonExtension
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)) (U : BigFppfOver B S hS)
    (x : X.obj (op U)) {p q : FieldValuedPoint B S hS (yoneda.obj U)}
    (h : FieldValuedPoint.HasCommonExtension B S hS (yoneda.obj U) p q) :
    (⟨p.carrier, p.contained, p.toBase, X.map p.value.op x⟩ :
        FieldValuedPointULift.{u + 1} B S hS X).class B S hS X =
      (⟨q.carrier, q.contained, q.toBase, X.map q.value.op x⟩ :
        FieldValuedPointULift.{u + 1} B S hS X).class B S hS X := by
  obtain ⟨r, ⟨f, hf⟩, ⟨g, hg⟩⟩ := h
  refine FieldValuedPointULift.class_eq_class_of_hasCommonExtension B S hS X
    ⟨⟨r.carrier, r.contained, r.toBase, X.map r.value.op x⟩, ⟨f, ?_⟩, ⟨g, ?_⟩⟩
  · simp [← hf]
  · simp [← hg]

/-- A section over the spectrum of a field in the site whose point-set image lies in `T` is
itself, as a field-valued point, a point of `X` lying in `T`: test the point-set image at the
identity field-valued point. -/
theorem class_mem_of_hasImageInULift (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1))
    (T : Set (pointsULift.{u + 1} B S hS X)) (K : Type u) [Field K]
    (hK : B.Contains (Spec (.of K))) (str : Spec (.of K) ⟶ S)
    (y : X.obj (op (Over.mk (⟨str⟩ : B.obj hK ⟶ B.obj hS))))
    (hy : HasImageInULift B S hS X T (Over.mk (⟨str⟩ : B.obj hK ⟶ B.obj hS)) y) :
    (⟨K, hK, str, y⟩ : FieldValuedPointULift.{u + 1} B S hS X).class B S hS X ∈ T := by
  refine Set.mem_of_eq_of_mem (congrArg (fun v ↦ (⟨K, hK, str, v⟩ :
      FieldValuedPointULift.{u + 1} B S hS X).class B S hS X) ?_)
    (hy { carrier := K, contained := hK, toBase := str, value := 𝟙 _ })
  rw [op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

/-- The presheaf induced by a covering sieve maps locally surjectively onto the presheaf
represented by the object the sieve is a sieve on: the image sieve of an arrow into that object
is the pullback of the covering sieve along it. -/
@[sga "3 IV 4.2.3" "Forward implication"]
theorem isLocallySurjective_sieveFunctorInclusion {U : BigFppfOver B S hS} (R : Sieve U)
    (hR : R ∈ BigFppfOver.topology B S hS U) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) R.functorInclusion := by
  constructor
  intro V t
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    ((BigFppfOver.topology B S hS).pullback_stable t hR)
  intro W g hg
  exact ⟨⟨g ≫ t, hg⟩, rfl⟩

/-- **The subfunctor of sections of an fppf sheaf `X` with point-set image in a set `T` of points
of `X` is itself an fppf sheaf.** A covering sieve is surjective on points, so a section all of
whose restrictions along the sieve have point-set image in `T` has point-set image in `T`. -/
theorem isSheaf_completionSubfunctorULift (X : FormalSpace.FppfSheaf B S hS)
    (T : Set (pointsULift.{u + 1} B S hS X.obj)) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (completionSubfunctorULift B S hS X.obj T).toFunctor := by
  have hX : Presieve.IsSheaf (BigFppfOver.topology B S hS) X.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).1 X.property
  rw [isSheaf_iff_isSheaf_of_type,
    Subfunctor.isSheaf_iff (completionSubfunctorULift B S hS X.obj T) hX]
  intro U s hs
  show HasImageInULift B S hS X.obj T U.unop s
  intro p
  obtain ⟨y, hy⟩ := surjective_pointsMap_of_isLocallySurjective B S hS
    ((completionSubfunctorULift B S hS X.obj T).sieveOfSection s).functorInclusion
    (isLocallySurjective_sieveFunctorInclusion B S hS _ hs)
    (p.class B S hS (yoneda.obj U.unop))
  obtain ⟨q, rfl⟩ := Quot.exists_rep y
  have hce := (FieldValuedPoint.class_eq_class_iff B S hS (yoneda.obj U.unop) _ p).1 hy
  exact Set.mem_of_eq_of_mem
    (class_restrict_eq_of_hasCommonExtension B S hS X.obj U.unop s hce).symm
    (class_mem_of_hasImageInULift B S hS X.obj T q.carrier q.contained q.toBase _ q.value.2)

end AlgebraicGeometry.Space

end
