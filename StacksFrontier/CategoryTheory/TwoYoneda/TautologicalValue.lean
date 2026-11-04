module

public import StacksFrontier.CategoryTheory.TwoYoneda.Basic

/-!
# The value of a 2-Yoneda point at the tautological object

Let `p : 𝒮 ⥤ 𝒞/X` be a category fibred in groupoids over a slice, let `U` be an object of `𝒞/X`
and let `x` be an object of the fibre of `p` over `U`. The 2-Yoneda lemma, Stacks 004B, attaches
to `x` the point `𝒞/U.left ⥤ 𝒮` of Stacks 02ZW assembled from the chosen cartesian lifts, namely
`CategoryTheory.Over.iteratedSliceBackward U ⋙ CategoryTheory.Functor.TwoYoneda.liftFunctor`.
This file computes its value at the tautological object `id_{U.left}` of `𝒞/U.left`: the chosen
lift there is a *vertical isomorphism* onto `x`.

The point is the bookkeeping. The image of the tautological object under the iterated slice
equivalence is the object of `(𝒞/X)/U` whose underlying object is `U` again and whose structure
morphism is the identity of `U.left` — that is, the canonical `eqToHom`
(`CategoryTheory.Over.iteratedSliceBackward_obj_mk_id_hom`). The chosen lift at that object is
therefore strongly cartesian over an isomorphism, hence an isomorphism, and lies over an
identity.

## Main definitions

* `CategoryTheory.Functor.TwoYoneda.liftFunctorTautIso`: the isomorphism from the value of the
  2-Yoneda point of `x` at the tautological object to `x` itself.

## Main results

* `CategoryTheory.Over.iteratedSliceBackward_obj_mk_id_left` and
  `CategoryTheory.Over.iteratedSliceBackward_obj_mk_id_hom`: the image of the tautological object
  of `𝒞/f.left` under the iterated slice equivalence is `f` again, by the canonical `eqToHom`.
* `CategoryTheory.Functor.TwoYoneda.isHomLift_liftFunctorTautIso_hom`: that isomorphism is
  vertical, in the shape `StacksRepresentableCFG.exists_natIso_of_iso_at_id` consumes.

## Implementation notes

`CategoryTheory.Functor.TwoYoneda.liftBasedEvaluationIso` is the same comparison read in the
fibre category over `U`, through `CategoryTheory.Functor.twoYonedaEvaluation`, which evaluates a
point of `(𝒞/X)/U` at the tautological object `id_U` of that slice. It is not used here: the
tautological object of `𝒞/U.left` is carried by the iterated slice equivalence to an object
*isomorphic* to `id_U` but not equal to it, so deducing the statement below from it would
reintroduce exactly the transport this file discharges once.

Every statement is made at the spelling `((Over.iteratedSliceBackward U).obj (Over.mk (𝟙
U.left))).left` of the base object, except the two final ones, which are made at the spelling
`(Over.map U.hom).obj (Over.mk (𝟙 U.left))` that a consumer of Stacks 02ZW holds. The two are
definitionally equal — `CategoryTheory.Over.iteratedSliceBackward_forget` is a `rfl` — but not
syntactically, and a rewrite or an instance search performed at the wrong one of the two fails.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

/-! ### The tautological object of an iterated slice -/

namespace Over

variable {C : Type u₁} [Category.{v₁} C] {X : C}

/-- The object of `C/X` underlying the image of the tautological object of `C/f.left` under the
iterated slice equivalence is `f` itself. -/
theorem iteratedSliceBackward_obj_mk_id_left (f : Over X) :
    ((Over.iteratedSliceBackward f).obj (Over.mk (𝟙 f.left))).left = f := by
  simp
  rfl

/-- The structure morphism of the image of the tautological object of `C/f.left` under the
iterated slice equivalence is the canonical `eqToHom`: its underlying morphism of `C` is the
identity. -/
theorem iteratedSliceBackward_obj_mk_id_hom (f : Over X) :
    ((Over.iteratedSliceBackward f).obj (Over.mk (𝟙 f.left))).hom
      = eqToHom (iteratedSliceBackward_obj_mk_id_left f) := by
  refine Over.OverMorphism.ext ?_
  simp only [Over.eqToHom_left]
  exact (eqToHom_refl _ _).symm

end Over

/-! ### The chosen lift at the tautological object -/

namespace Functor.TwoYoneda

variable {C : Type u₁} [Category.{v₁} C] {X : C} {𝒮 : Type u₂} [Category.{v₂} 𝒮]
  (p : 𝒮 ⥤ Over X) (hp : p.IsFiberedInGroupoids) (U : Over X) (x : p.Fiber U)

/-- The chosen lift at the tautological object is an isomorphism: it is strongly cartesian over
the structure morphism of the image of the tautological object under the iterated slice
equivalence, and that morphism is an `eqToHom`. -/
theorem isIso_chosenLift_phi : IsIso (chosenLift p hp U x
    ((Over.iteratedSliceBackward U).obj (Over.mk (𝟙 U.left)))).φ := by
  have hcart := (chosenLift p hp U x
    ((Over.iteratedSliceBackward U).obj (Over.mk (𝟙 U.left)))).isStronglyCartesian
  have hbase : IsIso ((Over.iteratedSliceBackward U).obj (Over.mk (𝟙 U.left))).hom := by
    rw [Over.iteratedSliceBackward_obj_mk_id_hom]
    infer_instance
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso p
    (f := ((Over.iteratedSliceBackward U).obj (Over.mk (𝟙 U.left))).hom)
    (chosenLift p hp U x ((Over.iteratedSliceBackward U).obj (Over.mk (𝟙 U.left)))).φ

/-- The chosen lift at the tautological object is vertical, stated over the underlying object of
the image of the tautological object under the iterated slice equivalence. -/
theorem isHomLift_chosenLift_phi' :
    p.IsHomLift (𝟙 ((Over.iteratedSliceBackward U).obj (Over.mk (𝟙 U.left))).left)
      (chosenLift p hp U x ((Over.iteratedSliceBackward U).obj (Over.mk (𝟙 U.left)))).φ := by
  have hlift := (chosenLift p hp U x
    ((Over.iteratedSliceBackward U).obj (Over.mk (𝟙 U.left)))).isStronglyCartesian.toIsHomLift
  refine (IsHomLift.lift_comp_eqToHom_iff p (𝟙 _) _
    (Over.iteratedSliceBackward_obj_mk_id_left U)).mp ?_
  rw [Category.id_comp, ← Over.iteratedSliceBackward_obj_mk_id_hom U]
  exact hlift

/-- **The chosen lift at the tautological object is vertical**, in the shape
`StacksRepresentableCFG.exists_natIso_of_iso_at_id` asks for: it lies over the identity of the
image of the tautological object in `C/X`. -/
theorem isHomLift_chosenLift_phi :
    p.IsHomLift (𝟙 ((Over.map U.hom).obj (Over.mk (𝟙 U.left))))
      (chosenLift p hp U x ((Over.iteratedSliceBackward U).obj (Over.mk (𝟙 U.left)))).φ :=
  isHomLift_chosenLift_phi' p hp U x

/-- **The value of the 2-Yoneda point of `x` at the tautological object is `x`**: the chosen lift
there is strongly cartesian over an isomorphism of the base. -/
noncomputable def liftFunctorTautIso :
    (Over.iteratedSliceBackward U ⋙ liftFunctor p hp U x).obj (Over.mk (𝟙 U.left)) ≅ x.1 :=
  @asIso _ _ _ _ (chosenLift p hp U x
      ((Over.iteratedSliceBackward U).obj (Over.mk (𝟙 U.left)))).φ
    (isIso_chosenLift_phi p hp U x)

/-- The isomorphism of `CategoryTheory.Functor.TwoYoneda.liftFunctorTautIso` is vertical. -/
theorem isHomLift_liftFunctorTautIso_hom :
    p.IsHomLift (𝟙 ((Over.map U.hom).obj (Over.mk (𝟙 U.left))))
      (liftFunctorTautIso p hp U x).hom :=
  isHomLift_chosenLift_phi p hp U x

end Functor.TwoYoneda

end CategoryTheory

end
