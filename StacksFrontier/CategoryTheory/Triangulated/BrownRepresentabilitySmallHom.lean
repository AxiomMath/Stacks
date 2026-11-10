module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Group.Shrink
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import StacksFrontier.CategoryTheory.Triangulated.BrownRepresentability

/-!
# Brown representability when only the morphisms out of the source are small

`CategoryTheory.Pretriangulated.exists_isTriangulated_rightAdjoint_of_compactlyGenerated`
([Stacks, Tag 0A8G]) asks for a single universe `v` to serve three roles at once: the morphism
universe of both the source `D` and the target `D'`, the universe indexing the coproducts of
`D`, and the universe indexing the generating family. In the application to [Stacks, Tag 09LK]
those roles come apart. There `D'` is the homotopy category of right differential graded modules
over a differential graded category `C`, whose morphism universe is `max u v` for
`C.Obj : Type u` and `C.Hom x y n : Type v`, while the coproducts the representable modules are
compact for are indexed by `Type v` alone. So `D'` is *not* `LocallySmall.{v}`, and the usual
repair — shrink the morphisms of both categories, as in
`StacksFrontier/CategoryTheory/Triangulated/BrownRepresentabilityShrinkHoms.lean` — is unavailable
on the target.

This file replaces local smallness of the target by the hypothesis that only matters:

`∀ (X : D) (Y : D'), Small.{w} (F.obj X ⟶ Y)`

i.e. the morphism groups *out of the image of* `F` are `Type w`-small. That is exactly what the
Brown representability argument consumes, because the only way `D'` enters it is through the
functor `X ↦ Hom_{D'}(F X, Y)` whose representability is being established; and in the 09LK
application it is supplied by `ObjectProperty.small_hom_of_localizingClosure`.

## How the universes are made to fit

Brown representability is applied to a functor into `AddCommGrpCat.{w}`, which is where the
smallness hypothesis is spent: `ObjectProperty.shrinkAb` replaces the groups
`Hom_{D'}(F X, Y) : Type (max u v)` by their `Type w`-shrinks. The two properties of this functor
that [Stacks, Tag 0A8F] needs — being homological, and transforming direct sums into products —
are transported from the unshrunk functor across
`AddCommGrpCat.uliftFunctor`, which is fully faithful and preserves and reflects both exactness
and limits. No elementwise argument is needed: the shrink and the original become isomorphic
functors once both are lifted into `AddCommGrpCat.{max w v'}`.

The source still has to be genuinely `Type w`-enriched, because `preadditiveYoneda` on it has to
land in `AddCommGrpCat.{w}` as well. That is a hypothesis here, and it is discharged for a merely
`LocallySmall.{w}` source by shrinking the source — and only the source — in
`StacksFrontier/CategoryTheory/Triangulated/BrownRepresentabilityShrinkHoms.lean`, where the
machinery for transporting a triangulated structure along `ShrinkHoms.equivalence` already
lives. In the 09LK application that local smallness is again
`ObjectProperty.small_hom_of_localizingClosure`.

One hypothesis that [Stacks, Tag 0A8F] needs is *not* available as an instance once `w` comes
apart from the target's morphism universe: Mathlib's `preservesLimits_preadditiveYoneda_obj` is
`PreservesLimitsOfSize.{v', v'}`. It is re-proved here at arbitrary size as
`preservesLimitsOfShape_preadditiveYoneda_obj`, and discharged inside the theorem rather than
assumed, so that nothing propagates out to 09LK.

## Main results

* `CategoryTheory.ObjectProperty.shrinkAb` and
  `CategoryTheory.ObjectProperty.shrinkAbIso`: the pointwise `Type w`-shrink of a functor into
  abelian groups with small values, and its identification with the original after both are
  lifted to a common universe.
* `CategoryTheory.preservesLimitsOfShape_preadditiveYoneda_obj`: `Hom(-, Y)` transforms colimits
  of any shape into limits, at an index category outside the morphism universe of its target.
* `CategoryTheory.Pretriangulated.exists_isTriangulated_rightAdjoint_of_small_hom`: Brown
  representability and an exact right adjoint, for a source which is already `Type w`-enriched
  and a target assumed only to have `Type w`-small morphism groups out of the image of `F`.

## References

* [Stacks Project, Tag 0A8G](https://stacks.math.columbia.edu/tag/0A8G)
-/

@[expose] public noncomputable section

universe w v' v u' u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CategoryTheory.ObjectProperty

namespace CategoryTheory.ObjectProperty

/-! ### The pointwise shrink of a functor into abelian groups -/

section Shrink

variable {C : Type u} [Category.{v} C] (P : C ⥤ AddCommGrpCat.{v'})
  [∀ U, Small.{w} (P.obj U)]

/-- The pointwise `Type w`-shrink of a functor into abelian groups whose values are
`Type w`-small: the group structure on `Shrink.{w} (P.obj U)` is the one transported along
`equivShrink`, and the morphisms are conjugated by `Shrink.addEquiv`. -/
def shrinkAb : C ⥤ AddCommGrpCat.{w} where
  obj U := AddCommGrpCat.of (Shrink.{w} (P.obj U))
  map f := AddCommGrpCat.ofHom
    ((Shrink.addEquiv.symm.toAddMonoidHom.comp (P.map f).hom).comp Shrink.addEquiv.toAddMonoidHom)
  map_id U := by ext x; simp
  map_comp f g := by ext x; simp

/-- The defining property of `ObjectProperty.shrinkAb`: transporting along `Shrink.addEquiv`
turns the action of the shrink into the action of `P`. -/
@[simp]
lemma shrinkAb_map_addEquiv {U V : C} (f : U ⟶ V) (z : Shrink.{w} (P.obj U)) :
    Shrink.addEquiv (ConcreteCategory.hom ((shrinkAb.{w} P).map f) z) =
      ConcreteCategory.hom (P.map f) (Shrink.addEquiv z) :=
  Shrink.addEquiv.apply_symm_apply _

/-- `ObjectProperty.shrinkAb P` and `P` become isomorphic once both are lifted into
`AddCommGrpCat.{max w v'}`. This is the only bridge between them that is needed: every property
of `shrinkAb P` used below is one that `AddCommGrpCat.uliftFunctor` both preserves and
reflects. -/
def shrinkAbIso :
    shrinkAb.{w} P ⋙ AddCommGrpCat.uliftFunctor.{v', w} ≅
      P ⋙ AddCommGrpCat.uliftFunctor.{w, v'} :=
  NatIso.ofComponents
    (fun _ ↦ (AddEquiv.ulift.trans (Shrink.addEquiv.trans AddEquiv.ulift.symm)).toAddCommGrpIso)
    (by
      intros
      ext x
      exact ULift.ext (Shrink.addEquiv.apply_symm_apply _))

/-- The shrink of a functor transforming coproducts of shape `Discrete α` into products does the
same: `AddCommGrpCat.uliftFunctor` preserves and reflects limits, and the lifts of the two
functors agree. -/
instance preservesLimitsOfShape_shrinkAb (α : Type w)
    [PreservesLimitsOfShape (Discrete α) P] :
    PreservesLimitsOfShape (Discrete α) (shrinkAb.{w} P) :=
  have : PreservesLimitsOfShape (Discrete α)
      (shrinkAb.{w} P ⋙ AddCommGrpCat.uliftFunctor.{v', w}) :=
    preservesLimitsOfShape_of_natIso (shrinkAbIso.{w} P).symm
  preservesLimitsOfShape_of_reflects_of_preserves _ AddCommGrpCat.uliftFunctor.{v', w}

end Shrink

section ShrinkZero

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (P : C ⥤ AddCommGrpCat.{v'})
  [∀ U, Small.{w} (P.obj U)] [P.PreservesZeroMorphisms]

/-- The shrink of a functor preserving zero morphisms preserves zero morphisms. -/
instance preservesZeroMorphisms_shrinkAb : (shrinkAb.{w} P).PreservesZeroMorphisms where
  map_zero U V := by ext x; simp [shrinkAb]; rfl

end ShrinkZero

section ShrinkHomological

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (P : C ⥤ AddCommGrpCat.{v'}) [∀ U, Small.{w} (P.obj U)] [P.IsHomological]

/-- The shrink of a homological functor is homological: `AddCommGrpCat.uliftFunctor` is exact and
faithful, so it both carries the exactness of `P` on a distinguished triangle to the lift of the
shrink and reflects it back. -/
instance isHomological_shrinkAb : (shrinkAb.{w} P).IsHomological where
  exact T hT := by
    rw [← ShortComplex.exact_map_iff_of_faithful _ AddCommGrpCat.uliftFunctor.{v', w}]
    exact ShortComplex.exact_of_iso (ShortComplex.mapNatIso _ (shrinkAbIso.{w} P)).symm
      ((P.map_distinguished_exact T hT).map AddCommGrpCat.uliftFunctor.{w, v'})

end ShrinkHomological

end CategoryTheory.ObjectProperty

/-! ### Brown representability with a small-hom target -/

namespace CategoryTheory

/-- `Hom(-, Y)` as a functor into abelian groups transforms colimits of *any* shape into limits.

Mathlib's `preservesLimits_preadditiveYoneda_obj` is `PreservesLimitsOfSize.{v', v'}`, so it does
not cover an index category outside the morphism universe of `D'`; but
`PreservesLimitsOfSize.{t, w} (yoneda.obj Y)` is available at arbitrary size, and reflecting along
`forget AddCommGrpCat` recovers the additive statement exactly as Mathlib does at its own size.
This is what lets the universe indexing the coproducts come apart from the morphism universe of
the target. -/
lemma preservesLimitsOfShape_preadditiveYoneda_obj {D' : Type u'} [Category.{v'} D']
    [Preadditive D'] {J : Type*} [Category* J] (Y : D') :
    Limits.PreservesLimitsOfShape J (preadditiveYoneda.obj Y) :=
  have : Limits.PreservesLimitsOfShape J (preadditiveYoneda.obj Y ⋙ forget AddCommGrpCat) :=
    inferInstanceAs (Limits.PreservesLimitsOfShape J (yoneda.obj Y))
  Limits.preservesLimitsOfShape_of_reflects_of_preserves _ (forget AddCommGrpCat)

namespace Pretriangulated

section SmallHom

variable {D : Type u} {D' : Type u'} [Category.{w} D] [Category.{v'} D']
  [HasZeroObject D] [HasZeroObject D'] [Preadditive D] [Preadditive D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D'] [IsTriangulated D] [HasCoproducts.{w} D]

/-- The partial right adjoint of `F` is defined at `Y`, assuming of the target only that the
morphism groups out of the image of `F` are `Type w`-small.

The cohomological functor `W ↦ Hom_{D'}(F W, Y)` takes values in `AddCommGrpCat.{v'}`, which is
too large for [Stacks, Tag 0A8F] once `v'` is not `w`: the Brown construction forms coproducts
indexed by the functor's own values. Its `Type w`-shrink `ObjectProperty.shrinkAb` is small
enough, and is still homological and still transforms direct sums into products. Brown
representability represents the shrink by an object `X` of `D`, and composing the resulting
bijections with `Shrink.addEquiv` exhibits `X` as representing `W ↦ Hom_{D'}(F W, Y)` itself. -/
private lemma rightAdjointObjIsDefined_of_small_hom
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    [∀ α : Type w, Limits.PreservesColimitsOfShape (Discrete α) F]
    {ι : Type w} (E : ι → D)
    [∀ (i : ι) (α : Type w),
      Limits.PreservesColimitsOfShape (Discrete α) (preadditiveCoyoneda.obj (op (E i)))]
    (hsmall : ∀ (W : D) (Z : D'), Small.{w} (F.obj W ⟶ Z))
    (hE : ∀ Z : D, ((ObjectProperty.ofObj E).shiftClosure ℤ).rightOrthogonal Z → IsZero Z)
    (Y : D') :
    F.rightAdjointObjIsDefined Y := by
  have : ∀ U : Dᵒᵖ, Small.{w} ((F.op ⋙ preadditiveYoneda.obj Y).obj U) :=
    fun U ↦ hsmall U.unop Y
  have : ∀ α : Type w,
      Limits.PreservesLimitsOfShape (Discrete α) (F.op ⋙ preadditiveYoneda.obj Y) := fun α ↦
    have := Limits.preservesLimitsOfShape_op (Discrete α) F
    have := preservesLimitsOfShape_preadditiveYoneda_obj (J := Discrete α) Y
    inferInstance
  obtain ⟨X, ⟨e⟩⟩ := exists_iso_preadditiveYoneda_of_compactlyGenerated E hE
    (ObjectProperty.shrinkAb.{w} (F.op ⋙ preadditiveYoneda.obj Y))
  refine (F.rightAdjointObjIsDefined_iff Y).2 (Functor.RepresentableBy.isRepresentable
    (Y := X) { homEquiv := fun {W} ↦ ?_, homEquiv_comp := ?_ })
  · exact ((forget AddCommGrpCat).mapIso (e.app (op W))).toEquiv.symm.trans
      Shrink.addEquiv.toEquiv
  · intro W W' f g
    have hnat : ConcreteCategory.hom (e.inv.app (op W))
          (ConcreteCategory.hom ((preadditiveYoneda.obj X).map f.op) g) =
        ConcreteCategory.hom
          ((ObjectProperty.shrinkAb.{w} (F.op ⋙ preadditiveYoneda.obj Y)).map f.op)
          (ConcreteCategory.hom (e.inv.app (op W')) g) :=
      ConcreteCategory.congr_hom (e.inv.naturality f.op) g
    change Shrink.addEquiv (ConcreteCategory.hom (e.inv.app (op W)) (f ≫ g)) =
      F.map f ≫ Shrink.addEquiv (ConcreteCategory.hom (e.inv.app (op W')) g)
    rw [show (f ≫ g) = ConcreteCategory.hom ((preadditiveYoneda.obj X).map f.op) g from rfl,
      hnat]
    exact ObjectProperty.shrinkAb_map_addEquiv (F.op ⋙ preadditiveYoneda.obj Y) f.op _

/-- **Brown representability and an exact right adjoint, with a small-hom target.** Let `D` be a
triangulated category with `Type w`-indexed coproducts, compactly generated by a family
`E : ι → D` indexed by `ι : Type w`, and whose own morphisms live in `Type w`. Let
`F : D ⥤ D'` be exact and `Type w`-coproduct-preserving into a pretriangulated `D'` whose
morphism universe is unrelated to `w`. If the morphism groups out of the image of `F` are
`Type w`-small, then `F` has a right adjoint, and it is again exact.

This is `CategoryTheory.Pretriangulated.exists_isTriangulated_rightAdjoint_of_compactlyGenerated`
with local smallness of the target replaced by the only consequence of it that the proof uses.
The target is left entirely alone: no shrinking of `D'`, and no hypothesis that its morphisms are
small, which is false in the [Stacks, Tag 09LK] application. -/
theorem exists_isTriangulated_rightAdjoint_of_small_hom
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    [∀ α : Type w, Limits.PreservesColimitsOfShape (Discrete α) F]
    {ι : Type w} (E : ι → D)
    [∀ (i : ι) (α : Type w),
      Limits.PreservesColimitsOfShape (Discrete α) (preadditiveCoyoneda.obj (op (E i)))]
    (hsmall : ∀ (W : D) (Z : D'), Small.{w} (F.obj W ⟶ Z))
    (hE : ∀ Z : D, ((ObjectProperty.ofObj E).shiftClosure ℤ).rightOrthogonal Z → IsZero Z) :
    ∃ (G : D' ⥤ D) (adj : F ⊣ G) (_ : G.CommShift ℤ), adj.IsTriangulated := by
  have : F.IsLeftAdjoint :=
    Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top (eq_top_iff.2 fun Y _ ↦
      rightAdjointObjIsDefined_of_small_hom F E hsmall hE Y)
  let adj : F ⊣ F.rightAdjoint := Adjunction.ofIsLeftAdjoint F
  let := adj.rightAdjointCommShift ℤ
  have := adj.commShift_of_leftAdjoint ℤ
  exact ⟨F.rightAdjoint, adj, inferInstance, Adjunction.IsTriangulated.mk' adj⟩

end SmallHom

end Pretriangulated

end CategoryTheory

end
