module

public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDeligneMumford
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SlicePointIso
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.SliceOverMap
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoYoneda.TautologicalValue

/-!
# The 2-Yoneda normalisation of a scheme-valued point of an arbitrary target

Let `𝒯` be a category over the big fppf site of a scheme `S` which is fibred in groupoids, and
let `f : 𝒵 ⟶ 𝒯` be a 1-morphism over the site. Representability of `f` by algebraic spaces,
Stacks 02ZW, quantifies over *all* scheme-valued points of `𝒯`: all 1-morphisms
`(Sch/U)_fppf ⟶ 𝒯` over `CategoryTheory.Over.map U.hom`. In practice the fibre of `f` can only be
computed over the particular points which the 2-Yoneda lemma, Stacks 004B, attaches to an
*object* `X` of `𝒯` — the points assembled from chosen strongly cartesian lifts. This file
records that testing those points is enough.

The argument is the one Stacks uses silently. A scheme-valued point `y` over `U` takes the
tautological object `id_U` of `(Sch/U)_fppf` to an object `X = y(id_U)` of `𝒯` lying over `U`,
because `y` is a 1-morphism over the site. The 2-Yoneda point of `X` takes the tautological
object to `X` as well, up to a vertical isomorphism — that is
`CategoryTheory.Functor.TwoYoneda.liftFunctorTautIso`. Two points of a category fibred in
groupoids whose values at the tautological object are identified by a vertical isomorphism are
2-isomorphic over the site, which is Stacks 02Y4 in the shape
`StacksRepresentableCFG.exists_natIso_of_iso_at_id`; and reindexing a 2-fibre product along a
2-isomorphism of one of its legs does not change its first projection up to equivalence over the
base, which is `CategoryTheory.TwoFibreProductOver.nonempty_equivalenceOver_reindex`. So the
2-fibre product over `y` is equivalent, over the site of `U`, to the one over the 2-Yoneda point
of `X`.

This is the generic form of the step performed inside
`StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbertRelativeRepresentable` for the target
`ℋ_d(𝒳/𝒴)`; it is stated here for an arbitrary target so that it can also be used for the
product `ℋ_d(𝒳) × 𝒴` of Stacks 05YH, whose objects carry no bespoke structure to hang a
universal family on.

## Main definitions

* `AlgebraicGeometry.Stack.objUniversalFamily`: the scheme-valued point of `𝒯` over the base of
  an object `X` of `𝒯` which the 2-Yoneda lemma attaches to `X`.
* `AlgebraicGeometry.Stack.objUniversalFamilyTautIso`: the vertical isomorphism from the value of
  that point at the tautological object to `X`.
* `AlgebraicGeometry.Stack.FibresOverObjUniversalFamiliesAlgebraic`: the condition of Stacks
  02ZW restricted to the points attached to objects.

## Main results

* `AlgebraicGeometry.Stack.objUniversalFamily_comp`: the 2-Yoneda point of an object is a
  1-morphism over the site.
* `AlgebraicGeometry.Stack.exists_isAlgebraicSpace_equivalenceOver_of_objTarget`: a scheme-valued
  point whose value at the tautological object is `X` has the same 2-fibre product, up to
  equivalence over the base, as the 2-Yoneda point of `X`.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_objUniversalFamilies`: **the
  normalisation**, a 1-morphism into `𝒯` whose 2-fibre product with the 2-Yoneda point of every
  object of `𝒯` is representable by an algebraic space is representable by algebraic spaces in
  the sense of Stacks 02ZW.

## What is and is not proved

Proved, in full, with no carried hypothesis: the implication above. Nothing is assumed about `𝒯`
beyond that its projection to the site is fibred in groupoids, and nothing is assumed about `f`.

No tag is claimed. The file states no result of the Stacks project: it is the normalisation step
that the proofs of Stacks 05YJ and Stacks 05YH take without comment, isolated so that the two
can share it.

## Implementation notes

`AlgebraicGeometry.Stack.objUniversalFamily` is semireducible, and the type of
`CategoryTheory.Functor.TwoYoneda.liftFunctorTautIso` is spelled with the composite it unfolds
to, so it is made `implicit_reducible` locally from the point where that isomorphism is
constructed.

`AlgebraicGeometry.Stack.exists_isAlgebraicSpace_equivalenceOver_of_objTarget` takes the object,
the base and the equality `𝒯.p.obj X = U` of the two as three separate arguments rather than
instantiating the base: the proof is by `subst` on that equality, which is what moves the
representation from the site of `𝒯.p.obj X` to the site of `U` without a transport of
categories.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 02Y4](https://stacks.math.columbia.edu/tag/02Y4)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v₂ u₂ a₁ b₁

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒯 : BasedCategory.{v₂, u₂} (BigFppfOver B S hS)}

/-- The scheme-valued point of `𝒯` over the base of an object `X` of `𝒯` which the 2-Yoneda
lemma attaches to `X`, assembled from chosen strongly cartesian lifts of the structure morphisms
of the slice. -/
noncomputable def objUniversalFamily (h𝒯 : 𝒯.p.IsFiberedInGroupoids) (X : 𝒯.obj) :
    Over (𝒯.p.obj X).left ⥤ 𝒯.obj :=
  Over.iteratedSliceBackward (𝒯.p.obj X) ⋙
    Functor.TwoYoneda.liftFunctor 𝒯.p h𝒯 (𝒯.p.obj X) (Functor.Fiber.mk rfl)

/-- The 2-Yoneda point of an object is a 1-morphism over the big fppf site. -/
theorem objUniversalFamily_comp (h𝒯 : 𝒯.p.IsFiberedInGroupoids) (X : 𝒯.obj) :
    objUniversalFamily h𝒯 X ⋙ 𝒯.p = Over.map (𝒯.p.obj X).hom := by
  dsimp only [objUniversalFamily]
  rw [Functor.assoc, Functor.TwoYoneda.liftFunctor_w]
  rfl

attribute [local implicit_reducible] objUniversalFamily

/-- **The value of the 2-Yoneda point of an object at the tautological object is that object.**
This is `CategoryTheory.Functor.TwoYoneda.liftFunctorTautIso` for the projection of `𝒯`. -/
noncomputable def objUniversalFamilyTautIso (h𝒯 : 𝒯.p.IsFiberedInGroupoids) (X : 𝒯.obj) :
    (objUniversalFamily h𝒯 X).obj (Over.mk (𝟙 (𝒯.p.obj X).left)) ≅ X :=
  Functor.TwoYoneda.liftFunctorTautIso 𝒯.p h𝒯 (𝒯.p.obj X) (Functor.Fiber.mk rfl)

/-- `AlgebraicGeometry.Stack.objUniversalFamilyTautIso` is vertical. -/
theorem isHomLift_objUniversalFamilyTautIso (h𝒯 : 𝒯.p.IsFiberedInGroupoids) (X : 𝒯.obj) :
    𝒯.p.IsHomLift (𝟙 ((Over.map (𝒯.p.obj X).hom).obj (Over.mk (𝟙 (𝒯.p.obj X).left))))
      (objUniversalFamilyTautIso h𝒯 X).hom :=
  Functor.TwoYoneda.isHomLift_liftFunctorTautIso_hom _ _ _ _

/-- The assertion that the 2-fibre product of a 1-morphism `f` into `𝒯` with the 2-Yoneda point
of an object `X` of `𝒯` is representable by an algebraic space over the base of `X`, for every
object `X`.

This is the condition of Stacks 02ZW restricted to those scheme-valued points of `𝒯` which the
2-Yoneda lemma attaches to an object. -/
abbrev FibresOverObjUniversalFamiliesAlgebraic {𝒵 : BasedCategory.{a₁, b₁} (BigFppfOver B S hS)}
    (h𝒯 : 𝒯.p.IsFiberedInGroupoids) (f : 𝒵 ⥤ᵇ 𝒯) : Prop :=
  ∀ X : 𝒯.obj,
    ∃ A : (BigFppfOver B (𝒯.p.obj X).left.1 (𝒯.p.obj X).left.2)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B (𝒯.p.obj X).left.1 (𝒯.p.obj X).left.2 A ∧
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map (𝒯.p.obj X).hom) 𝒵.p 𝒯.p
            (objUniversalFamily h𝒯 X) f.toFunctor)
          (presheafOfCategories (A ⋙ typeToCat)).p)

/-- **A scheme-valued point whose value at the tautological object is a given object `X` has the
same 2-fibre product as the 2-Yoneda point of `X`.** The two points agree, vertically, at the
tautological object — the value of the 2-Yoneda point there is `X` by
`AlgebraicGeometry.Stack.objUniversalFamilyTautIso` — so they are 2-isomorphic over the site by
Stacks 02Y4, and reindexing the 2-fibre product along that 2-isomorphism is an equivalence over
the site of the base. -/
theorem exists_isAlgebraicSpace_equivalenceOver_of_objTarget
    {𝒵 : BasedCategory.{a₁, b₁} (BigFppfOver B S hS)} (f : 𝒵 ⥤ᵇ 𝒯)
    (h𝒵 : 𝒵.p.IsFiberedInGroupoids) (h𝒯 : 𝒯.p.IsFiberedInGroupoids)
    (hfam : FibresOverObjUniversalFamiliesAlgebraic h𝒯 f)
    (X : 𝒯.obj) (U : BigFppfOver B S hS) (hXU : 𝒯.p.obj X = U)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒯.obj) (hy : y ⋙ 𝒯.p = Over.map U.hom)
    (hpt : y.obj (Over.mk (𝟙 U.left)) = X) :
    ∃ A : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B U.left.1 U.left.2 A ∧
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒵.p 𝒯.p y f.toFunctor)
          (presheafOfCategories (A ⋙ typeToCat)).p) := by
  subst hXU
  obtain ⟨A, hA, ⟨e⟩⟩ := hfam X
  refine ⟨A, hA, ?_⟩
  -- the two points agree at the tautological object, vertically
  have hid : 𝒯.p.obj (y.obj (Over.mk (𝟙 (𝒯.p.obj X).left))) =
      (Over.map (𝒯.p.obj X).hom).obj (Over.mk (𝟙 (𝒯.p.obj X).left)) :=
    congrArg (fun K => K.obj (Over.mk (𝟙 (𝒯.p.obj X).left))) hy
  have hptv : 𝒯.p.IsHomLift
      (𝟙 ((Over.map (𝒯.p.obj X).hom).obj (Over.mk (𝟙 (𝒯.p.obj X).left)))) (eqToHom hpt) := by
    refine IsHomLift.of_fac' _ _ _ hid (hid.symm.trans (congrArg _ hpt)).symm ?_
    simp [eqToHom_map]
  have hvert := isHomLift_objUniversalFamilyTautIso h𝒯 X
  have hinv := IsHomLift.lift_id_inv 𝒯.p
    ((Over.map (𝒯.p.obj X).hom).obj (Over.mk (𝟙 (𝒯.p.obj X).left)))
    (objUniversalFamilyTautIso h𝒯 X)
  have hθ : 𝒯.p.IsHomLift
      (𝟙 ((Over.map (𝒯.p.obj X).hom).obj (Over.mk (𝟙 (𝒯.p.obj X).left))))
      (eqToHom hpt ≫ (objUniversalFamilyTautIso h𝒯 X).inv) := by
    have := hptv
    have := hinv
    have hc := IsHomLift.comp 𝒯.p
      (𝟙 ((Over.map (𝒯.p.obj X).hom).obj (Over.mk (𝟙 (𝒯.p.obj X).left))))
      (𝟙 ((Over.map (𝒯.p.obj X).hom).obj (Over.mk (𝟙 (𝒯.p.obj X).left)))) (eqToHom hpt)
      (objUniversalFamilyTautIso h𝒯 X).inv
    rwa [Category.comp_id] at hc
  -- Stacks 02Y4: the two points are 2-isomorphic over the site
  obtain ⟨α, hα⟩ := StacksRepresentableCFG.exists_natIso_of_iso_at_id (𝒯.p.obj X).hom y
    (objUniversalFamily h𝒯 X) hy (objUniversalFamily_comp h𝒯 X) h𝒯
    (Iso.trans (eqToIso hpt) (objUniversalFamilyTautIso h𝒯 X).symm) hθ
  -- the 2-fibre product over any point over the site is fibred in groupoids over the site
  have hfib : ∀ (z : BigFppfOver B (𝒯.p.obj X).left.1 (𝒯.p.obj X).left.2 ⥤ 𝒯.obj)
      (hz : z ⋙ 𝒯.p = Over.map (𝒯.p.obj X).hom),
      (TwoFibreProductOver.fst (Over.map (𝒯.p.obj X).hom) 𝒵.p 𝒯.p z
        f.toFunctor).IsFiberedInGroupoids := fun z hz =>
    (Functor.isFiberedInGroupoids_comp_overMap_iff (𝒯.p.obj X).hom _).1 (by
      rw [TwoFibreProductOver.fst_comp_eq]
      exact TwoFibreProductOver.isFiberedInGroupoids (Over.map (𝒯.p.obj X).hom) 𝒵.p 𝒯.p z
        f.toFunctor (Functor.IsFiberedInGroupoids.over_map (𝒯.p.obj X).hom) h𝒵 h𝒯 hz f.w)
  obtain ⟨k⟩ := TwoFibreProductOver.nonempty_equivalenceOver_reindex α hα (hfib y hy)
    (hfib _ (objUniversalFamily_comp h𝒯 X))
  exact ⟨k.trans e⟩

/-- **The 2-Yoneda normalisation of a scheme-valued point.** A 1-morphism into `𝒯` whose 2-fibre
product with the 2-Yoneda point of every object of `𝒯` is representable by an algebraic space is
representable by algebraic spaces in the sense of Stacks 02ZW.

Given a scheme-valued point `y` over `U`, the object `X = y(id_U)` has base `U`, because `y` is a
1-morphism over the site, and `y` takes the tautological object to `X` by construction;
`AlgebraicGeometry.Stack.exists_isAlgebraicSpace_equivalenceOver_of_objTarget` then identifies
the 2-fibre product over `y` with the one over the 2-Yoneda point of `X`. -/
theorem isRepresentableByAlgebraicSpaces_of_objUniversalFamilies
    {𝒵 : BasedCategory.{a₁, b₁} (BigFppfOver B S hS)} (f : 𝒵 ⥤ᵇ 𝒯)
    (h𝒵 : 𝒵.p.IsFiberedInGroupoids) (h𝒯 : 𝒯.p.IsFiberedInGroupoids)
    (hfam : FibresOverObjUniversalFamiliesAlgebraic h𝒯 f) :
    IsRepresentableByAlgebraicSpaces B S hS f := by
  intro U 𝒰 p𝒰 y hy
  have hXU : 𝒯.p.obj (y.obj (Over.mk (𝟙 U.left))) = U :=
    (congrArg (fun K => K.obj (Over.mk (𝟙 U.left))) hy).trans
      (Over.iteratedSliceBackward_obj_mk_id_left U)
  exact exists_isAlgebraicSpace_equivalenceOver_of_objTarget f h𝒵 h𝒯 hfam
    (y.obj (Over.mk (𝟙 U.left))) U hXU y hy rfl

end AlgebraicGeometry.Stack

end
