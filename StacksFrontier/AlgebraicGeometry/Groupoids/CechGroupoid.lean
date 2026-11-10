module

public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation

/-!
# The Čech groupoid of a morphism of schemes

Let `f : X ⟶ Y` be a morphism of schemes over a base scheme `S`. Its kernel pair `X ×_Y X`
is an equivalence relation on `X`, and the resulting groupoid scheme over `S` has `X` for its
scheme of objects and `X ×_Y X` for its scheme of arrows, with the two projections as target
and source. This is the *Čech groupoid* of `f`.

## Main definitions

* `AlgebraicGeometry.cechPreRelation` is the kernel pair of `f`, as a pre-relation on `X`.
* `AlgebraicGeometry.cechGroupoid` is the Čech groupoid of `f`.

## Main results

* `AlgebraicGeometry.isEquivalenceRelation_cechPreRelation`: the kernel pair of `f` is an
  equivalence relation.
* `AlgebraicGeometry.extendsRelation_cechGroupoid` and
  `AlgebraicGeometry.groupoidSchemeOfIsEquivalenceRelation_cechPreRelation`: the Čech groupoid
  is the groupoid scheme canonically extending that equivalence relation.

## Implementation notes

The groupoid is written down explicitly rather than obtained from
`AlgebraicGeometry.groupoidSchemeOfIsEquivalenceRelation`, so that its composition, identity
and inverse maps are available by definition instead of only up to the uniqueness statement of
Tag 0233; `AlgebraicGeometry.groupoidSchemeOfIsEquivalenceRelation_cechPreRelation` identifies
the two. The scheme of arrows is literally a fibre product and the source and target maps are
literally its two projections, so every groupoid axiom is an instance of
`CategoryTheory.Limits.pullback.hom_ext`.

All of this takes place in the category of schemes over `S`, where the binary product is the
fibre product over `S`; the fibre product `X ×_Y X` is a pullback there, not a product.

## References

* [Stacks Project, Tag 022P](https://stacks.math.columbia.edu/tag/022P)
* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
* [Stacks Project, Tag 0233](https://stacks.math.columbia.edu/tag/0233)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)

/-- The kernel pair of a morphism `f : X ⟶ Y` of schemes over `S`, as a pre-relation on `X`:
the two projections of `X ×_Y X`, assembled into a single morphism to `X ×_S X`. -/
noncomputable abbrev cechPreRelation : PreRelation (pullback f f) X :=
  prod.lift (pullback.fst f f) (pullback.snd f f)

/-- The target map of the kernel-pair pre-relation is the first projection. -/
@[simp]
theorem cechPreRelation_target : (cechPreRelation f).target = pullback.fst f f :=
  prod.lift_fst _ _

/-- The source map of the kernel-pair pre-relation is the second projection. -/
@[simp]
theorem cechPreRelation_source : (cechPreRelation f).source = pullback.snd f f :=
  prod.lift_snd _ _

/-- The two projections of the kernel pair of `f` are an equivalence relation on `X`. -/
theorem isEquivalenceRelation_kernelPair :
    IsEquivalenceRelation (pullback.fst f f) (pullback.snd f f) :=
  EquivalenceRelation.isEquivalenceRelation
    ((IsKernelPair.of_hasPullback f).equivalenceRelation f (pullback.fst f f)
      (pullback.snd f f)
      (pullback.isLimit (pullback.snd f f) (pullback.fst f f)))

/-- The kernel pair of `f` is an equivalence relation in the sense of Tag 022P. -/
instance isEquivalenceRelation_cechPreRelation :
    IsEquivalenceRelation (cechPreRelation f).target (cechPreRelation f).source := by
  rw [cechPreRelation_target, cechPreRelation_source]
  exact isEquivalenceRelation_kernelPair f

/-- The Čech groupoid of a morphism `f : X ⟶ Y` of schemes over `S`: its scheme of objects is
`X`, its scheme of arrows is the kernel pair `X ×_Y X`, and its target and source maps are the
first and second projections. -/
noncomputable def cechGroupoid : GroupoidScheme S where
  objects := X
  arrows := pullback f f
  source := pullback.snd f f
  target := pullback.fst f f
  comp :=
    pullback.lift
      (pullback.fst (pullback.snd f f) (pullback.fst f f) ≫ pullback.fst f f)
      (pullback.snd (pullback.snd f f) (pullback.fst f f) ≫ pullback.snd f f)
      (by
        have h₁ : (pullback.fst f f : pullback f f ⟶ X) ≫ f = pullback.snd f f ≫ f :=
          pullback.condition
        have h₂ : pullback.fst (pullback.snd f f) (pullback.fst f f) ≫ pullback.snd f f =
            pullback.snd (pullback.snd f f) (pullback.fst f f) ≫ pullback.fst f f :=
          pullback.condition
        rw [Category.assoc, Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc, h₁])
  identity := pullback.lift (𝟙 X) (𝟙 X) rfl
  inverse := pullback.lift (pullback.snd f f) (pullback.fst f f) pullback.condition.symm
  source_identity := pullback.lift_snd _ _ _
  target_identity := pullback.lift_fst _ _ _
  source_inverse := pullback.lift_snd _ _ _
  target_inverse := pullback.lift_fst _ _ _
  source_comp := pullback.lift_snd _ _ _
  target_comp := pullback.lift_fst _ _ _
  left_identity := by
    intro T g w
    apply pullback.hom_ext <;>
      simp
  right_identity := by
    intro T g w
    apply pullback.hom_ext <;>
      simp
  left_inverse := by
    intro T g w
    apply pullback.hom_ext <;>
      simp
  right_inverse := by
    intro T g w
    apply pullback.hom_ext <;>
      simp
  assoc := by
    intro T g₁ g₂ g₃ w₁₂ w₂₃ w w'
    apply pullback.hom_ext <;>
      simp

/-- The objects of the Čech groupoid of `f` are `X`. -/
@[simp]
theorem cechGroupoid_objects : (cechGroupoid f).objects = X := rfl

/-- The arrows of the Čech groupoid of `f` are the kernel pair `X ×_Y X`. -/
@[simp]
theorem cechGroupoid_arrows : (cechGroupoid f).arrows = pullback f f := rfl

/-- The source map of the Čech groupoid is the second projection of the kernel pair. -/
@[simp]
theorem cechGroupoid_source : (cechGroupoid f).source = pullback.snd f f := rfl

/-- The target map of the Čech groupoid is the first projection of the kernel pair. -/
@[simp]
theorem cechGroupoid_target : (cechGroupoid f).target = pullback.fst f f := rfl

/-- The identity section of the Čech groupoid is the diagonal of the kernel pair. -/
@[simp]
theorem cechGroupoid_identity :
    (cechGroupoid f).identity = pullback.lift (𝟙 X) (𝟙 X) rfl := rfl

/-- Inversion in the Čech groupoid exchanges the two projections of the kernel pair. -/
@[simp]
theorem cechGroupoid_inverse :
    (cechGroupoid f).inverse =
      pullback.lift (pullback.snd f f) (pullback.fst f f) pullback.condition.symm := rfl

/-- The Čech groupoid extends the kernel-pair equivalence relation of `f`. -/
theorem extendsRelation_cechGroupoid :
    ExtendsRelation (cechPreRelation f) (cechGroupoid f) where
  objects_eq := rfl
  arrows_eq := rfl
  source_eq :=
    (Category.id_comp _).trans
      ((Category.comp_id _).trans (cechPreRelation_source f).symm)
  target_eq :=
    (Category.id_comp _).trans
      ((Category.comp_id _).trans (cechPreRelation_target f).symm)

/-- The Čech groupoid of `f` is the groupoid scheme that Tag 0233 attaches to the kernel-pair
equivalence relation of `f`. -/
theorem groupoidSchemeOfIsEquivalenceRelation_cechPreRelation :
    groupoidSchemeOfIsEquivalenceRelation (cechPreRelation f) = cechGroupoid f :=
  (existsUnique_groupoidScheme_of_isEquivalenceRelation (cechPreRelation f)).unique
    (groupoidSchemeOfIsEquivalenceRelation_extendsRelation _) (extendsRelation_cechGroupoid f)

end AlgebraicGeometry

end
