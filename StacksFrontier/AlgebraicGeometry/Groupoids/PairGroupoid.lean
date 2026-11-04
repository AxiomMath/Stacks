module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Compose

/-!
# The groupoid scheme of a morphism of schemes

Let `f : X ⟶ S` be a morphism of schemes.  The *pair groupoid* of `f` is the groupoid scheme
over `S` whose objects are `X`, whose arrows are `X ×_S X`, whose target is the first
projection and whose source is the second projection.  Its identity is the diagonal, its
inverse is the exchange of the two factors, and the composite of `(x, y)` and `(y, z)` is
`(x, z)`.

## Main definitions

* `AlgebraicGeometry.pairArrows` is the arrow scheme `X ×_S X`, as a scheme over `S`.  The
  object scheme is `CategoryTheory.Over.mk f`.
* `AlgebraicGeometry.pairTarget`, `AlgebraicGeometry.pairSource`,
  `AlgebraicGeometry.pairIdentity`, `AlgebraicGeometry.pairInverse` and
  `AlgebraicGeometry.pairComposition` are the structure morphisms.
* `AlgebraicGeometry.pairGroupoid` is the resulting groupoid scheme over `S`.
* `AlgebraicGeometry.pairArrowMk` is the generalized arrow with prescribed target and source.

## Main results

* `AlgebraicGeometry.pairArrow_ext`: a generalized arrow of the pair groupoid is determined by
  its target and its source.
* `AlgebraicGeometry.pairArrowMk_target` and `AlgebraicGeometry.pairArrowMk_source` read the
  target and source off `AlgebraicGeometry.pairArrowMk`, and
  `AlgebraicGeometry.pairArrowMk_eq` says every generalized arrow is of that form.
* `AlgebraicGeometry.pairGroupoid_compose_pairArrowMk`,
  `AlgebraicGeometry.pairArrowMk_comp_pairInverse` and
  `AlgebraicGeometry.comp_pairIdentity_eq` compute composition, inversion and the identity
  section on generalized arrows: `(x, y) ∘ (y, z) = (x, z)`, `(x, y)⁻¹ = (y, x)` and the
  identity arrow at `x` is `(x, x)`.

## References

* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
* [Stacks Project, Tag 0APF](https://stacks.math.columbia.edu/tag/0APF)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The arrow scheme of the pair groupoid of `f : X ⟶ S`: the scheme `X ×_S X` over `S`. -/
abbrev pairArrows : Over S := Over.mk (pullback.fst f f ≫ f)

/-- The structure morphism of `pairArrows f` is the first projection followed by `f`. -/
@[simp]
lemma pairArrows_hom : (pairArrows f).hom = pullback.fst f f ≫ f := rfl

/-- The target of an arrow of the pair groupoid: the first projection of `X ×_S X`. -/
def pairTarget : pairArrows f ⟶ Over.mk f := Over.homMk (pullback.fst f f)

/-- The source of an arrow of the pair groupoid: the second projection of `X ×_S X`. -/
def pairSource : pairArrows f ⟶ Over.mk f :=
  Over.homMk (pullback.snd f f) pullback.condition.symm

/-- On underlying schemes, the target is the first projection `X ×_S X ⟶ X`. -/
@[simp]
lemma pairTarget_left : (pairTarget f).left = pullback.fst f f := rfl

/-- On underlying schemes, the source is the second projection `X ×_S X ⟶ X`. -/
@[simp]
lemma pairSource_left : (pairSource f).left = pullback.snd f f := rfl

/-- A generalized arrow of the pair groupoid is determined by its target and its source. -/
lemma pairArrow_ext {T : Over S} {a b : T ⟶ pairArrows f}
    (ht : a ≫ pairTarget f = b ≫ pairTarget f)
    (hs : a ≫ pairSource f = b ≫ pairSource f) : a = b := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simpa using congrArg Over.Hom.left ht
  · simpa using congrArg Over.Hom.left hs

/-- The identity section of the pair groupoid: the diagonal `X ⟶ X ×_S X`. -/
def pairIdentity : Over.mk f ⟶ pairArrows f :=
  Over.homMk (pullback.lift (𝟙 X) (𝟙 X) rfl)
    (by rw [pairArrows_hom, pullback.lift_fst_assoc]; exact Category.id_comp f)

/-- Inversion in the pair groupoid: the exchange of the two factors of `X ×_S X`. -/
def pairInverse : pairArrows f ⟶ pairArrows f :=
  Over.homMk (pullback.lift (pullback.snd f f) (pullback.fst f f) pullback.condition.symm)
    (by rw [pairArrows_hom, pullback.lift_fst_assoc, pullback.condition])

/-- The target of the identity section is the identity of `X`. -/
@[simp]
lemma pairIdentity_target : pairIdentity f ≫ pairTarget f = 𝟙 (Over.mk f) :=
  Over.OverMorphism.ext (pullback.lift_fst _ _ _)

/-- The source of the identity section is the identity of `X`. -/
@[simp]
lemma pairIdentity_source : pairIdentity f ≫ pairSource f = 𝟙 (Over.mk f) :=
  Over.OverMorphism.ext (pullback.lift_snd _ _ _)

/-- The target of the inverse of an arrow is its source. -/
@[simp]
lemma pairInverse_target : pairInverse f ≫ pairTarget f = pairSource f :=
  Over.OverMorphism.ext (pullback.lift_fst _ _ _)

/-- The source of the inverse of an arrow is its target. -/
@[simp]
lemma pairInverse_source : pairInverse f ≫ pairSource f = pairTarget f :=
  Over.OverMorphism.ext (pullback.lift_snd _ _ _)

/-- For a composable pair of arrows of the pair groupoid, the first coordinate of the first
factor and the second coordinate of the second factor have the same image in `S`. -/
lemma pairComposition_aux :
    ((pullback.fst (pairSource f) (pairTarget f)).left ≫ pullback.fst f f) ≫ f =
      ((pullback.snd (pairSource f) (pairTarget f)).left ≫ pullback.snd f f) ≫ f := by
  have h1 := Over.w (pullback.fst (pairSource f) (pairTarget f))
  have h2 := Over.w (pullback.snd (pairSource f) (pairTarget f))
  rw [pairArrows_hom] at h1 h2
  rw [Category.assoc, Category.assoc, ← pullback.condition, h1, h2]

/-- Composition in the pair groupoid, on underlying schemes: the composite of `(x, y)` and
`(y, z)` is `(x, z)`. -/
def pairCompLeft : (pullback (pairSource f) (pairTarget f)).left ⟶ pullback f f :=
  pullback.lift ((pullback.fst (pairSource f) (pairTarget f)).left ≫ pullback.fst f f)
    ((pullback.snd (pairSource f) (pairTarget f)).left ≫ pullback.snd f f)
    (pairComposition_aux f)

/-- The first coordinate of `pairCompLeft f` is the first coordinate of the first factor. -/
@[simp]
lemma pairCompLeft_fst :
    pairCompLeft f ≫ pullback.fst f f =
      (pullback.fst (pairSource f) (pairTarget f)).left ≫ pullback.fst f f :=
  pullback.lift_fst _ _ _

/-- The second coordinate of `pairCompLeft f` is the second coordinate of the second factor. -/
@[simp]
lemma pairCompLeft_snd :
    pairCompLeft f ≫ pullback.snd f f =
      (pullback.snd (pairSource f) (pairTarget f)).left ≫ pullback.snd f f :=
  pullback.lift_snd _ _ _

/-- Composition in the pair groupoid: the composite of `(x, y)` and `(y, z)` is `(x, z)`. -/
def pairComposition : pullback (pairSource f) (pairTarget f) ⟶ pairArrows f :=
  Over.homMk (pairCompLeft f)
    (by simpa [reassoc_of% pairCompLeft_fst f] using
      Over.w (pullback.fst (pairSource f) (pairTarget f)))

/-- The target of a composite is the target of the first factor. -/
@[simp]
lemma pairComposition_target :
    pairComposition f ≫ pairTarget f =
      pullback.fst (pairSource f) (pairTarget f) ≫ pairTarget f :=
  Over.OverMorphism.ext (pairCompLeft_fst f)

/-- The source of a composite is the source of the second factor. -/
@[simp]
lemma pairComposition_source :
    pairComposition f ≫ pairSource f =
      pullback.snd (pairSource f) (pairTarget f) ≫ pairSource f :=
  Over.OverMorphism.ext (pairCompLeft_snd f)

/-- The target of a composite of generalized arrows is the target of the first factor. -/
lemma pairComposition_lift_target {T : Over S} (a b : T ⟶ pairArrows f)
    (w : a ≫ pairSource f = b ≫ pairTarget f) :
    (pullback.lift a b w ≫ pairComposition f) ≫ pairTarget f = a ≫ pairTarget f := by
  rw [Category.assoc, pairComposition_target, ← Category.assoc, pullback.lift_fst]

/-- The source of a composite of generalized arrows is the source of the second factor. -/
lemma pairComposition_lift_source {T : Over S} (a b : T ⟶ pairArrows f)
    (w : a ≫ pairSource f = b ≫ pairTarget f) :
    (pullback.lift a b w ≫ pairComposition f) ≫ pairSource f = b ≫ pairSource f := by
  rw [Category.assoc, pairComposition_source, ← Category.assoc, pullback.lift_snd]

/-- **The groupoid scheme of a morphism of schemes.**  For `f : X ⟶ S` this is the groupoid
scheme over `S` with objects `X`, arrows `X ×_S X`, target the first and source the second
projection, identity the diagonal, inverse the exchange of factors, and composition
`(x, y) ∘ (y, z) = (x, z)`. -/
def pairGroupoid : GroupoidScheme S where
  objects := Over.mk f
  arrows := pairArrows f
  source := pairSource f
  target := pairTarget f
  comp := pairComposition f
  identity := pairIdentity f
  inverse := pairInverse f
  source_identity := pairIdentity_source f
  target_identity := pairIdentity_target f
  source_inverse := pairInverse_source f
  target_inverse := pairInverse_target f
  source_comp := pairComposition_source f
  target_comp := pairComposition_target f
  left_identity := by
    intro T a w
    refine pairArrow_ext f ?_ ?_
    · rw [pairComposition_lift_target]
      simp
    · rw [pairComposition_lift_source]
  right_identity := by
    intro T a w
    refine pairArrow_ext f ?_ ?_
    · rw [pairComposition_lift_target]
    · rw [pairComposition_lift_source]
      simp
  left_inverse := by
    intro T a w
    refine pairArrow_ext f ?_ ?_
    · rw [pairComposition_lift_target]
      simp
    · rw [pairComposition_lift_source]
      simp
  right_inverse := by
    intro T a w
    refine pairArrow_ext f ?_ ?_
    · rw [pairComposition_lift_target]
      simp
    · rw [pairComposition_lift_source]
      simp
  assoc := by
    intro T a b c wab wbc w₁ w₂
    refine pairArrow_ext f ?_ ?_
    · rw [pairComposition_lift_target, pairComposition_lift_target,
        pairComposition_lift_target]
    · rw [pairComposition_lift_source, pairComposition_lift_source,
        pairComposition_lift_source]

/-- The object scheme of `pairGroupoid f` is `X` over `S`. -/
@[simp]
lemma pairGroupoid_objects : (pairGroupoid f).objects = Over.mk f := rfl

/-- The arrow scheme of `pairGroupoid f` is `pairArrows f`. -/
@[simp]
lemma pairGroupoid_arrows : (pairGroupoid f).arrows = pairArrows f := rfl

/-- The source morphism of `pairGroupoid f` is `pairSource f`. -/
@[simp]
lemma pairGroupoid_source : (pairGroupoid f).source = pairSource f := rfl

/-- The target morphism of `pairGroupoid f` is `pairTarget f`. -/
@[simp]
lemma pairGroupoid_target : (pairGroupoid f).target = pairTarget f := rfl

/-- The composition morphism of `pairGroupoid f` is `pairComposition f`. -/
@[simp]
lemma pairGroupoid_comp : (pairGroupoid f).comp = pairComposition f := rfl

/-- The identity section of `pairGroupoid f` is `pairIdentity f`. -/
@[simp]
lemma pairGroupoid_identity : (pairGroupoid f).identity = pairIdentity f := rfl

/-- The inversion morphism of `pairGroupoid f` is `pairInverse f`. -/
@[simp]
lemma pairGroupoid_inverse : (pairGroupoid f).inverse = pairInverse f := rfl

/-- The generalized arrow of the pair groupoid with target `x` and source `y`. -/
def pairArrowMk {T : Over S} (x y : T ⟶ Over.mk f) : T ⟶ pairArrows f :=
  Over.homMk (pullback.lift x.left y.left
      (show x.left ≫ f = y.left ≫ f from (Over.w x).trans (Over.w y).symm))
    (by rw [pairArrows_hom, pullback.lift_fst_assoc]; exact Over.w x)

/-- The target of the generalized arrow `pairArrowMk f x y` is `x`. -/
@[simp]
lemma pairArrowMk_target {T : Over S} (x y : T ⟶ Over.mk f) :
    pairArrowMk f x y ≫ pairTarget f = x :=
  Over.OverMorphism.ext (pullback.lift_fst _ _ _)

/-- The source of the generalized arrow `pairArrowMk f x y` is `y`. -/
@[simp]
lemma pairArrowMk_source {T : Over S} (x y : T ⟶ Over.mk f) :
    pairArrowMk f x y ≫ pairSource f = y :=
  Over.OverMorphism.ext (pullback.lift_snd _ _ _)

/-- A generalized arrow with target `x` and source `y` is `pairArrowMk f x y`. -/
private theorem eq_pairArrowMk {T : Over S} {a : T ⟶ pairArrows f} {x y : T ⟶ Over.mk f}
    (ht : a ≫ pairTarget f = x) (hs : a ≫ pairSource f = y) : a = pairArrowMk f x y :=
  pairArrow_ext f (by rw [pairArrowMk_target, ht]) (by rw [pairArrowMk_source, hs])

/-- Every generalized arrow of the pair groupoid is the arrow determined by its target and its
source. -/
lemma pairArrowMk_eq {T : Over S} (a : T ⟶ pairArrows f) :
    pairArrowMk f (a ≫ pairTarget f) (a ≫ pairSource f) = a :=
  (eq_pairArrowMk f rfl rfl).symm

/-- Precomposing the generalized arrow `(x, y)` with `k` gives `(k ≫ x, k ≫ y)`. -/
@[simp]
lemma comp_pairArrowMk {T U : Over S} (k : U ⟶ T) (x y : T ⟶ Over.mk f) :
    k ≫ pairArrowMk f x y = pairArrowMk f (k ≫ x) (k ≫ y) :=
  eq_pairArrowMk f (by simp) (by simp)

/-- The identity arrow at a generalized point `x` is `(x, x)`. -/
lemma comp_pairIdentity_eq {T : Over S} (x : T ⟶ Over.mk f) :
    x ≫ pairIdentity f = pairArrowMk f x x :=
  eq_pairArrowMk f (by simp) (by simp)

/-- The inverse of the generalized arrow `(x, y)` is `(y, x)`. -/
lemma pairArrowMk_comp_pairInverse {T : Over S} (x y : T ⟶ Over.mk f) :
    pairArrowMk f x y ≫ pairInverse f = pairArrowMk f y x :=
  eq_pairArrowMk f (by simp) (by simp)

/-- Composition of generalized arrows of the pair groupoid: `(x, y) ∘ (y, z) = (x, z)`. -/
lemma pairGroupoid_compose_pairArrowMk {T : Over S} (x y z : T ⟶ Over.mk f)
    (w : pairArrowMk f x y ≫ (pairGroupoid f).source =
      pairArrowMk f y z ≫ (pairGroupoid f).target) :
    (pairGroupoid f).compose (pairArrowMk f x y) (pairArrowMk f y z) w =
      pairArrowMk f x z := by
  refine eq_pairArrowMk f ?_ ?_
  · exact (groupoidCompose_target (pairGroupoid f) _ _ w).trans (pairArrowMk_target f x y)
  · exact (groupoidCompose_source (pairGroupoid f) _ _ w).trans (pairArrowMk_source f y z)

end AlgebraicGeometry

end

end
