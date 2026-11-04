module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic

/-!
# Base change of an inverse limit of schemes

Let `{ Dⱼ }` be an inverse system of schemes, let `i` be an index, and let `f : T ⟶ Dᵢ` exhibit a
scheme `T` over the stage `Dᵢ`. Base changing the system along `f` produces the inverse system
`{ Dⱼ ×_{Dᵢ} T }` indexed by the objects `j` of the index category lying over `i`, and base
changing a cone over `{ Dⱼ }` produces a cone over that system. The result proved here is that
base change carries a limit cone to a limit cone:
`(lim Dⱼ) ×_{Dᵢ} T = lim_{j ≥ i} (Dⱼ ×_{Dᵢ} T)`.

The content is formal. Base change along `f` is the functor `CategoryTheory.Over.pullback f`,
which is right adjoint to `CategoryTheory.Over.map f` and hence preserves all limits. The two
remaining steps are equally formal: the forgetful functor from an over category of the index
category is initial as soon as that category is cofiltered, so a limit over the index category is
also a limit over the objects lying over `i`; and the forgetful functor of an over category
preserves connected limits, so a limit in `Over T` may be read off in the category of schemes.

## Main definitions

* `AlgebraicGeometry.pullbackDiagram`: the inverse system `{ Dⱼ ×_{Dᵢ} T }_{j ≥ i}` of base
  changes of a diagram `{ Dⱼ }` of schemes along a morphism `f : T ⟶ Dᵢ`.
* `AlgebraicGeometry.pullbackCone`: the cone over `AlgebraicGeometry.pullbackDiagram` with vertex
  `c.pt ×_{Dᵢ} T` obtained by base changing a cone `c` over `{ Dⱼ }` along `f`.

## Main results

* `AlgebraicGeometry.isLimitPullbackCone`: base change along `f : T ⟶ Dᵢ` carries a limit cone of
  a cofiltered inverse system of schemes to a limit cone.
* `AlgebraicGeometry.isLimitPullbackConeLimitCone`: the same statement for the limit of an inverse
  system with affine transition morphisms, whose existence is automatic.

## Implementation notes

Following `AlgebraicGeometry.isLimitOpensCone`, which is the special case where `f` is the
inclusion of an open subscheme, the index category of the truncated system `{ Dⱼ }_{j ≥ i}` is the
over category `CategoryTheory.Over i` of the index category, and the ambient diagram is a functor
out of the index category itself rather than out of a category of schemes over a fixed base.

The fibre products are written with the base changed scheme `T` as the *second* factor, which is
the convention of Mathlib's base change functor `CategoryTheory.Over.pullback`: it sends a scheme
`g : Z ⟶ Dᵢ` over `Dᵢ` to the second projection out of `Z ×_{Dᵢ} T`. Writing the diagram and the
cone as literal composites of Mathlib functors and of `CategoryTheory.Functor.mapCone` is what
makes the limit statement hold by transport of structure, with no commutation left to check.

## References

* [Stacks Project, Tag 01YZ](https://stacks.math.columbia.edu/tag/01YZ)
* [Stacks Project, Tag 01YX](https://stacks.math.columbia.edu/tag/01YX)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] {T : Scheme.{u}} (D : I ⥤ Scheme.{u})
  (c : Cone D) (hc : IsLimit c)

/-- Given a diagram `{ Dⱼ }` of schemes, an index `i`, and a scheme `T` over the stage `Dᵢ` via
`f : T ⟶ Dᵢ`, this is the inverse system `{ Dⱼ ×_{Dᵢ} T }_{j ≥ i}` of base changes along `f`,
indexed by the category `Over i` of objects of the index category lying over `i`. It is the
composite of the functor regarding `{ Dⱼ }_{j ≥ i}` as a diagram of schemes over `Dᵢ`, the base
change functor along `f`, and the forgetful functor of the over category of `T`. -/
noncomputable def pullbackDiagram (i : I) (f : T ⟶ D.obj i) : Over i ⥤ Scheme.{u} :=
  Over.post D ⋙ Over.pullback f ⋙ Over.forget T

/-- The scheme at the stage `j ≥ i` of the base changed system is the fibre product
`Dⱼ ×_{Dᵢ} T`. -/
@[simp] lemma pullbackDiagram_obj (i : I) (f : T ⟶ D.obj i) (j : Over i) :
    (pullbackDiagram D i f).obj j = pullback (D.map j.hom) f :=
  rfl

/-- The transition morphism `Dⱼ ×_{Dᵢ} T ⟶ Dₖ ×_{Dᵢ} T` of the base changed system induced by a
morphism `g : j ⟶ k` of `Over i` is the base change of the transition morphism `Dⱼ ⟶ Dₖ`. -/
@[simp] lemma pullbackDiagram_map (i : I) (f : T ⟶ D.obj i) {j k : Over i} (g : j ⟶ k) :
    (pullbackDiagram D i f).map g =
      pullback.lift (pullback.fst (D.map j.hom) f ≫ D.map g.left) (pullback.snd (D.map j.hom) f)
        (by
          change (pullback.fst (D.map j.hom) f ≫ D.map g.left) ≫ D.map k.hom =
            pullback.snd (D.map j.hom) f ≫ f
          rw [Category.assoc, ← D.map_comp, Over.w g]; exact pullback.condition) :=
  rfl

/-- The base change along `f : T ⟶ Dᵢ` of a cone `c` over a diagram `{ Dⱼ }` of schemes: a cone
over the inverse system `{ Dⱼ ×_{Dᵢ} T }_{j ≥ i}` with vertex `c.pt ×_{Dᵢ} T`. It is limiting
whenever `c` is, as witnessed by `AlgebraicGeometry.isLimitPullbackCone` below. -/
noncomputable def pullbackCone (i : I) (f : T ⟶ D.obj i) : Cone (pullbackDiagram D i f) :=
  (Over.forget T).mapCone ((Over.pullback f).mapCone ((Over.conePost D i).obj c))

/-- The vertex of the base changed cone is the fibre product of the vertex of `c` with `T`
over `Dᵢ`. -/
@[simp] lemma pullbackCone_pt (i : I) (f : T ⟶ D.obj i) :
    (pullbackCone D c i f).pt = pullback (c.π.app i) f :=
  rfl

/-- The projection of the base changed cone to the stage `j ≥ i` is the base change of the
projection `c.pt ⟶ Dⱼ` of `c`. -/
@[simp] lemma pullbackCone_π_app (i : I) (f : T ⟶ D.obj i) (j : Over i) :
    (pullbackCone D c i f).π.app j =
      pullback.lift (pullback.fst (c.π.app i) f ≫ c.π.app j.left) (pullback.snd (c.π.app i) f)
        (by
          change (pullback.fst (c.π.app i) f ≫ c.π.app j.left) ≫ D.map j.hom =
            pullback.snd (c.π.app i) f ≫ f
          rw [Category.assoc, c.w j.hom]; exact pullback.condition) :=
  rfl

attribute [local instance] CategoryTheory.isConnected_of_hasTerminal

include hc in
/-- **Base change commutes with inverse limits of schemes.** Let `{ Dⱼ }` be an inverse system of
schemes indexed by a cofiltered category, let `c` be a limit cone over it, let `i` be an index,
and let `f : T ⟶ Dᵢ` be a scheme over the stage `Dᵢ`. Then
`(lim Dⱼ) ×_{Dᵢ} T = lim_{j ≥ i} (Dⱼ ×_{Dᵢ} T)`.

This is stated for an arbitrary limit cone `c`, so it applies in particular to the limit of a
system with affine transition morphisms, whose existence is
`AlgebraicGeometry.hasLimit_of_isCofiltered_of_isAffineHom`; that specialisation is recorded as
`AlgebraicGeometry.isLimitPullbackConeLimitCone`. -/
@[stacks 01YZ] noncomputable
def isLimitPullbackCone [IsCofiltered I] (i : I) (f : T ⟶ D.obj i) :
    IsLimit (pullbackCone D c i f) :=
  isLimitOfPreserves (Over.forget T)
    (isLimitOfPreserves (Over.pullback f) (Over.isLimitConePost i hc))

/-- **Base change commutes with inverse limits of schemes with affine transition morphisms.** Let
`{ Dⱼ }` be an inverse system of schemes indexed by a cofiltered category whose transition
morphisms are all affine, let `i` be an index, and let `f : T ⟶ Dᵢ` be a scheme over the stage
`Dᵢ`. Then the limit of `{ Dⱼ }` exists and `(lim Dⱼ) ×_{Dᵢ} T = lim_{j ≥ i} (Dⱼ ×_{Dᵢ} T)`. -/
noncomputable def isLimitPullbackConeLimitCone [IsCofiltered I]
    [∀ {j k : I} (g : j ⟶ k), IsAffineHom (D.map g)] (i : I) (f : T ⟶ D.obj i) :
    IsLimit (pullbackCone D (limit.cone D) i f) :=
  isLimitPullbackCone D (limit.cone D) (limit.isLimit D) i f

/-! ### Section 01YV

Lemma 01YZ, that base change commutes with the limit, is the last of the three assertions of
section 01YV. -/

add_to_stacks 01YV "base change commutes with the limit of the system (Lemma 01YZ)"
  AlgebraicGeometry.isLimitPullbackCone

end AlgebraicGeometry

end
