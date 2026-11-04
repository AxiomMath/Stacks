module

public import StacksFrontier.AlgebraicGeometry.Descent.Module.DescentData
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pushforward of module descent data

For a commutative ring map `R → A`, the pushforward of a module descent datum is the
`R`-module of sections of its underlying `A`-module on which the two canonical pullbacks
to `A ⊗[R] A` agree.

## Main definitions

* `ModuleCat.pushforward` is the functor from module descent data to `R`-modules.
* `ModuleCat.invariantSubmodule` is the submodule of invariant sections it is built from.

## Implementation notes

The object part is implemented as the submodule cut out by
`θ (m ⊗ 1) = 1 ⊗ m`.  Thus its subtype inclusion is the equalizer arrow in the source.
The morphism part is restriction of the underlying map of descent data; compatibility with
the transition maps makes this restriction well-defined.  The functor is marked
`implicit_reducible` so that dependent uses of its object and map projections compute.

## References

* [Stacks Project, Tag 08X5](https://stacks.math.columbia.edu/tag/08X5)
-/

@[expose] public section

universe u v w

noncomputable section

namespace ModuleCat

open CategoryTheory TensorProduct

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]

/-- The `R`-submodule of invariant sections of a module descent datum. -/
@[sga "1 VIII 1.6" "invariant submodule N"]
def invariantSubmodule (D : DescentData.{u, v, w} R A) :
    Submodule R (restrictModule R A D.module) where
  carrier := {m | D.transitionRestrictScalars R A (m ⊗ₜ[R] (1 : A)) =
    (1 : A) ⊗ₜ[R] m}
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [add_tmul, map_add, tmul_add, hx, hy]
  smul_mem' r x hx := by
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [← smul_tmul', map_smul, hx, tmul_smul]

/-- A morphism of descent data restricts to a map on invariant sections. -/
def pushforwardMap {D E : DescentData.{u, v, w} R A} (g : D ⟶ E) :
    invariantSubmodule R A D →ₗ[R] invariantSubmodule R A E where
  toFun x := ⟨restrictHom R A g.hom x, by
    change E.transitionRestrictScalars R A
      (restrictHom R A g.hom x.1 ⊗ₜ[R] (1 : A)) =
        (1 : A) ⊗ₜ[R] restrictHom R A g.hom x.1
    have h := LinearMap.congr_fun g.comm (x.1 ⊗ₜ[R] (1 : A))
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.rTensor_tmul] at h
    change E.transitionRestrictScalars R A
        (restrictHom R A g.hom x.1 ⊗ₜ[R] (1 : A)) =
      (restrictHom R A g.hom).lTensor A
        (D.transitionRestrictScalars R A (x.1 ⊗ₜ[R] (1 : A))) at h
    rwa [show D.transitionRestrictScalars R A (x.1 ⊗ₜ[R] (1 : A)) = (1 : A) ⊗ₜ[R] x.1 from x.2,
      LinearMap.lTensor_tmul] at h⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/-- Pushforward sends a module descent datum to the equalizer of its two pullbacks to
`A ⊗[R] A`. -/
@[implicit_reducible, stacks 08X5]
def pushforward : DescentData.{u, v, w} R A ⥤ ModuleCat.{w} R where
  obj D := ModuleCat.of R (invariantSubmodule R A D)
  map g := ModuleCat.ofHom (pushforwardMap R A g)
  map_id _ := rfl
  map_comp _ _ := rfl

end ModuleCat

end
