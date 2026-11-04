module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.Functoriality

/-!
# Transitivity of the automorphism group of a fibre functor on fibres

Let `(C, F)` be a Galois category and let `G = Aut F` be the automorphism group of its fibre
functor. For every connected object `X` of `C` the action of `G` on the fibre `F.obj X`, which
sends `σ` and `x` to `σ.hom.app X x`, is transitive.

## Main results

* `Stacks.FundamentalGroup.exists_aut_app_eq_of_isConnected` — the automorphism group of the
  fibre functor of a Galois category acts transitively on the fibre of a connected object.
* `Stacks.FundamentalGroup.isPretransitive_fiber_of_isConnected` — the same statement for a
  fibre functor with values in finite sets, phrased with `MulAction.IsPretransitive`.

## Implementation notes

The group acting is the automorphism group of the set-valued fibre functor, as in the
construction of the profinite group of Tag 0BMW. Transitivity is a statement about the
underlying group, so the topology plays no role.

A Galois category in the sense of Tag 0BMY carries its fibre functor as data, and that functor
takes values in sets whose finiteness is asserted separately rather than being part of the type.
The proof passes to Mathlib's `CategoryTheory.GaloisCategory` and equips the finite-set-valued
functor that `F` lifts to with a `CategoryTheory.PreGaloisCategory.FiberFunctor` structure; the
natural automorphism produced by Mathlib is returned to `Aut F` by whiskering with the inclusion
of finite sets into sets.

## References

* [Stacks Project, Tag 0BN3](https://stacks.math.columbia.edu/tag/0BN3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.FundamentalGroup

variable {C : Type u} [Category.{v, u} C]

/-- **Stacks Project, Tag 0BN3.** The automorphism group of the fibre functor of a Galois
category acts transitively on the fibre of a connected object. -/
@[stacks 0BN3, sga "1 V 5.3" "connected => transitive"]
theorem exists_aut_app_eq_of_isConnected (F : C ⥤ Type w) [hG : IsGaloisCategory F] (X : C)
    [PreGaloisCategory.IsConnected X] (x y : F.obj X) :
    ∃ σ : Aut F, σ.hom.app X x = y := by
  let : CategoryTheory.GaloisCategory C := IsGaloisCategory.toGaloisCategory F
  let F' : C ⥤ FintypeCat.{w} := ObjectProperty.lift _ F fun Y => hG.finite_obj Y
  let : IsGaloisCategory (F' ⋙ FintypeCat.incl) := hG
  let : PreGaloisCategory.FiberFunctor F' := IsGaloisCategory.fiberFunctor F'
  have h : MulAction.IsPretransitive (Aut F') (F'.obj X) := inferInstance
  obtain ⟨σ, hσ⟩ := h.exists_smul_eq (x : F'.obj X) (y : F'.obj X)
  exact ⟨Functor.isoWhiskerRight σ FintypeCat.incl, hσ⟩

/-- The automorphism group of a fibre functor with values in finite sets acts transitively on the
fibre of a connected object. -/
theorem isPretransitive_fiber_of_isConnected (F : C ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)] (X : C) [PreGaloisCategory.IsConnected X] :
    MulAction.IsPretransitive (Aut F) (F.obj X) := by
  let : CategoryTheory.GaloisCategory C :=
    IsGaloisCategory.toGaloisCategory (setValuedFiberFunctor F)
  let : PreGaloisCategory.FiberFunctor F := IsGaloisCategory.fiberFunctor F
  infer_instance

end Stacks.FundamentalGroup
