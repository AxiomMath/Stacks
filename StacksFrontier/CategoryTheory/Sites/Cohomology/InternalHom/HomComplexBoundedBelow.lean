module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexFunctoriality
import StacksCore.Tactic.StacksAttribute

/-! # The internal Hom complex out of a bounded-above complex into a bounded-below one

Let `(C, O)` be a ringed site, let `K` be a complex of `O`-modules concentrated in degrees `≤ d`
and let `M` be one concentrated in degrees `≥ b`. Then the internal Hom complex `SheafHom(K, M)`
of Stacks 0A8Z is concentrated in degrees `≥ b - d`.

The bound is read on sections. Over an object `U` of the site the degree-`n` sections of
`SheafHom(K, M)` are the degree-`n` cochains from `K|_U` to `M|_U`, and such a cochain is a
family of morphisms `K^p|_U ⟶ M^q|_U` indexed by the pairs with `p + n = q`. If `n < b - d` then
every such pair has `p > d` or `q < b`, so each component has a zero source or a zero target and
the whole cochain group is trivial. A sheaf of modules with no nonzero sections is zero.

## Main results

* `AlgebraicGeometry.RingedSite.isStrictlyGE_sheafHomComplex`: the bound `b - d`, on the nose
  rather than merely cohomologically.
* `AlgebraicGeometry.RingedSite.isStrictlyLE_sheafHomComplex`: the dual bound, out of a complex
  concentrated in degrees `≥ e` into one concentrated in degrees `≤ d`, by the same argument.

## Implementation notes

The internal Hom complex is available only through its characterising data, so the degree-`n`
term is reached through `AlgebraicGeometry.RingedSite.SheafHomComplex.sectionsEquiv`, the
additive description of its sections, and not by unfolding a product.

The three site universes and the module universe are independent, as they are for the internal
Hom complex itself; no sheafification, abelian structure or derived category is involved.

## References

* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe m u v w

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w})

/-- A sheaf of modules all of whose sections vanish is a zero object: its identity is the zero
morphism, because a morphism of sheaves of modules is determined by its action on sections. -/
private theorem isZero_of_forall_section_eq_zero
    {A : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (h : ∀ (U : X.Cᵒᵖ) (x : A.val.obj U), x = 0) : IsZero A := by
  rw [IsZero.iff_id_eq_zero]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [h U x]
  simp

/-- **The internal Hom complex of a bounded-above complex into a bounded-below complex is
bounded below.** If `K` is concentrated in degrees `≤ d` and `M` in degrees `≥ b`, then
`SheafHom(K, M)` is concentrated in degrees `≥ b - d`. -/
public theorem isStrictlyGE_sheafHomComplex
    (K M : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (d b : ℤ)
    [CochainComplex.IsStrictlyLE K d] [CochainComplex.IsStrictlyGE M b] :
    CochainComplex.IsStrictlyGE (sheafHomComplex X K M).obj (b - d) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  refine isZero_of_forall_section_eq_zero X fun U s => ?_
  refine (AddEquiv.map_eq_zero_iff
    ((sheafHomComplex X K M).sectionsEquiv U.unop n)).1 ?_
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [Cochain.zero_v]
  rcases lt_or_ge d p with hp | hp
  · exact IsZero.eq_of_src
      (Functor.map_isZero
        (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U.unop)
        (CochainComplex.isZero_of_isStrictlyLE K d p hp)) _ _
  · exact IsZero.eq_of_tgt
      (Functor.map_isZero
        (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U.unop)
        (CochainComplex.isZero_of_isStrictlyGE M b q (by omega))) _ _

/-- **The internal Hom complex of a bounded-below complex into a bounded-above complex is
bounded above.** If `K` is concentrated in degrees `≥ e` and `M` in degrees `≤ d`, then
`SheafHom(K, M)` is concentrated in degrees `≤ d - e`. -/
public theorem isStrictlyLE_sheafHomComplex
    (K M : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (e d : ℤ)
    [CochainComplex.IsStrictlyGE K e] [CochainComplex.IsStrictlyLE M d] :
    CochainComplex.IsStrictlyLE (sheafHomComplex X K M).obj (d - e) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  refine isZero_of_forall_section_eq_zero X fun U s => ?_
  refine (AddEquiv.map_eq_zero_iff
    ((sheafHomComplex X K M).sectionsEquiv U.unop n)).1 ?_
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [Cochain.zero_v]
  rcases lt_or_ge p e with hp | hp
  · exact IsZero.eq_of_src
      (Functor.map_isZero
        (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U.unop)
        (CochainComplex.isZero_of_isStrictlyGE K e p hp)) _ _
  · exact IsZero.eq_of_tgt
      (Functor.map_isZero
        (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U.unop)
        (CochainComplex.isZero_of_isStrictlyLE M d q (by omega))) _ _

end AlgebraicGeometry.RingedSite

end
