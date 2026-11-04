module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Order

/-!
# The order of a thickening of algebraic spaces is preserved by base change

Let `f : X' ⟶ Y'` be a morphism of algebraic spaces over a scheme `S` and let `Y ⊂ Y'` be an
`n`th-order thickening in the sense of Stacks 05ZK, part (4).  Its inverse image
`Y ×_{Y'} X' ⊂ X'` is then again an `n`th-order thickening.  This completes the order clauses
of Stacks 09ZX, whose order-free part is
`AlgebraicGeometry.Space.isThickening_preimage`.

## Main results

* `AlgebraicGeometry.Space.definingIdealAt_pow_eq_bot_of_ofArrows`: the vanishing of a power
  of the defining ideal of a closed subspace at one étale chart may be checked on a covering
  family of that chart.
* `AlgebraicGeometry.Space.isNthOrderThickening_preimage`: **Stacks 09ZX**, the inverse image
  of an `n`th-order thickening along an arbitrary morphism of algebraic spaces.
* `AlgebraicGeometry.Space.isFirstOrderThickening_preimage` and
  `AlgebraicGeometry.Space.isFiniteOrderThickening_preimage`: the first- and finite-order
  cases.

## Implementation notes

The defining ideal of an inverse image is the extension of the defining ideal of the original
subspace only on *affine* charts lying over *affine* charts, which is
`AlgebraicGeometry.Space.definingIdealAt_preimage_eq_map`; an arbitrary chart of `X'` need not
lie over a chart of `Y'` at all.  What bridges the gap is the cofinality of the affine chart
diagrams, Stacks 03G2, in the form
`AlgebraicGeometry.Space.exists_affine_chartDiagram_ofArrows`: every étale chart of `X'` is
covered by affine charts each of which does lie over an affine chart of `Y'`.  On each member
of that covering family the extension formula applies and the power of the extended ideal
vanishes because extension commutes with products of ideals.

Descending the vanishing from the covering family to the chart itself is the one point where
sheaf theory enters.  A power of an ideal is not a sheaf-local notion in general, but the
restriction of the defining ideal at a chart lands inside the defining ideal at a smaller
chart (`AlgebraicGeometry.Space.definingIdealAt_map`), so every section of the `(n+1)`st power
upstairs restricts into the `(n+1)`st power downstairs, where it vanishes; separatedness of the
structure sheaf of the small étale site then makes it zero.  That argument is isolated as
`AlgebraicGeometry.Space.definingIdealAt_pow_eq_bot_of_ofArrows`.

## References

* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

/-! ### Two elementary facts about powers of ideals -/

/-- A ring homomorphism carrying an ideal into an ideal carries the positive powers of the
first into the corresponding powers of the second. -/
private theorem le_comap_pow_succ {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S)
    {I : Ideal R} {J : Ideal S} (hIJ : I ≤ Ideal.comap φ J) (m : ℕ) :
    I ^ (m + 1) ≤ Ideal.comap φ (J ^ (m + 1)) := by
  induction m with
  | zero => rw [Submodule.pow_one, Submodule.pow_one]; exact hIJ
  | succ m ih =>
    rw [Submodule.pow_succ (n := m + 1), Submodule.pow_succ (n := m + 1)]
    refine Submodule.mul_le.2 fun r hr s hs => Ideal.mem_comap.2 ?_
    rw [map_mul]
    exact Submodule.mul_mem_mul (ih hr) (hIJ hs)

/-- The extension of an ideal with vanishing `m`th power along a ring homomorphism again has
vanishing `m`th power. -/
private theorem map_pow_eq_bot {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    {I : Ideal R} {m : ℕ} (h : I ^ m = ⊥) : Ideal.map φ I ^ m = ⊥ := by
  rw [← Ideal.map_pow, h, Ideal.map_bot]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Locality of the vanishing of a power of the defining ideal -/

/-- **The vanishing of a power of the defining ideal is local on the small étale site.** If a
family of arrows into an étale chart `U` generates a covering sieve and the `(n+1)`st power of
the defining ideal of a closed subspace vanishes on each member of the family, then it vanishes
on `U`. -/
theorem definingIdealAt_pow_eq_bot_of_ofArrows (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (n : ℕ) (U : SmallEtale B S hS X.1)
    {I : Type u} (W : I → SmallEtale B S hS X.1) (a : ∀ i, W i ⟶ U)
    (hcov : Sieve.ofArrows W a ∈ SmallEtale.topology B S hS X.1 U)
    (h : ∀ i, definingIdealAt B S hS X Z (op (W i)) ^ (n + 1) = ⊥) :
    definingIdealAt B S hS X Z (op U) ^ (n + 1) = ⊥ := by
  refine le_bot_iff.1 fun x hx => Ideal.mem_bot.2 ?_
  refine (structureRingSheaf B S hS X).property.isSeparated U _ hcov x 0 ?_
  rintro V m ⟨Y₀, g, k, ⟨i⟩, rfl⟩
  have hcomap : definingIdealAt B S hS X Z (op U) ≤
      Ideal.comap ((structureRingSheaf B S hS X).obj.map (a i).op).hom
        (definingIdealAt B S hS X Z (op (W i))) :=
    fun b hb => definingIdealAt_map B S hS X Z (a i).op b hb
  have hzero : ((structureRingSheaf B S hS X).obj.map (a i).op).hom x = 0 := by
    have hmem := Ideal.mem_comap.1
      (le_comap_pow_succ ((structureRingSheaf B S hS X).obj.map (a i).op).hom hcomap n hx)
    rw [h i] at hmem
    exact Ideal.mem_bot.1 hmem
  have hsplit : ∀ y : ToType ((structureRingSheaf B S hS X).obj.obj (op U)),
      ((structureRingSheaf B S hS X).obj.map (g ≫ a i).op).hom y =
        ((structureRingSheaf B S hS X).obj.map g.op).hom
          (((structureRingSheaf B S hS X).obj.map (a i).op).hom y) := by
    intro y
    rw [op_comp, Functor.map_comp]
    rfl
  rw [hsplit x, hsplit 0, hzero, map_zero, map_zero, map_zero]

/-! ### Base change of a thickening of a given order -/

/-- **Stacks 09ZX.** The inverse image of an `n`th-order thickening `Y ⊂ Y'` along an arbitrary
morphism `f : X' ⟶ Y'` of algebraic spaces is an `n`th-order thickening of `X'`.

It is a thickening by the order-free part of the tag.  Its defining ideal on an affine chart of
`X'` lying over an affine chart of `Y'` is the extension of the defining ideal of `Y` there, so
its `(n+1)`st power is the extension of the `(n+1)`st power and vanishes; the affine chart
diagrams are cofinal by Stacks 03G2, and the vanishing descends from a covering family. -/
@[stacks 09ZX "base change of an nth-order thickening"]
theorem isNthOrderThickening_preimage {n : ℕ} {Y' X' : AlgebraicSpaces B S hS}
    (Y : Subfunctor Y'.1) (f : X' ⟶ Y') (hY : IsNthOrderThickening B S hS n Y' Y) :
    IsNthOrderThickening B S hS n X' (Y.preimage f.hom) := by
  refine ⟨isThickening_preimage B S hS Y f hY.1, fun U => ?_⟩
  obtain ⟨J, W, a, d, hdU, hWaff, hVaff, hcov⟩ :=
    exists_affine_chartDiagram_ofArrows B S hS f U
  refine definingIdealAt_pow_eq_bot_of_ofArrows B S hS X' _ n U W a hcov fun i => ?_
  have hVa : IsAffine ((BigFppfOver.toScheme B S hS).obj (d i).V.1.left) := hVaff i
  have hUa : IsAffine ((BigFppfOver.toScheme B S hS).obj (d i).U.1.left) := by
    rw [hdU i]; exact hWaff i
  have hkey := definingIdealAt_preimage_eq_map B S hS f ⟨Y, hY.1.1⟩ (d i).V (d i).U
    (d i).g (d i).comm.symm
  rw [← hdU i, show (⟨Y.preimage f.hom, isThickening_preimage B S hS Y f hY.1 |>.1⟩ :
      ClosedSubspaces B S hS X'.1) =
    ⟨Y.preimage f.hom, isClosedSubspace_preimage B S hS f.hom Y Y'.2 X'.2 hY.1.1⟩ from rfl,
    hkey]
  exact map_pow_eq_bot ((BigFppfOver.toScheme B S hS).map (d i).g).appTop.hom (hY.2 (d i).V)

/-- **Stacks 09ZX.** The inverse image of a first-order thickening along an arbitrary morphism
of algebraic spaces is a first-order thickening: the case `n = 1` of
`AlgebraicGeometry.Space.isNthOrderThickening_preimage`. -/
@[stacks 09ZX "base change of a first-order thickening"]
theorem isFirstOrderThickening_preimage {Y' X' : AlgebraicSpaces B S hS}
    (Y : Subfunctor Y'.1) (f : X' ⟶ Y') (hY : IsFirstOrderThickening B S hS Y' Y) :
    IsFirstOrderThickening B S hS X' (Y.preimage f.hom) :=
  isNthOrderThickening_preimage B S hS Y f hY

/-- **Stacks 09ZX.** The inverse image of a finite-order thickening along an arbitrary morphism
of algebraic spaces is a finite-order thickening, with the same bound on the order. -/
@[stacks 09ZX "base change of a finite-order thickening"]
theorem isFiniteOrderThickening_preimage {Y' X' : AlgebraicSpaces B S hS}
    (Y : Subfunctor Y'.1) (f : X' ⟶ Y') (hY : IsFiniteOrderThickening B S hS Y' Y) :
    IsFiniteOrderThickening B S hS X' (Y.preimage f.hom) :=
  ⟨hY.choose, isNthOrderThickening_preimage B S hS Y f hY.choose_spec⟩

end AlgebraicGeometry.Space

end
