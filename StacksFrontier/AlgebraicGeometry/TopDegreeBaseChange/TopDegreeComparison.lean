module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle

/-!
# The top-degree comparison for a right t-exact functor of derived categories

The proof of [Stacks, Tag 0EX3] uses, in its explanation of conclusion (c), the identification

> since `Rf'_* F'` has no nonzero cohomology sheaves in degrees `> d` by (a) we have
> `H^d(Lh^* Rf_* F') = h^* R^d f_* F`.

That step is not about schemes, nor about derived pullback: it is the general statement that a
*right t-exact* triangulated functor between derived categories computes the top cohomology of a
complex from the top cohomology alone. This file isolates it, so that the geometric content of
the tag is not entangled with the homological bookkeeping.

The argument is the one-line one. For `K` with cohomology concentrated in degrees `≤ d`, the
canonical triangle `τ^{<d} K ⟶ K ⟶ τ^{≥d} K` of the canonical t-structure has first term with
cohomology in degrees `≤ d - 1`. A right t-exact functor keeps it there, so the long exact
homology sequence of the image triangle has zeros on both sides of degree `d`, and the middle
map is an isomorphism.

## Main results

* `Stacks.TopDegreeComparison.isIso_homologyMap_mor₂_of_isZero`: in a distinguished triangle of
  a derived category whose first term has vanishing cohomology in degrees `d` and `d + 1`, the
  second map induces an isomorphism on cohomology in degree `d`.
* `DerivedCategory.isIso_homologyMap_truncGEπ_app`: the canonical map
  `K ⟶ τ^{≥d} K` is an isomorphism on cohomology in every degree `≥ d`, for every `K`.
* `Stacks.TopDegreeComparison.isIso_homologyMap_map_truncGEπ_app`: the same after applying a
  triangulated right t-exact functor — this is the step quoted above.
* `Stacks.TopDegreeComparison.topDegreeIso`: the resulting isomorphism
  `H^d(L K) ≅ H^d(L K₀)` for any `K₀` identified with `τ^{≥d} K`, which in the intended
  application is the single complex on `H^d K` placed in degree `d`.

## Implementation notes

Right t-exactness is taken as an explicit hypothesis `∀ X n, X.IsLE n → (L.obj X).IsLE n`
rather than as a new class. There is no such predicate in Mathlib or in this development, and
coining one here would create a second name for a notion that belongs upstream; a bare `∀` costs
the consumer nothing and cannot drift.

`DerivedCategory.isIso_homologyMap_truncGEπ_app` needs no hypothesis on `K` at all:
the vanishing used is that of `τ^{<d} K` in degrees `≥ d`, which holds for every `K`. The
hypothesis `K.IsLE d` of the source's statement is what makes `τ^{≥d} K` a single complex, and
that is the consumer's business rather than this file's.

That declaration is the **public home of a lemma this development already had and could not
reach**: `StacksFrontier/Homology/DerivedComplete/TorsionAmplitude.lean:90` proves it, by the same
argument and at the same generality, as a `private lemma isIso_homology_truncGE`, and
`:66` and `:187` of that file prove its `mor₁` companion and the right t-exactness criterion
`isLE_map_of_homology` (for *bounded* objects) privately too. `private` declarations are
per-module mangled, so there is no shadowing and no collision — but there is also no way for a
consumer to use them, and the triangle step at `:78-88` and `:95-104` is written out twice
inline because no named form existed. Those three should be promoted and these forms retired
into them.

The instance `((TStructure.t.truncLT d).obj K).IsLE (d - 1)` has to be handed to
`DerivedCategory.isZero_of_isLE` by name: after `Functor.mapTriangle`, the first term prints as
`(L.mapTriangle.obj T).obj₁` rather than as `L.obj T.obj₁`, and instance search is syntactic.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated Triangulated

universe v v' u u' w w'

namespace Stacks.TopDegreeComparison

open DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]

/-- **A distinguished triangle whose first term is cohomologically silent in degrees `d` and
`d + 1` has an isomorphism for its second map in degree `d`.** Monomorphy comes from the
vanishing in degree `d`, epimorphy from the vanishing in degree `d + 1` through the connecting
homomorphism, and an abelian category turns the two into invertibility. -/
theorem isIso_homologyMap_mor₂_of_isZero
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _) (d : ℤ)
    (h₀ : IsZero ((homologyFunctor C d).obj T.obj₁))
    (h₁ : IsZero ((homologyFunctor C (d + 1)).obj T.obj₁)) :
    IsIso ((homologyFunctor C d).map T.mor₂) := by
  have : Mono ((homologyFunctor C d).map T.mor₂) := by
    rw [HomologySequence.mono_homologyMap_mor₂_iff T hT d]
    exact h₀.eq_of_src _ _
  have : Epi ((homologyFunctor C d).map T.mor₂) := by
    rw [HomologySequence.epi_homologyMap_mor₂_iff T hT d (d + 1) rfl]
    exact h₁.eq_of_tgt _ _
  exact isIso_of_mono_of_epi _

/- `isIso_homologyMap_truncGEπ_app` stood here: the same statement, for `K : DerivedCategory C`
and `d ≤ i`, as `DerivedCategory.isIso_homologyMap_truncGEπ_app` in
`StacksFrontier/Algebra/Homology/DerivedCategory/TruncGELTSingle.lean:98`, now imported above.
That one orders its arguments `(c i) (hi) (X)` rather than `(K) (d i) (hi)`, so the use below
passes `K` last. `open DerivedCategory` is in force, so the unqualified name resolves to it. -/

/-- **The top-degree comparison.** If `L` is a triangulated functor of derived categories which
is right t-exact — it does not raise the degrees in which cohomology lives — then the truncation
`K ⟶ τ^{≥d} K` still induces an isomorphism on cohomology in degree `d` after applying `L`.

This is the step [Stacks, Tag 0EX3] uses to say that the top cohomology of `L K` is computed by
the top cohomology of `K` alone. -/
theorem isIso_homologyMap_map_truncGEπ_app
    (L : DerivedCategory C ⥤ DerivedCategory D) [L.CommShift ℤ] [L.IsTriangulated]
    (hL : ∀ (X : DerivedCategory C) (n : ℤ), X.IsLE n → (L.obj X).IsLE n)
    (K : DerivedCategory C) (d i : ℤ) (hi : d ≤ i) :
    IsIso ((homologyFunctor D i).map (L.map ((TStructure.t.truncGEπ d).app K))) := by
  have hL1 : (L.obj ((TStructure.t.truncLT d).obj K)).IsLE (d - 1) :=
    hL _ (d - 1) inferInstance
  exact isIso_homologyMap_mor₂_of_isZero
    (L.mapTriangle.obj ((TStructure.t.triangleLTGE d).obj K))
    (L.map_distinguished _ (TStructure.t.triangleLTGE_distinguished d K)) i
    (isZero_of_isLE (hX := hL1) _ (d - 1) i (by lia))
    (isZero_of_isLE (hX := hL1) _ (d - 1) (i + 1) (by lia))

/-- **The top cohomology of `L K` reads off any model of the truncation `τ^{≥d} K`.** Given an
identification `e` of `τ^{≥d} K` with an object `K₀` — in the intended application, `K₀` is the
single complex on `H^d K` placed in degree `d` — the top cohomology of `L K` is that of
`L K₀`. -/
noncomputable def topDegreeIso
    (L : DerivedCategory C ⥤ DerivedCategory D) [L.CommShift ℤ] [L.IsTriangulated]
    (hL : ∀ (X : DerivedCategory C) (n : ℤ), X.IsLE n → (L.obj X).IsLE n)
    (K : DerivedCategory C) (d : ℤ) {K₀ : DerivedCategory C}
    (e : (TStructure.t.truncGE d).obj K ≅ K₀) :
    (homologyFunctor D d).obj (L.obj K) ≅ (homologyFunctor D d).obj (L.obj K₀) :=
  (@asIso _ _ _ _ _ (isIso_homologyMap_map_truncGEπ_app L hL K d d le_rfl)) ≪≫
    (homologyFunctor D d).mapIso (L.mapIso e)

/-- The degree-`d` cohomology of `K` itself is computed by any model of `τ^{≥d} K`, which is the
`L = 𝟭` case of `Stacks.TopDegreeComparison.topDegreeIso`. -/
noncomputable def homologyTruncIso (K : DerivedCategory C) (d : ℤ) {K₀ : DerivedCategory C}
    (e : (TStructure.t.truncGE d).obj K ≅ K₀) :
    (homologyFunctor C d).obj K ≅ (homologyFunctor C d).obj K₀ :=
  (@asIso _ _ _ _ _ (isIso_homologyMap_truncGEπ_app d d le_rfl K)) ≪≫
    (homologyFunctor C d).mapIso e

end Stacks.TopDegreeComparison

end
