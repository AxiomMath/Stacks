module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.Denominators
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

/-!
# The denominator rule

Let `X` be a scheme, `L` a sheaf of `𝒪_X`-modules and `s` a meromorphic section of `L`. The
ideal of denominators of `s` is realised in
`StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.Denominators` as the fibre product of
`𝒪_X` and `L` over `K_X(L)`. The source instead *defines* it by the rule
`I(V) = {f ∈ 𝒪_X(V) | f s ∈ L(V)}`.
This file proves that the two descriptions agree: a section of `𝒪_X` over `V` is in the image
of the ideal inclusion exactly when its product with `s` is a section of `L` over `V`.

## Main results

* `CategoryTheory.Limits.exists_map_pullback_fst_eq_iff`: for a functor into a concrete
  category which preserves a given pullback, an element of the image of the first factor lifts
  to the pullback exactly when it is compatible with some element of the second factor.
* `AlgebraicGeometry.exists_denominatorIdeal_inclusion_app_eq_iff`: the denominator rule, in
  the form of the tagged statement.
* `AlgebraicGeometry.range_denominatorIdeal_inclusion_app`: the same statement as a description
  of the range of the ideal inclusion on sections, the form in which
  `AlgebraicGeometry.denominatorIdealData` consumes it.

## Implementation notes

The evaluation functor `SheafOfModules.evaluation R V` preserves finite limits, so the
sections over `V` of the fibre product are the fibre product of the modules of sections. Only
the surjectivity half of that needs the preservation: the compatibility of a lift is
`pullback.condition` read on sections, which is pure functoriality.

Both halves are packaged in the general lemma
`CategoryTheory.Limits.exists_map_pullback_fst_eq_iff`, stated for an arbitrary functor into a
concrete category rather than for `SheafOfModules.evaluation`, because the element-level
constructor `CategoryTheory.Limits.Concrete.pullbackMk` has to be applied at the ascribed type
`ToType (G.obj A)`; at the specialised type `↑(A.val.obj V)` the rewrites fail under
`implicit` transparency.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 02P1](https://stacks.math.columbia.edu/tag/02P1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.ConcreteCategory

universe v u

namespace CategoryTheory.Limits

/-- Let `G` be a functor into a concrete category which preserves the pullback of `g` and `h`.
An element of `G.obj A` is the image of an element of `G.obj (pullback g h)` under the first
projection exactly when it agrees, after `G.map g`, with the image of some element of `G.obj B`
under `G.map h`. -/
theorem exists_map_pullback_fst_eq_iff {C : Type*} [Category C] {D : Type*} [Category.{v} D]
    {FD : D → D → Type*} {DD : D → Type v} [∀ X Y, FunLike (FD X Y) (DD X) (DD Y)]
    [ConcreteCategory.{v} D FD]
    (G : C ⥤ D) {A B S : C} (g : A ⟶ S) (h : B ⟶ S)
    [HasPullback g h] [PreservesLimit (cospan g h) G]
    [HasPullback (G.map g) (G.map h)]
    [PreservesLimit (cospan (G.map g) (G.map h)) (forget D)]
    (a : ToType (G.obj A)) :
    (∃ d : ToType (G.obj (pullback g h)), G.map (pullback.fst g h) d = a) ↔
      ∃ b : ToType (G.obj B), G.map g a = G.map h b := by
  constructor
  · rintro ⟨d, rfl⟩
    refine ⟨G.map (pullback.snd g h) d, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← G.map_comp,
      ← G.map_comp, pullback.condition]
  · rintro ⟨b, hab⟩
    refine ⟨(PreservesPullback.iso G g h).inv (Concrete.pullbackMk _ _ a b hab), ?_⟩
    rw [← ConcreteCategory.comp_apply, PreservesPullback.iso_inv_fst,
      Concrete.pullbackMk_fst]

end CategoryTheory.Limits

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-- **Stacks Project, Tag 02P0**, the denominator rule. A section `f` of `𝒪_X` over `V` lies in
the ideal of denominators of a meromorphic section `s` of `L` exactly when `f s` is a section
of `L` over `V`; here "lies in the ideal" means that `f` is the image of a section of the fibre
product under the ideal inclusion, and "`f s` is a section of `L`" means that `f s` is the
image of a section of `L` under the canonical map `L ⟶ K_X(L)`. -/
@[stacks 02P0 "the denominator rule"]
theorem exists_denominatorIdeal_inclusion_app_eq_iff
    (L : SheafOfModules.{u}
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf))
    (s : MeromorphicSection X.sheaf L) (V : Opens X)
    (f : (SheafOfModules.unit
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf)).val.obj
        (op V)) :
    (∃ d : (denominatorIdeal X L s).val.obj (op V),
      (denominatorIdealι X L s).val.app (op V) d = f) ↔
    (∃ t : L.val.obj (op V),
      (meromorphicSectionMul X L s).val.app (op V) f =
        (toMeromorphicSectionSheafAsModule X L).val.app (op V) t) :=
  exists_map_pullback_fst_eq_iff
    (SheafOfModules.evaluation
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf) (op V))
    (meromorphicSectionMul X L s) (toMeromorphicSectionSheafAsModule X L) f

/-- The range of the ideal inclusion on sections over `V` is the set of denominators of `s`
over `V`. This is `AlgebraicGeometry.exists_denominatorIdeal_inclusion_app_eq_iff` in the form
used by `AlgebraicGeometry.denominatorIdealData`, whose affine ideals are these ranges. -/
theorem range_denominatorIdeal_inclusion_app
    (L : SheafOfModules.{u}
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf))
    (s : MeromorphicSection X.sheaf L) (V : Opens X) :
    ((denominatorIdealι X L s).val.app (op V)).hom.range =
      { f | ∃ t : L.val.obj (op V),
          (meromorphicSectionMul X L s).val.app (op V) f =
            (toMeromorphicSectionSheafAsModule X L).val.app (op V) t } := by
  ext f
  exact exists_denominatorIdeal_inclusion_app_eq_iff X L s V f

end AlgebraicGeometry
