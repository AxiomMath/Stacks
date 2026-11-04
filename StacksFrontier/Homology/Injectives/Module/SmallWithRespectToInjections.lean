module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda
public import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered
public import Mathlib.CategoryTheory.Subobject.HasCardinalLT
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import Mathlib.SetTheory.Cardinal.Regular
public import StacksFrontier.Homology.Injectives.SmallObject
import StacksCore.Tactic.StacksAttribute

/-!
# Modules are small with respect to injections

Let `R` be a ring and let `M` be an `R`-module. Write `κ` for the cardinality of the set of
submodules of `M`. If `α` is an ordinal whose cofinality is bigger than `κ`, then `M` is
`α`-small with respect to injections: for every system `(B_β)_{β ∈ α}` of `R`-modules whose
transition maps are injective, the canonical map
`colim_β Hom(M, B_β) ⟶ Hom(M, colim_β B_β)` is bijective.

## Main results

* `Ordinal.isCardinalFiltered_toType_cof`: the index order `α.ToType` of an ordinal `α` is
  `α.cof`-filtered.
* `Stacks.Injectives.isSmallWithRespectTo_monomorphisms_of_hasCardinalLT_subobject`: the
  statement in an arbitrary Grothendieck abelian category, with the cardinality hypothesis
  phrased on the subobjects of the object.
* `Stacks.Injectives.isSmallWithRespectTo_monomorphisms_of_mk_submodule_lt_cof`: Tag 05NT
  itself, for an `R`-module.
* `Stacks.Injectives.exists_factorization_of_mk_submodule_lt_cof`: the concrete consequence
  that a map from `M` into the colimit of such a system factors through a single stage.

## Implementation notes

"Injections" are read as the monomorphisms of `ModuleCat R`, which by
`ModuleCat.mono_iff_injective` are exactly the maps with injective underlying function. Of
all classes of injections this is the largest, so `MorphismProperty.monomorphisms` gives the
strongest form of the conclusion (smallness with respect to a class of morphisms is
antitone in that class, since shrinking the class constrains the admissible systems).

The analytic content is already in Mathlib, as
`CategoryTheory.IsGrothendieckAbelian.preservesColimit_coyoneda_obj_of_mono`: in a
Grothendieck abelian category, if `κ` is a regular cardinal with
`HasCardinalLT (Subobject X) κ` and `J` is `κ`-filtered, then `coyoneda.obj (op X)`
preserves colimits of `J`-indexed diagrams of monomorphisms. Taking `κ = α.cof` and
`J = α.ToType`, what remains for Tag 05NT is to check the three hypotheses: `α.cof` is
regular because `α` is a limit ordinal (which follows from `1 ≤ κ < α.cof`), `α.ToType` is
`α.cof`-filtered, and subobjects of `M` in `ModuleCat R` are its submodules
(`ModuleCat.subobjectModule`), so the cardinality hypothesis transports.

## References

* [Stacks Project, Tag 05NT](https://stacks.math.columbia.edu/tag/05NT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Ordinal

/-- The canonical well-ordered index type `α.ToType` of an ordinal `α` is
`α.cof`-filtered: a family of indices of cardinality `< α.cof` is bounded above by its
supremum, which is still `< α` precisely because the cofinality of `α` exceeds the size of
the family. -/
theorem isCardinalFiltered_toType_cof (α : Ordinal.{u}) [Fact α.cof.IsRegular] :
    IsCardinalFiltered α.ToType α.cof := by
  apply isCardinalFiltered_preorder
  intro K s hs
  let e : α.ToType ≃o Set.Iio α := Ordinal.ToType.mk.symm
  have hlt (k : K) : (e (s k)).1 < α := (e (s k)).2
  have hb : (⨆ k, (e (s k)).1) < α := Ordinal.iSup_lt_of_lt_cof hs hlt
  have hBdd : BddAbove (Set.range fun k => (e (s k)).1) :=
    ⟨α, Set.forall_mem_range.2 fun k => (hlt k).le⟩
  refine ⟨e.symm ⟨_, hb⟩, fun k => ?_⟩
  rw [← e.symm_apply_apply (s k)]
  exact e.symm.monotone (le_ciSup hBdd k)

end Ordinal

namespace Stacks.Injectives

/-- In a Grothendieck abelian category, an object `X` whose subobjects are fewer than the
cofinality of a limit ordinal `α` is `α`-small with respect to the monomorphisms.

This is the categorical form of Tag 05NT; the hypothesis `1 < α.cof` says exactly that `α`
is a limit ordinal, which is what makes `α.cof` regular. -/
theorem isSmallWithRespectTo_monomorphisms_of_hasCardinalLT_subobject
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    (X : C) (α : Ordinal.{w}) (hlim : (1 : Cardinal.{w}) < α.cof)
    (hX : HasCardinalLT (Subobject X) α.cof) :
    IsSmallWithRespectTo X (MorphismProperty.monomorphisms C) α := by
  have : Fact α.cof.IsRegular := ⟨Cardinal.isRegular_cof (Ordinal.one_lt_cof_iff.mp hlim)⟩
  have : IsCardinalFiltered α.ToType α.cof := Ordinal.isCardinalFiltered_toType_cof α
  intro B hB
  have : ∀ (i j : α.ToType) (f : i ⟶ j), Mono (B.map f) := fun _ _ f => hB f
  exact IsGrothendieckAbelian.preservesColimit_coyoneda_obj_of_mono B hX

/-- **Stacks 05NT.** Let `R` be a ring, let `M` be an `R`-module and let `κ` be the
cardinality of the set of submodules of `M`. If `α` is an ordinal whose cofinality is
bigger than `κ`, then `M` is `α`-small with respect to injections, i.e. for every system
`(B_β)_{β ∈ α}` of `R`-modules with injective transition maps the canonical map
`colim_β Hom(M, B_β) ⟶ Hom(M, colim_β B_β)` is bijective. -/
@[stacks 05NT]
theorem isSmallWithRespectTo_monomorphisms_of_mk_submodule_lt_cof
    {R : Type u} [Ring R] (M : ModuleCat.{u} R) (α : Ordinal.{u})
    (hα : Cardinal.mk (Submodule R M) < α.cof) :
    IsSmallWithRespectTo M (MorphismProperty.monomorphisms (ModuleCat.{u} R)) α := by
  refine isSmallWithRespectTo_monomorphisms_of_hasCardinalLT_subobject M α
    ((Cardinal.one_le_iff_ne_zero.mpr (Cardinal.mk_ne_zero _)).trans_lt hα) ?_
  rwa [hasCardinalLT_iff_of_equiv (ModuleCat.subobjectModule M).toEquiv,
    hasCardinalLT_iff_cardinal_mk_lt]

/-- The surjectivity half of Tag 05NT, spelled out: under the cofinality hypothesis of
`isSmallWithRespectTo_monomorphisms_of_mk_submodule_lt_cof`, every map from `M` to the
colimit of an `α`-indexed system of `R`-modules with injective transition maps factors
through one of the stages. -/
theorem exists_factorization_of_mk_submodule_lt_cof
    {R : Type u} [Ring R] (M : ModuleCat.{u} R) (α : Ordinal.{u})
    (hα : Cardinal.mk (Submodule R M) < α.cof)
    (B : α.ToType ⥤ ModuleCat.{u} R)
    (hB : ∀ {i j : α.ToType} (f : i ⟶ j), Mono (B.map f))
    {c : Cocone B} (hc : IsColimit c) (f : M ⟶ c.pt) :
    ∃ (i : α.ToType) (g : M ⟶ B.obj i), g ≫ c.ι.app i = f := by
  have : PreservesColimit B (coyoneda.obj (op M)) :=
    isSmallWithRespectTo_monomorphisms_of_mk_submodule_lt_cof M α hα B
      (fun {_ _} g => hB g)
  obtain ⟨i, g, hg⟩ := Concrete.isColimit_exists_rep (B ⋙ coyoneda.obj (op M))
    (isColimitOfPreserves (coyoneda.obj (op M)) hc) f
  exact ⟨i, g, hg⟩

end Stacks.Injectives

end
