module

public import StacksFrontier.Homology.Injectives.Module.SmallWithRespectToInjections
public import StacksFrontier.Homology.Injectives.Size.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# Objects of a Grothendieck abelian category are small with respect to injections

Let `A` be a Grothendieck abelian category, let `M` be an object of `A` and let `κ = |M|` be
the size of `M`, that is the cardinality of its set of subobjects. If `α` is an ordinal whose
cofinality is bigger than `κ`, then `M` is `α`-small with respect to injections: for every
system `(B_β)_{β ∈ α}` in `A` whose transition maps are injections, the canonical map
`colim_β Hom(M, B_β) ⟶ Hom(M, colim_β B_β)` is bijective.

## Main results

* `Stacks.Injectives.isSmallWithRespectTo_monomorphisms_of_hasCardinalLT_subobject_cof`:
  Tag 079F, with `κ = |M| < cf(α)` written as `HasCardinalLT (Subobject M) α.cof`.
* `Stacks.Injectives.Size.isSmallWithRespectTo_monomorphisms_of_size_lt_cof`: the same
  statement with the size written as `Stacks.Injectives.Size.size`.
* `Stacks.Injectives.exists_factorization_of_hasCardinalLT_subobject_cof`: the concrete
  consequence that a map from `M` into the colimit of such a system factors through a single
  stage.

## Implementation notes

"Injections" are the monomorphisms of `A`. Of all classes of injections this is the largest,
so `MorphismProperty.monomorphisms` gives the strongest form of the conclusion (smallness
with respect to a class of morphisms is antitone in that class, since shrinking the class
constrains the admissible systems).

The size `|M|` is written as the cardinality of `CategoryTheory.Subobject M`, matching the
neighbouring Tag 079E in this section, and the comparison with `α.cof` is phrased with
`HasCardinalLT` so that the ordinal `α` may live in the universe `w` for which the
Grothendieck axioms are assumed, independently of the universes of `A`. The alternative
spelling `Stacks.Injectives.Size.size` of Tag 079C forces `α` into the universe `max u v`;
the bridge between the two spellings is
`Stacks.Injectives.Size.isSmallWithRespectTo_monomorphisms_of_size_lt_cof`.

The mathematical content is the categorical form of Tag 05NT, already available as
`Stacks.Injectives.isSmallWithRespectTo_monomorphisms_of_hasCardinalLT_subobject`, which
carries the extra hypothesis `1 < α.cof` saying that `α` is a limit ordinal. That hypothesis
is redundant here: the set of subobjects of `M` is nonempty (it contains `⊤`), so `1 ≤ |M|`,
and the cofinality hypothesis of Tag 079F already forces `1 < cf(α)`. This is why the
statement below is proved by discharging it rather than by assuming it, and hence has exactly
the hypotheses of the tag.

## References

* [Stacks Project, Tag 079F](https://stacks.math.columbia.edu/tag/079F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.Injectives

/-- If the subobjects of an object `M` are fewer than a cardinal `κ`, then `1 < κ`: the
subobject `⊤` alone witnesses `1 ≤ #(Subobject M)`. -/
theorem one_lt_of_hasCardinalLT_subobject {C : Type u} [Category.{v} C] {M : C}
    {κ : Cardinal.{w}} (hM : HasCardinalLT (Subobject M) κ) : 1 < κ := by
  have h : HasCardinalLT PUnit.{w + 1} κ :=
    hM.of_injective (fun _ => (⊤ : Subobject M)) fun _ _ _ => Subsingleton.elim _ _
  rwa [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_punit] at h

/-- **Stacks 079F.** Let `A` be a Grothendieck abelian category, let `M` be an object of `A`
and let `κ = |M|` be the cardinality of the set of subobjects of `M`. If `α` is an ordinal
whose cofinality is bigger than `κ`, then `M` is `α`-small with respect to injections: for
every system `(B_β)_{β ∈ α}` in `A` with monomorphic transition maps the canonical map
`colim_β Hom(M, B_β) ⟶ Hom(M, colim_β B_β)` is bijective. -/
@[stacks 079F]
theorem isSmallWithRespectTo_monomorphisms_of_hasCardinalLT_subobject_cof
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    (M : C) (α : Ordinal.{w}) (hM : HasCardinalLT (Subobject M) α.cof) :
    IsSmallWithRespectTo M (MorphismProperty.monomorphisms C) α :=
  isSmallWithRespectTo_monomorphisms_of_hasCardinalLT_subobject M α
    (one_lt_of_hasCardinalLT_subobject hM) hM

/-- The surjectivity half of Tag 079F, spelled out: if the subobjects of `M` are fewer than
the cofinality of `α`, then every map from `M` to the colimit of an `α`-indexed system in a
Grothendieck abelian category with monomorphic transition maps factors through one of the
stages. -/
theorem exists_factorization_of_hasCardinalLT_subobject_cof
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    (M : C) (α : Ordinal.{w}) (hM : HasCardinalLT (Subobject M) α.cof)
    (B : α.ToType ⥤ C) (hB : ∀ {i j : α.ToType} (f : i ⟶ j), Mono (B.map f))
    {c : Cocone B} (hc : IsColimit c) (f : M ⟶ c.pt) :
    ∃ (i : α.ToType) (g : M ⟶ B.obj i), g ≫ c.ι.app i = f := by
  have : PreservesColimit B (coyoneda.obj (op M)) :=
    isSmallWithRespectTo_monomorphisms_of_hasCardinalLT_subobject_cof M α hM B
      fun {_ _} g => hB g
  obtain ⟨i, g, hg⟩ := Concrete.isColimit_exists_rep (B ⋙ coyoneda.obj (op M))
    (isColimitOfPreserves (coyoneda.obj (op M)) hc) f
  exact ⟨i, g, hg⟩

namespace Size

/-- **Stacks 079F**, with `κ = |M|` written as `Stacks.Injectives.Size.size`: an object of a
Grothendieck abelian category whose size is smaller than the cofinality of an ordinal `α` is
`α`-small with respect to injections. -/
theorem isSmallWithRespectTo_monomorphisms_of_size_lt_cof {C : Type u} [Category.{v} C]
    [Abelian C] [IsGrothendieckAbelian.{max u v} C] (M : C) (α : Ordinal.{max u v})
    (hM : size M < α.cof) :
    IsSmallWithRespectTo M (MorphismProperty.monomorphisms C) α :=
  isSmallWithRespectTo_monomorphisms_of_hasCardinalLT_subobject_cof M α
    ((hasCardinalLT_iff_cardinal_mk_lt _ _).mpr hM)

end Size

end Stacks.Injectives

end
