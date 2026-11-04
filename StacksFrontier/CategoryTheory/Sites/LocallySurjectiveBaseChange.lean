module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Local surjectivity of presheaves of types is stable under base change

A base change of a locally surjective map of presheaves of types is locally surjective: if
`f : F ⟶ G` is locally surjective and the square with sides `p : W ⟶ G'`, `q : W ⟶ F`,
`g : G' ⟶ G` and `f` is a pullback square, then `p` is locally surjective.

## Main results

* `CategoryTheory.Presheaf.isLocallySurjective_of_isPullback`: local surjectivity is inherited
  by the projection of a pullback square.
* `CategoryTheory.Presheaf.isLocallySurjective_pullback_fst`: the special case of the chosen
  pullback in the category of presheaves.

## Implementation notes

The statement is for `Type`-valued presheaves, where a pullback square is detected objectwise:
evaluation at an object of the site preserves limits, so the fibre product of presheaves has the
expected sections. Over a map in the image sieve of `f` at the section pushed forward along `g`,
the local lift of that section and the section itself agree over `G`, hence come from a section
of `W`. This shows that the image sieve of `f` at the pushed section refines the image sieve of
`p`, which is therefore covering.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- **Local surjectivity is stable under base change.** If the square

```
W --q--> F
|        |
p        f
v        v
G' --g-> G
```

is a pullback square of presheaves of types and `f` is locally surjective, then so is `p`.

Local surjectivity of `f` is an instance argument, named `hf` so that a caller holding it as a
hypothesis can supply it as `(hf := ‹_›)`. -/
theorem isLocallySurjective_of_isPullback {W F G' G : Cᵒᵖ ⥤ Type w}
    {p : W ⟶ G'} {q : W ⟶ F} {g : G' ⟶ G} {f : F ⟶ G} (h : IsPullback p q g f)
    [hf : IsLocallySurjective J f] :
    IsLocallySurjective J p where
  imageSieve_mem {U} s := by
    refine J.superset_covering ?_ (imageSieve_mem J f (g.app (op U) s))
    rintro V i ⟨t, ht⟩
    have hV := h.map ((evaluation Cᵒᵖ (Type w)).obj (op V))
    have hcomm : (g.app (op V)) (G'.map i.op s) = (f.app (op V)) t := by
      rw [NatTrans.naturality_apply g i.op s, ht]
    obtain ⟨x, hx, -⟩ := Types.exists_of_isPullback hV (G'.map i.op s) t hcomm
    exact ⟨x, hx⟩

/-- Local surjectivity is inherited by the first projection of the chosen pullback. -/
theorem isLocallySurjective_pullback_fst {F G' G : Cᵒᵖ ⥤ Type w} (g : G' ⟶ G) (f : F ⟶ G)
    [IsLocallySurjective J f] :
    IsLocallySurjective J (pullback.fst g f) :=
  isLocallySurjective_of_isPullback J (IsPullback.of_hasPullback g f)

end CategoryTheory.Presheaf
