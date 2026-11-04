module

public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import StacksCore.Tactic.StacksAttribute

/-!
# The plus construction on presheaves of sets

Mathlib coverage for Stacks chapter 7 (Sites and Sheaves), sections 7.10 (Sheafification) and
7.49 (Sheafification in a topology).

For a Grothendieck topology `J` on `C` and a presheaf `P`, Mathlib's
`CategoryTheory.GrothendieckTopology.plusObj` is the colimit of the zeroth Čech cohomology
`H⁰(S, P)` over the covering **sieves** `S` of an object, together with the canonical map
`toPlus : P ⟶ J.plusObj P`. That is exactly the functor `L` of Stacks section 7.49 (whose
covering sieves index the colimit), and Mathlib proves the four assertions of Stacks 00ZJ for
it: `L P` is separated; if `P` is separated then `L P` is a sheaf and `P → L P` is injective; if
`P` is a sheaf then `P → L P` is an isomorphism; and `L L P` is always a sheaf.

Mathlib spells separatedness of the argument out as an explicit `∀`-statement over `J.Cover X`
rather than through the predicate `CategoryTheory.Presheaf.IsSeparated`; the two say the same
thing, since `Presheaf.IsSeparated` quantifies over covering sieves and a `J.Cover X` is a
covering sieve.

## References

* [Stacks Project, Tag 00W4](https://stacks.math.columbia.edu/tag/00W4)
* [Stacks Project, Tag 00ZJ](https://stacks.math.columbia.edu/tag/00ZJ)
-/

@[expose] public section

/-!
### Stacks 00W4: the plus construction is a presheaf, with a canonical map from `P`

Mathlib indexes the plus construction by covering sieves, i.e. it builds the functor `L` of
Stacks section 7.49 rather than the covering-family-indexed `F⁺` of section 7.10. For `L`, the
two declarations below are exactly parts (1) and (2) of Stacks 00ZH; 00W4 is credited to them as
the sieve-indexed analogue of `F⁺`, since neither Stacks nor Mathlib states a comparison
`F⁺ ≅ L F`. The functoriality in `F` (`plusFunctor`, `toPlusNatTrans`) is Stacks 00W5, which is
registered on `toPlus_naturality`.
-/

add_to_stacks 00W4 "The presheaf `F⁺`. Mathlib builds the colimit over covering sieves
  rather than over covering families, i.e. the functor `L` of Stacks section 7.49; the
  functoriality in the object that 00W4 asserts is the `map` field of this functor, and its
  compatibility with composition `F⁺(U) → F⁺(V) → F⁺(W)` is `Functor.map_comp`, which is
  exactly what the proof of 00W4 verifies."
  CategoryTheory.GrothendieckTopology.plusObj

add_to_stacks 00W4 "The canonical map of presheaves `F → F⁺` of 00W4."
  CategoryTheory.GrothendieckTopology.toPlus

/-!
### Stacks 00ZJ: the four assertions about `L`

All four are Mathlib's.
-/

add_to_stacks 00ZJ "(1) The presheaf `LF` is separated: two sections of `LF` over `X` whose
  restrictions along every arrow of a covering of `X` agree are equal."
  CategoryTheory.GrothendieckTopology.Plus.sep
add_to_sga "3 IV 4.3.11" "(i), LP separated" CategoryTheory.GrothendieckTopology.Plus.sep
add_to_sga "4 II 3.2" "2)" CategoryTheory.GrothendieckTopology.Plus.sep

add_to_stacks 00ZJ "(2) If `F` is separated then `LF` is a sheaf."
  CategoryTheory.GrothendieckTopology.Plus.isSheaf_of_sep
add_to_sga "4 II 3.2" "part of 3)" CategoryTheory.GrothendieckTopology.Plus.isSheaf_of_sep
add_to_sga "3 IV 4.3.11" "(iv), LP a sheaf" CategoryTheory.GrothendieckTopology.Plus.isSheaf_of_sep

add_to_stacks 00ZJ "(2) If `F` is separated then the map of presheaves `F → LF` is injective on
  the sections over every object."
  CategoryTheory.GrothendieckTopology.Plus.inj_of_sep
add_to_sga "3 IV 4.3.11" "(iv), mono part" CategoryTheory.GrothendieckTopology.Plus.inj_of_sep
add_to_sga "4 II 3.2" "3) sep ⇒ ℓ(F) mono" CategoryTheory.GrothendieckTopology.Plus.inj_of_sep

add_to_stacks 00ZJ "(3) If `F` is a sheaf then `F → LF` is an isomorphism."
  CategoryTheory.GrothendieckTopology.isIso_toPlus_of_isSheaf
add_to_sga "4 II 3.2" "4) (ii) ⇒ (i)" CategoryTheory.GrothendieckTopology.isIso_toPlus_of_isSheaf

add_to_stacks 00ZJ "(4) The presheaf `LLF` is always a sheaf."
  CategoryTheory.GrothendieckTopology.Plus.isSheaf_plus_plus
