module

public import StacksFrontier.CategoryTheory.Sites.Stackification.TwoFibreProductGroupoid.MorphismSections
public import StacksFrontier.CategoryTheory.Sites.Stackification.TwoFibreProductGroupoid.LocallySurjective
public import StacksFrontier.CategoryTheory.Sites.Stackification.TwoFibreProductGroupoid.LocalEssentialImage
public import StacksFrontier.CategoryTheory.Sites.Stackification.TwoFibreProductGroupoid.IsStackification

/-!
# The stackification of a 2-fibre product is the 2-fibre product of the stackifications

Stacks 04Y2: for stackifications `i : 𝒳 ⥤ 𝒳'`, `j : 𝒴 ⥤ 𝒴'`, `k : 𝒵 ⥤ 𝒵'` of categories fibred
in groupoids over a site, compatible with `f : 𝒳 ⥤ 𝒴`, `g : 𝒵 ⥤ 𝒴`, the canonical 1-morphism
`𝒳 ×_𝒴 𝒵 ⥤ 𝒳' ×_{𝒴'} 𝒵'` is a stackification
(`CategoryTheory.TwoFibreProductOver.isStackification_of_isStackification`).

The parts are:

* `StacksFrontier.CategoryTheory.Sites.Stackification.TwoFibreProductGroupoid.MorphismSections`:
  auxiliary lemmas on the 2-fibre product and on the components of sections of its morphism
  presheaves;
* `StacksFrontier.CategoryTheory.Sites.Stackification.TwoFibreProductGroupoid.LocallySurjective`:
  the map of morphism presheaves induced by the canonical 1-morphism is locally surjective;
* `StacksFrontier.CategoryTheory.Sites.Stackification.TwoFibreProductGroupoid.LocalEssentialImage`:
  clause (2) for one member of a covering: the objects of the target are locally in the
  essential image;
* `StacksFrontier.CategoryTheory.Sites.Stackification.TwoFibreProductGroupoid.IsStackification`:
  clause (2), local injectivity, and Stacks 04Y2 itself.
-/
