module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksCore.Tactic.StacksAttribute

/-! # Push-pull adjunction for sheaves of modules along a morphism of topoi

Let `f : Sh(C) ⟶ Sh(D)` be a morphism of topoi and `O` a sheaf of rings on `D`. Stacks tag
03D3 is the bijection `Hom_{f⁻¹O}(f⁻¹G, F) = Hom_O(G, f_*F)`, natural in the `O`-module `G`
and the `f⁻¹O`-module `F`, where the direct image `f_*F` is read as an `O`-module by
restriction of scalars along the unit `O ⟶ f_*f⁻¹O`. It is available for an arbitrary
morphism of topoi as `Stacks.Sheaves.RingedToposModules.inverseImageAdjDirectImageModules`,
so nothing is reproved here.

## References

* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
-/
