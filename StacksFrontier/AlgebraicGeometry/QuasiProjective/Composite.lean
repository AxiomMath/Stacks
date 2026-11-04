module

public import StacksFrontier.AlgebraicGeometry.AmplePullbackDatum.Composition
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-projectivity of a composition over a quasi-compact base

[Stacks, Tag 0C4M]: if `S` is quasi-compact and `f : X ⟶ Y`, `g : Y ⟶ S` are quasi-projective,
then `g ∘ f` is quasi-projective.

Quasi-projectivity is `AlgebraicGeometry.IsQuasiProjective`, the predicate of [Stacks, Tag 01VW]:
finite type together with an invertible sheaf on the source that is ample relative to the
morphism. Both conjuncts compose. Finite type does so because
`AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact` are both stable under
composition. The relatively ample sheaf is **not** the one for `f`: it is `L ⊗ f^* M ^⊗ a` for `L`
relatively ample over `f`, `M` relatively ample over `g` and `a` large, which is
[Stacks, Tag 0C4K], `Stacks.AmplePullbackDatum.exists_threshold_isRelativelyAmple_comp`. This is
the only place quasi-compactness of `S` is used, and it is why the source carries that hypothesis.

## Main results

* `AlgebraicGeometry.IsQuasiProjective.comp`: **[Stacks, Tag 0C4M].**

## Implementation notes

`AlgebraicGeometry.IsQuasiProjective` is stated over
`Stacks.RelativeAmple.IsRelativelyAmple` while
`Stacks.AmplePullbackDatum.exists_threshold_isRelativelyAmple_comp` is proved for
`Stacks.RelativeAmple.IsRelativelyAmple`; the bridge
`Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple`
identifies the two spellings of [Stacks, Tag 01VH], exactly as in
`StacksFrontier/AlgebraicGeometry/QuasiProjective/Composition.lean` for [Stacks, Tag 0C4N].
Invertibility of the chosen sheaves is existentially bound by the predicate, so after
destructuring it is reinstated as a local instance for the bridge and for
`Stacks.AmplePullbackPart1.tensorPullbackPowModule` to key on.

## References

* [Stacks Project, Tag 0C4M](https://stacks.math.columbia.edu/tag/0C4M)
* [Stacks Project, Tag 0C4K](https://stacks.math.columbia.edu/tag/0C4K)
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
-/

@[expose] public section

open CategoryTheory
open Stacks.AmplePullbackPart1 (tensorPullbackPowModule)

universe u

namespace AlgebraicGeometry

namespace IsQuasiProjective

/-- **[Stacks, Tag 0C4M].** Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes with `S`
quasi-compact. If `f` and `g` are quasi-projective, then so is `f ≫ g`.

Finite type composes. The relatively ample sheaf is produced by [Stacks, Tag 0C4K],
`Stacks.AmplePullbackDatum.exists_threshold_isRelativelyAmple_comp`: from sheaves `L` on `X` ample
relative to `f` and `M` on `Y` ample relative to `g` it gives a threshold beyond which
`L ⊗ f^* M ^⊗ a` is ample relative to `f ≫ g`, and the threshold itself is used as the
exponent. -/
@[stacks 0C4M, ega "I 6.6.4" "(ii), special case"]
public theorem comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [CompactSpace S]
    (hf : IsQuasiProjective f) (hg : IsQuasiProjective g) : IsQuasiProjective (f ≫ g) := by
  obtain ⟨L, hLinv, hLA⟩ := hf.exists_isRelativelyAmple
  obtain ⟨M, hMinv, hMA⟩ := hg.exists_isRelativelyAmple
  have hLi : Stacks.Ample.IsInvertibleModule X L := hLinv
  have hMi : Stacks.Ample.IsInvertibleModule Y M := hMinv
  obtain ⟨n, hn⟩ := Stacks.AmplePullbackDatum.exists_threshold_isRelativelyAmple_comp f g L M
    ((Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple f L).mpr hLA)
    ((Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple g M).mpr hMA)
  have hTi : Stacks.Ample.IsInvertibleModule X (tensorPullbackPowModule f L M n) := inferInstance
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (tensorPullbackPowModule f L M n) := hTi
  exact IsQuasiProjective.mk'
    (MorphismProperty.comp_mem _ _ _ hf.locallyOfFiniteType hg.locallyOfFiniteType)
    (tensorPullbackPowModule f L M n)
    ((Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple _ _).mp (hn n le_rfl))

end IsQuasiProjective

end AlgebraicGeometry

end
