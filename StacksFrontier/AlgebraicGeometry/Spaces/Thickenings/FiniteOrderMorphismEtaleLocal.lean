module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.UnramifiedLocalAtSource
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.CartesianFiniteOrderMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified

/-!
# Quasi-finiteness and unramifiedness across a cartesian morphism of finite-order thickenings

Let

```
X --f--→ Y
|        |
↓        ↓
X' -f'-→ Y'
```

be a commutative square of algebraic spaces over a scheme `S` in which `X ⊂ X'` and `Y ⊂ Y'`
are thickenings, the thickening `Y ⊂ Y'` is of finite order, and the square identifies `X` with
`Y ×_{Y'} X'`; that is, let it be a
`AlgebraicGeometry.Space.CartesianFiniteOrderMorphismOfThickenings`. This file records two more
clauses of Stacks 09ZZ for that situation: local quasi-finiteness, part (3), and
unramifiedness, part (6).

Both properties are defined for morphisms of algebraic spaces as the every-étale-chart
condition of Stacks 03MJ applied to a property of morphisms of schemes — local quasi-finiteness
to the conjunction of `AlgebraicGeometry.LocallyOfFiniteType` and
`AlgebraicGeometry.LocallyQuasiFinite`, following Stacks 03XJ, and unramifiedness to
`AlgebraicGeometry.Unramified`, following Stacks 03ZH. Each is therefore an instance of the
engine
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_of_cartesianFiniteOrderMorphismOfThickenings`
of the frame file, which reduces the clause to the corresponding clause of Stacks 09ZW for
morphisms of schemes, and the two inputs the engine needs are étale locality of the property on
the source and target (Stacks 04R3) and its invariance under a cartesian morphism of
finite-order thickenings of schemes (Stacks 09ZW).

For local quasi-finiteness the scheme-level input is already in the library. For
unramifiedness the library has the invariance for a cartesian morphism of thickenings whose
deformation is locally of finite type, and the finite-order hypothesis supplies that missing
local finite type through part (2) of Stacks 09ZW; that assembly is part (6) of Stacks 09ZW and
is proved here.

## Main results

* `Stacks.Thickenings.unramified_iff_of_isFiniteOrderThickening`: **Stacks 09ZW**, part (6),
  unramifiedness across a cartesian morphism of finite-order thickenings of schemes.
* `AlgebraicGeometry.Space.CartesianFiniteOrderMorphismOfThickenings.isLocallyQuasiFinite_iff`:
  part (3) of Stacks 09ZZ.
* `AlgebraicGeometry.Space.CartesianFiniteOrderMorphismOfThickenings.isUnramified_iff`:
  part (6) of Stacks 09ZZ.

## Implementation notes

**The finite-order hypothesis is on the target thickening `Y ⊂ Y'`, not on the source
`X ⊂ X'`.** This is the convention of the frame file
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/CartesianFiniteOrderMorphism.lean`, whose
implementation notes explain it: the tag's text puts finite order on the source, but the lemma
it reduces to, Stacks 09ZW, puts it on the target, and the tag's own proof argues by induction
on the order of the thickening `Y ⊂ Y'`. In the presence of the cartesian square target finite
order implies source finite order, by Stacks 09ZX, but not conversely, so the statements below
are weaker than the tag's text announces. The clause strings of the two theorems say so.

Part (6) is *not* routed through part (5), the vanishing of the relative differentials, as the
source does. The library has no quasi-coherent module of relative differentials of a morphism
of algebraic spaces, so its part (5) is stated through the every-étale-chart condition for
`AlgebraicGeometry.FormallyUnramified`, and the identification of that condition with the
vanishing of `Ω_{X/Y}` is not available. Routing part (6) through the engine avoids the
question: unramifiedness of morphisms of schemes is itself étale local on the source and target.

The scheme-level part (6) proved here is the composite of two facts already in the library:
`Stacks.Thickenings.IsThickening.unramified_iff_of_isPullback`, which needs no finiteness
condition on the thickenings but does need the deformation `f'` to be locally of finite type,
and `Stacks.Thickenings.locallyOfFiniteType_iff_of_isFiniteOrderThickening`, part (2) of
Stacks 09ZW, which transfers local finite type from `f` to `f'`. Local finite type of `f` comes
for free from `AlgebraicGeometry.locallyOfFiniteType_of_unramified` in the forward direction,
and in the backward direction `f'` is unramified by hypothesis, so it is locally of finite type
for the same reason.

## References

* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03XJ](https://stacks.math.columbia.edu/tag/03XJ)
* [Stacks Project, Tag 03ZH](https://stacks.math.columbia.edu/tag/03ZH)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 09ZW](https://stacks.math.columbia.edu/tag/09ZW)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
* [Stacks Project, Tag 09ZZ](https://stacks.math.columbia.edu/tag/09ZZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

/-- **Stacks 09ZW, part (6).** Unramifiedness ascends and descends across a cartesian morphism
of thickenings of schemes when the thickening of the base has finite order.

The invariance of unramifiedness under a cartesian morphism of thickenings,
`Stacks.Thickenings.IsThickening.unramified_iff_of_isPullback`, needs the deformation `f'` to be
locally of finite type; the finite order of `j` provides it from local finite type of `f`, by
part (2) of this tag. No finiteness hypothesis on the source thickening `i` is used. -/
@[stacks 09ZW "unramified"]
theorem unramified_iff_of_isFiniteOrderThickening
    {X X' S S' : Scheme.{u}} (i : X ⟶ X') (j : S ⟶ S') (f : X ⟶ S) (f' : X' ⟶ S')
    (hj : Stacks.Thickenings.IsFiniteOrderThickening j) (hcart : IsPullback i f f' j) :
    Unramified f ↔ Unramified f' := by
  have hft : LocallyOfFiniteType f ↔ LocallyOfFiniteType f' :=
    locallyOfFiniteType_iff_of_isFiniteOrderThickening i j f f' hj hcart
  refine ⟨fun hf => ?_, fun hf' => ?_⟩
  · have := hf
    have : LocallyOfFiniteType f' := hft.mp inferInstance
    exact (hj.isThickening.unramified_iff_of_isPullback hcart).mp hf
  · have := hf'
    exact (hj.isThickening.unramified_iff_of_isPullback hcart).mpr hf'

end Stacks.Thickenings

namespace AlgebraicGeometry.Space

namespace CartesianFiniteOrderMorphismOfThickenings

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 09ZZ, part (3).** Local quasi-finiteness is invariant under a cartesian morphism of
thickenings of algebraic spaces whose target thickening is of finite order: the map between the
smaller spaces is locally quasi-finite exactly when the map between the ambient spaces is.

The hypothesis is the finite order of the target thickening `Y ⊂ Y'`, which is stronger than
the finite order of the source thickening `X ⊂ X'` that the tag's text states; see the
implementation notes of this file. -/
@[stacks 09ZZ "part (3), locally quasi-finite; the finite-order hypothesis is on the TARGET \
thickening Y ⊆ Y', which is strictly stronger than the source hypothesis X ⊆ X' in the tag's \
text, so this is a weaker theorem than the tag announces. It is the hypothesis the tag's own \
proof uses: it reduces to Tag 09ZW, which puts finite order on the target, and says 'by \
induction on the order of the thickening we may assume that Y ⊆ Y' is a first order \
thickening'. Cartesianness plus target finite order gives source finite order by Tag 09ZX, \
but not conversely"]
theorem isLocallyQuasiFinite_iff (M : CartesianFiniteOrderMorphismOfThickenings B S hS) :
    IsLocallyQuasiFinite B S hS M.f ↔ IsLocallyQuasiFinite B S hS M.f' :=
  holdsOnEveryEtaleChart_iff_of_cartesianFiniteOrderMorphismOfThickenings B S hS M _
    locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget
    fun iU iV g g' hiU hiV hcart =>
      Stacks.Thickenings.locallyQuasiFinite_iff_of_isFiniteOrderThickening iU iV g g'
        hiU.isThickening hiV hcart

/-- **Stacks 09ZZ, part (6).** Unramifiedness is invariant under a cartesian morphism of
thickenings of algebraic spaces whose target thickening is of finite order: the map between the
smaller spaces is unramified exactly when the map between the ambient spaces is.

The hypothesis is the finite order of the target thickening `Y ⊂ Y'`, which is stronger than
the finite order of the source thickening `X ⊂ X'` that the tag's text states; see the
implementation notes of this file. -/
@[stacks 09ZZ "part (6), unramified; the finite-order hypothesis is on the TARGET thickening \
Y ⊆ Y', which is strictly stronger than the source hypothesis X ⊆ X' in the tag's text, so \
this is a weaker theorem than the tag announces. It is the hypothesis the tag's own proof \
uses: it reduces to Tag 09ZW, which puts finite order on the target, and says 'by induction \
on the order of the thickening we may assume that Y ⊆ Y' is a first order thickening'. \
Cartesianness plus target finite order gives source finite order by Tag 09ZX, but not \
conversely"]
theorem isUnramified_iff (M : CartesianFiniteOrderMorphismOfThickenings B S hS) :
    IsUnramified B S hS M.f ↔ IsUnramified B S hS M.f' :=
  holdsOnEveryEtaleChart_iff_of_cartesianFiniteOrderMorphismOfThickenings B S hS M _
    unramified_isEtaleLocalOnSourceAndTarget
    fun iU iV g g' _ hiV hcart =>
      Stacks.Thickenings.unramified_iff_of_isFiniteOrderThickening iU iV g g' hiV hcart

end CartesianFiniteOrderMorphismOfThickenings

end AlgebraicGeometry.Space

end
