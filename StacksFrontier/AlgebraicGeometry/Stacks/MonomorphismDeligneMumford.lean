module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalUnramified
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalTFAE
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsoluteQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationOverBase
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationOverBaseSource
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationTrivialImplications

/-!
# Monomorphisms and immersions of algebraic stacks are DM and separated (Stacks 06MY, 06MZ)

A monomorphism of algebraic stacks over `S` is representable by algebraic spaces by definition,
and a 1-morphism representable by algebraic spaces is Deligne–Mumford; it is quasi-Deligne–Mumford
by Stacks 050E. It is also separated: each algebraic space representing one of its base changes
has monomorphic structural morphism, hence separated structural morphism by Stacks 042N, so its
relative diagonal is proper by Stacks 04YS. Separatedness gives quasi-separatedness by Stacks
050E again.

Stacks 06MY asserts the same two properties for *immersions* of algebraic stacks (Stacks 04YL,
part (3)). An immersion is a monomorphism by Stacks 0504, so both assertions follow from the
monomorphism case; the separatedness one is proved here, and the Deligne–Mumford one is
`AlgebraicGeometry.Stack.AlgebraicStacks.isDM_of_isImmersion` of
`StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedImmersionAlgebraicStack`, which obtains it from
representability alone.

Combining the four conditions with parts (5)–(8) of Stacks 050L gives the inheritance statement
of **Stacks 06MZ**: whichever of the four properties the target of a monomorphism has, the source
has it too.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isDM_of_isMonomorphism` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_of_isMonomorphism`: **Stacks 06MY**, that a
  monomorphism is Deligne–Mumford and separated.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_of_isImmersion`: **Stacks 06MY** again,
  that an immersion is separated.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDM_of_isMonomorphism` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_of_isMonomorphism`: the
  quasi-Deligne–Mumford and quasi-separated consequences.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyDM_of_isMonomorphism`,
  `...isAbsolutelyQuasiDM_of_isMonomorphism`, `...isAbsolutelySeparated_of_isMonomorphism` and
  `...isAbsolutelyQuasiSeparated_of_isMonomorphism`: **Stacks 06MZ**, that the source of a
  monomorphism into a Deligne–Mumford, resp. quasi-Deligne–Mumford, separated, quasi-separated
  algebraic stack has the same property.

## Implementation notes

Of the immersion half of Stacks 06MY only the separatedness assertion is proved here, by the
source's own reduction: an immersion is a monomorphism, so
`AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_of_isMonomorphism` applies to it. Its
Deligne–Mumford assertion needs nothing of the immersion beyond representability by algebraic
spaces, and so is not a consequence of the monomorphism case that has to be drawn here: it is
already available as `AlgebraicGeometry.Stack.AlgebraicStacks.isDM_of_isImmersion`, proved
alongside the unramifiedness of an immersion, and it carries the `06MY` key there.

The four absolute statements carry the `06MZ` key, and they are more general than the source's
assertion. Stacks 06MZ concludes about *the* residual gerbe of `𝒳` at a point `x`, the algebraic
substack whose unique existence is asserted by Stacks 06MT; that construction does not exist in
this library, where Stacks 06MT is present only as the specification
`AlgebraicGeometry.Stack.IsResidualGerbeAt` together with its three equivalent conditions. The
residual gerbe enters the source's own proof only through the fact that its inclusion is a
monomorphism, so the statements about an arbitrary monomorphism proved here specialize to Stacks
06MZ as soon as that inclusion is available.

All four absolute statements go through parts (5)–(8) of Stacks 050L rather than through the
conditions over `S`, because the absolute properties of Stacks 050D are conditions on the
structure morphism to the terminal scheme and not a reading of the relative ones.

## References

* [Stacks Project, Tag 042M](https://stacks.math.columbia.edu/tag/042M)
* [Stacks Project, Tag 042N](https://stacks.math.columbia.edu/tag/042N)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 04YS](https://stacks.math.columbia.edu/tag/04YS)
* [Stacks Project, Tag 04ZW](https://stacks.math.columbia.edu/tag/04ZW)
* [Stacks Project, Tag 0504](https://stacks.math.columbia.edu/tag/0504)
* [Stacks Project, Tag 050E](https://stacks.math.columbia.edu/tag/050E)
* [Stacks Project, Tag 050L](https://stacks.math.columbia.edu/tag/050L)
* [Stacks Project, Tag 06MT](https://stacks.math.columbia.edu/tag/06MT)
* [Stacks Project, Tag 06MY](https://stacks.math.columbia.edu/tag/06MY)
* [Stacks Project, Tag 06MZ](https://stacks.math.columbia.edu/tag/06MZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒵 𝒳 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 06MY, the Deligne–Mumford assertion for monomorphisms.** A monomorphism of
algebraic stacks over `S` is Deligne–Mumford.

A monomorphism is representable by algebraic spaces — the first conjunct of
`AlgebraicGeometry.Stack.AlgebraicStacks.IsMonomorphism`, Stacks 04ZW — and a 1-morphism
representable by algebraic spaces is Deligne–Mumford, so the monomorphism condition on the
represented base changes is not needed. The source argues instead that the relative diagonal of a
monomorphism is an isomorphism and that an isomorphism of algebraic spaces is unramified; the
route taken here reaches the same conclusion from less. -/
@[stacks 06MY "monomorphisms are DM"]
theorem isDM_of_isMonomorphism (f : 𝒵 ⟶ 𝒳) (hf : IsMonomorphism B S hS f) :
    Stack.IsDM B S hS f :=
  Stack.isUnramified_relativeDiagonal_of_isRepresentableByAlgebraicSpaces B S hS f hf.1

/-- **A monomorphism of algebraic stacks over `S` is quasi-Deligne–Mumford.** Stacks 06MY at the
Deligne–Mumford condition, followed by Stacks 050E. -/
theorem isQuasiDM_of_isMonomorphism (f : 𝒵 ⟶ 𝒳) (hf : IsMonomorphism B S hS f) :
    IsQuasiDM B S hS f :=
  isQuasiDM_of_isDM B S hS (isDM_of_isMonomorphism.{u, w} B S hS f hf)

/-- **Stacks 06MY, the separatedness assertion for monomorphisms.** A monomorphism of algebraic
stacks over `S` is separated.

Every algebraic space representing a base change of a monomorphism has monomorphic structural
morphism, so that morphism is a monomorphism of presheaves (Stacks 042M) and hence separated
(Stacks 042N); so the monomorphism is separated in the relative sense of Stacks 04XB, and its
relative diagonal is therefore proper by Stacks 04YS.

The source argues instead that the relative diagonal of a monomorphism is an isomorphism and that
an isomorphism of algebraic spaces is proper; the route taken here reaches the same conclusion
without that comparison. -/
@[stacks 06MY "monomorphisms are separated"]
theorem isSeparated_of_isMonomorphism (f : 𝒵 ⟶ 𝒳) (hf : IsMonomorphism B S hS f) :
    IsSeparated B S hS f :=
  ((Stack.isSeparated_relativeDiagonal_tfae B S hS f hf.1).out 1 3).mp
    fun U y hy F hF hrep =>
      Space.isSeparated_of_mono B S hS _
        ((Space.mono_hom_iff_mono B S hS _).2 (hf.2 U y hy F hF hrep))

/-- **A monomorphism of algebraic stacks over `S` is quasi-separated.** Stacks 06MY at the
separatedness condition, followed by part (1) of Stacks 050E. -/
theorem isQuasiSeparated_of_isMonomorphism (f : 𝒵 ⟶ 𝒳) (hf : IsMonomorphism B S hS f) :
    IsQuasiSeparated B S hS f :=
  isQuasiSeparated_of_isSeparated B S hS (isSeparated_of_isMonomorphism.{u, w} B S hS f hf)

/-- **Stacks 06MY, the separatedness assertion for immersions.** An immersion of algebraic stacks
over `S` is separated.

An immersion is a monomorphism by Stacks 0504, so this is
`AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_of_isMonomorphism`. This is the reduction the
source makes when it says that the same is true for immersions. -/
@[stacks 06MY "immersions are separated"]
theorem isSeparated_of_isImmersion (j : 𝒵 ⟶ 𝒳) (hj : IsImmersion B S hS j) :
    IsSeparated B S hS j :=
  isSeparated_of_isMonomorphism.{u, w} B S hS j
    (isMonomorphism_of_isImmersion.{u, w} B S hS j hj)

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 06MZ, the Deligne–Mumford clause.** The source of a monomorphism into a
Deligne–Mumford algebraic stack is Deligne–Mumford.

The monomorphism is a Deligne–Mumford 1-morphism by Stacks 06MY, so part (5) of Stacks 050L
applies to it. The statement is made at an arbitrary monomorphism, which is the form in which
Stacks 06MZ's own proof uses it; see the implementation notes. -/
@[stacks 06MZ "DM case"]
theorem isAbsolutelyDM_of_isMonomorphism (f : 𝒵 ⟶ 𝒳) (hf : IsMonomorphism B S hS f)
    (h𝒳 : IsAbsolutelyDM B S hS hZ 𝒳) :
    IsAbsolutelyDM B S hS hZ 𝒵 :=
  isAbsolutelyDM_of_isDM B S hS hZ f h𝒳 (isDM_of_isMonomorphism.{u, w} B S hS f hf)

/-- **Stacks 06MZ, the quasi-Deligne–Mumford clause.** The source of a monomorphism into a
quasi-Deligne–Mumford algebraic stack is quasi-Deligne–Mumford.

The quasi-Deligne–Mumford counterpart of
`AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyDM_of_isMonomorphism`, through part (6) of
Stacks 050L. -/
@[stacks 06MZ "quasi-DM case"]
theorem isAbsolutelyQuasiDM_of_isMonomorphism (f : 𝒵 ⟶ 𝒳) (hf : IsMonomorphism B S hS f)
    (h𝒳 : IsAbsolutelyQuasiDM B S hS hZ 𝒳) :
    IsAbsolutelyQuasiDM B S hS hZ 𝒵 :=
  isAbsolutelyQuasiDM_of_isQuasiDM B S hS hZ f h𝒳
    (isQuasiDM_of_isMonomorphism.{u, w} B S hS f hf)

/-- **Stacks 06MZ, the separatedness clause.** The source of a monomorphism into a separated
algebraic stack is separated.

The monomorphism is a separated 1-morphism by Stacks 06MY, so part (7) of Stacks 050L applies to
it. -/
@[stacks 06MZ "separated case"]
theorem isAbsolutelySeparated_of_isMonomorphism (f : 𝒵 ⟶ 𝒳) (hf : IsMonomorphism B S hS f)
    (h𝒳 : IsAbsolutelySeparated B S hS hZ 𝒳) :
    IsAbsolutelySeparated B S hS hZ 𝒵 :=
  isAbsolutelySeparated_of_isSeparated B S hS hZ f h𝒳
    (isSeparated_of_isMonomorphism.{u, w} B S hS f hf)

/-- **Stacks 06MZ, the quasi-separatedness clause.** The source of a monomorphism into a
quasi-separated algebraic stack is quasi-separated.

The quasi-separated counterpart of
`AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelySeparated_of_isMonomorphism`, through part
(8) of Stacks 050L. -/
@[stacks 06MZ "quasi-separated case"]
theorem isAbsolutelyQuasiSeparated_of_isMonomorphism (f : 𝒵 ⟶ 𝒳)
    (hf : IsMonomorphism B S hS f) (h𝒳 : IsAbsolutelyQuasiSeparated B S hS hZ 𝒳) :
    IsAbsolutelyQuasiSeparated B S hS hZ 𝒵 :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ f h𝒳
    (isQuasiSeparated_of_isMonomorphism.{u, w} B S hS f hf)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
