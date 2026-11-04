module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffinePairLocality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Relative pseudo-coherence in a distinguished triangle

Let `f : X ⟶ S` be a morphism of schemes locally of finite type and let `(E, E', E'')` be a
distinguished triangle in the derived category of `𝒪_X`-modules. Relative pseudo-coherence of
two of the three terms gives it for the third, with the shift in degree the triangle forces. This
is Stacks 09UL.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_obj₃_of_distinguished`,
  `…_obj₂_of_distinguished` and `…_obj₁_of_distinguished`: parts (1), (2) and (3).
* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherent_obj₃_of_distinguished`,
  `…_obj₂_of_distinguished` and `…_obj₁_of_distinguished`: the "moreover" clause, that two out of
  three terms pseudo-coherent relative to `S` makes the third one so.

## Implementation notes

The whole content is the reduction to the sheaf-level statement, Stacks 08CD, which is proved as
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_obj₁_of_distinguished` and its two companions.
The reduction is not immediate from the definition of Stacks 09UI, because the two hypotheses come
with *separately chosen* affine covers and closed immersions, and the conclusion has to be proved
at a single one. Stacks 09UJ supplies both halves of the fix: it turns relative
`m`-pseudo-coherence into a condition at every compatible pair of affine opens, and — through
`AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFromOnAffinePair.forall_isClosedImmersion`, which is
Stacks 09VC — into a condition at every closed immersion over such a pair. One closed immersion
`i : U ⟶ 𝔸ⁿ_V`, taken from the witness of one hypothesis, therefore serves for all three terms.

At that closed immersion the local condition is sheaf-level `m`-pseudo-coherence of the derived
pushforward (`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff`), and
both restriction along an open immersion and pushforward along a closed immersion are exact, so
the functors they induce on derived categories are triangulated and carry the triangle to a
distinguished triangle on `𝔸ⁿ_V`.

The "moreover" clause is three one-line consequences of parts (1)–(3), the degree shifts of the
parts being absorbed by quantifying over all `m`.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these results makes the
same declaration.

## References

* [The Stacks Project, Lemma 36.61.6 (09UL)](https://stacks.math.columbia.edu/tag/09UL)
* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 36.61.5 (09UJ)](https://stacks.math.columbia.edu/tag/09UJ)
* [The Stacks Project, Lemma 20.46.10 (08CD)](https://stacks.math.columbia.edu/tag/08CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

namespace Scheme.Modules

/-- The image of a distinguished triangle of `D(𝒪_X)` under restriction to an open subscheme
followed by pushforward along a closed immersion `i : U ⟶ Y`, which is a distinguished triangle
of `D(𝒪_Y)`: both functors are exact, hence triangulated on derived categories. -/
public def pushforwardRestrictTriangle {X U Y : Scheme.{u}} (a : U ⟶ X) [IsOpenImmersion a]
    (i : U ⟶ Y) [IsClosedImmersion i] (T : Triangle (DerivedCategory X.Modules)) :
    Triangle (DerivedCategory Y.Modules) :=
  (pushforward i).mapDerivedCategory.mapTriangle.obj
    ((restrictFunctor a).mapDerivedCategory.mapTriangle.obj T)

/-- `AlgebraicGeometry.Scheme.Modules.pushforwardRestrictTriangle` is distinguished. -/
public theorem pushforwardRestrictTriangle_distinguished {X U Y : Scheme.{u}} (a : U ⟶ X)
    [IsOpenImmersion a] (i : U ⟶ Y) [IsClosedImmersion i]
    {T : Triangle (DerivedCategory X.Modules)} (hT : T ∈ distinguishedTriangles) :
    pushforwardRestrictTriangle a i T ∈ distinguishedTriangles :=
  (pushforward i).mapDerivedCategory.map_distinguished _
    ((restrictFunctor a).mapDerivedCategory.map_distinguished T hT)

end Scheme.Modules

namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Stacks 09UL, part (1).** If the first term of a distinguished triangle of `D(𝒪_X)` is
`(m + 1)`-pseudo-coherent relative to `S` and the second is `m`-pseudo-coherent relative to `S`,
then the third is `m`-pseudo-coherent relative to `S`. -/
@[stacks 09UL "part (1)",
  sga "6 I 2.6" "row 1 (n+1, n, n)",
  sga "6 III 1.4" "1st line (G underlined)"]
public theorem isPseudoCoherentFrom_obj₃_of_distinguished [LocallyOfFiniteType f] (m : ℤ)
    (T : Triangle (DerivedCategory X.Modules)) (hT : T ∈ distinguishedTriangles)
    (hE : IsPseudoCoherentFrom f T.obj₁ (m + 1)) (hE' : IsPseudoCoherentFrom f T.obj₂ m) :
    IsPseudoCoherentFrom f T.obj₃ m := by
  refine isPseudoCoherentFrom_of_forall_affinePair f T.obj₃ m fun U V hUV => ?_
  obtain ⟨n, i, hi, hio, hpc⟩ :=
    isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom f hE U V hUV
  have := hi
  have hpc' := IsPseudoCoherentFromOnAffinePair.forall_isClosedImmersion f
    (isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom f hE' U V hUV) n i hi hio
  refine ⟨n, i, hi, hio,
    (Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff i _ _).2 ?_⟩
  exact RingedSpace.isPseudoCoherentFrom_obj₃_of_distinguished
    m (Scheme.Modules.pushforwardRestrictTriangle U.1.ι i T)
    (Scheme.Modules.pushforwardRestrictTriangle_distinguished U.1.ι i hT)
    ((Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff i _ _).1 hpc)
    ((Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff i _ _).1 hpc')

/-- **Stacks 09UL, part (2).** If the first and third terms of a distinguished triangle of
`D(𝒪_X)` are `m`-pseudo-coherent relative to `S`, then so is the second. -/
@[stacks 09UL "part (2)",
  sga "6 I 2.6" "row 2 (n, n, n)",
  sga "6 III 1.4" "2nd line (F underlined)"]
public theorem isPseudoCoherentFrom_obj₂_of_distinguished [LocallyOfFiniteType f] (m : ℤ)
    (T : Triangle (DerivedCategory X.Modules)) (hT : T ∈ distinguishedTriangles)
    (hE : IsPseudoCoherentFrom f T.obj₁ m) (hE'' : IsPseudoCoherentFrom f T.obj₃ m) :
    IsPseudoCoherentFrom f T.obj₂ m := by
  refine isPseudoCoherentFrom_of_forall_affinePair f T.obj₂ m fun U V hUV => ?_
  obtain ⟨n, i, hi, hio, hpc⟩ :=
    isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom f hE U V hUV
  have := hi
  have hpc'' := IsPseudoCoherentFromOnAffinePair.forall_isClosedImmersion f
    (isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom f hE'' U V hUV) n i hi
    hio
  refine ⟨n, i, hi, hio,
    (Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff i _ _).2 ?_⟩
  exact RingedSpace.isPseudoCoherentFrom_obj₂_of_distinguished
    m (Scheme.Modules.pushforwardRestrictTriangle U.1.ι i T)
    (Scheme.Modules.pushforwardRestrictTriangle_distinguished U.1.ι i hT)
    ((Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff i _ _).1 hpc)
    ((Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff i _ _).1 hpc'')

/-- **Stacks 09UL, part (3).** If the second term of a distinguished triangle of `D(𝒪_X)` is
`(m + 1)`-pseudo-coherent relative to `S` and the third is `m`-pseudo-coherent relative to `S`,
then the first is `(m + 1)`-pseudo-coherent relative to `S`. -/
@[stacks 09UL "part (3)",
  sga "6 I 2.6" "row 3 (n, n, n-1)",
  sga "6 III 1.4" "3rd line (E underlined)"]
public theorem isPseudoCoherentFrom_obj₁_of_distinguished [LocallyOfFiniteType f] (m : ℤ)
    (T : Triangle (DerivedCategory X.Modules)) (hT : T ∈ distinguishedTriangles)
    (hE' : IsPseudoCoherentFrom f T.obj₂ (m + 1)) (hE'' : IsPseudoCoherentFrom f T.obj₃ m) :
    IsPseudoCoherentFrom f T.obj₁ (m + 1) := by
  refine isPseudoCoherentFrom_of_forall_affinePair f T.obj₁ (m + 1) fun U V hUV => ?_
  obtain ⟨n, i, hi, hio, hpc'⟩ :=
    isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom f hE' U V hUV
  have := hi
  have hpc'' := IsPseudoCoherentFromOnAffinePair.forall_isClosedImmersion f
    (isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom f hE'' U V hUV) n i hi
    hio
  refine ⟨n, i, hi, hio,
    (Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff i _ _).2 ?_⟩
  exact RingedSpace.isPseudoCoherentFrom_obj₁_of_distinguished
    m (Scheme.Modules.pushforwardRestrictTriangle U.1.ι i T)
    (Scheme.Modules.pushforwardRestrictTriangle_distinguished U.1.ι i hT)
    ((Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff i _ _).1 hpc')
    ((Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff i _ _).1 hpc'')

/-- **Stacks 09UL, the "moreover" clause for the third term.** If the first two terms of a
distinguished triangle of `D(𝒪_X)` are pseudo-coherent relative to `S`, so is the third. -/
@[stacks 09UL "moreover, third term"]
public theorem isPseudoCoherent_obj₃_of_distinguished [LocallyOfFiniteType f]
    (T : Triangle (DerivedCategory X.Modules)) (hT : T ∈ distinguishedTriangles)
    (hE : IsPseudoCoherent f T.obj₁) (hE' : IsPseudoCoherent f T.obj₂) :
    IsPseudoCoherent f T.obj₃ :=
  fun m => isPseudoCoherentFrom_obj₃_of_distinguished f m T hT (hE (m + 1)) (hE' m)

/-- **Stacks 09UL, the "moreover" clause for the second term.** If the first and third terms of a
distinguished triangle of `D(𝒪_X)` are pseudo-coherent relative to `S`, so is the second. -/
@[stacks 09UL "moreover, second term"]
public theorem isPseudoCoherent_obj₂_of_distinguished [LocallyOfFiniteType f]
    (T : Triangle (DerivedCategory X.Modules)) (hT : T ∈ distinguishedTriangles)
    (hE : IsPseudoCoherent f T.obj₁) (hE'' : IsPseudoCoherent f T.obj₃) :
    IsPseudoCoherent f T.obj₂ :=
  fun m => isPseudoCoherentFrom_obj₂_of_distinguished f m T hT (hE m) (hE'' m)

/-- **Stacks 09UL, the "moreover" clause for the first term.** If the last two terms of a
distinguished triangle of `D(𝒪_X)` are pseudo-coherent relative to `S`, so is the first. -/
@[stacks 09UL "moreover, first term"]
public theorem isPseudoCoherent_obj₁_of_distinguished [LocallyOfFiniteType f]
    (T : Triangle (DerivedCategory X.Modules)) (hT : T ∈ distinguishedTriangles)
    (hE' : IsPseudoCoherent f T.obj₂) (hE'' : IsPseudoCoherent f T.obj₃) :
    IsPseudoCoherent f T.obj₁ := by
  intro m
  simpa using isPseudoCoherentFrom_obj₁_of_distinguished f (m - 1) T hT
    (by simpa using hE' m) (hE'' (m - 1))

end Scheme.Hom

end AlgebraicGeometry

end
