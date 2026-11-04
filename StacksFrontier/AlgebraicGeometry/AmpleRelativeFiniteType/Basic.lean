module

public import StacksFrontier.AlgebraicGeometry.ImmersionTwistGapUniform
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksFrontier.AlgebraicGeometry.StalkwiseGeneration.Ample
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks Tag 01VT: ampleness over an affine base, with no named input

Let `f : X ⟶ S` be a morphism of finite type with `S` affine and let `L` be an invertible
`𝒪_X`-module. [Stacks, Tag 01VT] lists six equivalent conditions on `L`. This file proves the
equivalence of the four of them that are phrased in terms of ampleness and of immersions into
projective space over `S`:

1. `L` is ample on `X`;
2. `L` is `f`-ample;
3. (the source's (5)) some tensor power `L ^⊗ d` with `d ≥ 1` is `𝒪(1)` pulled back along an
   immersion `X ⟶ ℙⁿ_S` over `S`;
4. (the source's (6)) every tensor power `L ^⊗ d` with `d` sufficiently large is.

Everything here is unconditional. `Stacks.ProjectiveSpace.tfae_of_immersionTwistGapUniform`
proves the same four-term equivalence from one named hypothesis,
`Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform`, which is [Stacks, Tag 01VS] at
every scheme, morphism and invertible module; that hypothesis is a theorem,
`Stacks.VeryAmplePowersUniformDegree.immersionTwistGapUniform`, proved from
`Stacks.StalkwiseGeneration.immersionTwistGap_of_isAmple`, which gives Tag 01VS with no
hypothesis beyond ampleness and finite type.

## Main results

* `Stacks.AmpleRelativeFiniteType.tfae`: **[Stacks, Tag 01VT], conditions (1), (2), (5) and
  (6)**, with no named input.
* `Stacks.AmpleRelativeFiniteType.isAmple_iff_isRelativelyAmple`,
  `isAmple_iff_exists_hasImmersionTwistOver` and `isAmple_iff_eventually_hasImmersionTwistOver`:
  the three equivalences with (1) read off the list.

## The route

`Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform` is
`Stacks.AmpleProjectiveImmersion.ImmersionTwistGap` quantified over the situation, and
`Stacks.AmpleProjectiveImmersion.ImmersionTwistGap` is itself an implication with ampleness and
local finite type as its premises. So the uniform form is exactly what
`Stacks.StalkwiseGeneration.immersionTwistGap_of_isAmple` supplies at each situation, and the
discharge is a single application.

The remainder is already assembled: `Stacks.RelativeAmpleImplications.tfae` builds the cycle
(1) ⟹ (6) ⟹ (5) ⟹ (2) ⟹ (1), whose two unconditional steps are the two halves of
[Stacks, Tag 01VK] (`Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple`), and
`Stacks.ProjectiveSpace.tfae_of_immersionTwistGapUniform` discharges its [Stacks, Tag 02NN] and
[Stacks, Tag 0B3E] hypotheses.

## Implementation notes

**"`f` of finite type" is `[LocallyOfFiniteType f] [QuasiCompact f]`**, the two conditions whose
conjunction the source's hypothesis names; the repository has no single class for it.

**Conditions (3) and (4) of the source are absent from this file, and the attribute's clause
string says so; they are proved in the sibling module
`StacksFrontier.AlgebraicGeometry.AmpleRelativeFiniteType.VeryAmple`, where
`Stacks.AmpleRelativeFiniteType.tfae_six` states all six conditions with no named input.** They
assert relative very ampleness, [Stacks, Tag 01VM], of `L ^⊗ d`, and the link to the other four
conditions runs as follows:

* the predicate is `Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple`, which carries the Tag 01VM
  attribute and names the degree-one twist `𝒪_{𝐏(E)}(1)` as
  `Stacks.Tag01VMVeryAmple.twistOne`;
* (3) ⟹ (2) is [Stacks, Tag 01VN],
  `Stacks.RelativeAmple.isRelativelyAmple_of_isRelativelyVeryAmple`, which is unconditional,
  followed by the relative half of [Stacks, Tag 01PT],
  `Stacks.RelativeVeryAmple.isRelativelyAmple_of_isRelativelyAmple_tensorPowModule`;
* (5) ⟹ (3) and (6) ⟹ (4) are the source's "as `ℙⁿ_S` is a projective bundle over `S`", whose
  scheme half is [Stacks, Tag 01OE],
  `Stacks.SymGraded.projectiveBundleIsoProjectiveSpace` together with
  `Stacks.SymGraded.projectiveBundleIsoProjectiveSpace_hom_comp_fst`, and whose projective
  bundle `(Stacks.SymGraded.freeProjectiveBundle n).scheme` is
  `(relativeProj (symAlgebra (Stacks.SymGraded.freeModule (Stacks.SymGraded.coordIndex n))))`
  `.scheme` by `rfl`, so `Stacks.Tag01VMVeryAmple.isRelativelyVeryAmple_of_immersion` applies to
  the composite of the immersion with the inverse of that isomorphism.

The remaining input is the **module** half of Tag 01OE: that the isomorphism carries one
hyperplane sheaf to the other, that is

```
(Scheme.Modules.pullback (projectiveBundleIsoProjectiveSpace (X := S) n).hom).obj
    (projectiveSpaceTwistingSheaf n S)
  ≅ twistOne (Stacks.SymGraded.freeModule (Stacks.SymGraded.coordIndex n))
```

The two sheaves are built along different routes — `𝒪(1)` on `ℙⁿ_S` as the pullback of the
twisting sheaf of the integral model, `𝒪_{𝐏(E)}(1)` as the glueing of the degree-one twists of
the affine charts of `Proj_S(Sym(E))`. Over an affine base, which is the hypothesis of
Tag 01VT, there is nothing to glue and the comparison is a theorem:
`Stacks.SymGraded.hasFreeBundleTwistOne`.

**One difference of spelling from the source's clauses (5) and (6), disclosed in the clause
string.** The source writes `∃ n ≥ 1`, while
`Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver` writes `∃ n : ℕ` with no lower bound, so
conditions 3 and 4 below admit `n = 0`, where `ℙ⁰_S ≅ S`. **The two spellings are equivalent**,
by `Stacks.AmpleProjectiveImmersion.hasImmersionTwistOverPos_iff`: the linear embedding
`ℙⁿ_S ↪ ℙᴺ_S`, `Stacks.AmpleProjectiveImmersion.linearEmbeddingOver`, carries `𝒪(1)` to
`𝒪(1)`, so a witness at `n` gives one at `max n 1`. The source's clauses verbatim are
`Stacks.AmpleRelativeFiniteType.tfae_six_pos`.

## References

* [Stacks Project, Tag 01VT](https://stacks.math.columbia.edu/tag/01VT)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01VK](https://stacks.math.columbia.edu/tag/01VK)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [EGA II, Theorem 4.6.3]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.Ample
open Stacks.AmpleProjectiveImmersion

universe u

namespace Stacks.AmpleRelativeFiniteType

/-! ### [Stacks, Tag 01VT], conditions (1), (2), (5) and (6) -/

variable {X S : Scheme.{u}}

/-- **[Stacks, Tag 01VT], conditions (1), (2), (5) and (6), unconditionally.** For `f : X ⟶ S`
of finite type with `S` affine and `L` an invertible `𝒪_X`-module, the following are equivalent:

1. `L` is ample on `X`;
2. `L` is ample relative to `f`;
3. (the source's (5)) `L ^⊗ d` is `𝒪(1)` pulled back along an immersion `X ⟶ ℙⁿ_S` over `S`, for
   some `d ≥ 1`;
4. (the source's (6)) the same, for every sufficiently large `d`.

The cycle is (1) ⟹ (4) ⟹ (3) ⟹ (2) ⟹ (1). The first step is [Stacks, Tag 01VS] at the single
situation `(X, S, f, L)` — no covering of the base and no glueing, which is what affineness of
`S` buys — the second is dropping the lower bound on the degree, the third is [Stacks, Tag 01VN]
together with [Stacks, Tag 02NN], and the last two are the two halves of [Stacks, Tag 01VK].

The source's conditions (3) and (4), relative very ampleness, are not among the four; they join
them in `Stacks.AmpleRelativeFiniteType.tfae_six`, in the sibling module
`StacksFrontier.AlgebraicGeometry.AmpleRelativeFiniteType.VeryAmple`. -/
@[stacks 01VT "conditions (1), (2), (5) and (6) of the six; conditions (3) and (4), relative \
  very ampleness, are stated together with these four by \
  `Stacks.AmpleRelativeFiniteType.tfae_six`, and (5), (6) are taken with no lower bound on `n`, \
  which `Stacks.AmpleProjectiveImmersion.hasImmersionTwistOverPos_iff` shows is the source's \
  `n ≥ 1` clause"]
theorem tfae [IsAffine S] (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L]
    [LocallyOfFiniteType f] [QuasiCompact f] :
    List.TFAE [
      IsAmple X L,
      Stacks.RelativeAmple.IsRelativelyAmple f L,
      ∃ d : ℕ, 1 ≤ d ∧ HasImmersionTwistOver f (tensorPowModule X L (d : ℤ)),
      ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
        HasImmersionTwistOver f (tensorPowModule X L (d : ℤ))] :=
  Stacks.ProjectiveSpace.tfae_of_immersionTwistGapUniform
    Stacks.VeryAmplePowersUniformDegree.immersionTwistGapUniform f L ‹QuasiCompact f›

/-- **The equivalence of (1) and (2) of [Stacks, Tag 01VT]** over an affine base: ampleness and
`f`-ampleness agree. This is [Stacks, Tag 01VK] and needs neither the finite-type hypothesis nor
Tag 01VS; it is read off `Stacks.AmpleRelativeFiniteType.tfae` for uniformity with the other two
corollaries. -/
theorem isAmple_iff_isRelativelyAmple [IsAffine S] (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] [LocallyOfFiniteType f] [QuasiCompact f] :
    IsAmple X L ↔ Stacks.RelativeAmple.IsRelativelyAmple f L :=
  (tfae f L).out 1 2

/-- **The equivalence of (1) and the source's (5) of [Stacks, Tag 01VT]**: `L` is ample exactly
when some tensor power `L ^⊗ d` with `d ≥ 1` is `𝒪(1)` pulled back along an immersion
`X ⟶ ℙⁿ_S` over `S`. -/
theorem isAmple_iff_exists_hasImmersionTwistOver [IsAffine S] (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] [LocallyOfFiniteType f] [QuasiCompact f] :
    IsAmple X L ↔
      ∃ d : ℕ, 1 ≤ d ∧ HasImmersionTwistOver f (tensorPowModule X L (d : ℤ)) :=
  (tfae f L).out 1 3

/-- **The equivalence of (1) and the source's (6) of [Stacks, Tag 01VT]**: `L` is ample exactly
when every sufficiently high tensor power of `L` is `𝒪(1)` pulled back along an immersion
`X ⟶ ℙⁿ_S` over `S`. -/
theorem isAmple_iff_eventually_hasImmersionTwistOver [IsAffine S] (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] [LocallyOfFiniteType f] [QuasiCompact f] :
    IsAmple X L ↔
      ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
        HasImmersionTwistOver f (tensorPowModule X L (d : ℤ)) :=
  (tfae f L).out 1 4

end Stacks.AmpleRelativeFiniteType

end
