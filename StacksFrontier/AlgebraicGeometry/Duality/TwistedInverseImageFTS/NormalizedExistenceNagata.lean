module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NagataFormalism
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NormalizedExistence

/-!
# Normalized dualizing complexes for the upper shriek functors of Nagata compactifications

In Situation [Stacks, Tag 0AU4] (`S` Noetherian with a dualizing complex `ω_S^•`), for `X` of
finite type over `S` and the upper shriek functors `f^!` of Nagata compactifications
(`Stacks.Duality.UpperShriek.nagata`): a dualizing complex normalized relative to `ω_S^•` and a
finite covering of `X` by opens separated over `S` exists ([Stacks, Tag 0AU9]), is unique up to
unique isomorphism ([Stacks, Tag 0AU7]) and does not depend on the covering
([Stacks, Tag 0AU8]); this defines the dualizing complex `ω_X^•` normalized relative to `ω_S^•`
([Stacks, Tag 0AUA]).

## Main results

* `Stacks.Duality.Normalized.existsUnique_iso_nagata`: [Stacks, Tag 0AU7].
* `Stacks.Duality.Normalized.exists_existsUnique_iso_nagata`: [Stacks, Tag 0AU8].
* `Stacks.Duality.Normalized.exists_nagata`: [Stacks, Tag 0AU9].
* `Stacks.Duality.normalizedDualizingComplex`: [Stacks, Tag 0AUA].

## References

* [Stacks Project, Tag 0AU7](https://stacks.math.columbia.edu/tag/0AU7)
* [Stacks Project, Tag 0AU8](https://stacks.math.columbia.edu/tag/0AU8)
* [Stacks Project, Tag 0AU9](https://stacks.math.columbia.edu/tag/0AU9)
* [Stacks Project, Tag 0AUA](https://stacks.math.columbia.edu/tag/0AUA)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u w

namespace Stacks.Duality

namespace Normalized

variable {X S : Scheme.{u}} {p : X ⟶ S} {hp : IsFiniteTypeOverNoetherian p}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}

/-- **[Stacks, Tag 0AU7]** In Situation 0AU4, let `X` be of finite type over `S` and `𝒰` a finite
open covering of `X` by schemes separated over `S`. A dualizing complex normalized relative to
`ω_S^•` and `𝒰` is unique up to unique isomorphism: for two of them, `(K, α_i)` and `(K', α'_i)`,
exactly one isomorphism `K ≅ K'` carries `α_i` to `α'_i` on every member. -/
@[stacks 0AU7]
theorem existsUnique_iso_nagata
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) {ι : Type w}
    {𝒰 : SeparatedCovering p ι} (𝒩 𝒩' : Normalized UpperShriek.nagata hp ωS 𝒰) :
    ∃! e : 𝒩.complex ≅ 𝒩'.complex, ∀ i,
      (UpperShriek.nagata.shriek (𝒰.U i).ι (hp.isShriekable_ι _)).mapIso e ≪≫
        𝒩'.localIso i = 𝒩.localIso i :=
  existsUnique_iso_ofCompactifications nagataCompactification hωS 𝒩 𝒩'

/-- **[Stacks, Tag 0AU8]** In Situation 0AU4, let `X` be of finite type over `S` and `𝒰`, `𝒱` two
finite open coverings of `X` by schemes separated over `S`. If `(K, α_i)` is a dualizing complex
normalized relative to `ω_S^•` and `𝒰`, there is a dualizing complex `(K', α'_j)` normalized
relative to `ω_S^•` and `𝒱`, and the two are canonically isomorphic: exactly one isomorphism
`K ≅ K'` carries the restriction of `α_i` to `U_i ∩ V_j` to that of `α'_j`, for all `i`, `j`. -/
@[stacks 0AU8]
theorem exists_existsUnique_iso_nagata
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
    {ι J : Type w} {𝒰 : SeparatedCovering p ι} (𝒱 : SeparatedCovering p J)
    (𝒩 : Normalized UpperShriek.nagata hp ωS 𝒰) :
    ∃ 𝒩' : Normalized UpperShriek.nagata hp ωS 𝒱,
      (haveI := hp.source_noetherian; IsDualizingComplex 𝒩'.complex.obj.obj) ∧
      ∃! e : 𝒩.complex ≅ 𝒩'.complex, ∀ i j,
        (UpperShriek.nagata.shriek (𝒰.U i ⊓ 𝒱.U j).ι (hp.isShriekable_ι _)).mapIso e ≪≫
          UpperShriek.nagata.restrictLocalIso hp ωS 𝒩'.complex
            (inf_le_right : 𝒰.U i ⊓ 𝒱.U j ≤ 𝒱.U j) (𝒱.shriekable j) (𝒩'.localIso j) =
        UpperShriek.nagata.restrictLocalIso hp ωS 𝒩.complex
          (inf_le_left : 𝒰.U i ⊓ 𝒱.U j ≤ 𝒰.U i) (𝒰.shriekable i) (𝒩.localIso i) :=
  exists_existsUnique_iso_ofCompactifications nagataCompactification hωS 𝒱 𝒩

/-- **[Stacks, Tag 0AU9]** In Situation 0AU4, let `X` be of finite type over `S` and `𝒰` a finite
open covering of `X` by schemes separated over `S`. Then there exists a dualizing complex
normalized relative to `ω_S^•` and `𝒰`. -/
@[stacks 0AU9]
theorem exists_nagata
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
    {ι : Type w} (𝒰 : SeparatedCovering p ι) :
    ∃ 𝒩 : Normalized UpperShriek.nagata hp ωS 𝒰,
      haveI := hp.source_noetherian; IsDualizingComplex 𝒩.complex.obj.obj :=
  exists_ofCompactifications nagataCompactification hωS 𝒰

end Normalized

/-- **[Stacks, Tag 0AUA]** Let `S` be Noetherian with a dualizing complex `ω_S^•` and `X` of finite
type over `S`. The dualizing complex `ω_X^•` normalized relative to `ω_S^•`: a complex on `X` with
isomorphisms `α_W : ω_X^•|_W ≅ (W → S)^! ω_S^•` for every open `W` separated over `S`,
compatible with restriction. It is unique up to unique isomorphism
(`Stacks.Duality.NormalizedOnOpens.existsUnique_iso_ofCompactifications`) and normalized relative
to `ω_S^•` and every finite covering of `X` by opens separated over `S`
(`Stacks.Duality.NormalizedOnOpens.toNormalized`). -/
@[stacks 0AUA]
def normalizedDualizingComplex {X S : Scheme.{u}} {p : X ⟶ S}
    (hp : IsFiniteTypeOverNoetherian p) (ωS : quasiCoherentDerivedCategoryPlusOfModel S)
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) :
    NormalizedOnOpens UpperShriek.nagata hp ωS :=
  normalizedDualizingComplexOfCompactifications nagataCompactification hp ωS hωS

end Stacks.Duality
