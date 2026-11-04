module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NormalizedExistenceNagata
import StacksCore.Tactic.StacksAttribute

/-!
# The dualizing complex normalized relative to `ω_S^•`: its defining properties

In Situation [Stacks, Tag 0AU4], for a scheme `X` of finite type over `S`, the dualizing complex
`ω_X^•` normalized relative to `ω_S^•` (`Stacks.Duality.normalizedDualizingComplex`,
[Stacks, Tag 0AUA]) comes with isomorphisms `α_U : ω_X^•|_U ≅ (U → S)^! ω_S^•` for every open
`U ⊆ X` separated over `S`. This file records the properties the source attaches to it in the
discussion before Definition 0AUA: `ω_X^•` is a dualizing complex, the pair `(ω_X^•, α_U)` is
unique up to unique isomorphism, and for every finite covering `𝒰 : X = ⋃ U_i` by opens separated
over `S` the pair `(ω_X^•, α_{U_i})` is the dualizing complex normalized relative to `ω_S^•` and
`𝒰`, again up to unique isomorphism.

The upper shriek functors are those of Nagata compactifications,
`Stacks.Duality.UpperShriek.nagata`.

## Main results

* `Stacks.Duality.isDualizingComplex_normalizedDualizingComplex`
* `Stacks.Duality.existsUnique_iso_normalizedDualizingComplex`
* `Stacks.Duality.existsUnique_iso_normalizedDualizingComplex_toNormalized`

## References

* [Stacks Project, Tag 0AUA](https://stacks.math.columbia.edu/tag/0AUA)
* [Stacks Project, Tag 0AU7](https://stacks.math.columbia.edu/tag/0AU7)
* [Stacks Project, Tag 0AU8](https://stacks.math.columbia.edu/tag/0AU8)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u w

namespace Stacks.Duality

variable {X S : Scheme.{u}} {p : X ⟶ S} (hp : IsFiniteTypeOverNoetherian p)
  (ωS : quasiCoherentDerivedCategoryPlusOfModel S)
  (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)

/-- **[Stacks, Tag 0AUA], `ω_X^•` is a dualizing complex.** Let `S` be Noetherian with a
dualizing complex `ω_S^•` and `X` of finite type over `S`. The dualizing complex `ω_X^•`
normalized relative to `ω_S^•` is a dualizing complex on `X`. -/
@[stacks 0AUA "ω_X^• is a dualizing complex on X"]
theorem isDualizingComplex_normalizedDualizingComplex :
    haveI := hp.source_noetherian
    IsDualizingComplex (normalizedDualizingComplex hp ωS hωS).complex.obj.obj :=
  NormalizedOnOpens.isDualizingComplex_ofCompactifications nagataCompactification hωS _

/-- **[Stacks, Tag 0AUA], uniqueness up to unique isomorphism.** Let `S` be Noetherian with a
dualizing complex `ω_S^•` and `X` of finite type over `S`. For any complex `K` on `X` with
isomorphisms `β_U : K|_U ≅ (U → S)^! ω_S^•` for the opens `U ⊆ X` separated over `S`,
compatible with restriction, exactly one isomorphism `K ≅ ω_X^•` carries `β_U` to the
isomorphism `α_U` of `ω_X^•` for every such `U`. -/
@[stacks 0AUA "the pair (ω_X^•, α_U) is unique up to unique isomorphism"]
theorem existsUnique_iso_normalizedDualizingComplex
    (𝒦 : NormalizedOnOpens UpperShriek.nagata hp ωS) :
    ∃! e : 𝒦.complex ≅ (normalizedDualizingComplex hp ωS hωS).complex,
      ∀ (W : X.Opens) (hW : IsShriekable (W.ι ≫ p)),
        (UpperShriek.nagata.shriek W.ι (hp.isShriekable_ι W)).mapIso e ≪≫
          (normalizedDualizingComplex hp ωS hωS).localIso W hW = 𝒦.localIso W hW :=
  NormalizedOnOpens.existsUnique_iso_ofCompactifications nagataCompactification hωS 𝒦 _

/-- **[Stacks, Tag 0AUA], normalized relative to every covering.** Let `S` be Noetherian with a
dualizing complex `ω_S^•`, `X` of finite type over `S` and `𝒰 : X = ⋃ U_i` a finite open
covering by opens separated over `S`. Then `(ω_X^•, α_{U_i})` is a dualizing complex normalized
relative to `ω_S^•` and `𝒰` (`Stacks.Duality.NormalizedOnOpens.toNormalized`), and it is the one
up to unique isomorphism: for every dualizing complex `(K, β_i)` normalized relative to `ω_S^•`
and `𝒰`, exactly one isomorphism `K ≅ ω_X^•` carries `β_i` to `α_{U_i}` for all `i`. -/
@[stacks 0AUA "(ω_X^•, α_{U_i}) is normalized relative to ω_S^• and every finite covering by \
opens separated over S"]
theorem existsUnique_iso_normalizedDualizingComplex_toNormalized {ι : Type w}
    (𝒰 : SeparatedCovering p ι) (𝒩 : Normalized UpperShriek.nagata hp ωS 𝒰) :
    ∃! e : 𝒩.complex ≅ ((normalizedDualizingComplex hp ωS hωS).toNormalized 𝒰).complex,
      ∀ i, (UpperShriek.nagata.shriek (𝒰.U i).ι (hp.isShriekable_ι _)).mapIso e ≪≫
          ((normalizedDualizingComplex hp ωS hωS).toNormalized 𝒰).localIso i = 𝒩.localIso i :=
  Normalized.existsUnique_iso_nagata hωS 𝒩 _

end Stacks.Duality

end
