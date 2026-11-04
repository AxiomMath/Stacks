module

public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.ToSieve

/-!
# Comparing the two renderings of a stack

The library states "stack" twice. `CategoryTheory.Functor.IsStack` (Stacks 026F) is phrased with
*sieves* and with the *chosen* pullbacks of a fibred category: its condition (2) is that the
presheaves `Mor(x, y)` are sheaves on `𝒞/U`, and its condition (3) is effectivity of every
`CategoryTheory.Functor.SieveDescentDatum`. `CategoryTheory.Functor.IsStackInGroupoids`
(Stacks 02ZI) is phrased with *covering families* whose double and triple overlaps are *genuine
fibre products* in the base, and with arbitrary cartesian lifts
(`CategoryTheory.Functor.Restriction`) in place of the chosen ones.

This file relates them. The main result is the implication (3) ⟹ (1) of Stacks 02ZJ:

* `CategoryTheory.Functor.IsStack.isStackInGroupoids`: a stack in the sense of 026F whose structure
  functor is fibred in groupoids is a stack in groupoids in the sense of 02ZI.

The translation between the two renderings is built up in the files imported here: the dictionary
between arbitrary cartesian lifts and the chosen pullbacks
(`StacksFrontier/CategoryTheory/Sites/Stack/StackBridge/Dictionary.lean`), condition (2)
(`StacksFrontier/CategoryTheory/Sites/Stack/StackBridge/IsomSheaf.lean`), and the descent data of a covering family and their reading relative to the
generated sieve (`StacksFrontier/CategoryTheory/Sites/Stack/StackBridge/DescentDatum.lean`, `StacksFrontier/CategoryTheory/Sites/Stack/StackBridge/ToSieve.lean`).

## Implementation notes

The cocycle condition of a `CategoryTheory.Functor.DescentDatum` is stated through auxiliary
morphisms `αij`, `αjk`, `αik` over the triple overlap, each required only to be a *canonical
restriction* (`CategoryTheory.Functor.IsRestrictionOf`) of one of the gluing isomorphisms. That
condition does not by itself force such a morphism to lie over an identity of the triple overlap:
it forces only that the base morphism `e` it lies over satisfies `e ≫ s₁₂ = s₁₂`, which leaves `e`
free whenever `s₁₂` is not a monomorphism. Were the auxiliary morphisms genuinely free in that way
the cocycle condition would relate nothing, and effectivity could not be derived from it.

It does force it, and the *genuine fibre products* are exactly what does so: the cocycle condition
together with the restriction conditions for `αjk` and `αik` gives `e ≫ q₃ = q₃`, hence
`e ≫ s₂₃ = s₂₃` because `Vⱼ ×_U Vₖ` is a genuine fibre product, hence `e = 𝟙` because the triple
overlap is one as well. This is
`CategoryTheory.Functor.DescentDatum.isHomLift_id_αij`, and everything about descent data below
rests on it.

The two renderings are related in one direction only, and the asymmetry is not an artefact:

* Given a covering *family* with genuine fibre-product overlaps, the sieve it generates is covering
  and every arrow of that sieve factors through a member of the family; two factorizations of one
  arrow are compared by the *genuine* fibre product, which is what turns a family-indexed
  compatible system into a sieve-indexed one. Nothing beyond the data at hand is needed, so the
  conditions of 026F imply those of 02ZI outright, with no hypothesis on the base.
* In the other direction one starts from a covering *sieve* and must *produce* the fibre products
  `Uᵢ ×_U Uⱼ` in order to have anything to apply the conditions of 02ZI to. They need not exist:
  `IsStackInGroupoids` deliberately assumes no `HasPullbacks` on the base — that is the Stacks
  project's notion of a site — so over a base lacking the relevant fibre products its conditions
  (2) and (3) are not applicable to a covering sieve at all and carry no information about it.
  The converse implication is therefore not provable as stated; it needs those fibre products as a
  hypothesis, and is not proved here.
-/

@[expose] public section

namespace CategoryTheory

universe w v₁ v₂ u₁ u₂

namespace Functor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-- **The implication (3) ⟹ (1) of Stacks 02ZJ.** A stack in the sense of Stacks 026F
(`CategoryTheory.Functor.IsStack`) whose structure functor is fibred in groupoids is a stack in
groupoids in the sense of Stacks 02ZI (`CategoryTheory.Functor.IsStackInGroupoids`).

No hypothesis on the base beyond it being a site is needed: the fibre products `Vᵢ ×_U Vⱼ` that the
02ZI conditions quantify over are *given* in each instance of those conditions, and they are what
makes a system indexed by a covering family into one indexed by the sieve it generates. The
converse implication is *not* available in this generality — see the module docstring. -/
theorem IsStack.isStackInGroupoids {p : 𝒳 ⥤ 𝒞} {J : GrothendieckTopology 𝒞} (hp : p.IsStack J)
    (hgpd : p.IsFiberedInGroupoids) : IsStackInGroupoids.{w} p J where
  isFiberedInGroupoids := hgpd
  isom_isSheaf := by
    have := hp.isFibered
    intro U x y hx hy I V f hf Vij pr₁ pr₂ hVij xr yr xrij yrij
    exact isomIsSheafFor_of_isStack hp x y hx hy V f hf Vij pr₁ pr₂ hVij xr yr xrij yrij
  effective_descent := by
    have := hp.isFibered
    intro U I V f hf Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃ D
    exact D.isEffective_of_hasEffectiveDescent hp.hasEffectiveDescent hf

end Functor

end CategoryTheory
