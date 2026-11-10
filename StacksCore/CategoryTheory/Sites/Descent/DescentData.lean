module

public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
public import Mathlib.CategoryTheory.Sites.Descent.Precoverage
import StacksCore.Tactic.StacksAttribute

/-!
# Descent data

Mathlib formalizes descent for a pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` rather than for a
fibred category `p : 𝒮 ⥤ 𝒞` with a chosen cleavage: the pseudofunctor supplies the choice of
pullbacks that Stacks makes by hand, and the two presentations agree under the Grothendieck
construction `CategoryTheory.Pseudofunctor.CoGrothendieck`.

Descent data come in two flavours. `Pseudofunctor.DescentData'` is indexed by chosen double and
triple fibre products, as in Stacks; `Pseudofunctor.DescentData` replaces those by an arbitrary
object mapping to two members of the family, which needs no fibre products.
`Pseudofunctor.DescentData'.descentDataEquivalence` identifies the two.

This file registers the correspondence and adds no declarations of its own.

## References

* [Stacks Project, Tag 026B](https://stacks.math.columbia.edu/tag/026B)
* [Stacks Project, Tag 026D](https://stacks.math.columbia.edu/tag/026D)
* [Stacks Project, Tag 026E](https://stacks.math.columbia.edu/tag/026E)
* [Stacks Project, Tag 02ZD](https://stacks.math.columbia.edu/tag/02ZD)
* [Stacks Project, Tag 02ZE](https://stacks.math.columbia.edu/tag/02ZE)
-/

@[expose] public section

namespace CategoryTheory

/- Stacks 026B is `DescentData'`, the flavour indexed by chosen pullbacks: `obj i` is `X_i` in
`𝒮_{U_i}`, `hom i j` is `φ_{ij} : pr₀^* X_i ⟶ pr₁^* X_j` over the chosen `U_i ×_U U_j` (invertible,
by the `IsIso` instance on `DescentData'.hom`), and `pullHom'_hom_comp` is the cocycle condition
over the chosen `U_i ×_U U_j ×_U U_k`. `DescentData'.Hom.comm` is the square of part (2), and the
`Category` instance is `DD(𝒰)`. `pullHom'_hom_self`, `φ_{ii} = id` on the diagonal, is not in the
Stacks definition; it follows there from the cocycle condition at `i = j = k`. -/
add_to_stacks 026B "(1)" Pseudofunctor.DescentData'
add_to_stacks 026B "(2)" Pseudofunctor.DescentData'.Hom
add_to_stacks 026B "(3), the category DD(𝒰)" Pseudofunctor.DescentData'.instCategory

/- Stacks 026D. On the canonical descent datum of an object `X` of `𝒮_U` the comparison map is the
composite of the two cleavage isomorphisms of Categories, Lemma 02XO. The `simp` normal form of
`(DescentData.ofObj X).hom` is `(α_{f₂, f_j})_X ∘ (α_{f₁, f_i})_X⁻¹`, with `α` the comparison
isomorphism `Pseudofunctor.mapComp'`; reading it at the chosen `U_i ×_U U_j` with the two
projections gives `can_{ij}`. The equality `f_i ∘ f₁ = f_j ∘ f₂` over `U` is carried by the
arguments of `mapComp'` rather than by an `eqToHom`. -/
add_to_stacks 026D Pseudofunctor.DescentData.ofObj_hom

/- Stacks 026E. Parts (1) and (2) are one construction: the trivial descent datum `(X, id_X)` on
the one-element family `{𝟙 U}` and the canonical descent datum `(f_i^* X, can)` on
`{f_i : U_i → U}` are both `DescentData.ofObj X`, read at the respective family, and pulling the
first back along `{f_i} → {𝟙 U}` gives the second
(`DescentData.toDescentDataCompPullFunctorIso`). Part (3), effectivity of `(X_i, φ_{ij})`, is
membership in the essential image of `Pseudofunctor.toDescentData`: an object `X` of `𝒮_U`
together with an isomorphism `(f_i^* X, can) ≅ (X_i, φ_{ij})`. -/
add_to_stacks 026E "(1) and (2)" Pseudofunctor.DescentData.ofObj
add_to_stacks 026E "(2), as a functor 𝒮_U ⥤ DD(𝒰)" Pseudofunctor.toDescentData
add_to_stacks 026E "(3), effectivity is `(F.toDescentData f).essImage`" Functor.essImage

/- Stacks 02ZD, whose three parts are three declarations. Mathlib's variables run in the opposite
order to Stacks': the source family `f : X i ⟶ S` is Stacks' *target* family
`𝒱 = {V_j → V}`, and `f' : X' j ⟶ S'` is Stacks' `𝒰 = {U_i → U}`. With that dictionary the
morphism of families of maps with fixed target of Sites, Definition 00VT is the data
`(α, p, p', w)`: `α : I → J` reindexes, `p : U → V` is `h`, `p' i : U_i → V_{α(i)}` is `g_i`, and
`w i : g_i ≫ (V_{α(i)} → V) = (U_i → U) ≫ h` is the commutativity Stacks requires of it.

Part (1) is `DescentData.pullFunctorObj`, which sends a descent datum relative to `𝒱` to one
relative to `𝒰`, with `obj i` the pullback `g_i^* Y_{α(i)}` and the gluing isomorphism the pullback
of `Y`'s (`DescentData.pullFunctorObjHom`). Part (2) is that this is functorial,
`DescentData.pullFunctor`. Part (3) is `DescentData.pullFunctorIso`: a second choice `α'`, `g'_i`
is a second pair `β`, `p''` with its own commutativity `w'`, and since `p` is shared between `w`
and `w'` the hypothesis `h = h'` is built into the statement rather than assumed; the conclusion
is a canonical isomorphism of the two functors.

Stacks states 02ZD for the descent data of 026B, which are indexed by chosen fibre products
`U_i ×_U U_{i'}` and so require them to exist. Mathlib's `DescentData` is instead indexed by an
arbitrary object mapping to two members of the family, needs no fibre products, and agrees with the
former under `DescentData'.descentDataEquivalence` whenever they do exist; so no fibre-product
hypothesis appears here. -/
add_to_stacks 02ZD "(1)" Pseudofunctor.DescentData.pullFunctorObj
add_to_stacks 02ZD "(2)" Pseudofunctor.DescentData.pullFunctor
add_to_stacks 02ZD "(3), with `h = h'` built in by sharing `p`"
  Pseudofunctor.DescentData.pullFunctorIso

/- Stacks 02ZE. The pullback functor on descent data along a morphism of families of maps with
fixed target; `DescentData.pullFunctorIso` is its independence of the auxiliary data. -/
add_to_stacks 02ZE Pseudofunctor.DescentData.pullFunctor

/- A near-match for Stacks 0GEA, with the local hypotheses (3) and (4) replaced by a global one.
This is intentionally not registered with `add_to_stacks`: the two hypothesis sets are not
comparable, and the exact tag is formalized by
`Functor.isEquivalence_toFamilyDescentDatum_of_homOver` in
`StacksFrontier/CategoryTheory/Sites/Descent/OfRefinement.lean`. The refinement
`𝒱 → 𝒰` of Stacks, given by `α : J → I` and `f_j : V_j → U_{α(j)}` over `id : U → U`, is here the
inequality `h₂` of generated sieves, and `h₁` says `𝒱` is a covering family. Stacks' hypothesis
(2), that `𝒮_U → DD(𝒱)` is an equivalence, is the instance argument; the conclusion that
`𝒮_U → DD(𝒰)` is an equivalence is the same. Where Stacks assumes (3) and (4) — full faithfulness
of `𝒮_{U_i} → DD(𝒱_i)` and faithfulness of `𝒮_{U_i ×_U U_{i'}} → DD(𝒱_{ii'})` — and uses them,
together with its hypothesis (1) on the existence of fibre products, to prove the refinement
functor `DD(𝒰) ⥤ DD(𝒱)` fully faithful, Mathlib reaches the same intermediate step from
`F.IsPrestack J` (`DescentData.fullyFaithfulPullFunctor`) and so needs no fibre products. The two
hypothesis sets are therefore not comparable, and `IsStackFor.of_le'` is the same statement phrased
for presieves. -/

end CategoryTheory
