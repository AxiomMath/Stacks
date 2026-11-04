module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorFunctionFieldMeromorphic
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionRatio

/-!
# Stacks 0EPT at the canonical ratio

Let `X` be a decent, locally Noetherian, integral algebraic space over a scheme `S` and let `ℒ`
be an invertible `𝒪_X`-module. Two regular meromorphic sections `s`, `s'` of `ℒ` differ by an
invertible rational function `f ∈ R(X)^*`, and their orders of vanishing differ by `ord_Z(f)`:

`ord_{Z,ℒ}(s) = ord_{Z,ℒ}(s') + ord_Z(f)` for every prime divisor `Z`,

which summed over the prime divisors is `div_ℒ(s) = div_ℒ(s') + div(f)`. This is Stacks 0EPT, with
the order of vanishing read at the canonical ratio `s / s_ξ` of Stacks 0EPR and the embedding
`R(X) → Q(𝒪^h_{X, ξ})` of Stacks 0ENK being the canonical one.

## Main results

* `AlgebraicGeometry.Space.exists_units_rationalFunctions_canonicalLocalRatio_eq_emb_mul`:
  **the first conclusion of Stacks 0EPT**, that the ratio of two regular meromorphic sections of
  an invertible module lies in `R(X)^*`, read on the canonical ratios at the generic point of
  every prime divisor.
* `AlgebraicGeometry.Space.exists_units_orderOfVanishingSection_canonicalLocalRatio_eq_add_ord`:
  **the second conclusion of Stacks 0EPT**, coefficientwise, at the canonical ratio family and
  with no hypothesis beyond those on `X`.

## References

* [Stacks Project, Tag 02SH](https://stacks.math.columbia.edu/tag/02SH)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

include hInt hN in
/-- **The ratio of two regular meromorphic sections is an invertible rational function.** On a
decent, locally Noetherian, integral algebraic space the ratio of two regular meromorphic sections
`s`, `s'` of an invertible `𝒪_X`-module is an invertible rational function `f`: at the generic
point of every prime divisor the canonical ratio `s / s_ξ` of Stacks 0EPR is the image of `f` under
the embedding `R(X) → Q(𝒪^h_{X, ξ})` of Stacks 0ENK times the canonical ratio `s' / s_ξ`. -/
@[stacks 0EPT "the first conclusion, that the ratio s/s' of two regular meromorphic sections of \
an invertible module is an element of R(X)^*, read on the canonical ratios s/s_ξ of Stacks 0EPR \
through the embedding R(X) → Q(O^h_{X, ξ}) of Stacks 0ENK"]
theorem exists_units_rationalFunctions_canonicalLocalRatio_eq_emb_mul
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (s s' : MeromorphicSection.{u, u} B S hS X hX L)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS X hX L s)
    (hs' : IsRegularMeromorphicSection.{u, u} B S hS X hX L s') :
    ∃ f : (rationalFunctions B S hS hX)ˣ, ∀ W : PrimeDivisor B S hS X,
      (canonicalLocalRatioFamily B S hS hX hdec L hL hInt hN W s :
          W.genericTotalFractionRing B S hS hX hdec) =
        (genericFractionEmbedding B S hS hX hdec hInt hN).emb W
            (f : rationalFunctions B S hS hX) *
          (canonicalLocalRatioFamily B S hS hX hdec L hL hInt hN W s' :
            W.genericTotalFractionRing B S hS hX hdec) := by
  obtain ⟨g, hg, -⟩ := existsUnique_units_smul_eq_of_isRegularMeromorphicSection B S hS hX
    hInt hN L hL s s' hs hs'
  obtain ⟨f, hf⟩ := exists_units_rationalFunctions_meromorphicFunctionEval_eq_emb B S hS hX
    hdec hInt hN g
  refine ⟨f, fun W => ?_⟩
  rw [← hf W]
  refine (W.coe_canonicalLocalRatio B S hS hX hdec L hL hInt hN s hs).trans
    ((W.canonicalGenericRatio_smul_of_eval B S hS hX hdec L hL hInt hN s s' _
    (hg ▸ units_smul_eval B S hS hX L g s' (W.genericEtaleChart B S hS hX hdec))).trans ?_)
  exact congrArg _ (W.coe_canonicalLocalRatio B S hS hX hdec L hL hInt hN s' hs').symm

include hInt hN in
/-- **The orders of vanishing of two regular meromorphic sections differ by `ord_Z` of their
ratio.** On a decent, locally Noetherian, integral algebraic space the orders of vanishing of two
regular meromorphic sections `s`, `s'` of an invertible `𝒪_X`-module along a prime divisor differ
by `ord_Z(f)` for one invertible rational function `f`, namely their ratio. Summed over the prime
divisors this is the identity `div_ℒ(s) = div_ℒ(s') + div(f)` of Weil divisors. -/
@[stacks 0EPT "the second conclusion, div_ℒ(s) = div_ℒ(s') + div(f) coefficientwise, at the \
canonical ratio s/s_ξ of Stacks 0EPR and the embedding of Stacks 0ENK, with f = s/s' PRODUCED \
rather than assumed"]
theorem exists_units_orderOfVanishingSection_canonicalLocalRatio_eq_add_ord
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (s s' : MeromorphicSection.{u, u} B S hS X hX L)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS X hX L s)
    (hs' : IsRegularMeromorphicSection.{u, u} B S hS X hX L s') :
    haveI : ∀ W : PrimeDivisor B S hS X,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hN
    ∃ f : (rationalFunctions B S hS hX)ˣ, ∀ W : PrimeDivisor B S hS X,
      orderOfVanishingSection.{u, u} B S hS hX hdec W L s
          (canonicalLocalRatioFamily B S hS hX hdec L hL hInt hN W) =
        orderOfVanishingSection.{u, u} B S hS hX hdec W L s'
            (canonicalLocalRatioFamily B S hS hX hdec L hL hInt hN W) +
          (genericFractionEmbedding B S hS hX hdec hInt hN).ord f W := by
  have : ∀ W : PrimeDivisor B S hS X,
      Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
    W.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hN
  have : ∀ W : PrimeDivisor B S hS X,
      IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
    W.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hN
  have : ∀ W : PrimeDivisor B S hS X,
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
    W.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hN
  obtain ⟨f, hf⟩ := exists_units_rationalFunctions_canonicalLocalRatio_eq_emb_mul B S hS hX hdec
    hInt hN L hL s s' hs hs'
  exact ⟨f, fun W => orderOfVanishingSection_eq_add_ord_of_ratio_eq B S hS hX hdec
    (genericFractionEmbedding B S hS hX hdec hInt hN) W L L s s'
    (canonicalLocalRatioFamily B S hS hX hdec L hL hInt hN W)
    (canonicalLocalRatioFamily B S hS hX hdec L hL hInt hN W) f (hf W)⟩

end AlgebraicGeometry.Space

end
