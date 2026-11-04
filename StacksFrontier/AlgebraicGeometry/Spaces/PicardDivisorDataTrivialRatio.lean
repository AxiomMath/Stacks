module

public import StacksFrontier.AlgebraicGeometry.Spaces.PicardWeilDivisorClass

/-!
# The trivial ratio family on an algebraic space

Let `X` be a decent, locally Noetherian, integral algebraic space over `S`. The data
`AlgebraicGeometry.Space.PicardDivisorData` of the construction of Stacks 0EPW records, for
every invertible `𝒪_X`-module `ℒ`, a regular meromorphic section and a *ratio family*
`s ↦ s / s_ξ` at the generic point of every prime divisor, the latter being an arbitrary family
of maps from the meromorphic sections of `ℒ` to the units of `Q(𝒪^h_{X, ξ})`.

Replacing the ratio family of such data by the constant family `s ↦ 1` again gives such data:
all orders of vanishing then vanish, so the local finiteness required of `div_ℒ(s)` is
immediate and the two divisor identities of Stacks 0EPT and 0EPV hold with `f = 1`. This is
`AlgebraicGeometry.Space.PicardDivisorData.trivialRatio`.

## Main definitions

* `AlgebraicGeometry.Space.PicardDivisorData.trivialRatio` is the data obtained from given data
  by replacing its ratio family with the constant family `s ↦ 1`.

## Main results

* `AlgebraicGeometry.Space.PicardDivisorData.orderOfVanishingSection_trivialRatio`: every order
  of vanishing taken through the trivial ratio family is zero.
* `AlgebraicGeometry.Space.PicardDivisorData.eq_one_of_hscale_trivialRatio` and
  `AlgebraicGeometry.Space.PicardDivisorData.eq_zero_of_htriv_trivialRatio`: the two
  hypotheses of
  `AlgebraicGeometry.Space.PicardDivisorData.injective_picardToWeilDivisorClassGroup`
  (Stacks 0EPX) are false for the trivial ratio family unless `R(X)^* = 1`, respectively
  unless `Pic(X) = 0`. Both hypotheses therefore say something about the ratio family itself,
  and neither is a consequence of the hypotheses of Stacks 0EPX on `X`:
  `AlgebraicGeometry.Space.PicardDivisorData.not_hscale_trivialRatio` and
  `AlgebraicGeometry.Space.PicardDivisorData.not_htriv_trivialRatio` read this as the refutation
  it is.

## Implementation notes

The rescaling `t = f⁻¹ s` of a regular meromorphic section by an invertible rational function —
the hypothesis `hscale` of Stacks 0EPX — is a statement about the ratio family: it asks for a
meromorphic section whose ratio is `(f_ξ)⁻¹ s / s_ξ` at the generic point of every prime
divisor at once. For the trivial ratio family it asks that `f_ξ = 1` there, so by the
injectivity of `R(X) → Q(𝒪^h_{X, ξ})` of Stacks 0ENK it asks that `f = 1`. Likewise the claim
of Stacks 0EPX — the hypothesis `htriv`, that a regular meromorphic section with vanishing Weil
divisor trivializes the module — is vacuous in its hypothesis for the trivial ratio family and
so asks that every invertible `𝒪_X`-module be trivial.

Discharging either hypothesis therefore requires data whose ratio family is the honest
`s ↦ s / s_ξ`: a family of maps compatible with multiplication by meromorphic functions and
with the étale-local trivializations of `ℒ`. The source's proof of the claim uses exactly that
compatibility, through the identification
`(𝒪^h_{X, ξ})^{sh} = 𝒪_{X, ū} = (A_𝔭)^{sh}` of Stacks 0EMZ and 04KF over an affine integral
étale chart `Spec(A)` of Stacks 0357 trivializing `ℒ`, on which the normality of `X` makes
`A_𝔭` a discrete valuation ring and Stacks 031T recovers `f ∈ A` from `f ∈ A_𝔭` at all height
one primes.

## References

* [Stacks Project, Tag 0EPX](https://stacks.math.columbia.edu/tag/0EPX)
* [Stacks Project, Tag 0EPW](https://stacks.math.columbia.edu/tag/0EPW)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
variable (hdec : IsDecentSpace B S hS X)
variable (E : GenericFractionEmbedding B S hS hX hdec)
variable [∀ W : PrimeDivisor B S hS X,
  Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec)]
variable [∀ W : PrimeDivisor B S hS X,
  IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec)]
variable [∀ W : PrimeDivisor B S hS X,
  Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec)]

/-- The order of vanishing of a meromorphic section along a prime divisor is zero when it is
read through the constant ratio family `s ↦ 1`. -/
theorem orderOfVanishingSection_const_one (W : PrimeDivisor B S hS X)
    (L : Modules.{u, u} B S hS X hX) (t : MeromorphicSection.{u, u} B S hS X hX L) :
    orderOfVanishingSection.{u, u} B S hS hX hdec W L t (fun _ => 1) = 0 :=
  orderOfVanishingSection_eq_zero_of_isUnit.{u, u} B S hS hX hdec W L t (fun _ => 1)
    (v := 1) isUnit_one (by simp)

namespace PicardDivisorData

variable {B S hS hX hdec E}
variable (D : PicardDivisorData B S hS hX hdec E)

/-- The data of the construction of Stacks 0EPW obtained from given such data by replacing its
ratio family with the constant family `s ↦ 1`, which keeps the sections and makes every order
of vanishing zero. -/
def trivialRatio : PicardDivisorData B S hS hX hdec E where
  isLocallyNoetherian := D.isLocallyNoetherian
  irreducibleSpace := D.irreducibleSpace
  sect L hL := D.sect L hL
  ratio _ _ _ _ := 1
  generating L hL := by
    have := D.irreducibleSpace
    refine ⟨Set.univ, isOpen_univ, Set.univ_nonempty, fun W hW => absurd ?_ hW⟩
    exact orderOfVanishingSection_const_one B S hS hX hdec W L (D.sect L hL)
  exists_ord_sub_eq_of_iso L N hL hN _ := by
    refine ⟨1, fun W => ?_⟩
    rw [congrFun E.ord_one W, Pi.zero_apply]
    simp only [divisorCoefficients,
      orderOfVanishingSection_const_one B S hS hX hdec W L (D.sect L hL),
      orderOfVanishingSection_const_one B S hS hX hdec W N (D.sect N hN), sub_self]
  exists_ord_sub_eq_tensorModule L N hL hN := by
    refine ⟨1, fun W => ?_⟩
    rw [congrFun E.ord_one W, Pi.zero_apply]
    simp only [divisorCoefficients, orderOfVanishingSection_const_one B S hS hX hdec W _
      (D.sect _ (isInvertibleModule_picardTensorModule B S hS hX L N hL hN)),
      orderOfVanishingSection_const_one B S hS hX hdec W L (D.sect L hL),
      orderOfVanishingSection_const_one B S hS hX hdec W N (D.sect N hN), add_zero, sub_self]

/-- The ratio family of `D.trivialRatio` is constantly `1`. -/
@[simp]
theorem ratio_trivialRatio (L : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L) (W : PrimeDivisor B S hS X)
    (s : MeromorphicSection.{u, u} B S hS X hX L) :
    D.trivialRatio.ratio L hL W s = 1 :=
  rfl

/-- The regular meromorphic section of `D.trivialRatio` attached to an invertible module `L` is
that of `D`. -/
@[simp]
theorem sect_trivialRatio (L : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L) :
    D.trivialRatio.sect L hL = D.sect L hL :=
  rfl

/-- Every order of vanishing taken through the trivial ratio family is zero. -/
theorem orderOfVanishingSection_trivialRatio (W : PrimeDivisor B S hS X)
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (t : MeromorphicSection.{u, u} B S hS X hX L) :
    orderOfVanishingSection.{u, u} B S hS hX hdec W L t (D.trivialRatio.ratio L hL W) = 0 :=
  orderOfVanishingSection_const_one B S hS hX hdec W L t

/-- For the trivial ratio family, the rescaling of a regular meromorphic section by an
invertible rational function `f` — the hypothesis `hscale` of Stacks 0EPX — holds only if
`f = 1`, because it then asks for the image of `f` in `Q(𝒪^h_{X, ξ})` to be `1` and that image
is injective by Stacks 0ENK. -/
theorem eq_one_of_hscale_trivialRatio (W : PrimeDivisor B S hS X)
    (hscale : ∀ (L : Modules.{u, u} B S hS X hX)
      (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L) (f : (rationalFunctions B S hS hX)ˣ),
      ∃ t : MeromorphicSection.{u, u} B S hS X hX L, ∀ W : PrimeDivisor B S hS X,
        (D.trivialRatio.ratio L hL W (D.trivialRatio.sect L hL) :
            W.genericTotalFractionRing B S hS hX hdec) =
          E.emb W (f : rationalFunctions B S hS hX) *
            (D.trivialRatio.ratio L hL W t : W.genericTotalFractionRing B S hS hX hdec))
    (f : (rationalFunctions B S hS hX)ˣ) :
    (f : rationalFunctions B S hS hX) = 1 := by
  obtain ⟨L, hL, -⟩ := exists_picardClass (B := B) ⟨X, hX⟩ 0
  obtain ⟨t, ht⟩ := hscale L hL f
  have h := ht W
  simp only [ratio_trivialRatio, Units.val_one, mul_one] at h
  exact E.injective_emb W (by rw [← h, map_one])

/-- For the trivial ratio family, the claim of Stacks 0EPX — the hypothesis `htriv`, that a
regular meromorphic section of an invertible `𝒪_X`-module whose Weil divisor vanishes
trivializes that module — holds only if `Pic(X) = 0`, because every Weil divisor read through
that family vanishes. -/
theorem eq_zero_of_htriv_trivialRatio
    (htriv : ∀ (L : Modules.{u, u} B S hS X hX)
      (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
      (t : MeromorphicSection.{u, u} B S hS X hX L),
      (∀ W : PrimeDivisor B S hS X,
          orderOfVanishingSection.{u, u} B S hS hX hdec W L t
            (D.trivialRatio.ratio L hL W) = 0) →
        picardClass (B := B) ⟨X, hX⟩ L hL = 0)
    (x : picardGroup (B := B) (S := S) (hS := hS) ⟨X, hX⟩) :
    x = 0 := by
  obtain ⟨L, hL, rfl⟩ := exists_picardClass (B := B) ⟨X, hX⟩ x
  exact htriv L hL (D.sect L hL) fun W => D.orderOfVanishingSection_trivialRatio W L hL _

/-- On a space carrying a prime divisor and an invertible rational function other than `1`, the
hypothesis `hscale` of Stacks 0EPX fails for the trivial ratio family. -/
theorem not_hscale_trivialRatio (W : PrimeDivisor B S hS X)
    (f : (rationalFunctions B S hS hX)ˣ) (hf : (f : rationalFunctions B S hS hX) ≠ 1) :
    ¬ ∀ (L : Modules.{u, u} B S hS X hX)
      (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L) (f : (rationalFunctions B S hS hX)ˣ),
      ∃ t : MeromorphicSection.{u, u} B S hS X hX L, ∀ W : PrimeDivisor B S hS X,
        (D.trivialRatio.ratio L hL W (D.trivialRatio.sect L hL) :
            W.genericTotalFractionRing B S hS hX hdec) =
          E.emb W (f : rationalFunctions B S hS hX) *
            (D.trivialRatio.ratio L hL W t : W.genericTotalFractionRing B S hS hX hdec) :=
  fun hscale => hf (D.eq_one_of_hscale_trivialRatio W hscale f)

/-- On a space with a nonzero Picard class, the claim of Stacks 0EPX — the hypothesis `htriv` —
fails for the trivial ratio family. -/
theorem not_htriv_trivialRatio (x : picardGroup (B := B) (S := S) (hS := hS) ⟨X, hX⟩)
    (hx : x ≠ 0) :
    ¬ ∀ (L : Modules.{u, u} B S hS X hX)
      (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
      (t : MeromorphicSection.{u, u} B S hS X hX L),
      (∀ W : PrimeDivisor B S hS X,
          orderOfVanishingSection.{u, u} B S hS hX hdec W L t
            (D.trivialRatio.ratio L hL W) = 0) →
        picardClass (B := B) ⟨X, hX⟩ L hL = 0 :=
  fun htriv => hx (D.eq_zero_of_htriv_trivialRatio htriv x)

end PicardDivisorData

end AlgebraicGeometry.Space

end
