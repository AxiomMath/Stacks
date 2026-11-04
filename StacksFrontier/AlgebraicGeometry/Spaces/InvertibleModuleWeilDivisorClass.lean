module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorMeromorphicSectionRatio
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleModuleWeilDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.WeilDivisorClassGroupCanonical

/-!
# The Weil divisor class of an invertible module

Let `X` be a locally Noetherian integral algebraic space over a scheme `S` and let `ℒ` be an
invertible `𝒪_X`-module. The *Weil divisor class associated to `ℒ`* is the image in `Cl(X)` of
the Weil divisor `div_ℒ(s)` of any nonzero meromorphic section `s` of `ℒ`; this is part (2) of
Stacks 0EPU. It is well defined because a nonzero meromorphic section exists and because two of
them have Weil divisors differing by a principal divisor, which is Stacks 0EPT.

## Main definitions

* `AlgebraicGeometry.Space.weilDivisorClassOfInvertible` is **Stacks 0EPU, part (2)**: the Weil
  divisor class of `ℒ` in the class group `Cl(X)` of Stacks 0ENR.

## Main results

* `AlgebraicGeometry.Space.exists_weilDivisorOfSection_eq_add_divRationalFunction`: **Stacks
  0EPT in `Div(X)`**: for nonzero meromorphic sections `s`, `s'` of `ℒ` there is `f ∈ R(X)^*`,
  the ratio `s / s'` at the generic point of every prime divisor, with
  `div_ℒ(s) = div_ℒ(s') + div(f)`, `div` being the principal Weil divisor of Stacks 0ENQ by which
  `Cl(X)` is formed.
* `AlgebraicGeometry.Space.weilDivisorClassOfInvertible_eq`: the class is the image of
  `div_ℒ(s)` for *every* nonzero meromorphic section `s`.
* `AlgebraicGeometry.Space.existsUnique_ratio_weilDivisorOfSection_eq_add_divRationalFunction`:
  **Stacks 0EPT**: for nonzero meromorphic sections `s`, `s'` of `ℒ` the ratio `f = s / s'` is
  the unique element of `R(X)^*` with `s = f · s'`, and `div_ℒ(s) = div_ℒ(s') + div(f)`.
* `AlgebraicGeometry.Space.exists_ne_zero_weilDivisorOfSection_meromorphicSectionTensor_eq_add`:
  **Stacks 0EPV**: the product `st` of nonzero meromorphic sections of `ℒ` and of `𝒩` is
  nonzero, `div_{ℒ⊗𝒩}(st) = div_ℒ(s) + div_𝒩(t)`, and the class of `ℒ ⊗ 𝒩` in `Cl(X)` is the
  sum of the classes of `ℒ` and of `𝒩`.

## Implementation notes

The definition evaluates at the regular meromorphic section of Stacks 0EPQ, which is nonzero
(`AlgebraicGeometry.Space.exists_meromorphicSection_ne_zero`); by
`AlgebraicGeometry.Space.weilDivisorClassOfInvertible_eq` that choice is invisible, and nothing
about it is assumed.

## References

* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EPU](https://stacks.math.columbia.edu/tag/0EPU)
* [Stacks Project, Tag 0EPV](https://stacks.math.columbia.edu/tag/0EPV)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
variable (hInt : IsIntegralSpace B S hS X)
variable (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

/-- The generic Henselian local ring of a prime divisor is a nontrivial Noetherian ring of Krull
dimension at most one. -/
private theorem nontrivial_isNoetherianRing_krullDimLE_genericHenselianLocalRing
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y)) :
    ∀ W : PrimeDivisor B S hS X,
      Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hInt.isDecentSpace) ∧
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hInt.isDecentSpace) ∧
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hInt.isDecentSpace) := fun W =>
  ⟨W.nontrivial_genericHenselianLocalRing B S hS hX hInt.isDecentSpace hInt hN,
    W.isNoetherianRing_genericHenselianLocalRing B S hS hX hInt.isDecentSpace hInt hN,
    W.krullDimLE_genericHenselianLocalRing B S hS hX hInt.isDecentSpace hInt hN⟩

/-- **Stacks 0EPT, as an identity in `Div(X)`.** For nonzero meromorphic sections `s`, `s'` of
an invertible `𝒪_X`-module on a locally Noetherian integral algebraic space there is an
invertible rational function `f`, the ratio `s / s'` read at the generic point of every prime
divisor (the canonical ratios `s / s_ξ` and `s' / s_ξ` of Stacks 0EPR differ by the image of
`f`), such that

`div_ℒ(s) = div_ℒ(s') + div(f)`

in `Div(X)`, `div(f)` being the principal Weil divisor of Stacks 0ENQ. -/
theorem exists_weilDivisorOfSection_eq_add_divRationalFunction
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (s s' : MeromorphicSection.{u, u} B S hS X hX L) (hs : s ≠ 0) (hs' : s' ≠ 0) :
    ∃ f : (rationalFunctions B S hS hX)ˣ,
      (∀ W : PrimeDivisor B S hS X,
        (canonicalLocalRatioFamily B S hS hX hInt.isDecentSpace L hL hInt hN W s :
            W.genericTotalFractionRing B S hS hX hInt.isDecentSpace) =
          (genericFractionEmbedding B S hS hX hInt.isDecentSpace hInt hN).emb W
              (f : rationalFunctions B S hS hX) *
            (canonicalLocalRatioFamily B S hS hX hInt.isDecentSpace L hL hInt hN W s' :
              W.genericTotalFractionRing B S hS hX hInt.isDecentSpace)) ∧
      weilDivisorOfSection B S hS hX hInt hN L hL s hs =
        weilDivisorOfSection B S hS hX hInt hN L hL s' hs' +
          divRationalFunction B S hS hX hInt hN f := by
  have hr := isRegularMeromorphicSection_of_ne_zero B S hS hX hInt hN L hL s hs
  have hr' := isRegularMeromorphicSection_of_ne_zero B S hS hX hInt hN L hL s' hs'
  obtain ⟨f, hf⟩ := exists_units_rationalFunctions_canonicalLocalRatio_eq_emb_mul B S hS hX
    hInt.isDecentSpace hInt hN L hL s s' hr hr'
  refine ⟨f, hf, Subtype.ext (funext fun W => ?_)⟩
  have h := nontrivial_isNoetherianRing_krullDimLE_genericHenselianLocalRing B S hS hX hInt hN
  have := fun W => (h W).1
  have := fun W => (h W).2.1
  have := fun W => (h W).2.2
  have := orderOfVanishingSection_eq_add_ord_of_ratio_eq B S hS hX hInt.isDecentSpace
    (genericFractionEmbedding B S hS hX hInt.isDecentSpace hInt hN) W L L s s'
    (canonicalLocalRatioFamily B S hS hX hInt.isDecentSpace L hL hInt hN W)
    (canonicalLocalRatioFamily B S hS hX hInt.isDecentSpace L hL hInt hN W) f (hf W)
  exact this

/-- **Stacks 0EPU, part (2).** The *Weil divisor class associated to an invertible
`𝒪_X`-module* `ℒ` on a locally Noetherian integral algebraic space: the image of `div_ℒ(s)` in
the Weil divisor class group `Cl(X)` of Stacks 0ENR, for `s` a nonzero meromorphic section of
`ℒ`.

It is evaluated at the nonzero meromorphic section of
`AlgebraicGeometry.Space.exists_meromorphicSection_ne_zero`, and it is the image of `div_ℒ(s)`
for every nonzero `s` by `AlgebraicGeometry.Space.weilDivisorClassOfInvertible_eq`. -/
@[stacks 0EPU "part (2): the Weil divisor class of ℒ, the image of div_ℒ(s) in the canonical \
Cl(X) of Stacks 0ENR for a nonzero meromorphic section s, which exists; independence of s is \
weilDivisorClassOfInvertible_eq"]
def weilDivisorClassOfInvertible
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L) :
    weilDivisorClassGroup B S hS hX hInt hN :=
  QuotientAddGroup.mk (weilDivisorOfSection B S hS hX hInt hN L hL
    (exists_meromorphicSection_ne_zero B S hS hX hInt hN L hL).choose
    (exists_meromorphicSection_ne_zero B S hS hX hInt hN L hL).choose_spec)

/-- **Stacks 0EPU, part (2), well-definedness.** The Weil divisor class of `ℒ` is the image of
`div_ℒ(s)` in `Cl(X)` for every nonzero meromorphic section `s` of `ℒ`: two nonzero meromorphic
sections have Weil divisors differing by the principal divisor `div(s / s')`, by Stacks 0EPT. -/
@[stacks 0EPU "part (2): well-definedness, the class of div_ℒ(s) in Cl(X) is the same for every \
nonzero meromorphic section s, by Stacks 0EPT"]
theorem weilDivisorClassOfInvertible_eq
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (s : MeromorphicSection.{u, u} B S hS X hX L) (hs : s ≠ 0) :
    weilDivisorClassOfInvertible B S hS hX hInt hN L hL =
      (QuotientAddGroup.mk (weilDivisorOfSection B S hS hX hInt hN L hL s hs) :
        weilDivisorClassGroup B S hS hX hInt hN) := by
  obtain ⟨f, -, hf⟩ := exists_weilDivisorOfSection_eq_add_divRationalFunction B S hS hX hInt hN
    L hL s (exists_meromorphicSection_ne_zero B S hS hX hInt hN L hL).choose hs
    (exists_meromorphicSection_ne_zero B S hS hX hInt hN L hL).choose_spec
  refine (weilDivisorClassGroup_mk_eq_mk_iff B S hS hX hInt hN _ _).2 ⟨f, ?_⟩
  rw [hf]
  abel

/-! ### Stacks 0EPT: the ratio `s / s'` and the identity in `Div(X)` -/

/-- **The comparison `R(X) → Γ(X, 𝒦_X)` does not depend on the presentation.** The meromorphic
function attached to a rational function by
`AlgebraicGeometry.Space.rationalToMeromorphic` is the same for any two presentations `P`, `P'`
of the schematic locus at the codimension-zero points: both have, at a generic chart for `P`
inside the domain of a representative, the coordinate of that representative there
(`AlgebraicGeometry.Space.meromorphicOfPartial_val`), and a meromorphic function is determined
by its value at a generic chart. -/
theorem rationalToMeromorphic_eq_of_presentation {X : AlgebraicSpaces B S hS}
    (P P' : CodimensionZeroPresentation B S hS X.1)
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (x : rationalFunctions B S hS X.2) :
    rationalToMeromorphic P hwa hfin x = rationalToMeromorphic P' hwa hfin x := by
  obtain ⟨f, rfl⟩ := Quotient.exists_rep x
  show meromorphicOfPartial P hwa hfin f = meromorphicOfPartial P' hwa hfin f
  obtain ⟨D⟩ := nonempty_genericChartIn P hfin f.dense_open_domain
  refine (D.isGenericChart.bijective_val_genericChart hwa hfin).injective ?_
  show (meromorphicOfPartial P hwa hfin f).val (op D.chart) =
    (meromorphicOfPartial P' hwa hfin f).val (op D.chart)
  rw [meromorphicOfPartial_val P hwa hfin f D.chart D.factor D.factor_comp,
    meromorphicOfPartial_val P' hwa hfin f D.chart D.factor D.factor_comp]

/-- **Stacks 0EPT.** Let `X` be a locally Noetherian integral algebraic space over `S`, let `ℒ`
be an invertible `𝒪_X`-module and let `s`, `s'` be nonzero meromorphic sections of `ℒ`. Then
`f = s / s'` is an element of `R(X)^*` and

`∑ ord_{Z,ℒ}(s) [Z] = ∑ ord_{Z,ℒ}(s') [Z] + div(f)`

as Weil divisors.

The ratio is stated as the source means it: `f` is **the** unit of `R(X)` with `s = f · s'`,
`f` being read in `Γ(X, 𝒦_X)` through the canonical comparison `R(X) → Γ(X, 𝒦_X)` of Stacks
0ENA (`AlgebraicGeometry.Space.rationalToMeromorphic`), for every presentation the comparison
is built from — it does not depend on it,
`AlgebraicGeometry.Space.rationalToMeromorphic_eq_of_presentation` — and `f` is unique with this
property. The two sums are `AlgebraicGeometry.Space.weilDivisorOfSection` (Stacks 0EPU, part (1)),
which are Weil divisors by Stacks 0EPS, proved there; `div(f)` is the principal Weil divisor
`AlgebraicGeometry.Space.divRationalFunction` of Stacks 0ENQ, a Weil divisor by Stacks 0ENN.
Nothing is assumed beyond the hypotheses of the source.

The ratio in `Γ(X, 𝒦_X)^*` is
`AlgebraicGeometry.Space.existsUnique_units_smul_eq_of_isRegularMeromorphicSection` (nonzero
sections being regular, `AlgebraicGeometry.Space.isRegularMeromorphicSection_of_ne_zero`); it
comes from a unit of `R(X)` because the comparison is bijective; and at the generic point of every
prime divisor the canonical ratio `s / s_ξ` of Stacks 0EPR is the image of `f` times `s' / s_ξ`,
so that the orders of vanishing add up
(`AlgebraicGeometry.Space.orderOfVanishingSection_eq_add_ord_of_ratio_eq`). -/
@[stacks 0EPT "both conclusions at the source's hypotheses: for nonzero meromorphic sections s, \
s' of an invertible module on a locally Noetherian integral X, f = s/s' is THE element of R(X)^* \
with s = f s' (f read in Γ(X, 𝒦_X) through the canonical comparison of Stacks 0ENA, for every \
presentation), and div_ℒ(s) = div_ℒ(s') + div(f) in Div(X), the sums being Weil divisors by \
Stacks 0EPS (proved) and div(f) the principal divisor of Stacks 0ENQ"]
theorem existsUnique_ratio_weilDivisorOfSection_eq_add_divRationalFunction
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (s s' : MeromorphicSection.{u, u} B S hS X hX L) (hs : s ≠ 0) (hs' : s' ≠ 0) :
    ∃! f : (rationalFunctions B S hS hX)ˣ,
      (∀ P : CodimensionZeroPresentation B S hS X,
        s = (id (rationalToMeromorphic (X := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) P
              (fun _ hz => (weaklyAssociatedPointsOfSpace_eq_setOf_localRingDimension_eq_zero
                B S hS ⟨X, hX⟩ hInt.hasEtaleLocalProperty_isReduced).subset hz)
              (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN)
              (f : rationalFunctions B S hS hX)) :
            ↥(RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf
              (meromorphicRingedSite B S hS X hX).O).obj))) • s') ∧
      weilDivisorOfSection B S hS hX hInt hN L hL s hs =
        weilDivisorOfSection B S hS hX hInt hN L hL s' hs' +
          divRationalFunction B S hS hX hInt hN f := by
  have hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS),
      localRingDimension B S hS z = 0 := fun _ hz =>
    (weaklyAssociatedPointsOfSpace_eq_setOf_localRingDimension_eq_zero B S hS ⟨X, hX⟩
      hInt.hasEtaleLocalProperty_isReduced).subset hz
  have hfin := hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN
  obtain ⟨P₀⟩ := exists_codimensionZeroPresentation B S hS hX hfin
    (IsDecentWithFinitelyManyComponents.hasMonomorphicCodimensionZeroPoints B S hS
      ⟨hInt.isDecentSpace, hInt.finite_irreducibleComponents⟩)
  have hr := isRegularMeromorphicSection_of_ne_zero B S hS hX hInt hN L hL s hs
  have hr' := isRegularMeromorphicSection_of_ne_zero B S hS hX hInt hN L hL s' hs'
  -- the ratio `g = s / s'` in `Γ(X, 𝒦_X)^*`
  obtain ⟨g, hg, hguniq⟩ := existsUnique_units_smul_eq_of_isRegularMeromorphicSection B S hS hX
    hInt hN L hL s s' hr hr'
  -- `g` and `g⁻¹` come from `R(X)`, which makes `f` a unit of `R(X)`
  obtain ⟨x, hx⟩ := surjective_rationalToMeromorphic
    (X := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) P₀ hwa hfin g.val
  obtain ⟨y, hy⟩ := surjective_rationalToMeromorphic
    (X := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) P₀ hwa hfin g⁻¹.val
  have hxy : x * y = 1 := injective_rationalToMeromorphic
    (X := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) P₀ hwa hfin (by
      rw [rationalToMeromorphic_mul, rationalToMeromorphic_one, hx, hy]
      exact g.mul_inv)
  refine ⟨⟨x, y, hxy, (mul_comm y x).trans hxy⟩, ⟨fun P => ?_, ?_⟩, ?_⟩
  · -- `f · s' = s`, through the comparison built from any presentation
    show s = (id (rationalToMeromorphic (X := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) P hwa hfin x) :
      ↥(RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS X hX).O).obj))) • s'
    rw [rationalToMeromorphic_eq_of_presentation B S hS P P₀ hwa hfin x, hx]
    exact hg
  · -- the identity in `Div(X)`, coefficientwise
    refine Subtype.ext (funext fun W => ?_)
    have h := nontrivial_isNoetherianRing_krullDimLE_genericHenselianLocalRing B S hS hX hInt hN
    have := fun W => (h W).1
    have := fun W => (h W).2.1
    have := fun W => (h W).2.2
    -- the image of `g` at the generic point of `W` is the image of `f` under Stacks 0ENK
    have hemb : W.genericStalkMeromorphicToGeneric B S hS hX hInt.isDecentSpace hInt hN
          (chartMeromorphicRingedSitePullbackHom B S hS
            (W.genericStalkMorphism B S hS hX hInt.isDecentSpace)
            (W.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hInt.isDecentSpace)
            (W.genericStalkChartDiagram B S hS hX hInt.isDecentSpace)
            (meromorphicFunctionEval B S hS hX
              (W.genericEtaleChart B S hS hX hInt.isDecentSpace) g)) =
        (genericFractionEmbedding B S hS hX hInt.isDecentSpace hInt hN).emb W x := by
      refine Eq.trans ?_ (genericStalkMeromorphicToGeneric_rationalToMeromorphic_eq_emb B S hS
        hX hInt.isDecentSpace hInt hN P₀ hwa hfin x W)
      exact congrArg (fun m : ↥(RingCat.sectionsSubring
          ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj)) =>
        W.genericStalkMeromorphicToGeneric B S hS hX hInt.isDecentSpace hInt hN
          (chartMeromorphicRingedSitePullbackHom B S hS
            (W.genericStalkMorphism B S hS hX hInt.isDecentSpace)
            (W.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hInt.isDecentSpace)
            (W.genericStalkChartDiagram B S hS hX hInt.isDecentSpace)
            (meromorphicFunctionEval B S hS hX
              (W.genericEtaleChart B S hS hX hInt.isDecentSpace) m))) hx.symm
    -- so `s / s_ξ = f · (s' / s_ξ)` at the generic point of `W`
    have hratio : (canonicalLocalRatioFamily B S hS hX hInt.isDecentSpace L hL hInt hN W s :
          W.genericTotalFractionRing B S hS hX hInt.isDecentSpace) =
        (genericFractionEmbedding B S hS hX hInt.isDecentSpace hInt hN).emb W x *
          (canonicalLocalRatioFamily B S hS hX hInt.isDecentSpace L hL hInt hN W s' :
            W.genericTotalFractionRing B S hS hX hInt.isDecentSpace) := by
      rw [show (canonicalLocalRatioFamily B S hS hX hInt.isDecentSpace L hL hInt hN W s :
            W.genericTotalFractionRing B S hS hX hInt.isDecentSpace) =
          W.canonicalGenericRatio B S hS hX hInt.isDecentSpace L hL hInt hN s from
        W.coe_canonicalLocalRatio B S hS hX hInt.isDecentSpace L hL hInt hN s hr,
        show (canonicalLocalRatioFamily B S hS hX hInt.isDecentSpace L hL hInt hN W s' :
            W.genericTotalFractionRing B S hS hX hInt.isDecentSpace) =
          W.canonicalGenericRatio B S hS hX hInt.isDecentSpace L hL hInt hN s' from
        W.coe_canonicalLocalRatio B S hS hX hInt.isDecentSpace L hL hInt hN s' hr', ← hemb]
      refine W.canonicalGenericRatio_smul_of_eval B S hS hX hInt.isDecentSpace L hL hInt hN s s'
        _ ?_
      rw [hg]
      exact units_smul_eval B S hS hX L g s' (W.genericEtaleChart B S hS hX hInt.isDecentSpace)
    exact orderOfVanishingSection_eq_add_ord_of_ratio_eq B S hS hX hInt.isDecentSpace
      (genericFractionEmbedding B S hS hX hInt.isDecentSpace hInt hN) W L L s s'
      (canonicalLocalRatioFamily B S hS hX hInt.isDecentSpace L hL hInt hN W)
      (canonicalLocalRatioFamily B S hS hX hInt.isDecentSpace L hL hInt hN W)
      ⟨x, y, hxy, (mul_comm y x).trans hxy⟩ hratio
  · -- uniqueness: a second such unit has the same image `g` in `Γ(X, 𝒦_X)^*`
    rintro f' ⟨hf', -⟩
    have hu := hguniq (Units.map (rationalToMeromorphicRingHom
      (X := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) P₀ hwa hfin).toMonoidHom f') (hf' P₀)
    refine Units.ext (injective_rationalToMeromorphic
      (X := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) P₀ hwa hfin ?_)
    exact (congrArg Units.val hu).trans hx.symm

/-! ### Stacks 0EPV: the divisor of a product of sections -/

/-- **Stacks 0EPV.** Let `X` be a locally Noetherian integral algebraic space over `S`, let `ℒ`,
`𝒩` be invertible `𝒪_X`-modules and let `s`, resp. `t`, be a nonzero meromorphic section of `ℒ`,
resp. `𝒩`. Then `st` is a nonzero meromorphic section of `ℒ ⊗_{𝒪_X} 𝒩` and

`div_{ℒ⊗𝒩}(st) = div_ℒ(s) + div_𝒩(t)`

in `Div(X)`. In particular the Weil divisor class of `ℒ ⊗_{𝒪_X} 𝒩` is the sum of the Weil divisor
classes of `ℒ` and of `𝒩`, in the class group `Cl(X)` of Stacks 0ENR.

The product `st` is `AlgebraicGeometry.Space.meromorphicSectionTensor`, the global product of
the two sections (the chartwise product of their representatives over every affine chart), whose
hypotheses (a) and (b) of Stacks 0EN6 are `X`'s own; the divisors are
`AlgebraicGeometry.Space.weilDivisorOfSection` (Stacks 0EPU, part (1)). The product is regular,
hence nonzero; at the generic point of every prime divisor its coefficient is a unit times the
product of the coefficients of `s` and of `t`, so the orders of vanishing add up. The class
statement is then the definition of the class
(`AlgebraicGeometry.Space.weilDivisorClassOfInvertible`, Stacks 0EPU, part (2)) evaluated at `s`,
`t` and `st`, by `AlgebraicGeometry.Space.weilDivisorClassOfInvertible_eq`, and additivity of the
quotient map `Div(X) → Cl(X)`. -/
@[stacks 0EPV "the whole lemma at the source's hypotheses: for nonzero meromorphic sections s of \
ℒ and t of 𝒩 on a locally Noetherian integral X, the product st (meromorphicSectionTensor) is a \
nonzero meromorphic section of ℒ ⊗ 𝒩, div_{ℒ⊗𝒩}(st) = div_ℒ(s) + div_𝒩(t) in Div(X), and the \
Weil divisor class of ℒ ⊗ 𝒩 in the canonical Cl(X) of Stacks 0ENR is the sum of the classes of \
ℒ and 𝒩 (Stacks 0EPU part (2) evaluated at s, t and st)"]
theorem exists_ne_zero_weilDivisorOfSection_meromorphicSectionTensor_eq_add
    (L N : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (hNinv : IsInvertibleModule (B := B) ⟨X, hX⟩ N)
    (s : MeromorphicSection.{u, u} B S hS X hX L) (t : MeromorphicSection.{u, u} B S hS X hX N)
    (hs : s ≠ 0) (ht : t ≠ 0) :
    ∃ hst : meromorphicSectionTensor B S hS hX
        (fun _ hz => (weaklyAssociatedPointsOfSpace_eq_setOf_localRingDimension_eq_zero
          B S hS ⟨X, hX⟩ hInt.hasEtaleLocalProperty_isReduced).subset hz)
        (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN) L N s t
        (isQuasicoherentOnSite_of_isInvertibleModule (⟨X, hX⟩ : AlgebraicSpaces B S hS) L hL)
        (isQuasicoherentOnSite_of_isInvertibleModule (⟨X, hX⟩ : AlgebraicSpaces B S hS) N
          hNinv) ≠ 0,
      weilDivisorOfSection B S hS hX hInt hN (picardTensorModule B S hS hX L N)
          (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv) _ hst =
        weilDivisorOfSection B S hS hX hInt hN L hL s hs +
          weilDivisorOfSection B S hS hX hInt hN N hNinv t ht ∧
      weilDivisorClassOfInvertible B S hS hX hInt hN (picardTensorModule B S hS hX L N)
          (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv) =
        weilDivisorClassOfInvertible B S hS hX hInt hN L hL +
          weilDivisorClassOfInvertible B S hS hX hInt hN N hNinv := by
  have hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS),
      localRingDimension B S hS z = 0 := fun _ hz =>
    (weaklyAssociatedPointsOfSpace_eq_setOf_localRingDimension_eq_zero B S hS ⟨X, hX⟩
      hInt.hasEtaleLocalProperty_isReduced).subset hz
  have hcomp := hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN
  have hLqc := isQuasicoherentOnSite_of_isInvertibleModule
    (⟨X, hX⟩ : AlgebraicSpaces B S hS) L hL
  have hNqc := isQuasicoherentOnSite_of_isInvertibleModule
    (⟨X, hX⟩ : AlgebraicSpaces B S hS) N hNinv
  have hsr := isRegularMeromorphicSection_of_ne_zero B S hS hX hInt hN L hL s hs
  have htr := isRegularMeromorphicSection_of_ne_zero B S hS hX hInt hN N hNinv t ht
  -- `st` is regular, hence nonzero
  have hstreg := isRegularMeromorphicSection_meromorphicSectionTensor B S hS hX hwa hcomp L N
    s t hLqc hNqc hL hNinv hsr htr
  have hst := ne_zero_of_isRegularMeromorphicSection B S hS hX hInt hN _ _ hstreg
  -- the identity in `Div(X)`, coefficientwise
  have hdiv : weilDivisorOfSection B S hS hX hInt hN (picardTensorModule B S hS hX L N)
        (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv) _ hst =
      weilDivisorOfSection B S hS hX hInt hN L hL s hs +
        weilDivisorOfSection B S hS hX hInt hN N hNinv t ht := by
    refine Subtype.ext (funext fun Z => ?_)
    have h := nontrivial_isNoetherianRing_krullDimLE_genericHenselianLocalRing B S hS hX hInt hN
    have := fun W => (h W).1
    have := fun W => (h W).2.1
    have := fun W => (h W).2.2
    obtain ⟨w, hw, hwc⟩ := Z.exists_isUnit_genericStalkCoefficient_meromorphicSectionTensor
      B S hS hX hInt.isDecentSpace hInt hN hwa hcomp L N hL hNinv hLqc hNqc s t hsr htr
    exact
      Z.orderOfVanishingSection_canonicalLocalRatio_eq_add_of_genericStalkCoefficient_eq_unit_mul
        B S hS hX hInt.isDecentSpace L N hL hNinv hInt hN s t _ hsr htr hstreg w hw hwc
  refine ⟨hst, hdiv, ?_⟩
  -- the classes, evaluated at `st`, `s` and `t`
  rw [weilDivisorClassOfInvertible_eq B S hS hX hInt hN _ _ _ hst,
    weilDivisorClassOfInvertible_eq B S hS hX hInt hN L hL s hs,
    weilDivisorClassOfInvertible_eq B S hS hX hInt hN N hNinv t ht, hdiv]
  exact QuotientAddGroup.mk_add _ _ _

end AlgebraicGeometry.Space

end
