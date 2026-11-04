module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.RegularImmersionGysinComposition
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.RankLoci
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalSheaf
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.Implications
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.ConormalLocallyFree
public import StacksFrontier.Homology.DerivedCategory.ZeroDifferentialCoproduct
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero

/-!
# The object `⋀^r 𝒩 [-r]` of a Koszul-regular closed immersion

Let `i : X ⟶ Y` be a Koszul-regular closed immersion of schemes, `𝒞_{X/Y}` its conormal sheaf
and `𝒩 = 𝓗om_{𝒪_X}(𝒞_{X/Y}, 𝒪_X)` its normal sheaf (Morphisms, Section 29.31,
[Stacks, Tag 01R1]). The normal sheaf is finite locally free, so its rank `r` is a locally
constant function on `X`. [Stacks, Tag 0BR0] identifies `a(𝒪_Y)` with `⋀^r 𝒩 [-r]`.

Since `r` is only locally constant, the shift `[-r]` varies from one open and closed piece of `X`
to the next. `X` is the disjoint union of the open and closed loci `X_n = {r = n}`, and
`⋀^r 𝒩 [-r]` is the complex with zero differential whose degree-`n` term is `⋀ⁿ𝒩` on `X_n`,
extended by zero to `X`: on each `X_n` it restricts to `⋀ⁿ𝒩[-n]`.

## Main definitions

* `Stacks.Duality.KoszulRegular.normalRank`: the rank `r` of the normal sheaf, a locally
  constant function `X → ℕ`.
* `Stacks.Duality.KoszulRegular.normalRankLocus`: the open and closed locus `X_n` where `r = n`,
  for `n : ℤ` (empty for `n < 0`).
* `Stacks.Duality.KoszulRegular.normalExteriorTerm`: `⋀ⁿ𝒩` on `X_n`, extended by zero.
* `Stacks.Duality.KoszulRegular.normalExteriorComplex`: the complex `⋀^r 𝒩 [-r]`, with zero
  differential.

## Main results

* `Stacks.Duality.KoszulRegular.isFiniteLocallyFree_normalSheaf`: the normal sheaf of a
  Koszul-regular immersion is finite locally free.

## References

* [Stacks Project, Tag 0BR0](https://stacks.math.columbia.edu/tag/0BR0)
* [Stacks Project, Tag 01R1](https://stacks.math.columbia.edu/tag/01R1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace ExtensionByZeroModules

universe u

namespace Stacks.Duality.KoszulRegular

open Stacks.AlgebraicGeometry.RegularIdealSheaf

variable {X Y : Scheme.{u}} (i : X ⟶ Y) [IsImmersion i]

/-- **The normal sheaf of a Koszul-regular immersion is finite locally free.** -/
theorem isFiniteLocallyFree_normalSheaf (hi : IsKoszulRegularImmersion i) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.ringCatSheaf) (Stacks.Divisors.normalSheaf i) :=
  Stacks.Chow.isFiniteLocallyFree_dualSheaf_of_schemeOpens _
    (isFiniteLocallyFree_conormalSheaf_of_isQuasiRegularImmersion i
      (isQuasiRegularImmersion_of_isH1RegularImmersion i
        (isH1RegularImmersion_of_isKoszulRegularImmersion i hi)))

/-- **The rank `r` of the normal sheaf** of a Koszul-regular immersion, as a locally constant
function `X → ℕ`. -/
def normalRank (hi : IsKoszulRegularImmersion i) : LocallyConstant X ℕ :=
  @Stacks.Chow.moduleRank X (Stacks.Divisors.normalSheaf i) (isFiniteLocallyFree_normalSheaf i hi)

/-- **The locus `X_n` where the normal sheaf has rank `n`**, an open subset of `X` (it is also
closed, being a fibre of a locally constant function). For `n < 0` it is empty. -/
def normalRankLocus (hi : IsKoszulRegularImmersion i) (n : ℤ) : X.Opens :=
  ⟨{x | ((normalRank i hi x : ℕ) : ℤ) = n},
    ((normalRank i hi).isLocallyConstant.comp (fun m : ℕ => (m : ℤ))).isOpen_fiber n⟩

/-- A point `x` lies in `normalRankLocus i hi n` if and only if the rank of the normal sheaf at
`x` is `n`. -/
theorem mem_normalRankLocus (hi : IsKoszulRegularImmersion i) {n : ℤ} {x : X} :
    x ∈ normalRankLocus i hi n ↔ ((normalRank i hi x : ℕ) : ℤ) = n :=
  Iff.rfl

/-- **The degree-`n` term of `⋀^r 𝒩 [-r]`**: the `n`-th exterior power of the normal sheaf over
`𝒪_X`, restricted to the locus `X_n` where the rank is `n` and extended by zero. -/
def normalExteriorTerm (hi : IsKoszulRegularImmersion i) (n : ℤ) :
    SheafOfModules.{u} (structureSheaf X.toRingedSpace.sheaf) :=
  (jShriek (normalRankLocus i hi n) (structureSheaf X.toRingedSpace.sheaf)).obj
    ((jStar (normalRankLocus i hi n) (structureSheaf X.toRingedSpace.sheaf)).obj
      (Scheme.Modules.exteriorPower (Stacks.Divisors.normalSheaf i) n))

/-- **The complex `⋀^r 𝒩 [-r]`**, with zero differential: its degree-`n` term is `⋀ⁿ𝒩` on the
locus where the rank `r` of `𝒩` is `n`, extended by zero. On each such locus it is `⋀ⁿ𝒩[-n]`. -/
def normalExteriorComplex (hi : IsKoszulRegularImmersion i) :
    CochainComplex (SheafOfModules.{u} (structureSheaf X.toRingedSpace.sheaf)) ℤ :=
  CochainComplex.zeroDifferentialComplex (normalExteriorTerm i hi)

end Stacks.Duality.KoszulRegular
