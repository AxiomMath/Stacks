module

public import StacksFrontier.AlgebraicGeometry.Chow.StalkLocalSituation.ComponentDimension
public import StacksFrontier.AlgebraicGeometry.Chow.StalkLocalSituation.KrullDimension
public import StacksFrontier.AlgebraicGeometry.Chow.StalkLocalSituation.Localization
public import StacksFrontier.AlgebraicGeometry.Chow.StalkLocalSituation.NonZeroDivisors
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.SchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.SupportsOfModules
public import StacksFrontier.AlgebraicGeometry.Reflexive.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization

/-!
# The local situation at a point of delta-dimension `k`

The length formula of [Stacks, Tag 02QH]
(`Ideal.length_fractionalProduct_quotient_sub_length_denominator_quotient`) is stated for a
one-dimensional Noetherian local ring `R`, a finite `R`-module `M` with full support and no
embedded associated primes, and two nonzerodivisors `a, b : R`. This file instantiates all of
that data at `R = 𝒪_{X, ξ}` and `M = ℱ_ξ`, for `ξ` a point of delta-dimension `k` on a scheme
`X` of delta-dimension at most `k + 1` over the base of a Chow situation, and `a / b` a local
ratio for a meromorphic section on an affine open `V` containing `ξ`. That is the local
situation of the proof of [Stacks, Tag 02SW] part (4).

Of the nine hypotheses of the length formula, `CommRing`, `IsNoetherianRing` and `IsLocalRing`
are found at the stalk by instance search. The other six are assembled here.

## Main results

* `Stacks.Chow.StalkLocalSituation.hasNoEmbeddedAssociatedPrimes_stalk`: the stalk of a
  quasi-coherent module with no embedded associated points has no embedded associated primes
  over the local ring. This is the stalk-level form of the bridge of
  `Stacks.AlgebraicGeometry.AssociatedPointPrime.Embedded`, which stops at an affine open.
* `Stacks.Chow.StalkLocalSituation.support_stalk_eq_univ`: the stalk of a quasi-coherent module
  of full support has full support over the local ring.
* `Stacks.Chow.StalkLocalSituation.lengthFormula_hypotheses`: the six conditions together,
  with the geometric hypotheses of [Stacks, Tag 02SW] as input.

The Krull dimension of the stalk is
`Stacks.Chow.StalkLocalSituation.ringKrullDim_stalk_eq_one_of_mem_isNowhereDense`, in
`StacksFrontier.AlgebraicGeometry.Chow.StalkLocalSituation.KrullDimension`. The two
nonzerodivisor conditions are not restated here: the germ of a nonzerodivisor section on an
affine open is a nonzerodivisor in the local ring by
`Stacks.Divisors.germ_mem_nonZeroDivisors`, which takes its hypothesis in the `IsRegular`
spelling and is converted with Mathlib's `isRegular_iff_mem_nonZeroDivisors`. The germs of a
local ratio of a regular meromorphic section are handled in
`StacksFrontier.AlgebraicGeometry.Chow.StalkLocalSituation.NonZeroDivisors`.

## Implementation notes

All three stalk statements are quantified over an **arbitrary** affine open `V` and an
arbitrary point `ξ ∈ V`: none of them produces its own chart, so a consumer that has obtained a
chart together with a ratio `a, b : Γ(X, V)` from elsewhere can use it directly. The two whose
conclusion does not mention `V` — the associated-primes bridge and the support statement — hold
for every such `V`, and the chart is used only to run the proof.

Each of the three is the corresponding statement over `Γ(X, V)` — the already proved
`AlgebraicGeometry.hasNoEmbeddedAssociatedPrimes_sections`,
`AlgebraicGeometry.Scheme.Modules.fromSpec_preimage_supp`, and the hypothesis itself for a
nonzerodivisor — transported along a localization: `𝒪_{X, ξ}` is the localization of `Γ(X, V)`
at the prime of `ξ` (`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`) and `ℱ_ξ` is the
corresponding localization of `Γ(ℱ, V)`
(`Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ`). The transport statements are in
`StacksFrontier.AlgebraicGeometry.Chow.StalkLocalSituation.Localization`.

The `𝒪_X`-module `ℱ` is taken at the spelling `AlgebraicGeometry.Scheme.Modules`, which is the
spelling in which the stalk carries a module structure over the local ring
(`AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf`, an instance) and in which the
affine-open statements above are available. The `Γ(X, V)`-module structure on the stalk and the
germ map as a `Γ(X, V)`-linear map are not instances and are introduced in the proofs, as in
`StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization`.

## References

* [Stacks Project, Tag 02QH](https://stacks.math.columbia.edu/tag/02QH)
* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
* [Stacks Project, Tag 02OK](https://stacks.math.columbia.edu/tag/02OK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Topology TopologicalSpace

universe u

namespace Stacks.Chow.StalkLocalSituation

variable {X : Scheme.{u}}

/-! ### Embedded associated primes -/

/-- **The absence of embedded associated points, read at a stalk.** For a quasi-coherent module
with no embedded associated points on a locally Noetherian scheme, the stalk at any point has no
embedded associated primes over the local ring at that point.

The affine open `V` is arbitrary and does not appear in the conclusion; it is where the
statement `AlgebraicGeometry.hasNoEmbeddedAssociatedPrimes_sections` over `Γ(X, V)` is read
before being localized at the prime of `x`. -/
theorem hasNoEmbeddedAssociatedPrimes_stalk [IsLocallyNoetherian X] (F : X.Modules)
    [F.IsQuasicoherent] (hF : HasNoEmbeddedAssociatedPoints F) {V : X.Opens}
    (hV : IsAffineOpen V) {x : X} (hx : x ∈ V) :
    HasNoEmbeddedAssociatedPrimes (X.presheaf.stalk x) (F.presheaf.stalk x) := by
  have hNoeth : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let : Algebra Γ(X, V) (X.presheaf.stalk x) := (X.presheaf.germ V x hx).hom.toAlgebra
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hx⟩
  let _ := Stacks.ModuleStalkSpecialization.sectionsStalkModule F hx
  have _ := Stacks.ModuleStalkSpecialization.isScalarTower_sectionsStalk F hx
  have _ := Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ F hV hx
  exact hasNoEmbeddedAssociatedPrimes_of_isLocalizedModule
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (Stacks.ModuleStalkSpecialization.germₗ F hx)
    (AlgebraicGeometry.hasNoEmbeddedAssociatedPrimes_sections F hF hV)

/-! ### Support -/

/-- **A quasi-coherent module of full support has stalks of full support.** The support of the
sections over an affine open is the preimage of the support of the sheaf
([Stacks, Tag 056H]), hence everything, and full support passes to a localization.

As for the associated primes, the affine open is arbitrary and absent from the conclusion. -/
theorem support_stalk_eq_univ (F : X.Modules) [F.IsQuasicoherent]
    (hSupp : SheafOfModules.supp F = Set.univ) {V : X.Opens} (hV : IsAffineOpen V) {x : X}
    (hx : x ∈ V) :
    Module.support (X.presheaf.stalk x) (F.presheaf.stalk x) = Set.univ := by
  have hsec : Module.support Γ(X, V) Γ(F, V) = Set.univ := by
    rw [← AlgebraicGeometry.Scheme.Modules.fromSpec_preimage_supp F ⟨V, hV⟩, hSupp]
    exact Set.preimage_univ
  let : Algebra Γ(X, V) (X.presheaf.stalk x) := (X.presheaf.germ V x hx).hom.toAlgebra
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hx⟩
  let _ := Stacks.ModuleStalkSpecialization.sectionsStalkModule F hx
  have _ := Stacks.ModuleStalkSpecialization.isScalarTower_sectionsStalk F hx
  have _ := Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ F hV hx
  exact support_eq_univ_of_isLocalizedModule
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (Stacks.ModuleStalkSpecialization.germₗ F hx)
    hsec

/-! ### The package -/

/-- **The hypotheses of the length formula of [Stacks, Tag 02QH], at a point of
delta-dimension `k`.** Let `X` be locally of finite type over the base of a Chow situation with
`dim_δ(X) ≤ k + 1`, let `ℱ` be coherent with full support and no embedded associated points,
let `T` be a closed nowhere dense subset of `X`, and let `ξ ∈ T` have `δ(ξ) = k`. Then for an
arbitrary affine open `V` containing `ξ` and arbitrary nonzerodivisors `a, b : Γ(X, V)`:

* `ℱ_ξ` is a finite `𝒪_{X, ξ}`-module;
* `germ a` and `germ b` are nonzerodivisors in `𝒪_{X, ξ}`;
* `𝒪_{X, ξ}` has Krull dimension one;
* `ℱ_ξ` has no embedded associated primes over `𝒪_{X, ξ}`;
* `ℱ_ξ` has full support over `𝒪_{X, ξ}`;
* every minimal prime `q` of `𝒪_{X, ξ}` has `ringKrullDim (𝒪_{X, ξ} ⧸ q) = 1`, which is the
  component through `ξ` having coheight one there — not a hypothesis of the length formula
  itself, but what the right-hand side's sum over the minimal primes needs in order to be
  rewritten as an order of vanishing.

The remaining three hypotheses of the length formula — `CommRing`, `IsNoetherianRing` and
`IsLocalRing` for the local ring — are found by instance search, the second from the local
Noetherianity of `X` that `LocallyOfFiniteType f` supplies. Finiteness is included in the
conclusion rather than left to instance search because the module structure on the stalk is
itself not an instance in every spelling; the statement used is
`SheafOfModules.finite_stalk`. -/
theorem lengthFormula_hypotheses (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent] {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt))
    (hF : HasNoEmbeddedAssociatedPoints F)
    (hSupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).supp = Set.univ)
    {T : Set X} (hT : IsClosed T) (hT' : IsNowhereDense T)
    {V : X.Opens} (hV : IsAffineOpen V) {ξ : X} (hξV : ξ ∈ V) (hξT : ξ ∈ T)
    (hξ : relativeDimension C.dimensionFunction f ξ = k)
    {a b : Γ(X, V)} (ha : a ∈ nonZeroDivisors Γ(X, V)) (hb : b ∈ nonZeroDivisors Γ(X, V)) :
    Module.Finite (X.presheaf.stalk ξ) (F.presheaf.stalk ξ) ∧
      X.presheaf.germ V ξ hξV a ∈ nonZeroDivisors (X.presheaf.stalk ξ) ∧
      X.presheaf.germ V ξ hξV b ∈ nonZeroDivisors (X.presheaf.stalk ξ) ∧
      ringKrullDim (X.presheaf.stalk ξ) = 1 ∧
      HasNoEmbeddedAssociatedPrimes (X.presheaf.stalk ξ) (F.presheaf.stalk ξ) ∧
      Module.support (X.presheaf.stalk ξ) (F.presheaf.stalk ξ) = Set.univ ∧
      ∀ q ∈ minimalPrimes (X.presheaf.stalk ξ),
        ringKrullDim ((X.presheaf.stalk ξ) ⧸ q) = 1 := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have : F.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1
  have : F.IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType
  refine ⟨_root_.SheafOfModules.finite_stalk X.sheaf F ξ,
    Stacks.Divisors.germ_mem_nonZeroDivisors hV
      (isRegular_iff_mem_nonZeroDivisors.mpr ha) ξ hξV,
    Stacks.Divisors.germ_mem_nonZeroDivisors hV
      (isRegular_iff_mem_nonZeroDivisors.mpr hb) ξ hξV,
    ringKrullDim_stalk_eq_one_of_mem_isNowhereDense C f hdim hT hT' hξT hξ,
    hasNoEmbeddedAssociatedPrimes_stalk F hF hV hξV, support_stalk_eq_univ F hSupp hV hξV,
    fun _ hq => ringKrullDim_quotient_minimalPrime_stalk_eq_one C f hdim hT hT' hξT hξ hq⟩

end Stacks.Chow.StalkLocalSituation

end
