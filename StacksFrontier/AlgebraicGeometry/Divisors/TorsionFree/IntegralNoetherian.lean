module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.TorsionFree
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.Depth
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Embedded
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.MinimalSupport
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Serre
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TorsionFree
public import StacksFrontier.AlgebraicGeometry.Reflexive.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.AffineOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation

/-!
# Torsion-free coherent modules on locally Noetherian integral schemes

Let `X` be a locally Noetherian integral scheme and let `F` be a coherent `𝒪_X`-module with
nonempty support. This file proves that four properties of `F` agree: torsion freeness; the
generic point of `X` being the only associated point of `F`; support at the generic point
together with Serre's condition `(S₁)`; and support at the generic point together with the
absence of embedded associated points.

The argument is affine-local. On an affine open `U` meeting the support, the ring `Γ(X, U)` is a
Noetherian domain and the module `Γ(F, U)` is finite and nonzero, so torsion freeness of
`Γ(F, U)` is the same as the zero ideal being its only associated prime. Translating associated
primes of sections into associated points of `F` and reading the zero ideal of `Γ(X, U)` as the
generic point of `X` turns that into the second property. The remaining two properties are
obtained from the comparison between embedded associated points and Serre's condition `(S₁)`.

## Main results

* `Stacks.AlgebraicGeometry.ReflexiveModules.isTorsionFree_tfae`: the four equivalent
  characterizations.

## Implementation notes

The unique generic point of `X` is `genericPoint X`. Nonzeroness of `F` is expressed by nonempty
support, equivalently by the existence of a nonzero stalk. "The generic point is the only
associated point" is phrased as equality of the set of associated points with the singleton
`{genericPoint X}`.

The statement supplies quasi-coherence of `F` inside the statement by a `letI`, since it is a
consequence of coherence rather than an instance that synthesis finds on its own.

## References

* [Stacks Project, Tag 0AUV](https://stacks.math.columbia.edu/tag/0AUV)
* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
* [Stacks Project, Tag 02OK](https://stacks.math.columbia.edu/tag/02OK)
* [Stacks Project, Tag 0341](https://stacks.math.columbia.edu/tag/0341)
* [Stacks Project, Tag 0346](https://stacks.math.columbia.edu/tag/0346)
* [Stacks Project, Tag 056I](https://stacks.math.columbia.edu/tag/056I)
* [Stacks Project, Tag 05AD](https://stacks.math.columbia.edu/tag/05AD)
* [Stacks Project, Tag 05AH](https://stacks.math.columbia.edu/tag/05AH)
* [Stacks Project, Tag 05AK](https://stacks.math.columbia.edu/tag/05AK)
* [Stacks Project, Tag 0AXS](https://stacks.math.columbia.edu/tag/0AXS)
* [Stacks Project, Tag 0AXY](https://stacks.math.columbia.edu/tag/0AXY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

namespace Stacks.AlgebraicGeometry.ReflexiveModules

/-- Over a Noetherian domain a nonzero finite module is torsion free exactly when the zero ideal
is its only associated prime. This is the projection of Stacks tag 0AUV onto the two properties
used below. -/
private theorem module_isTorsionFree_iff_associatedPrimes_eq_bot
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] :
    Module.IsTorsionFree R M ↔ associatedPrimes R M = {⊥} :=
  have h := isTorsionFree_iff_finiteFreeEmbedding_iff_associatedPrimes_iff_propertyS1
    (R := R) (M := M)
  h.1.trans h.2.1

/-- A point of the support of a quasi-coherent module which lies in an affine open `U` forces the
module of sections over `U` to be nonzero. -/
private theorem nontrivial_sections_of_mem_supp {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] (U : X.affineOpens) (x : X) (hx : x ∈ U.1)
    (hxs : x ∈ SheafOfModules.supp F) :
    Nontrivial Γ(F, U.1) := by
  have hp := (AlgebraicGeometry.Scheme.Modules.mem_support_sections_iff_mem_supp F U x hx).mpr hxs
  rw [Module.mem_support_iff] at hp
  by_contra hM
  have : Subsingleton Γ(F, U.1) := not_nontrivial_iff_subsingleton.mp hM
  exact not_nontrivial_iff_subsingleton.mpr inferInstance hp

private theorem genericPoint_mem_of_nonempty {X : Scheme.{u}} [IsIntegral X] (U : X.Opens)
    [Nonempty U] : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

private theorem primeIdealOf_genericPoint_eq_bot {X : Scheme.{u}} [IsIntegral X] {U : X.Opens}
    (hU : IsAffineOpen U) [Nonempty U] :
    hU.primeIdealOf ⟨genericPoint X, genericPoint_mem_of_nonempty U⟩ = ⊥ := by
  have : IsDomain Γ(X, U) := IsIntegral.component_integral U
  rw [hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]

/-- A point of an affine open is an associated point of a quasi-coherent module exactly when its
prime ideal is an associated prime of the sections over the open. -/
private theorem mem_associatedPoints_iff_primeIdealOf_mem_associatedPrimes {X : Scheme.{u}}
    [IsLocallyNoetherian X] (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    x ∈ Stacks.Divisors.associatedPoints F ↔
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal ∈ associatedPrimes Γ(X, U) Γ(F, U) := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  rw [Stacks.Divisors.mem_associatedPoints_iff, ← isAssociatedPrimeStacks_iff_mem_associatedPrimes,
    AlgebraicGeometry.isAssociatedPrime_sections_iff_isAssociatedPoint_of_isLocallyNoetherian F U hU
      hx]

/-- On an affine open meeting the support of a torsion-free coherent module, the zero ideal is the
only associated prime of the sections. -/
private theorem associatedPrimes_sections_eq_bot {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsIntegral X] (F : X.Modules) [F.IsCoherent] (hTF : IsTorsionFree F) {U : X.Opens}
    (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) (hxs : x ∈ SheafOfModules.supp F) :
    associatedPrimes Γ(X, U) Γ(F, U) = {⊥} := by
  have hqc : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have hft : F.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  have : IsDomain Γ(X, U) := IsIntegral.component_integral U
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : Module.Finite Γ(X, U) Γ(F, U) := AlgebraicGeometry.moduleFinite_sections_on_affine F U hU
  have : Nontrivial Γ(F, U) := nontrivial_sections_of_mem_supp F ⟨U, hU⟩ x hx hxs
  exact module_isTorsionFree_iff_associatedPrimes_eq_bot.mp
    ((AlgebraicGeometry.isTorsionFree_iff_forall_isAffineOpen F).mp hTF U hU)

private theorem genericPoint_mem_associatedPoints_of_isTorsionFree {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsIntegral X] (F : X.Modules) [F.IsCoherent]
    (hF : (SheafOfModules.supp F).Nonempty) (hTF : IsTorsionFree F) :
    genericPoint X ∈ Stacks.Divisors.associatedPoints F := by
  have hqc : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  obtain ⟨x, hx⟩ := hF
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by trivial)
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have hass := associatedPrimes_sections_eq_bot F hTF hW x hxW hx
  rw [mem_associatedPoints_iff_primeIdealOf_mem_associatedPrimes F hW
    (genericPoint_mem_of_nonempty W), primeIdealOf_genericPoint_eq_bot hW]
  simp [hass]

private theorem eq_genericPoint_of_mem_associatedPoints_of_isTorsionFree {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsIntegral X] (F : X.Modules) [F.IsCoherent]
    (hTF : IsTorsionFree F) {x : X} (hx : x ∈ Stacks.Divisors.associatedPoints F) :
    x = genericPoint X := by
  have hqc : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by trivial)
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have hass := associatedPrimes_sections_eq_bot F hTF hW x hxW
    (AlgebraicGeometry.associatedPoints_subset_support F hx)
  have hp := (mem_associatedPoints_iff_primeIdealOf_mem_associatedPrimes F hW hxW).mp hx
  have hpx : hW.primeIdealOf ⟨x, hxW⟩ =
      hW.primeIdealOf ⟨genericPoint X, genericPoint_mem_of_nonempty W⟩ := by
    rw [primeIdealOf_genericPoint_eq_bot hW]
    apply PrimeSpectrum.ext
    simpa [hass] using hp
  simpa only [hW.fromSpec_primeIdealOf] using congrArg hW.fromSpec hpx

/-- If the generic point is the only associated point, every associated prime of the sections over
a nonempty affine open is the zero ideal. -/
private theorem eq_bot_of_mem_associatedPrimes_sections {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsIntegral X] (F : X.Modules) [F.IsCoherent]
    (hass : Stacks.Divisors.associatedPoints F = {genericPoint X}) {U : X.Opens}
    (hU : IsAffineOpen U) [Nonempty U] {p : Ideal Γ(X, U)}
    (hp : p ∈ associatedPrimes Γ(X, U) Γ(F, U)) : p = ⊥ := by
  have hqc : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let p' : PrimeSpectrum Γ(X, U) := ⟨p, (AssociatedPrimes.mem_iff.mp hp).isPrime⟩
  let y : U := hU.isoSpec.inv p'
  have hyPrime : hU.primeIdealOf y = p' := by
    change (hU.isoSpec.inv ≫ hU.isoSpec.hom) p' = p'
    rw [hU.isoSpec.inv_hom_id]
    rfl
  have hyAssoc : y.1 ∈ Stacks.Divisors.associatedPoints F :=
    (mem_associatedPoints_iff_primeIdealOf_mem_associatedPrimes F hU y.2).mpr (by
      change (hU.primeIdealOf y).asIdeal ∈ _
      rw [hyPrime]
      exact hp)
  rw [hass] at hyAssoc
  have hp' : p' = ⊥ := by
    rw [← hyPrime, show y = ⟨genericPoint X, genericPoint_mem_of_nonempty U⟩ from
      Subtype.ext (Set.mem_singleton_iff.mp hyAssoc), primeIdealOf_genericPoint_eq_bot hU]
  simpa [p'] using congrArg PrimeSpectrum.asIdeal hp'

/-- If the generic point is the only associated point, the sections over a nonempty affine open
are torsion free. -/
private theorem isTorsionFree_sections_of_associatedPoints_eq {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsIntegral X] (F : X.Modules) [F.IsCoherent]
    (hass : Stacks.Divisors.associatedPoints F = {genericPoint X}) {U : X.Opens}
    (hU : IsAffineOpen U) [Nonempty U] : Module.IsTorsionFree Γ(X, U) Γ(F, U) := by
  have hqc : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have hft : F.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  have : IsDomain Γ(X, U) := IsIntegral.component_integral U
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : Module.Finite Γ(X, U) Γ(F, U) := AlgebraicGeometry.moduleFinite_sections_on_affine F U hU
  have hηU := genericPoint_mem_of_nonempty U
  have hηassoc : genericPoint X ∈ Stacks.Divisors.associatedPoints F := by simp [hass]
  have : Nontrivial Γ(F, U) := nontrivial_sections_of_mem_supp F ⟨U, hU⟩ (genericPoint X) hηU
    (AlgebraicGeometry.associatedPoints_subset_support F hηassoc)
  have hη := (mem_associatedPoints_iff_primeIdealOf_mem_associatedPrimes F hU hηU).mp hηassoc
  rw [primeIdealOf_genericPoint_eq_bot hU] at hη
  exact module_isTorsionFree_iff_associatedPrimes_eq_bot.mpr <|
    Set.eq_singleton_iff_unique_mem.mpr
      ⟨hη, fun _ hp => eq_bot_of_mem_associatedPrimes_sections F hass hU hp⟩

/-- For a coherent module with nonempty support on a locally Noetherian integral scheme, torsion
freeness is the same as the generic point being the only associated point. -/
private theorem isTorsionFree_iff_associatedPoints_eq_genericPoint {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsIntegral X] (F : X.Modules) [F.IsCoherent]
    (hF : (SheafOfModules.supp F).Nonempty) :
    IsTorsionFree F ↔ Stacks.Divisors.associatedPoints F = {genericPoint X} := by
  have hqc : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  refine ⟨fun hTF => Set.eq_singleton_iff_unique_mem.mpr
    ⟨genericPoint_mem_associatedPoints_of_isTorsionFree F hF hTF,
      fun _ hx => eq_genericPoint_of_mem_associatedPoints_of_isTorsionFree F hTF hx⟩,
    fun hass => (AlgebraicGeometry.isTorsionFree_iff_forall_isAffineOpen F).2 fun U hU => ?_⟩
  by_cases hne : Nonempty U
  · exact isTorsionFree_sections_of_associatedPoints_eq F hass hU
  · obtain rfl : U = ⊥ := by
      ext x
      exact ⟨fun hx => (hne ⟨⟨x, hx⟩⟩).elim, by simp⟩
    refine ⟨fun r hr s t hst => ?_⟩
    apply TopCat.Presheaf.IsSheaf.section_ext (U := Opposite.op (⊥ : X.Opens)) F.isSheaf
    exact fun x hx => (hne ⟨⟨x, hx⟩⟩).elim

private theorem eq_genericPoint_of_specializes {X : Scheme.{u}} [IsIntegral X] {y : X}
    (h : y ⤳ genericPoint X) : y = genericPoint X :=
  (h.antisymm (genericPoint_specializes y)).eq

private theorem hasNoEmbeddedAssociatedPoints_of_associatedPoints_eq {X : Scheme.{u}}
    [IsIntegral X] (F : X.Modules)
    (h : Stacks.Divisors.associatedPoints F = {genericPoint X}) :
    genericPoint X ∈ SheafOfModules.supp F ∧
      AlgebraicGeometry.HasNoEmbeddedAssociatedPoints F := by
  refine ⟨AlgebraicGeometry.associatedPoints_subset_support F (by simp [h]), ?_⟩
  rintro x ⟨hxassoc, y, hyassoc, -, hyne⟩
  have hxη : x = genericPoint X := by
    simpa [h] using (Stacks.Divisors.mem_associatedPoints_iff F x).mpr hxassoc
  have hyη : y = genericPoint X := by
    simpa [h] using (Stacks.Divisors.mem_associatedPoints_iff F y).mpr hyassoc
  exact hyne (hyη.trans hxη.symm)

private theorem associatedPoints_eq_of_hasNoEmbeddedAssociatedPoints {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent]
    (hηsupp : genericPoint X ∈ SheafOfModules.supp F)
    (hnoEmbedded : AlgebraicGeometry.HasNoEmbeddedAssociatedPoints F) :
    Stacks.Divisors.associatedPoints F = {genericPoint X} := by
  have hηassoc : genericPoint X ∈ Stacks.Divisors.associatedPoints F :=
    AlgebraicGeometry.mem_associatedPoints_of_mem_supp_of_specialization X F
      (genericPoint X) hηsupp fun _ _ hspec => eq_genericPoint_of_specializes hspec
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨hηassoc, fun x hxassoc => ?_⟩
  by_contra hxeq
  exact hnoEmbedded x ⟨hxassoc, genericPoint X, hηassoc, genericPoint_specializes x,
    fun heq => hxeq heq.symm⟩

/-- **Stacks Project, Tag 0AXY.** The characterizations of a nonzero torsion-free coherent
module on a locally Noetherian integral scheme: torsion freeness, uniqueness of the generic
point as associated point, Serre's condition `(S₁)` with support at the generic point, and
absence of embedded associated points with support at the generic point. -/
@[stacks 0AXY, ega "IV 5.10.14" "integral case, (i)"]
theorem isTorsionFree_tfae
    (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
    (F : X.Modules) [F.IsCoherent] (hF : (SheafOfModules.supp F).Nonempty) :
    letI : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
    List.TFAE [
      IsTorsionFree F,
      Stacks.Divisors.associatedPoints F = {genericPoint X},
      genericPoint X ∈ SheafOfModules.supp F ∧ AlgebraicGeometry.SheafHasPropertySk X F 1,
      genericPoint X ∈ SheafOfModules.supp F ∧
        AlgebraicGeometry.HasNoEmbeddedAssociatedPoints F] := by
  have hqc : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  tfae_have 1 ↔ 2 := isTorsionFree_iff_associatedPoints_eq_genericPoint F hF
  tfae_have 2 ↔ 4 := ⟨hasNoEmbeddedAssociatedPoints_of_associatedPoints_eq F,
    fun h => associatedPoints_eq_of_hasNoEmbeddedAssociatedPoints F h.1 h.2⟩
  tfae_have 3 ↔ 4 := and_congr Iff.rfl
    (AlgebraicGeometry.hasNoEmbeddedAssociatedPoints_iff_hasPropertySk_one X F).symm
  tfae_finish

end Stacks.AlgebraicGeometry.ReflexiveModules

end
