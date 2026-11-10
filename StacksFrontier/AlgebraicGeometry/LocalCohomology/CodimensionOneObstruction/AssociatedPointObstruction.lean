module

public import Mathlib.Algebra.Module.Torsion.Basic
public import StacksCore.Algebra.Module.FinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Coherence
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.AssociatedPointTransfer
public import
StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.AssociatedTorsionSections
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.ClosureStalkHeight
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.TorsionNakayama

/-!
# The codimension-one obstruction at an associated point

Let `X` be a locally Noetherian scheme, `U` an open subscheme with complement `Z`, and `𝓕` an
`𝒪_U`-module. If `𝓕` has an associated point `x` and the reduced closure `X'` of `{x}` in `X` has
a point `z` in `Z` at which `dim 𝒪_{X', z} ≤ 1`, then the direct image of `𝓕` along `U → X` is
**not** coherent.

This is the first paragraph of [Stacks, Tag 0AWC]. It generalizes
`not_isCoherent_pushforward_restrict_of_modStalk_ne_zero`, the case where `X` is integral, the
module is the restriction of a module on `X`, and the associated point is the generic point of `X`
itself, so that `X' = X` and the hypothesis is `dim 𝒪_{X, z} ≤ 1`.

## Main results

* `not_moduleFinite_sections_of_isAssociatedPoint`, in the namespace
  `Stacks.AlgebraicGeometry.CodimensionOneObstruction`: on an affine chart `V₀` containing both
  `x` and `z`, the sections of `F` over an open `S ≤ V₀` containing `x` and avoiding `z` are not a
  finite `Γ(X, V₀)`-module.
* `not_isCoherent_pushforward_restrict_of_height_quotient_le_one`, in the same namespace: the
  non-coherence for a module of the form `F|_U`, with the codimension hypothesis in its
  ring-theoretic form on a chart.
* `not_isCoherent_pushforward_restrict_of_isAssociatedPoint`, in the same namespace: the same
  statement with the codimension hypothesis as [Stacks, Tag 0AWC] writes it,
  `dim 𝒪_{\overline{\{x\}}, z} ≤ 1`.
* `not_isCoherent_pushforward_of_isAssociatedPoint`, in the same namespace: the first paragraph of
  the cited remark for an arbitrary `𝒪_U`-module.

## References

* [Stacks Project, Tag 0AWC](https://stacks.math.columbia.edu/tag/0AWC)
* [Stacks Project, Tag 0BK1](https://stacks.math.columbia.edu/tag/0BK1)
* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.SheafOfModules.SheafHomStalk
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.AlgebraicGeometry.CodimensionOneObstruction

variable {X : Scheme.{u}}

/-- **The sections of `F` near an associated point are not finite over an affine chart.** Let `X`
be locally Noetherian, `V₀` an affine open, `F` quasi-coherent, `x` an associated point of `F` in
`V₀`, and `z` a point of `V₀` in the closure of `{x}` with `dim 𝒪_{\overline{\{x\}}, z} ≤ 1` —
written here as a height in `Γ(X, V₀) ⧸ 𝔭`. Then for every open `S ≤ V₀` containing `x` and
avoiding `z`, the sections `Γ(F, S)` are not a finite `Γ(X, V₀)`-module. -/
theorem not_moduleFinite_sections_of_isAssociatedPoint [IsLocallyNoetherian X]
    {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀) (F : X.Modules) [F.IsQuasicoherent]
    {x z : X} (hx : x ∈ V₀) (hz : z ∈ V₀) (hxz : x ⤳ z)
    (hdim : ((hV₀.primeIdealOf ⟨z, hz⟩).asIdeal.map
        (Ideal.Quotient.mk (hV₀.primeIdealOf ⟨x, hx⟩).asIdeal)).height ≤ 1)
    (hass : Stacks.Divisors.IsAssociatedPoint F x)
    {S : X.Opens} (hSV : S ≤ V₀) (hxS : x ∈ S) (hzS : z ∉ S) :
    ¬ (letI := moduleOfLE F hSV; Module.Finite Γ(X, V₀) Γ(F, S)) := by
  intro hfin
  let := moduleOfLE F hSV
  have hnR : IsNoetherianRing Γ(X, V₀) := IsLocallyNoetherian.component_noetherian ⟨V₀, hV₀⟩
  set p := (hV₀.primeIdealOf ⟨x, hx⟩).asIdeal
  set q := (hV₀.primeIdealOf ⟨z, hz⟩).asIdeal
  have hpq : p ≤ q := primeIdealOf_le_primeIdealOf_of_specializes hV₀ hx hz hxz
  have hxz' : x ≠ z := fun h => hzS (h ▸ hxS)
  have hpnq : p ≠ q := fun h ↦ hxz' (inseparable_iff_specializes_and.mpr
    ⟨hxz, specializes_of_primeIdealOf_le hV₀ hx hz (le_of_eq h.symm)⟩).eq
  obtain ⟨s, hsq, hsp⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hpq hpnq)
  obtain ⟨m, hmgerm, hmkill⟩ :=
    exists_section_smul_eq_zero_of_isAssociatedPoint hV₀ F hx hass hSV hxS
  have hkey : ∀ g : Γ(X, V₀), g ∉ q → X.presheaf.map (homOfLE hSV).op g • m ≠ 0 := by
    intro g hgq hzero
    have h1 := germ_mem_maximalIdeal_of_smul_eq_zero F hxS hmgerm hzero
    rw [TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hSV) x hxS g] at h1
    exact hgq (hpq ((mem_primeIdealOf_iff_germ_mem_maximalIdeal hV₀ hx g).mpr h1))
  set Λ : Submodule Γ(X, V₀) Γ(F, S) := Submodule.torsionBySet Γ(X, V₀) Γ(F, S) (p : Set Γ(X, V₀))
    with hΛdef
  have hmemΛ : ∀ v : Γ(F, S),
      v ∈ Λ ↔ ∀ a ∈ p, X.presheaf.map (homOfLE hSV).op a • v = 0 := by
    intro v
    rw [hΛdef, Submodule.mem_torsionBySet_iff]
    exact ⟨fun h a ha => h ⟨a, ha⟩, fun h a => h a.1 a.2⟩
  have hmΛ : m ∈ Λ := (hmemΛ m).mpr hmkill
  have hdiv : ∀ w ∈ Λ, ∃ w' ∈ Λ, ∃ g : Γ(X, V₀), g ∉ q ∧ s • w' = g • w := by
    intro w hw
    obtain ⟨w', g, hgq, hw', he⟩ := exists_section_smul_eq_smul_of_notMem_primeIdealOf
      hV₀ F hx hz hxz hdim hSV hzS ((hmemΛ w).mp hw) hsp
    exact ⟨w', (hmemΛ w').mpr hw', g, hgq, he⟩
  obtain ⟨g, hgq, hg0⟩ := exists_notMem_smul_eq_zero_of_mem Λ hsq hdiv hmΛ
  exact hkey g hgq hg0

/-- **The direct image of the restriction of `F` to `U` is not coherent**, with the codimension
hypothesis in its ring-theoretic form on an affine chart `V₀` containing `z`. Such a chart
contains `x` as well, because `z` lies in the closure of `{x}`. -/
theorem not_isCoherent_pushforward_restrict_of_height_quotient_le_one [IsLocallyNoetherian X]
    {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀) (F : X.Modules) [F.IsQuasicoherent]
    {x z : X} (hz : z ∈ V₀) (hxz : x ⤳ z)
    (hdim : ((hV₀.primeIdealOf ⟨z, hz⟩).asIdeal.map
        (Ideal.Quotient.mk (hV₀.primeIdealOf ⟨x, hxz.mem_open V₀.isOpen hz⟩).asIdeal)).height ≤ 1)
    (hass : Stacks.Divisors.IsAssociatedPoint F x)
    {U : X.Opens} (hxU : x ∈ U) (hzU : z ∉ U) :
    ¬ ((Scheme.Modules.pushforward U.ι).obj (F.restrict U.ι)).IsCoherent := by
  intro hcoh
  have hx : x ∈ V₀ := hxz.mem_open V₀.isOpen hz
  let := moduleOfLE F (inf_le_right : U ⊓ V₀ ≤ V₀)
  have hfin : Module.Finite Γ(X, V₀)
      Γ((Scheme.Modules.pushforward U.ι).obj (F.restrict U.ι), V₀) :=
    AlgebraicGeometry.moduleFinite_sections _ ⟨V₀, hV₀⟩
  exact not_moduleFinite_sections_of_isAssociatedPoint hV₀ F hx hz hxz hdim hass
    (inf_le_right : U ⊓ V₀ ≤ V₀) ⟨hxU, hx⟩ (fun h => hzU h.1)
    (Module.Finite.of_surjective (pushforwardRestrictSectionsHom F U V₀)
      (pushforwardRestrictSectionsHom_surjective F U V₀))

/-- **First paragraph of [Stacks, Tag 0AWC], for the restriction of a quasi-coherent module on
the ambient scheme.** Let `X` be a locally Noetherian scheme, `U` an open subscheme with
complement `Z`, and `F` a quasi-coherent `𝒪_X`-module. Let `x` be an associated point of `F`
lying in `U`, let `X'` be the reduced closed subscheme supported on the closure of `{x}`, and let
`z'` be a point of `X'` whose image lies in `Z` and at which `dim 𝒪_{X', z'} ≤ 1`. Then the
direct image along `U → X` of `F|_U` is not coherent.

`X'` is integral with generic point `x` by
`AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure` and
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure`, so a
point of `X'` whose image avoids `U` is exactly a point `z ∈ Z ∩ \overline{\{x\}}` of the cited
remark, and `𝒪_{X', z'}` is its `𝒪_{\overline{\{x\}}, z}`. -/
@[ega "IV 5.10.10" "Clause (ii) for closed Z",
  ega "IV 5.11.1" "a) ⇒ c), for Z closed",
  ega "IV 7.8.3" "(ix), partial"]
theorem not_isCoherent_pushforward_restrict_of_isAssociatedPoint [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] {x : X}
    (hass : Stacks.Divisors.IsAssociatedPoint F x) {U : X.Opens} (hxU : x ∈ U)
    {I : X.IdealSheafData}
    (hI : I = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)))
    (z' : I.subscheme) (hzU : I.subschemeι z' ∉ U)
    (hdim : ringKrullDim (I.subscheme.presheaf.stalk z') ≤ 1) :
    ¬ ((Scheme.Modules.pushforward U.ι).obj (F.restrict U.ι)).IsCoherent := by
  have hsupp : (I.support : Set X) = (Closeds.closure ({x} : Set X) : Set X) := by
    rw [hI]
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hmem : I.subschemeι z' ∈ (Closeds.closure ({x} : Set X) : Set X) := by
    have h1 : I.subschemeι z' ∈ Set.range I.subschemeι := ⟨z', rfl⟩
    rw [I.range_subschemeι] at h1
    exact hsupp ▸ h1
  have hxz : x ⤳ I.subschemeι z' := specializes_iff_mem_closure.mpr hmem
  obtain ⟨V₀, hV₀, hz, -⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
    (U := (⊤ : X.Opens)) (x := I.subschemeι z') trivial
  have hx : x ∈ V₀ := hxz.mem_open V₀.isOpen hz
  rw [ringKrullDim_stalk_vanishingIdeal_closure hV₀ hx hI z' hz] at hdim
  exact not_isCoherent_pushforward_restrict_of_height_quotient_le_one hV₀ F hz hxz
    (by exact_mod_cast hdim) hass hxU hzU

/-- **First paragraph of [Stacks, Tag 0AWC].** Let `X` be a locally Noetherian scheme, `U` an open
subscheme with complement `Z`, and `𝓕` an `𝒪_U`-module. Let `x` be a point of `U` associated to
`𝓕`, let `X'` be the reduced closed subscheme of `X` supported on the closure of `{x}`, and let
`z'` be a point of `X'` whose image lies in `Z` and at which `dim 𝒪_{X', z'} ≤ 1`. Then the direct
image of `𝓕` along `U → X` is not coherent.

`X'` is integral with generic point `x` by
`AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure` and
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure`, so a
point of `X'` whose image avoids `U` is exactly a point `z ∈ Z ∩ \overline{\{x\}}` of the cited
remark, and `𝒪_{X', z'}` is its `𝒪_{\overline{\{x\}}, z}`.

The remark assumes `𝓕` coherent; no hypothesis on `𝓕` is needed here. -/
@[stacks 0AWC "first paragraph",
  ega "IV 5.10.10" "Clause (ii) for closed Z",
  ega "IV 5.11.1" "a) ⇒ c), for Z closed",
  ega "IV 5.11.4" "more general",
  ega "IV 7.8.3" "(ix), partial"]
theorem not_isCoherent_pushforward_of_isAssociatedPoint [IsLocallyNoetherian X]
    {U : X.Opens} (𝓕 : U.toScheme.Modules) {x : X} (hxU : x ∈ U)
    (hass : Stacks.Divisors.IsAssociatedPoint 𝓕 ⟨x, hxU⟩)
    {I : X.IdealSheafData}
    (hI : I = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)))
    (z' : I.subscheme) (hzU : I.subschemeι z' ∉ U)
    (hdim : ringKrullDim (I.subscheme.presheaf.stalk z') ≤ 1) :
    ¬ ((Scheme.Modules.pushforward U.ι).obj 𝓕).IsCoherent := by
  intro hcoh
  have := isQuasicoherent_of_isCoherent ((Scheme.Modules.pushforward U.ι).obj 𝓕)
  let e : ((Scheme.Modules.pushforward U.ι).obj 𝓕).restrict U.ι ≅ 𝓕 :=
    (Scheme.Modules.restrictFunctorAdjCounitIso U.ι).app 𝓕
  exact not_isCoherent_pushforward_restrict_of_isAssociatedPoint _
    ((isAssociatedPoint_restrict_iff U.ι _ ⟨x, hxU⟩).mp ((isAssociatedPoint_congr e _).mpr hass))
    hxU hI z' hzU hdim
    (CoherentDevissage.isCoherent_of_iso ((Scheme.Modules.pushforward U.ι).mapIso e))

end Stacks.AlgebraicGeometry.CodimensionOneObstruction

end
