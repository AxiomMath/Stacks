module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AssociatedPointPrime.Divisors
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.EtaleLocus
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.QuasiFiniteGorenstein
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafSections
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeRegular

/-!
# The different is an effective Cartier divisor cutting out the relative dualizing module

Let `f : Y ⟶ X` be a flat locally quasi-finite morphism of locally Noetherian schemes with
relative dualizing module `ω_{Y/X}` and trace element `τ_{Y/X}`, and let `R ⊆ Y` be the closed
subscheme defined by the different `𝔇_f`.  If `ω_{Y/X}` is invertible then `R` is the zero
scheme of `τ_{Y/X}`, and if moreover `f` is étale at the associated points of `Y` then `R` is an
effective Cartier divisor and `𝒪_Y(R) ≅ ω_{Y/X}` by a unique isomorphism carrying the canonical
section `1_R` to `τ_{Y/X}`.

## Main results

* `Stacks.Discriminant.differentIdealSheaf_eq_zeroScheme`: `R` is the zero scheme of the trace
  element, viewed as a global section of the invertible module `ω_{Y/X}`.
* `Stacks.Discriminant.isEffectiveCartierDivisor_differentIdealSheaf`: `R` is an effective
  Cartier divisor.
* `Stacks.Discriminant.existsUnique_invertibleSheafIso_differentIdealSheaf`: the isomorphism
  `𝒪_Y(R) ≅ ω_{Y/X}` sending `1_R` to `τ_{Y/X}`, and its uniqueness.

## Implementation notes

That `R` is the zero scheme of `τ_{Y/X}` is the invertible-module computation of
[Stacks, Tag 0BW6] read on each affine chart: the ideal of sections of the different over an
affine open `V` is the annihilator of `Coker(τ_{Y/X})` there, hence the annihilator of
`Γ(ω_{Y/X}, V)` modulo the line through the restricted trace element, and for an invertible
module that annihilator is the image of evaluation at the trace element
(`Stacks.Discriminant.range_eval_eq_annihilator_quotient_span`) — which is exactly the ideal
`AlgebraicGeometry.zeroScheme` is built from.  Invertibility of the sections over an affine open
is `Stacks.Discriminant.module_invertible_sections`.

Effectivity is the affine-local criterion [Stacks, Tag 01WS] in the form
`Stacks.Divisors.isEffectiveCartierDivisor_of_forall_mem_support`: local principality of `R`
is [Stacks, Tag 0C17 (1)], and the local generator is a nonzerodivisor because in a Noetherian
ring the zerodivisors are the union of the associated primes
(`biUnion_associatedPrimes_eq_compl_nonZeroDivisors`), the associated primes of `Γ(Y, V)` are
the associated points of `Y` lying in `V`
(`Stacks.AlgebraicGeometry.AssociatedPointPrime.associatedPrimes_eq_image_associatedPoints`), and
the generator vanishes at a point exactly when that point lies in the support of the different,
which by [Stacks, Tag 0BW9] is the non-étale locus.

The identification of `𝒪_Y(R)` with `ω_{Y/X}` is then [Stacks, Tag 01X0]: effectivity of the
zero scheme of a section of an invertible module is equivalent to regularity of that section
(Tag 02OR), and a regular section trivializes `𝒪_Y(Z(s))`.

## References

* [Stacks Project, Tag 0BWA](https://stacks.math.columbia.edu/tag/0BWA)
* [Stacks Project, Tag 0BW6](https://stacks.math.columbia.edu/tag/0BW6)
* [Stacks Project, Tag 0BW9](https://stacks.math.columbia.edu/tag/0BW9)
* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Tag 0C16](https://stacks.math.columbia.edu/tag/0C16)
* [Stacks Project, Tag 0C17](https://stacks.math.columbia.edu/tag/0C17)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open scoped AlgebraicGeometry

universe u

namespace Stacks.Discriminant

variable {X Y : Scheme.{u}} {f : Y ⟶ X}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat f] [LocallyQuasiFinite f]

variable (ω : RelativeDualizingModuleData f) (τ : RelativeTraceSection ω)
  [hinv : Stacks.SheafOfModules.IsInvertible Y.presheaf
    (structureSheafRing Y.toRingedSpace).property ω.sheaf]

omit [Flat f] in
/-- Invertibility of the relative dualizing module, in the spelling the zero-scheme construction
of [Stacks, Tag 02OQ] is stated for.  The two realizations of Tag 01CS are bridged by
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`. -/
theorem isInvertible_sheaf_algebraicGeometry :
    AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj
      Y.ringCatSheaf.property ω.sheaf :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ ω.sheaf).mp hinv

attribute [local instance] isInvertible_sheaf_algebraicGeometry

/-- On an affine open the ideal of the different is the ideal of the zero scheme of the trace
element: both are the image of the evaluation of the `Γ(Y, V)`-linear functionals on
`Γ(ω_{Y/X}, V)` at the restricted trace element. -/
theorem differentIdealSheaf_ideal_eq_zeroScheme_ideal (V : Y.affineOpens) :
    (differentIdealSheaf ω τ).ideal V =
      (AlgebraicGeometry.zeroScheme Y ω.sheaf τ.sect).ideal V := by
  have hI := module_invertible_sections ω V
  set t : Γ(ω.sheaf, V.1) :=
    (ω.sheaf.presheaf.map (homOfLE (show V.1 ≤ ⊤ from le_top)).op).hom τ.sect
  have ht : (traceHom ω τ).app V.1 (1 : Γ(Y, V.1)) = t := traceMorphism_app_one ω τ V.1
  rw [differentIdealSheaf_ideal ω τ V, different_sections_eq_annihilator ω τ V,
    AlgebraicGeometry.zeroScheme_ideal, ← (cokernelSectionsEquiv ω τ V).annihilator_eq, ht]
  have hset : {a : Γ(Y, V.1) | ∃ φ : Γ(ω.sheaf, V.1) →ₗ[Γ(Y, V.1)] Γ(Y, V.1), a = φ t} =
      (Module.annihilator Γ(Y, V.1)
        (Γ(ω.sheaf, V.1) ⧸ Submodule.span Γ(Y, V.1) {t}) : Set Γ(Y, V.1)) := by
    rw [← range_eval_eq_annihilator_quotient_span t]
    exact Set.ext fun a => ⟨fun ⟨φ, hφ⟩ => ⟨φ, hφ.symm⟩, fun ⟨φ, hφ⟩ => ⟨φ, hφ.symm⟩⟩
  rw [hset]
  exact (Ideal.span_eq _).symm

/-- **The closed subscheme cut out by the different is the zero scheme of the trace element**
when `ω_{Y/X}` is invertible.  Quasi-coherent ideal sheaves agree as soon as their ideals on the
affine opens agree. -/
theorem differentIdealSheaf_eq_zeroScheme :
    differentIdealSheaf ω τ = AlgebraicGeometry.zeroScheme Y ω.sheaf τ.sect :=
  Scheme.IdealSheafData.ext (funext fun V => differentIdealSheaf_ideal_eq_zeroScheme_ideal ω τ V)

variable [LocallyOfFiniteType f]

omit hinv in
/-- A local generator of the different on an affine open is a nonzerodivisor as soon as `f` is
étale at the associated points of `Y`.

In a Noetherian ring the zerodivisors are the union of the associated primes, the associated
primes of `Γ(Y, V)` are the associated points of `Y` lying in `V`, and a point at which `f` is
étale lies outside the support of the different by [Stacks, Tag 0BW9], hence outside the zero
locus of the generator. -/
theorem mem_nonZeroDivisors_of_differentIdealSheaf_ideal_eq_span
    (hét : ∀ y ∈ Stacks.Divisors.schemeAssociatedPoints Y, EtaleAt f y)
    (V : Y.affineOpens) (h : Γ(Y, V.1))
    (hh : (differentIdealSheaf ω τ).ideal V = Ideal.span {h}) :
    h ∈ nonZeroDivisors Γ(Y, V.1) := by
  have : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  have : (unitModule Y).IsQuasicoherent := isQuasicoherent_unitModule Y
  by_contra hc
  have hmem : h ∈ (↑(nonZeroDivisors Γ(Y, V.1)) : Set Γ(Y, V.1))ᶜ := hc
  rw [← biUnion_associatedPrimes_eq_compl_nonZeroDivisors Γ(Y, V.1)] at hmem
  simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at hmem
  obtain ⟨p, hp, hhp⟩ := hmem
  have hp' : p ∈ associatedPrimes Γ(Y, V.1) Γ(unitModule Y, V.1) := hp
  rw [Stacks.AlgebraicGeometry.AssociatedPointPrime.associatedPrimes_eq_image_associatedPoints
    (unitModule Y) V.2] at hp'
  obtain ⟨y, hy, rfl⟩ := hp'
  have hyass : (y : Y) ∈ Stacks.Divisors.schemeAssociatedPoints Y := hy
  have hsupp : (y : Y) ∉ (differentIdealSheaf ω τ).support := by
    rw [mem_support_differentIdealSheaf_iff_not_etaleAt ω τ]
    exact fun hne => hne (hét _ hyass)
  rw [mem_support_iff_primeIdealOf (differentIdealSheaf ω τ) V (y : Y) y.2, hh] at hsupp
  refine hsupp ((PrimeSpectrum.mem_zeroLocus _ _).mpr ?_)
  exact SetLike.coe_subset_coe.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hhp))

/-- **[Stacks, Tag 0BWA (3)], effectivity.**  Let `f : Y ⟶ X` be a flat quasi-finite morphism of
locally Noetherian schemes with relative dualizing module `ω_{Y/X}` and trace element `τ_{Y/X}`.
If `ω_{Y/X}` is invertible and `f` is étale at the associated points of `Y`, then the closed
subscheme `R ⊆ Y` defined by the different `𝔇_f` is an effective Cartier divisor.

By [Stacks, Tag 0C17 (1)] the different is locally principal, and the local generator is a
nonzerodivisor because it does not vanish at any associated point of `Y`. -/
@[stacks 0BWA "part (3), R is an effective Cartier divisor"]
theorem isEffectiveCartierDivisor_differentIdealSheaf
    (hét : ∀ y ∈ Stacks.Divisors.schemeAssociatedPoints Y, EtaleAt f y) :
    Stacks.Divisors.IsEffectiveCartierDivisor (differentIdealSheaf ω τ) := by
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_forall_mem_support _ fun x _ => ?_
  obtain ⟨V, hxV, hprinc⟩ := isLocallyPrincipal_differentIdealSheaf ω τ x
  obtain ⟨h, hh⟩ := hprinc.principal
  exact ⟨V, h, hxV, hh,
    mem_nonZeroDivisors_of_differentIdealSheaf_ideal_eq_span ω τ hét V h hh⟩

/-- **[Stacks, Tag 0BWA (3)], the isomorphism `𝒪_Y(R) = ω_{Y/X}`.**  Under the hypotheses of
[Stacks, Tag 0BWA (3)] there is exactly one isomorphism `𝒪_Y(R) ≅ ω_{Y/X}` carrying the
canonical section `1_R` of `𝒪_Y(R)` to the trace element `τ_{Y/X}`.

The subscheme `R` is the zero scheme of `τ_{Y/X}`, so its effectivity makes `τ_{Y/X}` a regular
section of `ω_{Y/X}` ([Stacks, Tag 02OR]), and [Stacks, Tag 01X0] trivializes `𝒪_Y(Z(τ_{Y/X})))`
along it. -/
@[stacks 0BWA "part (3), O_Y(R) = omega_{Y/X}"]
theorem existsUnique_invertibleSheafIso_differentIdealSheaf
    (hét : ∀ y ∈ Stacks.Divisors.schemeAssociatedPoints Y, EtaleAt f y) :
    ∃! e : Stacks.Divisors.invertibleSheaf' (differentIdealSheaf ω τ) ≅ ω.sheaf,
      Scheme.Modules.Hom.app e.hom ⊤
        ((Stacks.Divisors.canonicalSection' (differentIdealSheaf ω τ)).eval (op ⊤)) = τ.sect := by
  set s : ω.sheaf.sections := Stacks.SheafOfModules.sectionsOfTopOfRingSheaf ω.sheaf τ.sect
  have hs : s.eval (op ⊤) = τ.sect :=
    Stacks.SheafOfModules.sectionsOfTopOfRingSheaf_eval_top ω.sheaf τ.sect
  have heq : differentIdealSheaf ω τ = AlgebraicGeometry.zeroScheme Y ω.sheaf (s.eval (op ⊤)) := by
    rw [hs]
    exact differentIdealSheaf_eq_zeroScheme ω τ
  have hreg : AlgebraicGeometry.IsRegularSection Y.sheaf.obj Y.ringCatSheaf.property s :=
    (AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection
      Y ω.sheaf s).mp (heq ▸ isEffectiveCartierDivisor_differentIdealSheaf ω τ hét)
  have H := AlgebraicGeometry.existsUnique_invertibleSheafIso_zeroScheme Y ω.sheaf s hreg
  rw [hs] at H
  rw [heq, hs]
  exact H

end Stacks.Discriminant

end
