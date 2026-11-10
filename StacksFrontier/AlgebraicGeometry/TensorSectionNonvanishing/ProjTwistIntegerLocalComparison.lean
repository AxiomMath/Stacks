module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionComparison
public import StacksFrontier.AlgebraicGeometry.TensorSectionNonvanishing.ProjTwistLocalComparison

/-!
# The local comparison map on a standard open, for the integer-graded twisted global sections

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a graded ring, `X = Proj 𝒮`, let `ℱ` be an arbitrary sheaf of
`𝒪_X`-modules and let `M = ⨁_{n ∈ ℤ} Γ(X, ℱ(n))` be the **integer-graded** `S`-module of twisted
global sections of Tag 03GK. For `f ∈ 𝒮 d` homogeneous of positive degree, the sections of the
associated sheaf `M̃` over the standard open `D₊(f)` are the degree-zero fractions `x / f ^ n`
with `x` homogeneous of degree `n d`, and Tag 0B5I's comparison map sends such a fraction to the
section of `ℱ` obtained by restricting `x` to `D₊(f)` and dividing by the trivializing section
`f ^ n`.

This file builds that map, `Γ(D₊(f), M̃) → Γ(D₊(f), ℱ)`, proves it linear over `Γ(D₊(f), 𝒪)`,
proves the maps attached to two standard opens agree on the smaller one, and glues them into the
comparison morphism `M̃ ⟶ ℱ` of Tag 0B5I.

## Why this file exists next to `ProjTwistLocalComparison`

`Stacks.AlgebraicGeometry.ProjTwistLocalComparison` carries out the same two steps for the
**natural**-graded module `⨁_{d ≥ 0} Γ(X, ℱ(d))` of Tag 03GM, whose carrier
`Stacks.AlgebraicGeometry.ProjTwistSectionModule.twistSectionModule` is a direct sum over `ℕ`.
Tag 0B5I's module is a direct sum over `ℤ`, so it is a different type with a different grading,
a different decomposition and a different scalar action, and the statements of that file do not
apply to it. The mathematics is the same: a fraction `x / f ^ k` of degree zero only ever sees
the components `M_{k d}` with `k ≥ 0`, so no content beyond the natural-graded case is needed.
What changes is that the homogeneous scalar action is no longer the `DirectSum.Gmodule` action of
a family indexed by `ℕ` but the datum
`Stacks.AlgebraicGeometry.ProjTwistedSections.TwistedGlobalSectionsModule`, whose characterizing
formula `Stacks.AlgebraicGeometry.ProjTwistedSections.IsTwistedSectionsSMul` replaces the
`smul_of` of the natural-graded module. Everything in `ProjTwistLocalComparison` that does not
mention the module — division by the trivializing section, the scalar laws on the twists, the
rewriting of a fraction's denominator, and the restriction of a fraction section, which is
already stated for an arbitrary integer-graded module — is reused rather than copied.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistIntegerComparison.degreeComponent`: the degree-`k`
  component of an element of `⨁_{n ∈ ℤ} Γ(X, ℱ(n))`.
* `Stacks.AlgebraicGeometry.ProjTwistIntegerComparison.numerSection`: the map on numerators —
  take the degree-`n d` component, restrict, divide by `f ^ n`.
* `Stacks.AlgebraicGeometry.ProjTwistIntegerComparison.chartHom`: **the comparison map
  `Γ(D₊(f), M̃) ⟶ Γ(D₊(f), ℱ)` on a chart**, a morphism of modules over `Γ(D₊(f), 𝒪)`.
* `Stacks.AlgebraicGeometry.ProjTwistIntegerComparison.positiveChartHom` and
  `Stacks.AlgebraicGeometry.ProjTwistIntegerComparison.standardOpenHomData`: the chart maps
  indexed by the positive-degree homogeneous elements, and the local datum they form.
* `Stacks.AlgebraicGeometry.ProjTwistIntegerComparison.comparison`: **Tag 0B5I's comparison
  morphism `M̃ ⟶ ℱ`**, the morphism the chart maps glue to.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistIntegerComparison.numerSection_pow_smul`: the numerator
  maps are compatible with multiplying numerator and denominator by `f`, so they descend to the
  degree-zero localization `M₍f₎`.
* `Stacks.AlgebraicGeometry.ProjTwistIntegerComparison.numerSection_smul`: they are semilinear
  over `AlgebraicGeometry.Proj.awayToSection`, which is what makes the chart map linear.
* `Stacks.AlgebraicGeometry.ProjTwistIntegerComparison.mulTrivSection_chartHom`: **the
  fraction-wise formula** — the image of the fraction `x / f ^ n` is the section whose product
  with `f ^ n` is the restriction of the degree-`n d` component of `x`.
* `Stacks.AlgebraicGeometry.ProjTwistIntegerComparison.chartHom_restrict`: **the chart maps
  agree on overlaps.**
* `Stacks.AlgebraicGeometry.ProjTwistIntegerComparison.existsUnique_comparison`: **Tag 0B5I's
  comparison morphism exists and is unique**, now with no hypothesis on the local maps: they are
  the chart maps built here.
* `Stacks.AlgebraicGeometry.ProjTwistIntegerComparison.chartHom_naturality` and
  `Stacks.AlgebraicGeometry.ProjTwistIntegerComparison.integerComparison_naturality`:
  **Tag 0B5I's functoriality in `ℱ`**, likewise with nothing hypothesised. The local half is
  that a morphism `ψ : ℰ ⟶ ℱ` rewrites the numerator of a fraction
  (`associatedModuleSheafMap_standardOpen` together with `twistedSectionsMap_of`) and commutes
  with multiplication by the trivializing section (`twistSheafMap_mulTrivSection`, the
  naturality of the sheafification unit on the pure tensor `t ⊗ f ^ n`).

Every statement of `Stacks.AlgebraicGeometry.ProjTwistComparison` about an arbitrary compatible
family `θ`/`hθ` applies to the family built here: `integerComparison` is that file's `comparison`
instantiated at `localComparison`/`localComparison_restrict`.

## The degree-zero normalization

Tag 0B5I's third assertion — that the comparison induces the identity on `Γ(X, ℱ)` in degree
zero, which the source reads through the identification `Γ(X, ℱ(0)) = Γ(X, ℱ)` — is proved in
`StacksFrontier/AlgebraicGeometry/TensorSectionNonvanishing/ProjTwistDegreeZeroNormalization.lean`.
The local half is the material of this file: a degree-zero element `m` restricts on `D₊(f)` to
the fraction `m / f ^ 0`
(`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections_basicOpen`), so
`mulTrivSection_chartHom_of` at `n = 0` says the chart value of the comparison, multiplied by
the trivializing section `f ^ 0`, is the restriction of `m`. What that file adds is the global
identification itself,
`Stacks.AlgebraicGeometry.ProjTwistDegreeZeroNormalization.twistZeroCancelIso` — the trivialization
`𝒪_X(0) ≅ 𝒪_X` tensored into `ℱ ⊗ 𝒪_X(0)` and cancelled by the right unit constraint — which is
what names the global section `t` of `ℱ` the comparison produces from `m`, and which the hypothesis
`t` of `Stacks.AlgebraicGeometry.ProjTwistComparison.comparison_degreeZeroToGlobalSections` stands
in for.

## References

* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory DirectSum
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistSheafScalarMap
  twistedSectionsComponent twistedGlobalSectionsGrading IsTwistedSectionsSMul
  homogeneousScalarTwistedSections cast_homogeneousScalarTwistedSections
  TwistedGlobalSectionsModule twistedGlobalSectionsAssociatedSheaf
  isTwistedSectionsSMul_twistedGlobalSectionsModule twistSheafMap twistedSectionsMapComponent
  twistedSectionsMap twistedSectionsMap_of twistedSectionsLinearMap)
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality (associatedModuleSheafMap
  associatedModuleSheafMap_standardOpen)
open Stacks.SheafOfModules.TensorStalkRingedSpace (tensorSheafMap_app_toTensorSheafSection)
open Stacks.AlgebraicGeometry.ProjTrivialization (trivializingSection projRingSheaf)
open Stacks.AlgebraicGeometry.ProjTwistRestriction (mulTrivSection bijective_mulTrivSection
  twistSheafScalarMap_mulTrivSection twistSheafScalarMap_mulTrivSection_pow)
open Stacks.AlgebraicGeometry.ProjTwistLocalComparison (divTriv divTriv_add
  mulTrivSection_divTriv mulTrivSection_restrict map_smul_of_semilinear
  twistSheafScalarMap_mulTrivSection_smul subsingleton_sections_of_eq_bot
  standardOpenEquiv_restrict_mk map_map exists_rewrite_data)
open scoped Stacks.GradedLocalization
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.ProjTwistIntegerComparison

universe u w

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

variable {f : S} {d : ℕ}

/-! ### The components of the integer-graded module -/

section Component

variable (F : SheafOfModules.{u} (projRingSheaf 𝒮))

/-- The degree-`k` component of an element of `⨁_{n ∈ ℤ} Γ(X, ℱ(n))`. -/
def degreeComponent (k : ℤ) :
    twistedGlobalSections 𝒮 F →+ twistedSectionsComponent 𝒮 F k :=
  (DirectSum.component ℤ ℤ (fun m : ℤ => twistedSectionsComponent 𝒮 F m) k).toAddMonoidHom

/-- The degree-`k` component of the image of `s ∈ Γ(X, ℱ(k))` in the direct sum is `s`. -/
@[simp] theorem degreeComponent_of (k : ℤ) (s : twistedSectionsComponent 𝒮 F k) :
    degreeComponent 𝒮 F k
        (DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) k s) = s :=
  DirectSum.of_eq_same k s

/-- An element of the degree-`k` grading piece is the image of a section in `Γ(X, ℱ(k))`. -/
private theorem exists_of_mem_grading {k : ℤ} {x : twistedGlobalSections 𝒮 F}
    (hx : x ∈ twistedGlobalSectionsGrading 𝒮 F k) :
    ∃ s : twistedSectionsComponent 𝒮 F k,
      x = DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) k s :=
  (DirectSum.mem_rangeGrading ℤ (fun m : ℤ => twistedSectionsComponent 𝒮 F m) k x).mp hx

variable [Module S (twistedGlobalSections 𝒮 F)]

/-- **The degree-`j` component of `r • x` for `x` homogeneous of degree `n`**: it is the global
sections of the morphism `ℱ(n) ⟶ ℱ(j)` that multiplication by the homogeneous `r` induces. This
is the one place where the integer-graded module's scalar action enters, and it is exactly the
formula `IsTwistedSectionsSMul` that the datum of Tag 03GK supplies. -/
theorem degreeComponent_smul_of (hsmul : IsTwistedSectionsSMul 𝒮 F) {i : ℕ} {n j : ℤ} {r : S}
    (hr : r ∈ 𝒮 i) (hj : (i : ℤ) + n = j) (s : twistedSectionsComponent 𝒮 F n) :
    degreeComponent 𝒮 F j
        (r • (DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) n s :
          twistedGlobalSections 𝒮 F)) =
      (twistSheafScalarMap 𝒮 F i n j hj ⟨r, hr⟩).val.app (op ⊤) s := by
  subst hj
  rw [hsmul i n ⟨r, hr⟩ s, degreeComponent_of]
  rfl

/-- **Acting by a homogeneous `r` of degree `i` on a homogeneous element of degree `n` lands in
degree `i + n`.** This is the graded action of Tag 03GK, read off its characterizing formula
rather than off the `SetLike.GradedSMul` instance, which is stated for the shifted index
`i +ᵥ n`. -/
theorem smul_of_mem_grading (hsmul : IsTwistedSectionsSMul 𝒮 F) {i : ℕ} {n j : ℤ} {r : S}
    (hr : r ∈ 𝒮 i) (hj : (i : ℤ) + n = j) (s : twistedSectionsComponent 𝒮 F n) :
    r • (DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) n s :
        twistedGlobalSections 𝒮 F) ∈ twistedGlobalSectionsGrading 𝒮 F j := by
  subst hj
  rw [hsmul i n ⟨r, hr⟩ s]
  exact (DirectSum.mem_rangeGrading ℤ (fun m : ℤ => twistedSectionsComponent 𝒮 F m) _ _).mpr
    ⟨_, rfl⟩

/-- The restriction to `W` of the degree-`j` component of `r • x`, for `x` homogeneous of
degree `n` and `r` homogeneous of degree `i` with `i + n = j`: it is multiplication by `r` on
the twists, applied to the restriction of `x`. -/
theorem restrict_degreeComponent_smul (hsmul : IsTwistedSectionsSMul 𝒮 F) {i : ℕ} {n j : ℤ}
    {r : S} (hr : r ∈ 𝒮 i) (hj : (i : ℤ) + n = j) (s : twistedSectionsComponent 𝒮 F n)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} :
    (twistSheafOfModules 𝒮 F j).val.map (homOfLE (le_top : W ≤ ⊤)).op
        (degreeComponent 𝒮 F j
          (r • (DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) n s :
            twistedGlobalSections 𝒮 F))) =
      (twistSheafScalarMap 𝒮 F i n j hj ⟨r, hr⟩).val.app (op W)
        ((twistSheafOfModules 𝒮 F n).val.map (homOfLE (le_top : W ≤ ⊤)).op s) := by
  rw [degreeComponent_smul_of 𝒮 F hsmul hr hj s]
  exact (PresheafOfModules.naturality_apply
    (twistSheafScalarMap 𝒮 F i n j hj ⟨r, hr⟩).val (homOfLE (le_top : W ≤ ⊤)).op s).symm

end Component

/-! ### The maps on numerators -/

section Numerator

variable (F : SheafOfModules.{u} (projRingSheaf 𝒮))

/-- **The numerator map**: the degree-`n d` component of an element of `M`, restricted to
`W ⊆ D₊(f)` and divided by `f ^ n`. This is the family that Tag 0B5I's local comparison lifts
to the degree-zero localization. -/
def numerSection (hf : f ∈ 𝒮 d) (n : ℕ) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) :
    twistedGlobalSections 𝒮 F →+ F.val.obj (op W) :=
  AddMonoidHom.mk'
    (fun x => divTriv 𝒮 F hf n hW
      ((twistSheafOfModules 𝒮 F ((n : ℤ) * d)).val.map (homOfLE (le_top : W ≤ ⊤)).op
        (degreeComponent 𝒮 F ((n * d : ℕ) : ℤ) x)))
    (fun x y => by
      simp only [map_add]
      exact divTriv_add 𝒮 F hf n hW _ _)

/-- Multiplying the numerator map back by `f ^ n` recovers the restriction of the degree-`n d`
component. -/
theorem mulTrivSection_numerSection (hf : f ∈ 𝒮 d) (n : ℕ)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (x : twistedGlobalSections 𝒮 F) :
    mulTrivSection 𝒮 hf (n : ℤ) F hW (numerSection 𝒮 F hf n hW x) =
      (twistSheafOfModules 𝒮 F ((n : ℤ) * d)).val.map (homOfLE (le_top : W ≤ ⊤)).op
        (degreeComponent 𝒮 F ((n * d : ℕ) : ℤ) x) :=
  mulTrivSection_divTriv 𝒮 F hf n hW _

/-- Multiplying the numerator map of a homogeneous element `s` of degree `n d` back by `f ^ n`
recovers the restriction of `s`. -/
private theorem mulTrivSection_numerSection_of (hf : f ∈ 𝒮 d) (n : ℕ)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (s : twistedSectionsComponent 𝒮 F ((n * d : ℕ) : ℤ)) :
    mulTrivSection 𝒮 hf (n : ℤ) F hW (numerSection 𝒮 F hf n hW
        (DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) ((n * d : ℕ) : ℤ) s)) =
      (twistSheafOfModules 𝒮 F ((n : ℤ) * d)).val.map (homOfLE (le_top : W ≤ ⊤)).op s := by
  rw [mulTrivSection_numerSection, degreeComponent_of]

variable [Module S (twistedGlobalSections 𝒮 F)]

/-- **The numerator maps are compatible with multiplying numerator and denominator by `f`**:
this is what makes them descend to the degree-zero localization. -/
theorem numerSection_pow_smul (hsmul : IsTwistedSectionsSMul 𝒮 F) (hf : f ∈ 𝒮 d) (n k : ℕ)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (x : twistedGlobalSections 𝒮 F)
    (hx : x ∈ twistedGlobalSectionsGrading 𝒮 F ((n * d : ℕ) : ℤ)) :
    numerSection 𝒮 F hf (n + k) hW (f ^ k • x) = numerSection 𝒮 F hf n hW x := by
  obtain ⟨s, rfl⟩ := exists_of_mem_grading 𝒮 F hx
  have hpow : f ^ k ∈ 𝒮 (k * d) := by
    simpa [mul_comm] using SetLike.pow_mem_graded k hf
  have hk : ((k * d : ℕ) : ℤ) + ((n * d : ℕ) : ℤ) = ((n + k : ℕ) : ℤ) * d := by
    push_cast
    ring
  refine (bijective_mulTrivSection 𝒮 hf ((n + k : ℕ) : ℤ) F hW).1 ?_
  refine (mulTrivSection_numerSection 𝒮 F hf (n + k) hW _).trans ?_
  refine Eq.trans (restrict_degreeComponent_smul 𝒮 F hsmul hpow hk s (W := W)) ?_
  refine Eq.trans ?_ (twistSheafScalarMap_mulTrivSection_pow 𝒮 hf n k F hW _)
  exact congrArg _ (mulTrivSection_numerSection_of 𝒮 F hf n hW s).symm

end Numerator

/-! ### The comparison map on a chart -/

section ChartLift

variable (F : SheafOfModules.{u} (projRingSheaf 𝒮))
  [Module S (twistedGlobalSections 𝒮 F)]

/-- **The numerator maps are semilinear** over the comparison map
`A₍f₎ → Γ(D₊(f), 𝒪)`: acting by a homogeneous `r` of degree `m d` on a numerator of degree
`n d` and then dividing by `f ^ (m + n)` is multiplication by the degree-zero fraction
`r / f ^ m`. -/
theorem numerSection_smul (hsmul : IsTwistedSectionsSMul 𝒮 F) (hf : f ∈ 𝒮 d) (m n : ℕ) (r : S)
    (x : twistedGlobalSections 𝒮 F) (hr : r ∈ 𝒮 (m • d))
    (hx : x ∈ twistedGlobalSectionsGrading 𝒮 F ((n * d : ℕ) : ℤ)) :
    numerSection 𝒮 F hf (m + n) (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f)) (r • x) =
      (ProjectiveSpectrum.Proj.awayToSection 𝒮 f).hom
          (HomogeneousLocalization.Away.mk 𝒮 hf m r hr) •
        numerSection 𝒮 F hf n (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f)) x := by
  obtain ⟨s, rfl⟩ := exists_of_mem_grading 𝒮 F hx
  have hW : ProjectiveSpectrum.basicOpen 𝒮 f ≤ ProjectiveSpectrum.basicOpen 𝒮 f := le_rfl
  have hr' : r ∈ 𝒮 (m * d) := by simpa [smul_eq_mul] using hr
  have hk : ((m * d : ℕ) : ℤ) + ((n * d : ℕ) : ℤ) = ((m + n : ℕ) : ℤ) * d := by
    push_cast
    ring
  have hc : ∀ y : ProjectiveSpectrum.basicOpen 𝒮 f,
      HomogeneousLocalization.val
        (((ProjectiveSpectrum.Proj.awayToSection 𝒮 f).hom
          (HomogeneousLocalization.Away.mk 𝒮 hf m r hr)).1 y) =
        Localization.mk r ⟨f ^ m,
          y.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hW y.2) m⟩ := fun _ => rfl
  refine (bijective_mulTrivSection 𝒮 hf ((m + n : ℕ) : ℤ) F hW).1 ?_
  refine (mulTrivSection_numerSection 𝒮 F hf (m + n) hW _).trans ?_
  refine Eq.trans (restrict_degreeComponent_smul 𝒮 F hsmul hr' hk s
    (W := ProjectiveSpectrum.basicOpen 𝒮 f)) ?_
  refine Eq.trans ?_ (twistSheafScalarMap_mulTrivSection_smul 𝒮 hf hr' (Nat.add_comm m n) hk F
    hW _ hc _)
  exact congrArg _ (mulTrivSection_numerSection_of 𝒮 F hf n hW s).symm

variable [SetLike.GradedSMul 𝒮 (twistedGlobalSectionsGrading 𝒮 F)]

/-- **The comparison map on the chart `D₊(f)`, as an additive map**: the lift of the numerator
maps to the degree-zero localization `M₍f₎`. -/
def chartLift (hsmul : IsTwistedSectionsSMul 𝒮 F) (hf : f ∈ 𝒮 d) :
    GradedModuleDegreeZeroLocalization 𝒮 (twistedGlobalSectionsGrading 𝒮 F) f →+
      F.val.obj (op (ProjectiveSpectrum.basicOpen 𝒮 f)) :=
  Stacks.SheafOfModules.degreeZeroLocalizationLiftOfDegree 𝒮
    (twistedGlobalSectionsGrading 𝒮 F) hf
    (fun n => numerSection 𝒮 F hf n (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f)))
    (fun n k x hx => numerSection_pow_smul 𝒮 F hsmul hf n k _ x hx)

/-- **The value of the chart comparison on a fraction**: the fraction `x / f ^ n` with `x` of
degree `n d` goes to the restriction of `x` divided by `f ^ n`. -/
theorem chartLift_fraction (hsmul : IsTwistedSectionsSMul 𝒮 F) (hf : f ∈ 𝒮 d)
    (z : GradedModuleDegreeZeroLocalization 𝒮 (twistedGlobalSectionsGrading 𝒮 F) f)
    (n : ℕ) (x : twistedGlobalSections 𝒮 F)
    (hx : x ∈ twistedGlobalSectionsGrading 𝒮 F ((n * d : ℕ) : ℤ))
    (hz : (z : LocalizedModule.Away f (twistedGlobalSections 𝒮 F)) =
      LocalizedModule.mk (S := Submonoid.powers f) x ⟨f ^ n, by exact ⟨n, rfl⟩⟩) :
    chartLift 𝒮 F hsmul hf z =
      numerSection 𝒮 F hf n (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f)) x :=
  Stacks.SheafOfModules.degreeZeroLocalizationLiftOfDegree_fraction 𝒮
    (twistedGlobalSectionsGrading 𝒮 F) hf _ _ z n x hx hz

/-- The chart comparison is semilinear over `A₍f₎ → Γ(D₊(f), 𝒪)`. -/
theorem chartLift_smul (hsmul : IsTwistedSectionsSMul 𝒮 F) (hf : f ∈ 𝒮 d)
    (a : HomogeneousLocalization.Away 𝒮 f)
    (z : GradedModuleDegreeZeroLocalization 𝒮 (twistedGlobalSectionsGrading 𝒮 F) f) :
    chartLift 𝒮 F hsmul hf (a • z) =
      (ProjectiveSpectrum.Proj.awayToSection 𝒮 f).hom a • chartLift 𝒮 F hsmul hf z :=
  Stacks.SheafOfModules.degreeZeroLocalizationLiftOfDegree_smul 𝒮
    (twistedGlobalSectionsGrading 𝒮 F) hf _ _
    (ProjectiveSpectrum.Proj.awayToSection 𝒮 f).hom
    (fun m n r x hr hx => numerSection_smul 𝒮 F hsmul hf m n r x hr hx) a z

end ChartLift

/-! ### The comparison map as a morphism of modules on the chart -/

section ChartHom

variable (F : SheafOfModules.{u} (projRingSheaf 𝒮))
  [Module S (twistedGlobalSections 𝒮 F)]
  [SetLike.GradedSMul 𝒮 (twistedGlobalSectionsGrading 𝒮 F)]

/-- The chart comparison, read on the sections of `M̃` over `D₊(f)` through the standard-open
identification with `M₍f₎`. -/
def chartAddHom (hsmul : IsTwistedSectionsSMul 𝒮 F) (hf : f ∈ 𝒮 d) (hd : 0 < d) :
    (associatedModuleSheaf 𝒮 (twistedGlobalSectionsGrading 𝒮 F)).val.obj
        (op (ProjectiveSpectrum.basicOpen 𝒮 f)) →+
      F.val.obj (op (ProjectiveSpectrum.basicOpen 𝒮 f)) :=
  (chartLift 𝒮 F hsmul hf).comp
    (associatedModuleSheafStandardOpenEquiv 𝒮 (twistedGlobalSectionsGrading 𝒮 F)
      hf hd).toLinearMap.toAddMonoidHom

/-- The chart comparison is semilinear over the comparison map `A₍f₎ → Γ(D₊(f), 𝒪)`. -/
theorem chartAddHom_smul (hsmul : IsTwistedSectionsSMul 𝒮 F) (hf : f ∈ 𝒮 d) (hd : 0 < d)
    (a : HomogeneousLocalization.Away 𝒮 f)
    (z : (associatedModuleSheaf 𝒮 (twistedGlobalSectionsGrading 𝒮 F)).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒮 f))) :
    chartAddHom 𝒮 F hsmul hf hd (a • z) =
      (ProjectiveSpectrum.Proj.awayToSection 𝒮 f).hom a • chartAddHom 𝒮 F hsmul hf hd z := by
  change chartLift 𝒮 F hsmul hf
      (associatedModuleSheafStandardOpenEquiv 𝒮 (twistedGlobalSectionsGrading 𝒮 F) hf hd
        (a • z)) = _
  rw [map_smul]
  exact chartLift_smul 𝒮 F hsmul hf a _

/-- **The comparison map on the chart `D₊(f)`**, as a morphism of modules over
`Γ(D₊(f), 𝒪)`: the linearity is the transfer of the semilinearity above along the surjection
`A₍f₎ → Γ(D₊(f), 𝒪)`. -/
def chartHom (hsmul : IsTwistedSectionsSMul 𝒮 F) (hf : f ∈ 𝒮 d) (hd : 0 < d) :
    (associatedModuleSheaf 𝒮 (twistedGlobalSectionsGrading 𝒮 F)).val.obj
        (op (ProjectiveSpectrum.basicOpen 𝒮 f)) ⟶
      F.val.obj (op (ProjectiveSpectrum.basicOpen 𝒮 f)) :=
  ModuleCat.ofHom (R := ((ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj
      (op (ProjectiveSpectrum.basicOpen 𝒮 f))))
    { toFun := fun z => chartAddHom 𝒮 F hsmul hf hd z
      map_add' := fun z w => map_add (chartAddHom 𝒮 F hsmul hf hd) z w
      map_smul' := fun c z => map_smul_of_semilinear
        (ProjectiveSpectrum.Proj.awayToSection 𝒮 f).hom
        (ProjectiveSpectrum.Proj.surjective_awayToSection 𝒮 hf hd) (fun _ _ => rfl)
        (chartAddHom 𝒮 F hsmul hf hd) (chartAddHom_smul 𝒮 F hsmul hf hd) c z }

/-- The chart comparison `chartHom` agrees, as a function, with `chartAddHom`. -/
@[simp] theorem chartHom_apply (hsmul : IsTwistedSectionsSMul 𝒮 F) (hf : f ∈ 𝒮 d) (hd : 0 < d)
    (z : (associatedModuleSheaf 𝒮 (twistedGlobalSectionsGrading 𝒮 F)).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒮 f))) :
    chartHom 𝒮 F hsmul hf hd z = chartAddHom 𝒮 F hsmul hf hd z := rfl

/-- **The chart comparison does not depend on the degree in which `f` is homogeneous.** A
nonzero `f` is homogeneous in one degree only, so the two witnesses are the same and the two
maps are the same by proof irrelevance; and `D₊(0)` is empty, so for `f = 0` the two maps are
maps into a module with a single element.

This is what lets a formula proved at a given degree witness be read off the comparison map
attached to a positive-degree element, whose witness is chosen by `Exists.choose`. -/
theorem chartHom_congr {d' : ℕ} (hsmul : IsTwistedSectionsSMul 𝒮 F) (hf : f ∈ 𝒮 d) (hd : 0 < d)
    (hf' : f ∈ 𝒮 d') (hd' : 0 < d') :
    chartHom 𝒮 F hsmul hf hd = chartHom 𝒮 F hsmul hf' hd' := by
  by_cases h0 : f = 0
  · subst h0
    have hbot : ProjectiveSpectrum.basicOpen 𝒮 (0 : S) = ⊥ := by simp
    have hsub := subsingleton_sections_of_eq_bot 𝒮 F hbot
    exact ModuleCat.hom_ext (LinearMap.ext fun z => Subsingleton.elim _ _)
  · have hdd : d = d' := DirectSum.degree_eq_of_mem_mem 𝒮 hf hf' h0
    subst hdd
    rfl

/-- **The fraction-wise formula for the comparison map on a chart.** If the section `z` of `M̃`
over `D₊(f)` is the fraction `x / f ^ n` with `x` homogeneous of degree `n d`, then the image of
`z` is the section of `ℱ` whose product with the trivializing section `f ^ n` is the restriction
of the degree-`n d` component of `x`. By
`Stacks.AlgebraicGeometry.ProjTwistRestriction.bijective_mulTrivSection` that pins the image
down. -/
theorem mulTrivSection_chartHom (hsmul : IsTwistedSectionsSMul 𝒮 F) (hf : f ∈ 𝒮 d) (hd : 0 < d)
    (z : (associatedModuleSheaf 𝒮 (twistedGlobalSectionsGrading 𝒮 F)).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒮 f)))
    (n : ℕ) (x : twistedGlobalSections 𝒮 F)
    (hx : x ∈ twistedGlobalSectionsGrading 𝒮 F ((n * d : ℕ) : ℤ))
    (hz : ((associatedModuleSheafStandardOpenEquiv 𝒮 (twistedGlobalSectionsGrading 𝒮 F)
          hf hd z :
        GradedModuleDegreeZeroLocalization 𝒮 (twistedGlobalSectionsGrading 𝒮 F) f) :
        LocalizedModule.Away f (twistedGlobalSections 𝒮 F)) =
      LocalizedModule.mk (S := Submonoid.powers f) x ⟨f ^ n, by exact ⟨n, rfl⟩⟩) :
    mulTrivSection 𝒮 hf (n : ℤ) F
          (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f)) (chartHom 𝒮 F hsmul hf hd z) =
      (twistSheafOfModules 𝒮 F ((n : ℤ) * d)).val.map
        (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒮 f ≤ ⊤)).op
        (degreeComponent 𝒮 F ((n * d : ℕ) : ℤ) x) := by
  refine Eq.trans (congrArg (mulTrivSection 𝒮 hf (n : ℤ) F
    (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f)))
    ((chartHom_apply 𝒮 F hsmul hf hd z).trans
      (chartLift_fraction 𝒮 F hsmul hf _ n x hx hz))) ?_
  exact mulTrivSection_numerSection 𝒮 F hf n _ x

/-- **The fraction-wise formula with the numerator given as a homogeneous element.** If the
section `z` of `M̃` over `D₊(f)` is the fraction `s / f ^ n` with `s` in the degree-`n d`
summand, then the product of its image with `f ^ n` is the restriction of `s`. -/
theorem mulTrivSection_chartHom_of (hsmul : IsTwistedSectionsSMul 𝒮 F) (hf : f ∈ 𝒮 d)
    (hd : 0 < d)
    (z : (associatedModuleSheaf 𝒮 (twistedGlobalSectionsGrading 𝒮 F)).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒮 f)))
    (n : ℕ) (s : twistedSectionsComponent 𝒮 F ((n * d : ℕ) : ℤ))
    (hz : ((associatedModuleSheafStandardOpenEquiv 𝒮 (twistedGlobalSectionsGrading 𝒮 F)
          hf hd z :
        GradedModuleDegreeZeroLocalization 𝒮 (twistedGlobalSectionsGrading 𝒮 F) f) :
        LocalizedModule.Away f (twistedGlobalSections 𝒮 F)) =
      LocalizedModule.mk (S := Submonoid.powers f)
        (DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) ((n * d : ℕ) : ℤ) s)
        ⟨f ^ n, by exact ⟨n, rfl⟩⟩) :
    mulTrivSection 𝒮 hf (n : ℤ) F
          (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f)) (chartHom 𝒮 F hsmul hf hd z) =
      (twistSheafOfModules 𝒮 F ((n : ℤ) * d)).val.map
        (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒮 f ≤ ⊤)).op s := by
  refine Eq.trans (mulTrivSection_chartHom 𝒮 F hsmul hf hd z n _
    ((DirectSum.mem_rangeGrading ℤ (fun m : ℤ => twistedSectionsComponent 𝒮 F m)
      ((n * d : ℕ) : ℤ) _).mpr ⟨s, rfl⟩) hz) ?_
  exact congrArg ((twistSheafOfModules 𝒮 F ((n : ℤ) * d)).val.map
    (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒮 f ≤ ⊤)).op)
    (degreeComponent_of 𝒮 F ((n * d : ℕ) : ℤ) s)

/-- Every section of `M̃` over `D₊(f)` is a fraction `x / f ^ n` with `x` homogeneous of degree
`n d`. -/
theorem exists_fraction (hf : f ∈ 𝒮 d) (hd : 0 < d)
    (z : (associatedModuleSheaf 𝒮 (twistedGlobalSectionsGrading 𝒮 F)).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒮 f))) :
    ∃ (n : ℕ) (x : twistedGlobalSections 𝒮 F),
      x ∈ twistedGlobalSectionsGrading 𝒮 F ((n * d : ℕ) : ℤ) ∧
      ((associatedModuleSheafStandardOpenEquiv 𝒮 (twistedGlobalSectionsGrading 𝒮 F)
            hf hd z :
          GradedModuleDegreeZeroLocalization 𝒮 (twistedGlobalSectionsGrading 𝒮 F) f) :
          LocalizedModule.Away f (twistedGlobalSections 𝒮 F)) =
        LocalizedModule.mk (S := Submonoid.powers f) x ⟨f ^ n, by exact ⟨n, rfl⟩⟩ :=
  Stacks.SheafOfModules.degreeZeroLocalization_exists_fraction_of_degree 𝒮
    (twistedGlobalSectionsGrading 𝒮 F) hf _

end ChartHom

/-! ### Compatibility of the chart comparisons with restriction -/

section Compatibility

variable (F : SheafOfModules.{u} (projRingSheaf 𝒮))
  [Module S (twistedGlobalSections 𝒮 F)]
  [SetLike.GradedSMul 𝒮 (twistedGlobalSectionsGrading 𝒮 F)]

/-- The chart comparisons agree on an overlap, with the rewritten fraction supplied. -/
private theorem chartHom_restrict_aux (hsmul : IsTwistedSectionsSMul 𝒮 F) {g : S} {e : ℕ}
    (hf : f ∈ 𝒮 d) (hd : 0 < d) (hg : g ∈ 𝒮 e) (he : 0 < e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒮 g ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (z : (associatedModuleSheaf 𝒮 (twistedGlobalSectionsGrading 𝒮 F)).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒮 f)))
    (n b : ℕ) {c : S} (hc : c ^ n ∈ 𝒮 (n * (b * e - d)))
    (hgm : g ^ (n * b) = f ^ n * c ^ n)
    (hdeg : ((n * (b * e - d) : ℕ) : ℤ) + (n : ℤ) * (d : ℤ) = ((n * b : ℕ) : ℤ) * (e : ℤ))
    (x : twistedGlobalSections 𝒮 F)
    (hx : x ∈ twistedGlobalSectionsGrading 𝒮 F ((n * d : ℕ) : ℤ))
    (hz : ((associatedModuleSheafStandardOpenEquiv 𝒮 (twistedGlobalSectionsGrading 𝒮 F)
          hf hd z :
        GradedModuleDegreeZeroLocalization 𝒮 (twistedGlobalSectionsGrading 𝒮 F) f) :
        LocalizedModule.Away f (twistedGlobalSections 𝒮 F)) =
      LocalizedModule.mk (S := Submonoid.powers f) x ⟨f ^ n, by exact ⟨n, rfl⟩⟩) :
    chartHom 𝒮 F hsmul hg he
        ((associatedModuleSheaf 𝒮 (twistedGlobalSectionsGrading 𝒮 F)).val.map
          (homOfLE hfg).op z) =
      (F.val.map (homOfLE hfg).op).hom (chartHom 𝒮 F hsmul hf hd z) := by
  obtain ⟨s, rfl⟩ := exists_of_mem_grading 𝒮 F hx
  have hcx : c ^ n •
      (DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) ((n * d : ℕ) : ℤ) s :
        twistedGlobalSections 𝒮 F) ∈
      twistedGlobalSectionsGrading 𝒮 F ((n * b * e : ℕ) : ℤ) :=
    smul_of_mem_grading 𝒮 F hsmul hc hdeg s
  have hz' : associatedModuleSheafStandardOpenEquiv 𝒮 (twistedGlobalSectionsGrading 𝒮 F) hg he
      ((associatedModuleSheaf 𝒮 (twistedGlobalSectionsGrading 𝒮 F)).val.map
        (homOfLE hfg).op z) =
      ⟨LocalizedModule.mk (S := Submonoid.powers g)
          (c ^ n •
            (DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) ((n * d : ℕ) : ℤ) s :
              twistedGlobalSections 𝒮 F))
          ⟨g ^ (n * b), by exact ⟨n * b, rfl⟩⟩,
        Stacks.SheafOfModules.mk_mem_degreeZeroLocalization_of_degree 𝒮
          (twistedGlobalSectionsGrading 𝒮 F) hg (n * b) _ hcx⟩ :=
    standardOpenEquiv_restrict_mk 𝒮 (twistedGlobalSectionsGrading 𝒮 F) hf hd hg he hfg hgm
      z _ hz rfl
  refine (bijective_mulTrivSection 𝒮 hg ((n * b : ℕ) : ℤ) F
    (le_refl (ProjectiveSpectrum.basicOpen 𝒮 g))).1 ?_
  refine Eq.trans ((mulTrivSection_chartHom 𝒮 F hsmul hg he _ (n * b) _ hcx
      (by rw [hz'])).trans
    (restrict_degreeComponent_smul 𝒮 F hsmul hc hdeg s
      (W := ProjectiveSpectrum.basicOpen 𝒮 g))) ?_
  refine Eq.trans ?_ (twistSheafScalarMap_mulTrivSection 𝒮 hf hg hc n (n * b) hgm hdeg F hfg
    (le_refl (ProjectiveSpectrum.basicOpen 𝒮 g)) _)
  refine congrArg (fun y =>
    (twistSheafScalarMap 𝒮 F (n * (b * e - d)) ((n : ℤ) * d) (((n * b : ℕ) : ℤ) * e) hdeg
      ⟨c ^ n, hc⟩).val.app (op (ProjectiveSpectrum.basicOpen 𝒮 g)) y) ?_
  refine Eq.trans ?_ (mulTrivSection_restrict 𝒮 F hf (n : ℤ)
    (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f)) hfg (chartHom 𝒮 F hsmul hf hd z))
  refine Eq.trans ?_ (congrArg ((twistSheafOfModules 𝒮 F ((n : ℤ) * d)).val.map
    (homOfLE hfg).op) (mulTrivSection_chartHom_of 𝒮 F hsmul hf hd z n s hz).symm)
  exact (map_map 𝒮 F (le_top : ProjectiveSpectrum.basicOpen 𝒮 f ≤ ⊤) hfg _).symm

/-- The chart comparisons agree on an overlap, for a section given as a fraction. -/
private theorem chartHom_restrict_of_fraction (hsmul : IsTwistedSectionsSMul 𝒮 F) {g : S}
    {e : ℕ} (hf : f ∈ 𝒮 d) (hd : 0 < d) (hg : g ∈ 𝒮 e) (he : 0 < e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒮 g ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (z : (associatedModuleSheaf 𝒮 (twistedGlobalSectionsGrading 𝒮 F)).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒮 f)))
    (n : ℕ) (x : twistedGlobalSections 𝒮 F)
    (hx : x ∈ twistedGlobalSectionsGrading 𝒮 F ((n * d : ℕ) : ℤ))
    (hz : ((associatedModuleSheafStandardOpenEquiv 𝒮 (twistedGlobalSectionsGrading 𝒮 F)
          hf hd z :
        GradedModuleDegreeZeroLocalization 𝒮 (twistedGlobalSectionsGrading 𝒮 F) f) :
        LocalizedModule.Away f (twistedGlobalSections 𝒮 F)) =
      LocalizedModule.mk (S := Submonoid.powers f) x ⟨f ^ n, by exact ⟨n, rfl⟩⟩) :
    chartHom 𝒮 F hsmul hg he
        ((associatedModuleSheaf 𝒮 (twistedGlobalSectionsGrading 𝒮 F)).val.map
          (homOfLE hfg).op z) =
      (F.val.map (homOfLE hfg).op).hom (chartHom 𝒮 F hsmul hf hd z) := by
  obtain ⟨b, c, hc, hgm, _, hdeg⟩ := exists_rewrite_data 𝒮 hf hd hg he hfg n
  exact chartHom_restrict_aux 𝒮 F hsmul hf hd hg he hfg z n b hc hgm hdeg x hx hz

/-- **The chart comparisons agree on overlaps.** For `D₊(g) ⊆ D₊(f)` with `f` and `g`
homogeneous of positive degrees, the comparison attached to `g` applied to the restriction of a
section of `M̃` is the restriction of the comparison attached to `f`. This is the compatibility
with restriction that glues the chart comparisons into one morphism `M̃ ⟶ ℱ`.

The fraction `x / f ^ n` representing the section is rewritten with denominator a power of `g`
by `ProjectiveSpectrum.exists_pow_eq_mul_of_basicOpen_le_degree`: `g ^ b = c f` with `c`
homogeneous, hence `g ^ (n b) = c ^ n f ^ n`, and both sides are then multiplication by `c ^ n`
applied to the restriction of `x`. -/
theorem chartHom_restrict (hsmul : IsTwistedSectionsSMul 𝒮 F) {g : S} {e : ℕ} (hf : f ∈ 𝒮 d)
    (hd : 0 < d) (hg : g ∈ 𝒮 e) (he : 0 < e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒮 g ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (z : (associatedModuleSheaf 𝒮 (twistedGlobalSectionsGrading 𝒮 F)).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒮 f))) :
    chartHom 𝒮 F hsmul hg he
        ((associatedModuleSheaf 𝒮 (twistedGlobalSectionsGrading 𝒮 F)).val.map
          (homOfLE hfg).op z) =
      (F.val.map (homOfLE hfg).op).hom (chartHom 𝒮 F hsmul hf hd z) := by
  obtain ⟨n, x, hx, hz⟩ := exists_fraction 𝒮 F hf hd z
  exact chartHom_restrict_of_fraction 𝒮 F hsmul hf hd hg he hfg z n x hx hz

end Compatibility

/-! ### The glued comparison morphism -/

section Glued

open Stacks.AlgebraicGeometry.ProjTwistComparison (PositiveElem positiveBasicOpen
  StandardOpenHomData homOfStandardOpenHomData homOfStandardOpenHomData_app
  eq_homOfStandardOpenHomData isBasis_positiveBasicOpen)

variable (F : SheafOfModules.{u} (projRingSheaf 𝒮))
  [Module S (twistedGlobalSections 𝒮 F)]
  [SetLike.GradedSMul 𝒮 (twistedGlobalSectionsGrading 𝒮 F)]

/-- The comparison map on the standard open of a positive-degree homogeneous element: the chart
comparison for a degree witnessing that the element is homogeneous of positive degree. -/
def positiveChartHom (hsmul : IsTwistedSectionsSMul 𝒮 F) (p : PositiveElem 𝒮) :
    (associatedModuleSheaf 𝒮 (twistedGlobalSectionsGrading 𝒮 F)).val.obj
        (op (positiveBasicOpen 𝒮 p)) ⟶
      F.val.obj (op (positiveBasicOpen 𝒮 p)) :=
  chartHom 𝒮 F hsmul p.2.choose_spec.2 p.2.choose_spec.1

/-- The comparison maps on the positive-degree standard opens are compatible with
restriction. -/
theorem positiveChartHom_restrict (hsmul : IsTwistedSectionsSMul 𝒮 F) (p q : PositiveElem 𝒮)
    (h : positiveBasicOpen 𝒮 q ≤ positiveBasicOpen 𝒮 p)
    (z : (associatedModuleSheaf 𝒮 (twistedGlobalSectionsGrading 𝒮 F)).val.obj
      (op (positiveBasicOpen 𝒮 p))) :
    positiveChartHom 𝒮 F hsmul q
        ((associatedModuleSheaf 𝒮 (twistedGlobalSectionsGrading 𝒮 F)).val.map
          (homOfLE h).op z) =
      F.val.map (homOfLE h).op (positiveChartHom 𝒮 F hsmul p z) :=
  chartHom_restrict 𝒮 F hsmul p.2.choose_spec.2 p.2.choose_spec.1 q.2.choose_spec.2
    q.2.choose_spec.1 h z

/-- **The comparison map attached to a positive-degree element is the chart comparison for any
degree in which the element is homogeneous**, not only for the degree `Exists.choose` picks out
of its positivity witness. -/
theorem positiveChartHom_eq_chartHom (hsmul : IsTwistedSectionsSMul 𝒮 F) (p : PositiveElem 𝒮)
    (hf : (p.1 : S) ∈ 𝒮 d) (hd : 0 < d) :
    positiveChartHom 𝒮 F hsmul p = chartHom 𝒮 F hsmul hf hd :=
  chartHom_congr 𝒮 F hsmul p.2.choose_spec.2 p.2.choose_spec.1 hf hd

/-- **The local datum the chart comparisons form** — the `StandardOpenHomData` of Tag 0B5I's
proof, for the integer-graded module of twisted global sections. -/
def standardOpenHomData (hsmul : IsTwistedSectionsSMul 𝒮 F) :
    StandardOpenHomData 𝒮 (twistedGlobalSectionsGrading 𝒮 F) F where
  app := positiveChartHom 𝒮 F hsmul
  app_restrict := positiveChartHom_restrict 𝒮 F hsmul

end Glued

/-! ### Tag 0B5I's comparison morphism, with the local maps supplied -/

section Comparison

open Stacks.AlgebraicGeometry.ProjTwistComparison (PositiveElem positiveBasicOpen comparison
  comparison_app)

variable (F : SheafOfModules.{u} (projRingSheaf 𝒮)) (D : TwistedGlobalSectionsModule 𝒮 F)

/-- **The comparison maps on the positive-degree standard opens of Tag 0B5I**, for the
integer-graded module of twisted global sections with the graded module structure `D` of
Tag 03GK: the chart comparison of
`Stacks.AlgebraicGeometry.ProjTwistIntegerComparison.chartHom`, read on the sections of `M̃`.

No `stacks` attribute: this is the local datum, and the assertions carrying it are
`existsUnique_comparison` and the statements of
`Stacks.AlgebraicGeometry.ProjTwistComparison` that it discharges. -/
def localComparison (p : PositiveElem 𝒮) :
    (twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.obj (op (positiveBasicOpen 𝒮 p)) ⟶
      F.val.obj (op (positiveBasicOpen 𝒮 p)) :=
  letI := D.moduleInst
  letI := D.gradedSMul
  positiveChartHom 𝒮 F (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 F D) p

/-- **The local comparison maps of Tag 0B5I are compatible with restriction.** With
`localComparison` this is the pair `θ`, `hθ` that the statements of
`Stacks.AlgebraicGeometry.ProjTwistComparison` take as hypotheses, so those statements become
unconditional once instantiated here. -/
theorem localComparison_restrict (p q : PositiveElem 𝒮)
    (h : positiveBasicOpen 𝒮 q ≤ positiveBasicOpen 𝒮 p)
    (s : (twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.obj
      (op (positiveBasicOpen 𝒮 p))) :
    localComparison 𝒮 F D q
        ((twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.map (homOfLE h).op s) =
      F.val.map (homOfLE h).op (localComparison 𝒮 F D p s) := by
  let := D.moduleInst
  let := D.gradedSMul
  exact positiveChartHom_restrict 𝒮 F
    (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 F D) p q h s

/-- **Tag 0B5I's comparison morphism `M̃ ⟶ ℱ`**, where `M = ⨁_{n ∈ ℤ} Γ(Proj 𝒮, ℱ(n))` carries
the graded `S`-module structure `D` of Tag 03GK: the morphism glued from the chart comparisons.

No `stacks` attribute. This is the construction; the tag's assertion that such a morphism exists
and is unique is `existsUnique_comparison`, which carries the attribute. -/
def integerComparison : twistedGlobalSectionsAssociatedSheaf 𝒮 F D ⟶ F :=
  comparison 𝒮 F D (localComparison 𝒮 F D) (localComparison_restrict 𝒮 F D)

/-- The comparison morphism restricts on each positive-degree standard open to the chart
comparison. -/
theorem integerComparison_app (p : PositiveElem 𝒮) :
    (integerComparison 𝒮 F D).val.app (op (positiveBasicOpen 𝒮 p)) =
      localComparison 𝒮 F D p :=
  comparison_app 𝒮 F D (localComparison 𝒮 F D) (localComparison_restrict 𝒮 F D) p

/-- **Tag 0B5I: the comparison morphism `M̃ ⟶ ℱ` from the integer-graded twisted global sections
exists and is unique.** Here `M = ⨁_{n ∈ ℤ} Γ(Proj 𝒮, ℱ(n))` carries the graded `S`-module
structure `D` of Tag 03GK and `M̃` is its associated sheaf. There is exactly one morphism
`M̃ ⟶ ℱ` restricting on the standard open `D₊(f)` of every positive-degree homogeneous element
to the map `m / f ^ k ↦ m|_{D₊(f)} ⊗ f ^ (-k)` of
`Stacks.AlgebraicGeometry.ProjTwistIntegerComparison.chartHom`, namely `integerComparison`.

Nothing is hypothesised: the local maps are the chart comparisons constructed in this file, and
their compatibility with restriction is `localComparison_restrict`. The proof is
`Stacks.AlgebraicGeometry.ProjTwistComparison.existsUnique_comparison` — the conditional form,
which quantifies over the standard-open comparison maps — instantiated at those two, so this is
that statement with its hypotheses discharged rather than a second proof of it. -/
theorem existsUnique_comparison :
    ∃! φ : twistedGlobalSectionsAssociatedSheaf 𝒮 F D ⟶ F,
      ∀ p : PositiveElem 𝒮,
        φ.val.app (op (positiveBasicOpen 𝒮 p)) = localComparison 𝒮 F D p :=
  Stacks.AlgebraicGeometry.ProjTwistComparison.existsUnique_comparison 𝒮 F D
    (localComparison 𝒮 F D) (localComparison_restrict 𝒮 F D)

end Comparison

/-! ### Functoriality in `ℱ` -/

section Naturality

open Stacks.AlgebraicGeometry.ProjTwistComparison (PositiveElem positiveBasicOpen
  twistedSectionsMap_mem_grading twistedGlobalSectionsAssociatedSheafMap comparison
  comparison_naturality)

variable {E F : SheafOfModules.{u} (projRingSheaf 𝒮)}

/-- **A morphism `ψ : ℰ ⟶ ℱ` commutes with multiplication by the trivializing section
`f ^ n`.** Both `ℰ(nd) ⟶ ℱ(nd)` and the section `t ⊗ f ^ n` are the identity on the `𝒪(nd)`
factor of the tensor product, so this is the naturality of the sheafification unit for the
pure tensor `t ⊗ f ^ n`. -/
theorem twistSheafMap_mulTrivSection (hf : f ∈ 𝒮 d) (n : ℤ) (ψ : E ⟶ F)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (t : E.val.obj (op W)) :
    (twistSheafMap 𝒮 ψ (n * d)).val.app (op W) (mulTrivSection 𝒮 hf n E hW t) =
      mulTrivSection 𝒮 hf n F hW (ψ.val.app (op W) t) :=
  tensorSheafMap_app_toTensorSheafSection (AlgebraicGeometry.Proj 𝒮).toRingedSpace
    E (twistingSheaf 𝒮 (n * d)) F (twistingSheaf 𝒮 (n * d)) ψ
    (𝟙 (twistingSheaf 𝒮 (n * d))) W t (trivializingSection 𝒮 hf n hW)

variable [Module S (twistedGlobalSections 𝒮 E)] [Module S (twistedGlobalSections 𝒮 F)]
  [SetLike.GradedSMul 𝒮 (twistedGlobalSectionsGrading 𝒮 E)]
  [SetLike.GradedSMul 𝒮 (twistedGlobalSectionsGrading 𝒮 F)]

/-- **The induced map on the sections over a chart rewrites the numerator of a fraction.** The
fraction `x / f ^ n` of `M̃_ℰ` goes to `ψ x / f ^ n`, with the degree-`n d` numerator carried by
the degree-`n d` twist of `ψ` on global sections. -/
private theorem standardOpenEquiv_associatedModuleSheafMap_mk
    (hE : IsTwistedSectionsSMul 𝒮 E) (hF : IsTwistedSectionsSMul 𝒮 F) (ψ : E ⟶ F)
    (hf : f ∈ 𝒮 d) (hd : 0 < d)
    (z : (associatedModuleSheaf 𝒮 (twistedGlobalSectionsGrading 𝒮 E)).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒮 f)))
    (n : ℕ) (s : twistedSectionsComponent 𝒮 E ((n * d : ℕ) : ℤ))
    (hz : ((associatedModuleSheafStandardOpenEquiv 𝒮 (twistedGlobalSectionsGrading 𝒮 E)
          hf hd z :
        GradedModuleDegreeZeroLocalization 𝒮 (twistedGlobalSectionsGrading 𝒮 E) f) :
        LocalizedModule.Away f (twistedGlobalSections 𝒮 E)) =
      LocalizedModule.mk (S := Submonoid.powers f)
        (DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 E m) ((n * d : ℕ) : ℤ) s)
        ⟨f ^ n, by exact ⟨n, rfl⟩⟩) :
    ((associatedModuleSheafStandardOpenEquiv 𝒮 (twistedGlobalSectionsGrading 𝒮 F)
          hf hd ((associatedModuleSheafMap 𝒮 (twistedGlobalSectionsGrading 𝒮 E)
            (twistedGlobalSectionsGrading 𝒮 F) (twistedSectionsLinearMap 𝒮 hE hF ψ)
            (twistedSectionsMap_mem_grading 𝒮 ψ)).val.app _ z) :
        GradedModuleDegreeZeroLocalization 𝒮 (twistedGlobalSectionsGrading 𝒮 F) f) :
        LocalizedModule.Away f (twistedGlobalSections 𝒮 F)) =
      LocalizedModule.mk (S := Submonoid.powers f)
        (DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) ((n * d : ℕ) : ℤ)
          (twistedSectionsMapComponent 𝒮 ψ ((n * d : ℕ) : ℤ) s))
        ⟨f ^ n, by exact ⟨n, rfl⟩⟩ := by
  rw [associatedModuleSheafMap_standardOpen 𝒮 (twistedGlobalSectionsGrading 𝒮 E)
    (twistedGlobalSectionsGrading 𝒮 F) (twistedSectionsLinearMap 𝒮 hE hF ψ)
    (twistedSectionsMap_mem_grading 𝒮 ψ) hf hd z, hz, LocalizedModule.map_mk]
  exact congrArg (fun y => LocalizedModule.mk (S := Submonoid.powers f) y
    ⟨f ^ n, by exact ⟨n, rfl⟩⟩) (twistedSectionsMap_of 𝒮 ψ ((n * d : ℕ) : ℤ) s)

/-- The chart comparisons of `ℰ` and of `ℱ` commute with `ψ`, for a section given as a
fraction. -/
private theorem chartHom_naturality_of_fraction (hE : IsTwistedSectionsSMul 𝒮 E)
    (hF : IsTwistedSectionsSMul 𝒮 F) (ψ : E ⟶ F) (hf : f ∈ 𝒮 d) (hd : 0 < d)
    (z : (associatedModuleSheaf 𝒮 (twistedGlobalSectionsGrading 𝒮 E)).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒮 f)))
    (n : ℕ) (s : twistedSectionsComponent 𝒮 E ((n * d : ℕ) : ℤ))
    (hz : ((associatedModuleSheafStandardOpenEquiv 𝒮 (twistedGlobalSectionsGrading 𝒮 E)
          hf hd z :
        GradedModuleDegreeZeroLocalization 𝒮 (twistedGlobalSectionsGrading 𝒮 E) f) :
        LocalizedModule.Away f (twistedGlobalSections 𝒮 E)) =
      LocalizedModule.mk (S := Submonoid.powers f)
        (DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 E m) ((n * d : ℕ) : ℤ) s)
        ⟨f ^ n, by exact ⟨n, rfl⟩⟩) :
    chartHom 𝒮 F hF hf hd
        ((associatedModuleSheafMap 𝒮 (twistedGlobalSectionsGrading 𝒮 E)
            (twistedGlobalSectionsGrading 𝒮 F) (twistedSectionsLinearMap 𝒮 hE hF ψ)
            (twistedSectionsMap_mem_grading 𝒮 ψ)).val.app
          (op (ProjectiveSpectrum.basicOpen 𝒮 f)) z) =
      ψ.val.app (op (ProjectiveSpectrum.basicOpen 𝒮 f)) (chartHom 𝒮 E hE hf hd z) := by
  refine (bijective_mulTrivSection 𝒮 hf (n : ℤ) F
    (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f))).1 ?_
  refine Eq.trans (mulTrivSection_chartHom_of 𝒮 F hF hf hd _ n _
    (standardOpenEquiv_associatedModuleSheafMap_mk 𝒮 hE hF ψ hf hd z n s hz)) ?_
  refine Eq.trans ?_ (twistSheafMap_mulTrivSection 𝒮 hf (n : ℤ) ψ
    (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f)) (chartHom 𝒮 E hE hf hd z))
  refine Eq.trans ?_ (congrArg ((twistSheafMap 𝒮 ψ ((n : ℤ) * d)).val.app
      (op (ProjectiveSpectrum.basicOpen 𝒮 f)))
    (mulTrivSection_chartHom_of 𝒮 E hE hf hd z n s hz).symm)
  exact (PresheafOfModules.naturality_apply (twistSheafMap 𝒮 ψ ((n : ℤ) * d)).val
    (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒮 f ≤ ⊤)).op s).symm

/-- The chart comparisons of `ℰ` and of `ℱ` commute with `ψ`, for a section whose numerator is
given as a homogeneous element. -/
private theorem chartHom_naturality_of_mem (hE : IsTwistedSectionsSMul 𝒮 E)
    (hF : IsTwistedSectionsSMul 𝒮 F) (ψ : E ⟶ F) (hf : f ∈ 𝒮 d) (hd : 0 < d)
    (z : (associatedModuleSheaf 𝒮 (twistedGlobalSectionsGrading 𝒮 E)).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒮 f)))
    (n : ℕ) (x : twistedGlobalSections 𝒮 E)
    (hx : x ∈ twistedGlobalSectionsGrading 𝒮 E ((n * d : ℕ) : ℤ))
    (hz : ((associatedModuleSheafStandardOpenEquiv 𝒮 (twistedGlobalSectionsGrading 𝒮 E)
          hf hd z :
        GradedModuleDegreeZeroLocalization 𝒮 (twistedGlobalSectionsGrading 𝒮 E) f) :
        LocalizedModule.Away f (twistedGlobalSections 𝒮 E)) =
      LocalizedModule.mk (S := Submonoid.powers f) x ⟨f ^ n, by exact ⟨n, rfl⟩⟩) :
    chartHom 𝒮 F hF hf hd
        ((associatedModuleSheafMap 𝒮 (twistedGlobalSectionsGrading 𝒮 E)
            (twistedGlobalSectionsGrading 𝒮 F) (twistedSectionsLinearMap 𝒮 hE hF ψ)
            (twistedSectionsMap_mem_grading 𝒮 ψ)).val.app
          (op (ProjectiveSpectrum.basicOpen 𝒮 f)) z) =
      ψ.val.app (op (ProjectiveSpectrum.basicOpen 𝒮 f)) (chartHom 𝒮 E hE hf hd z) := by
  obtain ⟨s, rfl⟩ := exists_of_mem_grading 𝒮 E hx
  exact chartHom_naturality_of_fraction 𝒮 hE hF ψ hf hd z n s hz

/-- **The chart comparisons are natural in the sheaf.** On the chart `D₊(f)`, the chart
comparison of `ℱ` after the map `M̃_ℰ ⟶ M̃_ℱ` that `ψ` induces agrees with `ψ` after the chart
comparison of `ℰ`: both send the fraction `x / f ^ n` to the restriction of the degree-`n d`
component of `ψ x`, divided by `f ^ n`. -/
theorem chartHom_naturality (hE : IsTwistedSectionsSMul 𝒮 E) (hF : IsTwistedSectionsSMul 𝒮 F)
    (ψ : E ⟶ F) (hf : f ∈ 𝒮 d) (hd : 0 < d)
    (z : (associatedModuleSheaf 𝒮 (twistedGlobalSectionsGrading 𝒮 E)).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒮 f))) :
    chartHom 𝒮 F hF hf hd
        ((associatedModuleSheafMap 𝒮 (twistedGlobalSectionsGrading 𝒮 E)
            (twistedGlobalSectionsGrading 𝒮 F) (twistedSectionsLinearMap 𝒮 hE hF ψ)
            (twistedSectionsMap_mem_grading 𝒮 ψ)).val.app
          (op (ProjectiveSpectrum.basicOpen 𝒮 f)) z) =
      ψ.val.app (op (ProjectiveSpectrum.basicOpen 𝒮 f)) (chartHom 𝒮 E hE hf hd z) := by
  obtain ⟨n, x, hx, hz⟩ := exists_fraction 𝒮 E hf hd z
  exact chartHom_naturality_of_mem 𝒮 hE hF ψ hf hd z n x hx hz

end Naturality

/-! ### Tag 0B5I's functoriality, with the local maps supplied -/

section Functoriality

open Stacks.AlgebraicGeometry.ProjTwistComparison (PositiveElem positiveBasicOpen
  twistedGlobalSectionsAssociatedSheafMap)

variable {E F : SheafOfModules.{u} (projRingSheaf 𝒮)}
  (DE : TwistedGlobalSectionsModule 𝒮 E) (DF : TwistedGlobalSectionsModule 𝒮 F)

/-- **The local comparison maps of Tag 0B5I are natural in the sheaf.** This is the `hnat` that
`Stacks.AlgebraicGeometry.ProjTwistComparison.comparison_naturality` takes as a hypothesis. -/
theorem localComparison_naturality (ψ : E ⟶ F) (p : PositiveElem 𝒮)
    (s : (twistedGlobalSectionsAssociatedSheaf 𝒮 E DE).val.obj
      (op (positiveBasicOpen 𝒮 p))) :
    localComparison 𝒮 F DF p
        ((twistedGlobalSectionsAssociatedSheafMap 𝒮 DE DF ψ).val.app
          (op (positiveBasicOpen 𝒮 p)) s) =
      ψ.val.app (op (positiveBasicOpen 𝒮 p)) (localComparison 𝒮 E DE p s) := by
  let := DE.moduleInst
  let := DE.gradedSMul
  let := DF.moduleInst
  let := DF.gradedSMul
  exact chartHom_naturality 𝒮 (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 E DE)
    (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 F DF) ψ
    p.2.choose_spec.2 p.2.choose_spec.1 s

/-- **Tag 0B5I: the comparison morphism is functorial in `ℱ`.** For a morphism `ψ : ℰ ⟶ ℱ` of
modules on `Proj 𝒮`, the square

`M̃_ℰ ⟶ M̃_ℱ ⟶ ℱ  =  M̃_ℰ ⟶ ℰ ⟶ ℱ`

commutes, where the horizontal maps `M̃ ⟶ ℱ` are the comparison morphisms of
`Stacks.AlgebraicGeometry.ProjTwistIntegerComparison.integerComparison` and `M̃_ℰ ⟶ M̃_ℱ` is the
map on associated sheaves induced by `ψ`.

Nothing is hypothesised: the local maps are the chart comparisons constructed in this file, and
their naturality is `localComparison_naturality`. -/
theorem integerComparison_naturality (ψ : E ⟶ F) :
    twistedGlobalSectionsAssociatedSheafMap 𝒮 DE DF ψ ≫ integerComparison 𝒮 F DF =
      integerComparison 𝒮 E DE ≫ ψ :=
  Stacks.AlgebraicGeometry.ProjTwistComparison.comparison_naturality 𝒮 DE DF ψ
    (localComparison 𝒮 E DE) (localComparison_restrict 𝒮 E DE)
    (localComparison 𝒮 F DF) (localComparison_restrict 𝒮 F DF)
    (localComparison_naturality 𝒮 DE DF ψ)

end Functoriality

end Stacks.AlgebraicGeometry.ProjTwistIntegerComparison

end
