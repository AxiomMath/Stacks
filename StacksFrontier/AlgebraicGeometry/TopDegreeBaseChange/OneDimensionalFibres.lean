module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsHypotheses
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StalkVanishingCohomology

/-!
# Tag 0E7H for a proper morphism with one-dimensional fibres

[Stacks, Tag 0E7H] fixes a proper morphism `f : X ⟶ Y` with `dim(X_y) ≤ 1` and
`H¹(X_y, 𝒪_{X_y}) = 0` for every `y ∈ Y`, and a quasi-coherent `ℱ` on `X`, and asserts

1. `Rᵖ f_* ℱ = 0` for `p > 1`,
2. `R¹ f_* ℱ = 0` if there is a surjection `f^*𝒢 ⟶ ℱ` with `𝒢` quasi-coherent on `Y`,

and, when `Y` is affine,

3. `Hᵖ(X, ℱ) = 0` for `p ∉ {0, 1}`,
4. `H¹(X, ℱ) = 0` if `ℱ` is globally generated.

The source derives (1) from [Stacks, Tag 0E7D] at `d = 1`, then (3) from (1), then (4) from (3)
together with `H¹(X, 𝒪_X) = 0` — which it gets from [Stacks, Tag 0E7G] — and finally (2) from
(4) by localizing on `Y`.

This file carries out those derivations. The two inputs the source uses and which this
development does not have are carried as hypotheses, in the exact shape in which the rest of this
directory already carries them:

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.CohomologyVanishesAboveOne` is literally the
  hypothesis `hcoh` of `exists_isAffineOpen_vanishing_of_cohomology_vanishing` specialised to
  `d = 1`, i.e. the residue of [Stacks, Tag 0E7D] at fibre dimension one. `ZeroDimensionalFibres`
  discharges the same hypothesis at `d = 0`; the implementation notes say why `d = 1` is out of
  reach here.
* `H¹(X, 𝒪_X) = 0` over the affine base, which is the conclusion of [Stacks, Tag 0E7G] and is
  *not* derived here.

What is proved is the whole of the source's own argument from those two inputs, and in particular
its last paragraph — the long exact sequence of a presentation by global generators together with
the commutation of `H¹(X, -)` with direct sums — which is new in this development and is also the
entire proof of [Stacks, Tag 0B4X] (2).

## Main results

All in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `CohomologyVanishesAboveOne`: the residue of [Stacks, Tag 0E7D] at `d = 1`, as a `Prop`.
* `isZero_cohomology_of_affine_of_fiber_dimension_le_one`: part (3) of [Stacks, Tag 0E7H].
* `isZero_rightDerivedPlus_pushforward_of_fiber_dimension_le_one`: part (1).
* `isZero_rightDerived_of_isColimit_cofan` and `isZero_rightDerived_free_of_isZero_unit`:
  `Hᵖ(X, ⨁_{i ∈ I} 𝒪_X) = 0` whenever `Hᵖ(X, 𝒪_X) = 0`, by [Stacks, Tag 01FF] in its direct-sum
  form.
* `isZero_rightDerivedPlus_one_of_shortExact`: the one degree of the long exact sequence the
  source's last paragraph uses.
* `isZero_rightDerivedPlus_one_of_generatingSections`: that last paragraph, for an arbitrary
  quasi-compact quasi-separated scheme.
* `isZero_cohomology_one_of_generatingSections_of_fiber_dimension_le_one`: part (4).

## Implementation notes

Cohomology is `Hⁱ(X, ℱ) = ((moduleGlobalSections X).rightDerivedPlus i).obj ℱ`, the model used
throughout `StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/`, and higher direct images are
`((Scheme.Modules.pushforward f).rightDerivedPlus p).obj ℱ`. Mathlib's `ℕ`-indexed
`CategoryTheory.Functor.rightDerived` appears only inside proofs, because the two inputs the long
exact sequence step needs — direct sums through
`preservesColimitsOfShape_discrete_rightDerived_moduleGlobalSections`, and
`exact_and_epi_map_rightDerived_of_isZero` — are stated for it; the two indexings are compared by
`Stacks.DerivedIndexing.rightDerivedIso`. No other model of cohomology occurs.

"Globally generated" is Mathlib's `SheafOfModules.GeneratingSections`: a family of global
sections whose induced morphism out of `SheafOfModules.free` is an epimorphism. Since
`SheafOfModules.free` is a coproduct of copies of `SheafOfModules.unit`, that morphism is exactly
the surjection `⨁_{i ∈ I} 𝒪_X ⟶ ℱ` the source's last paragraph starts from.

The short exact sequence `0 → ker σ.π → ⨁_{i ∈ I} 𝒪_X → ℱ → 0` is built by hand from
`CategoryTheory.Limits.kernelIsKernel` rather than taken as
`CategoryTheory.ShortComplex.kernelSequence`, so that its three objects are the *syntactic*
`kernel σ.π`, `SheafOfModules.free σ.I` and `ℱ`; with `kernelSequence` they are projections of a
non-exposed definition and no longer unify with the hypotheses.

**Part (2) of the tag is not proved here**, and no `@[stacks 0E7H]` attribute is attached to
anything. Beyond part (4), which is available above, part (2) needs two further facts not found
in this development: that a quasi-coherent module on an affine scheme is globally generated, and
that the pullback of a free module sheaf is free.

**`d = 1` is not dischargeable here**, which is why `CohomologyVanishesAboveOne` is a hypothesis
and not a theorem. `ZeroDimensionalFibres.lean` discharges the `d = 0` case by Zariski's main
theorem, a route specific to `d = 0`. For `d = 1` the source goes through [Stacks, Tag 02V7],
whose proof needs three inputs. Two of them are available unconditionally, and only the third
blocks the route.

* Grothendieck vanishing on the Noetherian space underlying the fibre, [Stacks, Tag 02UZ]. For
  abelian sheaves this is
  `Stacks.CohomologyVanishing.subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le`; in the
  spelling used here — modules, and the derived functors of `moduleGlobalSections` — it is
  `Stacks.CohomologyVanishing`'s
  `isZero_rightDerivedPlus_moduleGlobalSections_of_noetherianSpace_of_dim_le` in
  `StacksFrontier/AlgebraicGeometry/Spaces/ModuleVanishingAboveTheDimension.lean`, together with
  the closed-immersion form `isZero_rightDerivedPlus_pushforward_of_noetherianSpace_of_dim_le`
  there, which is the shape the source's argument on the infinitesimal neighbourhoods of the
  fibre consumes.
* The coherence of the higher direct images of a proper morphism, [Stacks, Tag 02O5]. This **is**
  in this development, unconditionally: `AlgebraicGeometry.ProperCoherenceWitness`'s
  `higherDirectImageIsCoherent` and `isCoherent_pushforward` in
  `StacksFrontier/AlgebraicGeometry/ProperCoherenceWitness/ChowStalk.lean`, together with
  [Stacks, Tag 02O6] as `moduleFinite_cohomology` there.
* The theorem on formal functions, [Stacks, Tag 02OD]. This is what is missing, and the
  library's chain towards it is a tower of conditional statements:
  `Stacks.Cohomology.FormalFunctions.formalFunctionsEquiv` proves [Stacks, Tag 02OC] granted
  [Stacks, Tag 02OB]; `exists_uniform_bound_cohomology_idealPowerQuotient` proves that granted
  [Stacks, Tag 02OA]; `exists_uniform_bound_cohomology` proves that granted [Stacks, Tag 02O8];
  and `isCohomologyReesFinite_of_isCoherent` proves that granted [Stacks, Tag 0897] part (1).
  That last one, `Stacks.AlgebraicGeometry.GradedProperCohomology`'s
  `moduleFinite_gradedCohomologySum`, is no longer conditional: [Stacks, Tags 01LX and 01SB] are
  now available in a form that builds `X'` together with its coherent `F'`, by
  `…GradedProperCohomology.exists_isCoherent_pushforward_baseChange_iso_intCoprod`. What stands
  between it and `h0897` is the `B`-action — the existing theorem transports one from
  `Hᵖ(X', F')` along [Stacks, Tag 089W], while `h0897` asks for the degreewise one of
  `Stacks.Cohomology.FormalFunctions.cohomologyGradedModule` — and the graded algebra the two
  are stated over, `f^* B̃` against `⨁ₙ ℐⁿ`. The base change is not carried as binders,
  and the shape of the finite-type hypothesis is no obstruction: `h0897`'s antecedent is
  `Stacks.Coherent.IsFiniteTypeOnAffine`, exactly what part (1) consumes. The chain
  stops there, not at 02O5.

**The theorem on formal functions is not the only route to [Stacks, Tag 02V7], and what the
other route still needs.** The source uses [Stacks, Tag 02OD] to turn the vanishing of
`Hᵖ(X_n, ℱ_n)` on the infinitesimal neighbourhoods of a fibre into the vanishing of the completed
stalk `(Rᵖ f_* ℱ)^∧_y`, and then applies Nakayama's lemma. Over an affine base the conclusion
Nakayama consumes — `Hᵖ(X, ℱ) = 𝔪 · Hᵖ(X, ℱ)` — follows instead from the acyclicity of the
*single* quotient `ℱ/𝔪ℱ` together with one degree of vanishing on a kernel, with no completion
and no inverse system: `IdealMultiplesCohomology.lean`'s `top_le_smul_top_rightDerived` and
`isZero_rightDerived_of_isZero_cokernel` are that step, unconditionally. Its two inputs stand as
follows.

* The vanishing of `Hᵖ⁺¹` on the auxiliary kernel is reachable by descending induction on the
  degree: `AlgebraicGeometry.exists_isZero_rightDerived_moduleGlobalSections_of_isProper` of
  `StacksFrontier/AlgebraicGeometry/CohomologyFinitenessNoetherian/Basic.lean` gives, with no
  Noetherian and no dimension hypothesis, a degree beyond which `Hᵖ` kills every quasi-coherent
  module on a scheme proper over an affine base, so the induction starts. The finiteness
  Nakayama needs is [Stacks, Tag 02O6], `…ProperCoherenceWitness.moduleFinite_cohomology`, and
  the passage from coherent back to quasi-coherent modules inside the induction is
  `isZero_rightDerivedPlus_moduleGlobalSections_of_forall_isCoherent` of
  `FinitePresentationSuffices.lean`.
* What is **not** available is the acyclicity of `ℱ/𝔪ℱ` above the fibre dimension. That module
  is quasi-coherent and killed by `𝔪`, so its stalks vanish off the fibre, but the library's
  Grothendieck vanishing in this spelling,
  `Stacks.CohomologyVanishing.isZero_rightDerived_pushforward_of_noetherianSpace_of_dim_le`,
  asks for a *pushforward along a closed immersion* rather than for a bound on the support.
  Closing that gap means either identifying `ℱ/𝔪ℱ` with `i_* i^* ℱ` for `i` the fibre — for
  which [Stacks, Tag 08M3] is proved at the level of ringed topoi, as
  `Stacks.Sheaves.PushforwardEssentialImage.essImage_pushforwardModules_iff_of_isClosedImmersion`,
  what is missing being the bridge from a closed immersion of schemes to it together with the
  identification of the sectionwise kernel of `i^♯` with the ideal generated by `𝔪` — or proving
  Grothendieck vanishing for an abelian sheaf whose support lies in a closed subset of bounded
  dimension, whose topological criterion is
  `Stacks.ClosedImmersion.essImage_closedInclusionPushforward_iff_support_subset`.

The fully general `CohomologyVanishesAboveOne` also quantifies over an **arbitrary** affine base,
not a Noetherian one, and over quasi-coherent rather than coherent modules.
`FinitePresentationSuffices.lean` carries out the reduction to modules of finite presentation;
the source's two further limit reductions — to a morphism of finite presentation and to a
Noetherian base — are separate, and are also absent.

## References

* [Stacks Project, Tag 0E7H](https://stacks.math.columbia.edu/tag/0E7H)
* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
* [Stacks Project, Tag 0E7G](https://stacks.math.columbia.edu/tag/0E7G)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard

noncomputable section

/-- **The residue of [Stacks, Tag 0E7D] at fibre dimension one.** A proper morphism onto an
affine scheme all of whose fibres have dimension at most one has vanishing cohomology of
quasi-coherent modules in every degree above one.

This is the hypothesis `hcoh` of `exists_isAffineOpen_vanishing_of_cohomology_vanishing` and of
`isZero_stalk_rightDerivedPlus_of_cohomology_vanishing` at `d = 1`. -/
abbrev CohomologyVanishesAboveOne : Prop :=
  ∀ {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀), IsProper g → IsAffine Y₀ →
    (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞)) →
    ∀ i : ℤ, ((1 : ℕ) : ℤ) < i → ∀ F : X₀.Modules, F.IsQuasicoherent →
      IsZero (((moduleGlobalSections X₀).rightDerivedPlus i).obj F)

/-- **[Stacks, Tag 0E7H] part (3).** For a proper morphism onto an affine scheme all of whose
fibres have dimension at most one, the cohomology of a quasi-coherent module vanishes outside
degrees `0` and `1`.

The source deduces this from part (1) together with the quasi-coherence of the higher direct
images; here it is the hypothesis `hcoh` read at the morphism `f` itself, the two statements
being interchangeable over an affine base by
`isZero_cohomology_iff_isZero_rightDerivedPlus_pushforward`. -/
theorem isZero_cohomology_of_affine_of_fiber_dimension_le_one
    (hcoh : CohomologyVanishesAboveOne.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    [IsAffine Y] (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (F : X.Modules) [F.IsQuasicoherent] (p : ℤ) (hp : 1 < p) :
    IsZero (((moduleGlobalSections X).rightDerivedPlus p).obj F) :=
  hcoh f ‹IsProper f› ‹IsAffine Y› hdim p (by exact_mod_cast hp) F ‹F.IsQuasicoherent›

/-- **[Stacks, Tag 0E7H] part (1).** For a proper morphism all of whose fibres have dimension at
most one, the higher direct images of a quasi-coherent module vanish above degree one.

A sheaf of modules on a scheme is a zero object as soon as all its stalks are
(`AlgebraicGeometry.isZero_of_forall_isZero_stalk`), and the stalks of `Rᵖ f_* ℱ` are killed by
`isZero_stalk_rightDerivedPlus_of_cohomology_vanishing` at `d = 1`, which is part (1) of
[Stacks, Tag 0E7D] granted the vanishing over an affine base. -/
theorem isZero_rightDerivedPlus_pushforward_of_fiber_dimension_le_one
    (hcoh : CohomologyVanishesAboveOne.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (F : X.Modules) [F.IsQuasicoherent] (p : ℤ) (hp : 1 < p) :
    IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F) :=
  AlgebraicGeometry.isZero_of_forall_isZero_stalk _ fun y =>
    isZero_stalk_rightDerivedPlus_of_cohomology_vanishing f y 1 (hdim y) hcoh F p
      (by exact_mod_cast hp)

/-- **The cohomology of a coproduct of copies of a single module.** On a quasi-compact
quasi-separated scheme, if `Hᵖ(X, 𝒩) = 0` and `𝑐` exhibits an object as a coproduct of copies of
`𝒩`, then `Hᵖ` of that object vanishes.

`preservesColimitsOfShape_discrete_rightDerived_moduleGlobalSections` — which is
[Stacks, Tag 01FF] in its direct-sum form — says that `Hᵖ(X, -)` preserves coproducts, so the
image of `𝑐` is again a colimit cofan, and a cofan all of whose legs start at a zero object has a
zero point. -/
theorem isZero_rightDerived_of_isColimit_cofan (X : Scheme.{u})
    [CompactSpace (X : Type u)] [QuasiSeparatedSpace (X : Type u)] (q : ℕ) {I : Type u}
    {N : X.Modules} (c : Cofan fun _ : I => N) (hc : IsColimit c)
    (h : IsZero (((moduleGlobalSections X).rightDerived q).obj N)) :
    IsZero (((moduleGlobalSections X).rightDerived q).obj c.pt) := by
  have hpres : PreservesColimitsOfShape (Discrete I)
      ((moduleGlobalSections X).rightDerived q) :=
    preservesColimitsOfShape_discrete_rightDerived_moduleGlobalSections X q I
  have : PreservesColimit (Discrete.functor fun _ : I => N)
      ((moduleGlobalSections X).rightDerived q) := hpres.preservesColimit
  have hc' : IsColimit (((moduleGlobalSections X).rightDerived q).mapCocone c) :=
    isColimitOfPreserves _ hc
  exact (IsZero.iff_id_eq_zero _).2 (hc'.hom_ext fun _ => h.eq_of_src _ _)

/-- **The cohomology of a direct sum of copies of the structure sheaf.** On a quasi-compact
quasi-separated scheme, if `Hᵖ(X, 𝒪_X) = 0` then `Hᵖ(X, ⨁_{i ∈ I} 𝒪_X) = 0` for every index type
`I`.

This is the appeal to [Stacks, Tag 01FF] in the last sentence of the proof of
[Stacks, Tag 0E7H] — *"`H¹(X, -)` commutes with direct sums"* — at `SheafOfModules.free`, which
`SheafOfModules.isColimitFreeCofan` exhibits as a coproduct of copies of
`SheafOfModules.unit`. -/
theorem isZero_rightDerived_free_of_isZero_unit (X : Scheme.{u})
    [CompactSpace (X : Type u)] [QuasiSeparatedSpace (X : Type u)] (q : ℕ) (I : Type u)
    (h : IsZero (((moduleGlobalSections X).rightDerived q).obj
      (SheafOfModules.unit X.ringCatSheaf))) :
    IsZero (((moduleGlobalSections X).rightDerived q).obj
      (SheafOfModules.free (R := X.ringCatSheaf) I)) :=
  isZero_rightDerived_of_isColimit_cofan X q (SheafOfModules.freeCofan (R := X.ringCatSheaf) I)
    (SheafOfModules.isColimitFreeCofan I) h

/-- Vanishing of `Hⁿ(X, 𝒩)` is the same in the `ℕ`-indexed and the `ℤ`-indexed models. -/
private theorem isZero_rightDerived_iff_rightDerivedPlus (X : Scheme.{u}) (q : ℕ)
    {N : X.Modules} :
    IsZero (((moduleGlobalSections X).rightDerived q).obj N) ↔
      IsZero (((moduleGlobalSections X).rightDerivedPlus (q : ℤ)).obj N) :=
  ⟨fun h => IsZero.of_iso h ((Stacks.DerivedIndexing.rightDerivedIso _ q).app N).symm,
    fun h => IsZero.of_iso h ((Stacks.DerivedIndexing.rightDerivedIso _ q).app N)⟩

/-- **One degree of the long exact sequence, in the form the source's last paragraph uses it.**
For a short exact sequence `0 → 𝒜 → ℬ → 𝒞 → 0` of module sheaves on a scheme, if
`H¹(X, ℬ) = 0` and `H²(X, 𝒜) = 0` then `H¹(X, 𝒞) = 0`.

The vanishing of `H²(X, 𝒜)` makes `H¹(X, ℬ) ⟶ H¹(X, 𝒞)` an epimorphism — this is
`exact_and_epi_map_rightDerived_of_isZero`, which reads one degree of right exactness off one
degree of vanishing — and an epimorphism out of a zero object has a zero target. -/
theorem isZero_rightDerivedPlus_one_of_shortExact {X : Scheme.{u}}
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (hX₂ : IsZero (((moduleGlobalSections X).rightDerivedPlus 1).obj S.X₂))
    (hX₁ : IsZero (((moduleGlobalSections X).rightDerivedPlus 2).obj S.X₁)) :
    IsZero (((moduleGlobalSections X).rightDerivedPlus 1).obj S.X₃) := by
  have hX₁' : IsZero (((moduleGlobalSections X).rightDerivedPlus (((1 : ℕ) : ℤ) + 1)).obj S.X₁) :=
    hX₁
  obtain ⟨-, hepi⟩ :=
    exact_and_epi_map_rightDerived_of_isZero (moduleGlobalSections X) hS 1 hX₁'
  exact (isZero_rightDerived_iff_rightDerivedPlus X 1).1
    (IsZero.of_epi (((moduleGlobalSections X).rightDerived 1).map S.g)
      ((isZero_rightDerived_iff_rightDerivedPlus X 1).2 hX₂))

/-- **The last paragraph of the proof of [Stacks, Tag 0E7H].** Let `X` be a quasi-compact
quasi-separated scheme and let `ℱ` be a module sheaf generated by a family `σ` of global
sections, so that `σ.π : ⨁_{i ∈ σ.I} 𝒪_X ⟶ ℱ` is an epimorphism. If `H¹(X, 𝒪_X) = 0` and `H²`
vanishes on every quasi-coherent module, then `H¹(X, ℱ) = 0`.

The sequence `0 → ker σ.π → ⨁_{i ∈ σ.I} 𝒪_X → ℱ → 0` is short exact, so
`isZero_rightDerivedPlus_one_of_shortExact` applies; its hypothesis on the middle term is
`isZero_rightDerived_free_of_isZero_unit`, and its hypothesis on the left-hand term is `h₂`,
whose side condition is met because the kernel of a morphism between quasi-coherent modules is
quasi-coherent — `SheafOfModules.free` being locally free, hence quasi-coherent.

The vanishing of `H²` is asked for as a statement about all quasi-coherent modules rather than
about `ker σ.π` alone. The reason is the two spellings `Scheme.Modules X` and
`SheafOfModules X.ringCatSheaf` of one category: they carry different `HasKernel` instances, so
a `kernel σ.π` written in a statement about `X.Modules` and the one `ObjectProperty.prop_kernel`
produces are two terms that instance search will not match, and a hypothesis naming the kernel
could only be used by a caller who happened to write it in the same spelling.

This is also the entire proof of [Stacks, Tag 0B4X] (2), where `H¹(X, 𝒪_X) = 0` holds because the
base has a rational singularity rather than by [Stacks, Tag 0E7G]. -/
theorem isZero_rightDerivedPlus_one_of_generatingSections {X : Scheme.{u}}
    [CompactSpace (X : Type u)] [QuasiSeparatedSpace (X : Type u)] (F : X.Modules)
    [F.IsQuasicoherent] (σ : SheafOfModules.GeneratingSections F)
    (hunit : IsZero (((moduleGlobalSections X).rightDerivedPlus 1).obj
      (SheafOfModules.unit X.ringCatSheaf)))
    (h₂ : ∀ G : X.Modules, G.IsQuasicoherent →
      IsZero (((moduleGlobalSections X).rightDerivedPlus 2).obj G)) :
    IsZero (((moduleGlobalSections X).rightDerivedPlus 1).obj F) := by
  have hfree : IsZero (((moduleGlobalSections X).rightDerivedPlus 1).obj
      (SheafOfModules.free (R := X.ringCatSheaf) σ.I)) :=
    (isZero_rightDerived_iff_rightDerivedPlus X 1).1
      (isZero_rightDerived_free_of_isZero_unit X 1 σ.I
        ((isZero_rightDerived_iff_rightDerivedPlus X 1).2 hunit))
  have hS : (ShortComplex.mk (kernel.ι σ.π) σ.π (kernel.condition σ.π)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel σ.π))
      (mono_of_isLimit_fork (c := Fork.ofι _ _) (kernelIsKernel σ.π)) σ.epi
  have hqc : (kernel σ.π).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_kernel σ.π inferInstance
      ‹F.IsQuasicoherent›
  exact isZero_rightDerivedPlus_one_of_shortExact hS hfree (h₂ _ hqc)

/-- **[Stacks, Tag 0E7H] part (4).** Let `f : X ⟶ Y` be proper with `Y` affine and all fibres of
dimension at most one, and let `ℱ` be a globally generated quasi-coherent module on `X` with
`H¹(X, 𝒪_X) = 0`. Then `H¹(X, ℱ) = 0`.

This is `isZero_rightDerivedPlus_one_of_generatingSections` with its hypothesis on the degree-two
cohomology of quasi-coherent modules discharged by part (3). -/
theorem isZero_cohomology_one_of_generatingSections_of_fiber_dimension_le_one
    (hcoh : CohomologyVanishesAboveOne.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    [IsAffine Y] (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hunit : IsZero (((moduleGlobalSections X).rightDerivedPlus 1).obj
      (SheafOfModules.unit X.ringCatSheaf)))
    (F : X.Modules) [F.IsQuasicoherent] (σ : SheafOfModules.GeneratingSections F) :
    IsZero (((moduleGlobalSections X).rightDerivedPlus 1).obj F) := by
  have _ : CompactSpace (X : Type u) := QuasiCompact.compactSpace_of_compactSpace f
  have _ : QuasiSeparatedSpace (X : Type u) := quasiSeparatedSpace_of_quasiSeparated f
  exact isZero_rightDerivedPlus_one_of_generatingSections F σ hunit
    fun G hG => hcoh f ‹IsProper f› ‹IsAffine Y› hdim 2 (by norm_num) G hG

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
