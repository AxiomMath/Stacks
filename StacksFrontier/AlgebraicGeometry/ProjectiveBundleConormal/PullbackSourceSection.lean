module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.AffineGenerators
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartConormalTarget
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartTwistProduct
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.IdealSheafLiftSection
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.PullbackTautologicalSection
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.RestrictTensorSection

/-!
# The conormal map of Tag 0B3V clause 3 on a product section

`Stacks.ProjectiveBundleConormal.restrictConormalSourceIsoTilde_inv_unit_toOpen` reads the
generator of the chart computation of [Stacks, Tag 0B3V] clause 3 as a *product* section
`k ⊗ s̄^{⊗ -1}` of `ker(q) ⊗ 𝓛^{⊗ -1}` over the chart. **This file applies the clause's map to
such a section.**

The map is `σ^*` of `Stacks.ProjectiveBundleConormal.idealSheafLift`, read through
`Stacks.ProjectiveBundleConormal.pullbackSourceIso`, and the computation has to happen on
`𝐏(ℰ)` and not after `σ^*`: the lift is pinned by `kernel.ι` being a monomorphism and `σ^*`
destroys that, so `Stacks.ProjectiveBundleConormal.conormalCanonicalMap_comp_ι` says only that a
composite vanishes —
`Stacks.ProjectiveBundleConormal.pullback_kernelTautologicalMapTwisted_eq_zero` — and determines
nothing. So the product section is carried *up* to `π⁻¹W` by
`Stacks.ProjectiveBundleConormal.pullbackSourceIso` inverse, the lift is computed there by
`Stacks.ProjectiveBundleConormal.idealSheafLift_val_app_eq_of_ι`, and the result comes back down
as `AlgebraicGeometry.Scheme.Modules.pullbackSection`.

## Main results

* `Stacks.ProjectiveBundleConormal.pullbackSectionNatIso_hom_app_val_app`: the collapse
  `F ≅ σ^*π^*F` on a section, in the form
  `Stacks.ProjectiveBundleConormal.pullbackSourceIso` uses it.
* `Stacks.ProjectiveBundleConormal.pullbackSourceIso_inv_tensorSectionsAt`: **the identification
  of the clause's source, inverted, on a product section.** The section determined by `κ` and `w`
  goes to the pullback along `σ` of the section of `(π^*ker q) ⊗ 𝒪(-1)` over an open `V` of
  `𝐏(ℰ)` determined by the pullback of `κ` along `π`, restricted to `V`, and by whatever section
  of `𝒪(-1)` over `V` the base-change comparison carries `w` to.
* `Stacks.ProjectiveBundleConormal.conormalCanonicalMap_val_app_tensorSectionsAt`: **the clause's
  map on a product section.** It is the section of the conormal sheaf named, through
  `Stacks.CartierConormal.conormalSheafIsoPullbackSelf`, by the pullback along `σ` of the section
  of the ideal sheaf `ℐ(σ)` over `V` whose image in `𝒪_{𝐏(ℰ)}` is the value of the untwisted
  tautological map on that product section upstairs.
* `Stacks.ProjectiveBundleConormal.exists_conormalCanonicalMap_val_app_tensorSectionsAt`: **the
  same formula with that section produced rather than assumed**, its pin handed back as the
  scalar equation `ι y = v(π^*κ) · w₀`.
* `Stacks.ProjectiveBundleConormal.exists_conormalCanonicalMap_val_app_tensorSectionsAt_chart`:
  **the same formula on a chart with `hw` gone.** The open `V`, the section `w₀` and the
  base-change equation are all produced, the only hypothesis left on `w` being that it generate
  `𝓛^{⊗ -1}` over every open of `W`.
* `Stacks.ProjectiveBundleConormal`
  `.exists_conormalCanonicalMap_val_app_tensorSectionsAt_chart_unit`: **the chart formula with no
  hypothesis on `w` at all**, for the generator a trivialisation of `(𝓛^{⊗ -1})|_W` names — which
  is what `Stacks.ProjectiveBundleConormal.restrictInverseTwistIso` supplies on a chart.

## Implementation notes

The three parametrised results carry the base-change step as a *hypothesis* `hw`, and the upstairs
open `V` with it; `conormalCanonicalMap_val_app_tensorSectionsAt` carries the ideal-sheaf section
as a hypothesis `hy` too, and `exists_conormalCanonicalMap_val_app_tensorSectionsAt` is the
version that does not. The two `_chart` results at the end of the file carry neither: `hw` is a
theorem on a chart, and they instantiate `V` at
`Stacks.ProjectiveBundleConormal.tautologicalChart`.

**The upstairs open is a parameter, and has to be.** The section of `𝒪(-1)` that `hw` asks for
lives on an open `V` of `𝐏(ℰ)` with `V ≤ π⁻¹W` and `W ≤ σ⁻¹V`, not on the full preimage `π⁻¹W`.
Over the full preimage there is no such section but `0` once `ℰ` has rank at least two:
`π_*𝒪(-1) = 0`, because `Γ(𝐏^{r-1}_A, 𝒪(-1))` is the degree `-1` part of `A[x_1, …, x_r]`, which
is zero — on each standard open `D_+(x_i)` a section of degree `-1` is `g/x_i^n` with
`deg g = n - 1`, and for `r ≥ 2` the only element of `⋂_i A[x][1/x_i]` is a polynomial. So with
`π⁻¹W` in place of `V` the hypothesis would pin `w` to `0` instead of pinning the comparison, and
the chart computation of clause 3 — which applies these results at the *generator*
`s̄^{⊗ -1}` of `𝓛^{⊗ -1}|_W` produced by
`Stacks.ProjectiveBundleConormal.restrictConormalSourceIsoTilde_inv_unit_toOpen` — could never
instantiate them. On a chart of `𝐏(ℰ)` the twist is trivial and the section exists, which is why
`V` is free. The price is that the first factor's
`Stacks.AlgebraicGeometry.RelativeProjDegreeOne.unitSection`, which lives on `π⁻¹W`, appears
restricted to `V`; `Stacks.Conormal.pullbackSection_restrict_source` is what moves the pullback
of a section between the two opens.

The re-seated monoidal structure used here does not have the tensor product of two morphisms
as the action of the tensor bifunctor on a pair: `MonoidalCategory.tensorHom_def` splits it into
two whiskerings first, and only those are the bifunctor on a pair. So
`Stacks.ProjectiveBundleConormal.tensorSectionsAt_tensorIso_inv` goes through
`Stacks.ProjectiveBundleConormal.tensorSectionsAt_whiskerRight` and
`tensorSectionsAt_whiskerLeft` and not through
`Stacks.SheafOfModules.tensorSections_tensorMapAt` directly, because the direct route is a
type mismatch.

The tensor product of the two comparisons is kept at the `CategoryTheory.Iso` spelling
`i ⊗ᵢ j` rather than at `i.inv ⊗ₘ j.inv`. Writing the `⊗ₘ` spelling into the statement of
`Stacks.ProjectiveBundleConormal.pullbackSourceIso_inv` fails to synthesize
`MonoidalCategoryStruct (SheafOfModules X.ringCatSheaf)` — the problem described in the
implementation notes of `StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.Basic`: the
local instance is stated for `AlgebraicGeometry.Scheme.Modules`, which is a `def`, and the
elaborated type has unfolded it. At the `⊗ᵢ` spelling the instance is found and the split is a
`rfl`.

Nothing is rewritten; every split of a composite is named at the level of *morphisms*, where it
is a `rfl`, and only then read on a section through
`SheafOfModules.comp_val_app_apply`. See the implementation notes of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartRatio` for why no `rw` occurs on
this layer.

## Not done here

**The base-change comparison of the inverse twist is read on a section elsewhere, and `hw` is
discharged.** `Stacks.ProjectiveBundleConormal.inverseTwistBaseChangeIso` is
`Stacks.ProjBundleInverseBaseChange.inverseQuotientBaseChangeIso`, which is
`Stacks.TensorPowers.TensorInverse.invIso` applied to two tensor inverses of `σ^*𝒪(1)`, and
`Stacks.ProjBundleInverseBaseChange.invIso_inv_val_app` reads that comparison on a section: if
`a ⊗ b` pairs to `1` under the one inverse's right trivialisation and `b ⊗ w` pairs to `1` under
the other's left trivialisation, then the comparison carries `w` back to `a`. The substitution
`a = σ^*w₀`, `b = σ^*b₀` is carried out in
`Stacks.ProjBundleInverseBaseChange.inverseTwistBaseChangeIso_inv_val_app`, which is `hw` itself
given the two pairings. Both pairings
are discharged on a chart by
`Stacks.ProjectiveBundleConormal.exists_pullbackSection_inverseTwistBaseChangeIso_inv_val_app`
(`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartTwistProduct`), which is why this
file ends with `hw`-free chart formulas and imports that module.

The constraints of
`Stacks.SheafInternalHom.monoidalCategory` *do* have formulas on a product section, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalLocalizedSections` — all three of them,
both whiskerings, and the tensor product of two morphisms. And no comparison between those
constraints and the re-seated `Stacks.ProjectiveBundleConormal.monoidalSheafTensor` is needed or
wanted: `invIso_inv_val_app` stays inside the localized structure from end to end, and `hw` never
meets the re-seated one.

**The section of the ideal sheaf need not be supplied.**
`Stacks.ProjectiveBundleConormal.exists_conormalCanonicalMap_val_app_tensorSectionsAt` produces
it: `Stacks.ProjectiveBundleConormal.exists_idealSheaf_section_kernelTautologicalMapTwisted`
discharges `hy` over an arbitrary open of `𝐏(ℰ)`, because
`Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff` reduces the existence of
`y` to the scalar equation `σ.app V (ṽ z) = 0`, which is
`Stacks.ProjectiveBundleConormal.kernelTautologicalMapTwisted_comp_structureSheafUnit` read on a
section. So no ratio computation is needed to *exhibit* `y`, and no chart is needed either.

What the chart still owes is the identification of that `y` with the section the *target* side of
the clause names — by `Stacks.Conormal.Locality.idealSheaf_section_injective` a single equation
between sections of `𝒪_{𝐏(ℰ)}` over `V`, in which the image of `y` appears as
`Stacks.SheafOfModules.Invertible.sectionMulNegOne` of `v(π^*κ)` and `w₀`. That is the ratio
computation of `StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartRatio`, and it is not
done here.

**Everything else that the meeting of the two halves needs is now here.** The target half, in the
shape a generator computation can use, is
`Stacks.ProjectiveBundleConormal.restrictConormalIsoOfOpenFactor_trans_zeroSection_hom_unit_toOpen`
(`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartConormalTarget`), and it has to be
instantiated over the *tautological chart* rather than over `π⁻¹W`; the final section of this
file supplies its four pieces of input there —
`Stacks.ProjectiveBundleConormal.preimage_tautologicalChart`,
`Stacks.ProjectiveBundleConormal.tautologicalChartLift` with its open-immersion instance,
`Stacks.ProjectiveBundleConormal.isoSpec_comp_zeroSection_comp_tautologicalChartLift_comp_ι` and
`Stacks.ProjectiveBundleConormal.top_eq_preimage_tautologicalChartLift_preimage_ι`. With those,
the hypothesis `h` that
`Stacks.ProjectiveBundleConormal.isIso_conormalCanonicalMap_of_forall_exists_isIso_restrict`
reduces clause (b) to is one equation short, and the equation is the paragraph above.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjDegreeOne (unitSection)
open Stacks.ProjectiveBundleSplitting
open Stacks.SheafOfModules (tensorSectionsAt)
open Stacks.SymGraded

universe u

namespace Stacks.ProjectiveBundleConormal

attribute [local instance] monoidalSheafTensor

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
  (Q : Stacks.Divisors.InvertibleQuotient X E)
  {σ : X ⟶ (bundle E).scheme} (hσ : σ ≫ (bundle E).toBase = 𝟙 X)

/-- **The inverse of a tensor product of two isomorphisms, on a product section.** It acts
factorwise, by the inverses. `MonoidalCategory.tensorHom_def` splits the tensor product of two
morphisms into the two whiskerings, which is what the re-seated monoidal structure
computes on sections. -/
theorem tensorSectionsAt_tensorIso_inv {A A' B B' : X.Modules} (i : A ≅ A') (j : B ≅ B')
    (V : X.Opens) (z : A'.val.obj (op V)) (w : B'.val.obj (op V)) :
    (i ⊗ᵢ j).inv.val.app (op V)
        (tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op V) A' B' z w) =
      tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op V) A B
        (i.inv.val.app (op V) z) (j.inv.val.app (op V) w) := by
  refine Eq.trans (congrArg (fun φ : A' ⊗ B' ⟶ A ⊗ B =>
      φ.val.app (op V) (tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op V) A' B' z w))
    ((rfl : (i ⊗ᵢ j).inv = i.inv ⊗ₘ j.inv).trans
      (MonoidalCategory.tensorHom_def i.inv j.inv))) ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply (i.inv ▷ B') (A ◁ j.inv) (op V) _) ?_
  refine Eq.trans (congrArg (fun y : (A ⊗ B').val.obj (op V) => (A ◁ j.inv).val.app (op V) y)
    (tensorSectionsAt_whiskerRight i.inv B' V z w)) ?_
  exact tensorSectionsAt_whiskerLeft A j.inv V (i.inv.val.app (op V) z) w

include hσ in
/-- **The collapse `F ≅ σ^*π^*F` on a section**, at the spelling
`Stacks.ProjectiveBundleConormal.pullbackSourceIso` is built from: the natural isomorphism
`Stacks.ProjectiveBundleConormal.pullbackSectionNatIso` carries a section of `F` over `W` to the
pullback along `σ` of its pullback along `π`. This is
`Stacks.ProjectiveBundleConormal.pullbackSection_collapse` read through
`Stacks.ProjectiveBundleConormal.pullbackSectionNatIso_hom_app`. -/
theorem pullbackSectionNatIso_hom_app_val_app (F : X.Modules) (W : X.Opens)
    (s : F.val.obj (op W)) :
    ((pullbackSectionNatIso E hσ).hom.app F).val.app (op W) s =
      Scheme.Modules.pullbackSection σ
        ((Scheme.Modules.pullback (bundle E).toBase).obj F)
        ((bundle E).toBase ⁻¹ᵁ W) W (preimage_toBase_preimage E hσ W).ge
        (unitSection (bundle E).toBase F W s) :=
  (congrArg (fun φ : F ⟶ (Scheme.Modules.pullback σ).obj
      ((Scheme.Modules.pullback (bundle E).toBase).obj F) => φ.val.app (op W) s)
    (pullbackSectionNatIso_hom_app E hσ F)).trans
    (pullbackSection_collapse E hσ F W s).symm

include hσ in
/-- **The collapse `F ≅ σ^*π^*F` on a section, over an open of `𝐏(ℰ)` that need not be the whole
preimage.** For `V ≤ π⁻¹W` with `W ≤ σ⁻¹V` the pullback along `σ` may be taken from `V`, at the
restriction of the pullback of `s` along `π`.

This is `Stacks.ProjectiveBundleConormal.pullbackSectionNatIso_hom_app_val_app` moved along
`Stacks.Conormal.pullbackSection_restrict_source`. It is the form the formulas below use: `𝒪(-1)`
has no nonzero section on `π⁻¹W`, so the second factor's section has to be taken on a chart, and
then the first factor's has to be taken there too. -/
theorem pullbackSectionNatIso_hom_app_val_app_le (F : X.Modules) (W : X.Opens)
    (V : (bundle E).scheme.Opens) (hV : V ≤ (bundle E).toBase ⁻¹ᵁ W) (hWV : W ≤ σ ⁻¹ᵁ V)
    (s : F.val.obj (op W)) :
    ((pullbackSectionNatIso E hσ).hom.app F).val.app (op W) s =
      Scheme.Modules.pullbackSection σ
        ((Scheme.Modules.pullback (bundle E).toBase).obj F) V W hWV
        (((Scheme.Modules.pullback (bundle E).toBase).obj F).val.map (homOfLE hV).op
          (unitSection (bundle E).toBase F W s)) :=
  (pullbackSectionNatIso_hom_app_val_app E hσ F W s).trans
    (Stacks.Conormal.pullbackSection_restrict_source σ
      ((Scheme.Modules.pullback (bundle E).toBase).obj F)
      ((bundle E).toBase ⁻¹ᵁ W) V hV W hWV (unitSection (bundle E).toBase F W s))

variable (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L)

include hσ e in
/-- `Stacks.ProjectiveBundleConormal.pullbackSourceIso` inverted: the tensor product of the two
comparisons, then Tag 01CD. The composite is a single `CategoryTheory.Iso.trans`, so the split is
`rfl`; naming it as an equation of *morphisms* keeps the section formula below from having to
perform it inside a larger term. -/
theorem pullbackSourceIso_inv :
    (pullbackSourceIso E Q hσ e).inv =
      (((pullbackSectionNatIso E hσ).app (kernel Q.q)).symm ⊗ᵢ
          inverseTwistBaseChangeIso E Q e).inv ≫
        (pullbackTensorComparisonIso σ
          ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q))
          (inverseTautologicalTwist E)).inv :=
  rfl

include hσ e in
/-- **The identification of the source of the clause's map, inverted, on a product section.** The
section of `ker(q) ⊗ 𝓛^{⊗ -1}` over `W` determined by `κ` and `w` is the pullback along `σ` of
the section of `(π^*ker q) ⊗ 𝒪(-1)` over an open `V` of `𝐏(ℰ)` with `V ≤ π⁻¹W` and `W ≤ σ⁻¹V`
determined by the pullback of `κ` along `π`, restricted to `V`, and by `w₀`, *provided* the
base-change comparison of the inverse twist carries `w` to the pullback of `w₀` — which is the
hypothesis `hw`, and is what the library cannot yet supply (see the module's "Not done here").

The upstairs open is a parameter and not `π⁻¹W`: over the full preimage `𝒪(-1)` has no nonzero
section, so at `V = π⁻¹W` the hypothesis would force `w = 0`. See the module's implementation
notes.

Tag 01CD is `Stacks.ProjectiveBundleConormal.pullbackTensorComparison_inv_tensorSectionsAt`, the
first factor is `Stacks.ProjectiveBundleConormal.pullbackSectionNatIso_hom_app_val_app_le`, and
the tensor product of the two comparisons is
`Stacks.ProjectiveBundleConormal.tensorSectionsAt_tensorIso_inv`. -/
theorem pullbackSourceIso_inv_tensorSectionsAt (W : X.Opens)
    (V : (bundle E).scheme.Opens) (hV : V ≤ (bundle E).toBase ⁻¹ᵁ W) (hWV : W ≤ σ ⁻¹ᵁ V)
    (κ : (kernel Q.q).val.obj (op W))
    (w : (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
      Q.L (-1)).val.obj (op W))
    (w₀ : (inverseTautologicalTwist E).val.obj (op V))
    (hw : (inverseTwistBaseChangeIso E Q e).inv.val.app (op W) w =
      Scheme.Modules.pullbackSection σ (inverseTautologicalTwist E) V W hWV w₀) :
    (pullbackSourceIso E Q hσ e).inv.val.app (op W)
        (tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op W) (kernel Q.q)
          (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1))
          κ w) =
      Scheme.Modules.pullbackSection σ
        ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q) ⊗
          inverseTautologicalTwist E) V W hWV
        (tensorSectionsAt (bundle E).scheme.presheaf (bundle E).scheme.ringCatSheaf.2 (op V)
          ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q))
          (inverseTautologicalTwist E)
          (((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q)).val.map
            (homOfLE hV).op (unitSection (bundle E).toBase (kernel Q.q) W κ)) w₀) := by
  refine Eq.trans (congrArg (fun φ : kernel Q.q ⊗
      Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1) ⟶
        (Scheme.Modules.pullback σ).obj
          ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q) ⊗
            inverseTautologicalTwist E) =>
    φ.val.app (op W)
      (tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op W) (kernel Q.q)
        (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1))
        κ w))
    (pullbackSourceIso_inv E Q hσ e)) ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply
    ((((pullbackSectionNatIso E hσ).app (kernel Q.q)).symm ⊗ᵢ
      inverseTwistBaseChangeIso E Q e).inv)
    (pullbackTensorComparisonIso σ
      ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q))
      (inverseTautologicalTwist E)).inv (op W) _) ?_
  refine Eq.trans (congrArg (fun y : ((Scheme.Modules.pullback σ).obj
        ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q)) ⊗
      (Scheme.Modules.pullback σ).obj (inverseTautologicalTwist E)).val.obj (op W) =>
      (pullbackTensorComparisonIso σ
        ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q))
        (inverseTautologicalTwist E)).inv.val.app (op W) y)
    (tensorSectionsAt_tensorIso_inv ((pullbackSectionNatIso E hσ).app (kernel Q.q)).symm
      (inverseTwistBaseChangeIso E Q e) W κ w)) ?_
  refine Eq.trans (congrArg (fun y : ((Scheme.Modules.pullback σ).obj
        ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q))).val.obj (op W) =>
      (pullbackTensorComparisonIso σ
          ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q))
          (inverseTautologicalTwist E)).inv.val.app (op W)
        (tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op W)
          ((Scheme.Modules.pullback σ).obj
            ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q)))
          ((Scheme.Modules.pullback σ).obj (inverseTautologicalTwist E)) y
          ((inverseTwistBaseChangeIso E Q e).inv.val.app (op W) w)))
    (pullbackSectionNatIso_hom_app_val_app_le E hσ (kernel Q.q) W V hV hWV κ)) ?_
  refine Eq.trans (congrArg (fun y : ((Scheme.Modules.pullback σ).obj
        (inverseTautologicalTwist E)).val.obj (op W) =>
      (pullbackTensorComparisonIso σ
          ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q))
          (inverseTautologicalTwist E)).inv.val.app (op W)
        (tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op W)
          ((Scheme.Modules.pullback σ).obj
            ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q)))
          ((Scheme.Modules.pullback σ).obj (inverseTautologicalTwist E))
          (Scheme.Modules.pullbackSection σ
            ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q)) V W hWV
            (((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q)).val.map
              (homOfLE hV).op (unitSection (bundle E).toBase (kernel Q.q) W κ))) y))
    hw) ?_
  exact pullbackTensorComparison_inv_tensorSectionsAt σ
    ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q))
    (inverseTautologicalTwist E) V W hWV
    (((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q)).val.map
      (homOfLE hV).op (unitSection (bundle E).toBase (kernel Q.q) W κ)) w₀

variable (hqe : (Scheme.Modules.pullbackId X).inv.app E ≫
    (Scheme.Modules.pullbackCongr hσ).inv.app E ≫
      (Scheme.Modules.pullbackComp σ (bundle E).toBase).inv.app E ≫
        (Scheme.Modules.pullback σ).map (tautologicalMap E (symPieces E)) ≫ e.hom = Q.q)
  [IsImmersion σ]

include hσ e hqe in
/-- **The conormal map of [Stacks, Tag 0B3V] clause 3 on a product section.** On the section of
`ker(q) ⊗ 𝓛^{⊗ -1}` over `W` determined by `κ` and `w`, the clause's map is the section of the
conormal sheaf named — through `Stacks.CartierConormal.conormalSheafIsoPullbackSelf` — by the
pullback along `σ` of the section `y` of the ideal sheaf `ℐ(σ)` over an open `V` of `𝐏(ℰ)` with
`V ≤ π⁻¹W` and `W ≤ σ⁻¹V`, whose image in `𝒪_{𝐏(ℰ)}` is the value of the untwisted tautological
map `ṽ` on the corresponding product section upstairs.

Both inputs that the library does not yet supply are hypotheses: `hw`, the base-change
comparison of the inverse twist on a section, and `hy`, the existence of `y`. See the module's
"Not done here". The upstairs open is a parameter for the reason recorded in the module's
implementation notes: at `V = π⁻¹W` the hypothesis `hw` forces `w = 0`.

The map is `σ^*` of `Stacks.ProjectiveBundleConormal.idealSheafLift` by definition;
`Stacks.ProjectiveBundleConormal.pullbackSourceIso_inv_tensorSectionsAt` carries the section up,
`AlgebraicGeometry.Scheme.Modules.pullbackSection_naturality` moves the lift past the pullback of
the section, and `Stacks.ProjectiveBundleConormal.idealSheafLift_val_app_eq_of_ι` computes the
lift. -/
theorem conormalCanonicalMap_val_app_tensorSectionsAt (W : X.Opens)
    (V : (bundle E).scheme.Opens) (hV : V ≤ (bundle E).toBase ⁻¹ᵁ W) (hWV : W ≤ σ ⁻¹ᵁ V)
    (κ : (kernel Q.q).val.obj (op W))
    (w : (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
      Q.L (-1)).val.obj (op W))
    (w₀ : (inverseTautologicalTwist E).val.obj (op V))
    (hw : (inverseTwistBaseChangeIso E Q e).inv.val.app (op W) w =
      Scheme.Modules.pullbackSection σ (inverseTautologicalTwist E) V W hWV w₀)
    (y : (kernel (structureSheafUnit σ)).val.obj (op V))
    (hy : (kernel.ι (structureSheafUnit σ)).val.app (op V) y =
      (kernelTautologicalMapTwisted E Q).val.app (op V)
        (tensorSectionsAt (bundle E).scheme.presheaf (bundle E).scheme.ringCatSheaf.2 (op V)
          ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q))
          (inverseTautologicalTwist E)
          (((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q)).val.map
            (homOfLE hV).op (unitSection (bundle E).toBase (kernel Q.q) W κ)) w₀)) :
    (conormalCanonicalMap E Q hσ e hqe).val.app (op W)
        (tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op W) (kernel Q.q)
          (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1))
          κ w) =
      (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).inv.val.app (op W)
        (Scheme.Modules.pullbackSection σ (kernel (structureSheafUnit σ)) V W hWV y) := by
  refine Eq.trans (SheafOfModules.comp_val_app_apply (pullbackSourceIso E Q hσ e).inv
    ((Scheme.Modules.pullback σ).map (idealSheafLift E Q hσ e hqe) ≫
      (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).inv) (op W) _) ?_
  refine Eq.trans (congrArg (fun z : ((Scheme.Modules.pullback σ).obj
        ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q) ⊗
          inverseTautologicalTwist E)).val.obj (op W) =>
      ((Scheme.Modules.pullback σ).map (idealSheafLift E Q hσ e hqe) ≫
        (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).inv).val.app (op W) z)
    (pullbackSourceIso_inv_tensorSectionsAt E Q hσ e W V hV hWV κ w w₀ hw)) ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply
    ((Scheme.Modules.pullback σ).map (idealSheafLift E Q hσ e hqe))
    (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).inv (op W) _) ?_
  refine Eq.trans (congrArg (fun z : ((Scheme.Modules.pullback σ).obj
        (kernel (structureSheafUnit σ))).val.obj (op W) =>
      (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).inv.val.app (op W) z)
    (Scheme.Modules.pullbackSection_naturality σ (idealSheafLift E Q hσ e hqe) V W hWV _)) ?_
  exact congrArg (fun z : (kernel (structureSheafUnit σ)).val.obj (op V) =>
    (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).inv.val.app (op W)
      (Scheme.Modules.pullbackSection σ (kernel (structureSheafUnit σ)) V W hWV z))
    (idealSheafLift_val_app_eq_of_ι E Q hσ e hqe V _ y hy)

include hσ e hqe in
/-- **The clause's map on a product section, with the ideal-sheaf section no longer a
hypothesis.** The section `y` of `ℐ(σ)` over `V` is produced rather than assumed, and its pin is
handed back in the *scalar* form the chart computation reads: the image of `y` in `𝒪_{𝐏(ℰ)}` is
the product of the section `v(π^*κ)` of `𝒪(1)` with `w₀`, under
`Stacks.SheafOfModules.Invertible.sectionMulNegOne`.

This is `Stacks.ProjectiveBundleConormal.conormalCanonicalMap_val_app_tensorSectionsAt` with its
hypotheses `y` and `hy` discharged by
`Stacks.ProjectiveBundleConormal.exists_idealSheaf_section_kernelTautologicalMapTwisted`, and the
pin moved to `Stacks.SheafOfModules.Invertible.sectionMulNegOne` by
`Stacks.ProjectiveBundleConormal.kernelTautologicalMapTwisted_tensorSectionsAt`. Only `hw` — the
base-change comparison of the inverse twist on a section — is still assumed; see the module's
"Not done here".

**Why the existential form is the usable one.** A chart computation that names its own candidate
section `y'` of `ℐ(σ)` and proves the same scalar pin gets `y = y'` from
`Stacks.Conormal.Locality.idealSheaf_section_injective`, so the conclusion transfers to `y'`. The
remaining work at the chart is therefore exactly one equation between sections of `𝒪_{𝐏(ℰ)}` over
`V`, with no section of the ideal sheaf to construct.

No `@[stacks 0B3V]` attribute is attached. This is one formula for the clause's map on one
section, still carrying `hw`; the clause asserts that the map is an isomorphism, which is
`Stacks.ProjectiveBundleConormal.isIso_conormalCanonicalMap_of_restrict_eq'` away. -/
theorem exists_conormalCanonicalMap_val_app_tensorSectionsAt (W : X.Opens)
    (V : (bundle E).scheme.Opens) (hV : V ≤ (bundle E).toBase ⁻¹ᵁ W) (hWV : W ≤ σ ⁻¹ᵁ V)
    (κ : (kernel Q.q).val.obj (op W))
    (w : (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
      Q.L (-1)).val.obj (op W))
    (w₀ : (inverseTautologicalTwist E).val.obj (op V))
    (hw : (inverseTwistBaseChangeIso E Q e).inv.val.app (op W) w =
      Scheme.Modules.pullbackSection σ (inverseTautologicalTwist E) V W hWV w₀) :
    ∃ y : (kernel (structureSheafUnit σ)).val.obj (op V),
      (kernel.ι (structureSheafUnit σ)).val.app (op V) y =
          Stacks.SheafOfModules.Invertible.sectionMulNegOne (bundle E).scheme.presheaf
            (bundle E).scheme.ringCatSheaf.2 (tautologicalTwist E (symPieces E)) (op V)
            ((kernelTautologicalMap E Q).val.app (op V)
              (((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q)).val.map
                (homOfLE hV).op (unitSection (bundle E).toBase (kernel Q.q) W κ))) w₀ ∧
        (conormalCanonicalMap E Q hσ e hqe).val.app (op W)
            (tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op W) (kernel Q.q)
              (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1))
              κ w) =
          (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).inv.val.app (op W)
            (Scheme.Modules.pullbackSection σ (kernel (structureSheafUnit σ)) V W hWV y) := by
  obtain ⟨y, hy⟩ := exists_idealSheaf_section_kernelTautologicalMapTwisted E Q hσ e hqe V
    (tensorSectionsAt (bundle E).scheme.presheaf (bundle E).scheme.ringCatSheaf.2 (op V)
      ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q))
      (inverseTautologicalTwist E)
      (((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q)).val.map
        (homOfLE hV).op (unitSection (bundle E).toBase (kernel Q.q) W κ)) w₀)
  exact ⟨y, hy.trans (kernelTautologicalMapTwisted_tensorSectionsAt E Q V _ w₀),
    conormalCanonicalMap_val_app_tensorSectionsAt E Q hσ e hqe W V hV hWV κ w w₀ hw y hy⟩

/-! ### The chart formula, with the base-change hypothesis discharged -/

/-- The chart formula follows from the base-change equation `hw` alone, for some section `w₀`. -/
private theorem exists_conormalCanonicalMap_val_app_tensorSectionsAt_chart_of_exists
    (W : X.Opens) (s : Γ(E, W)) (hW : IsAffineOpen W) (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W))
    (hs : chartLinearForm Q W eL s = 1) (κ : Γ(kernel Q.q, W))
    (w : Γ(Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1), W))
    (h : ∃ w₀ : Γ(inverseTautologicalTwist E, tautologicalChart E W s),
      (inverseTwistBaseChangeIso E Q e).inv.val.app (op W) w =
        Scheme.Modules.pullbackSection σ (inverseTautologicalTwist E)
          (tautologicalChart E W s) W
          (le_preimage_tautologicalChart E Q hσ e hqe W s hW eL hs) w₀) :
    ∃ (w₀ : Γ(inverseTautologicalTwist E, tautologicalChart E W s))
      (y : Γ(kernel (structureSheafUnit σ), tautologicalChart E W s)),
      (inverseTwistBaseChangeIso E Q e).inv.val.app (op W) w =
          Scheme.Modules.pullbackSection σ (inverseTautologicalTwist E)
            (tautologicalChart E W s) W
            (le_preimage_tautologicalChart E Q hσ e hqe W s hW eL hs) w₀ ∧
        (kernel.ι (structureSheafUnit σ)).val.app (op (tautologicalChart E W s)) y =
            Stacks.SheafOfModules.Invertible.sectionMulNegOne (bundle E).scheme.presheaf
              (bundle E).scheme.ringCatSheaf.2 (tautologicalTwist E (symPieces E))
              (op (tautologicalChart E W s))
              ((kernelTautologicalMap E Q).val.app (op (tautologicalChart E W s))
                (((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q)).val.map
                  (homOfLE (tautologicalChart_le E W s)).op
                  (unitSection (bundle E).toBase (kernel Q.q) W κ))) w₀ ∧
          (conormalCanonicalMap E Q hσ e hqe).val.app (op W)
              (tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op W) (kernel Q.q)
                (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
                  Q.L (-1)) κ w) =
            (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).inv.val.app (op W)
              (Scheme.Modules.pullbackSection σ (kernel (structureSheafUnit σ))
                (tautologicalChart E W s) W
                (le_preimage_tautologicalChart E Q hσ e hqe W s hW eL hs) y) := by
  obtain ⟨w₀, hw⟩ := h
  obtain ⟨y, hy, hmap⟩ := exists_conormalCanonicalMap_val_app_tensorSectionsAt E Q hσ e hqe W
    (tautologicalChart E W s) (tautologicalChart_le E W s)
    (le_preimage_tautologicalChart E Q hσ e hqe W s hW eL hs) κ w w₀ hw
  exact ⟨w₀, y, hw, hy, hmap⟩

include hσ e hqe in
/-- **The clause's map on a product section over a chart, with nothing left to assume about the
base change.** Over an affine `W` carrying a frame `eL` in which `s` has linear form `1`, on the
chart `Stacks.ProjectiveBundleConormal.tautologicalChart E W s` the hypothesis `hw` of
`Stacks.ProjectiveBundleConormal.exists_conormalCanonicalMap_val_app_tensorSectionsAt` is a
theorem, so neither the upstairs open nor the section `w₀` of `𝒪(-1)` over it need be supplied:
both are produced, together with the section `y` of `ℐ(σ)` and its scalar pin.

`Stacks.ProjectiveBundleConormal.exists_pullbackSection_inverseTwistBaseChangeIso_inv_val_app`
produces `w₀` and `hw` at exactly this instantiation — `V := tautologicalChart E W s`,
`hV := tautologicalChart_le`, `hWV := le_preimage_tautologicalChart` — and the rest is the
existential form above.

The hypothesis on `w` is the one that lemma cannot drop: `w` must generate the sections of
`𝓛^{⊗ -1}` over every open of `W`, because the downstairs pairing of
`Stacks.ProjBundleInverseBaseChange.inverseTwistBaseChangeIso_inv_val_app` asks `w` for a pairing
partner and only a generator has one. On a chart it is automatic for the generator a
trivialisation names; that is
`Stacks.ProjectiveBundleConormal.exists_conormalCanonicalMap_val_app_tensorSectionsAt_chart_unit`.

**No `@[stacks 0B3V]` attribute is attached.** This closes the *source* half of the clause's
chart computation. The target half
`Stacks.ProjectiveBundleConormal.restrictConormalIsoOfOpenFactor_trans_zeroSection_hom_unit_toOpen`
must be instantiated at `V := tautologicalChart E W s` — the factorization data for which
this file supplies below — and not at `π⁻¹W`: the `π⁻¹W` instance names its conormal generator by
a section of `ℐ(σ)` over the whole preimage, where this one produces a section only over the
chart, and no section of `ℐ(σ)` over `π⁻¹W` restricts to the chart generator wanted. What the two
halves then still need to meet is the equation recorded in the module's "Not done here". -/
theorem exists_conormalCanonicalMap_val_app_tensorSectionsAt_chart (W : X.Opens) (s : Γ(E, W))
    (hW : IsAffineOpen W) (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W))
    (hs : chartLinearForm Q W eL s = 1) (κ : Γ(kernel Q.q, W))
    (w : Γ(Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1), W))
    (hgen : ∀ (V : X.Opens) (hVW : V ≤ W), Function.Bijective fun d : Γ(X, V) =>
      d • (show X.Modules from Stacks.SheafOfModules.Invertible.tensorPower X.presheaf
        X.ringCatSheaf.2 Q.L (-1)).presheaf.map (homOfLE hVW).op w) :
    ∃ (w₀ : Γ(inverseTautologicalTwist E, tautologicalChart E W s))
      (y : Γ(kernel (structureSheafUnit σ), tautologicalChart E W s)),
      (inverseTwistBaseChangeIso E Q e).inv.val.app (op W) w =
          Scheme.Modules.pullbackSection σ (inverseTautologicalTwist E)
            (tautologicalChart E W s) W
            (le_preimage_tautologicalChart E Q hσ e hqe W s hW eL hs) w₀ ∧
        (kernel.ι (structureSheafUnit σ)).val.app (op (tautologicalChart E W s)) y =
            Stacks.SheafOfModules.Invertible.sectionMulNegOne (bundle E).scheme.presheaf
              (bundle E).scheme.ringCatSheaf.2 (tautologicalTwist E (symPieces E))
              (op (tautologicalChart E W s))
              ((kernelTautologicalMap E Q).val.app (op (tautologicalChart E W s))
                (((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q)).val.map
                  (homOfLE (tautologicalChart_le E W s)).op
                  (unitSection (bundle E).toBase (kernel Q.q) W κ))) w₀ ∧
          (conormalCanonicalMap E Q hσ e hqe).val.app (op W)
              (tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op W) (kernel Q.q)
                (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
                  Q.L (-1)) κ w) =
            (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).inv.val.app (op W)
              (Scheme.Modules.pullbackSection σ (kernel (structureSheafUnit σ))
                (tautologicalChart E W s) W
                (le_preimage_tautologicalChart E Q hσ e hqe W s hW eL hs) y) := by
  exact exists_conormalCanonicalMap_val_app_tensorSectionsAt_chart_of_exists E Q hσ e hqe W s hW
    eL hs κ w (exists_pullbackSection_inverseTwistBaseChangeIso_inv_val_app E Q hσ e hqe
      W s hW eL hs w hgen)

include hσ e hqe in
/-- **The chart formula for the generator a trivialisation of the inverse twist names, with no
hypothesis on `w` at all.** On the chart the inverse twist is trivial —
`Stacks.ProjectiveBundleConormal.restrictInverseTwistIso` turns a trivialisation of `𝓛|_W` into
one of `(𝓛^{⊗ -1})|_W` — and the section `θ⁻¹(1)` it names generates over every open of `W`, so
the generation hypothesis of
`Stacks.ProjectiveBundleConormal.exists_conormalCanonicalMap_val_app_tensorSectionsAt_chart`
is discharged by
`Stacks.ProjectiveBundleConormal`
`.exists_pullbackSection_inverseTwistBaseChangeIso_inv_val_app_restrictIsoUnit`.

This is the shape the chart computation of clause 3 reads: the source generator produced by
`Stacks.ProjectiveBundleConormal.restrictConormalSourceIsoTilde_inv_unit_toOpen` is the product
`κ ⊗ s̄^{⊗ -1}` with `s̄^{⊗ -1}` exactly the section `θ` names, and `hUW` is the inequality
`AlgebraicGeometry.Scheme.Opens.ι_image_top` supplies.

**No `@[stacks 0B3V]` attribute is attached**, for the reason recorded on
`exists_conormalCanonicalMap_val_app_tensorSectionsAt_chart`: the `y` this produces is pinned by
its image in `𝒪_{𝐏(ℰ)}`, and identifying that pin with the one the target half asks for is the
equation of the module's "Not done here". -/
theorem exists_conormalCanonicalMap_val_app_tensorSectionsAt_chart_unit (W : X.Opens)
    (s : Γ(E, W)) (hW : IsAffineOpen W) (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W))
    (hs : chartLinearForm Q W eL s = 1) (κ : Γ(kernel Q.q, W))
    (θ : (Scheme.Modules.restrictFunctor W.ι).obj
        (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1)) ≅
      𝟙_ (↑W : Scheme.{u}).Modules)
    (hUW : W ≤ W.ι ''ᵁ (⊤ : (↑W : Scheme.{u}).Opens))
    (w : Γ(Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1), W))
    (hwθ : w = (show X.Modules from Stacks.SheafOfModules.Invertible.tensorPower X.presheaf
          X.ringCatSheaf.2 Q.L (-1)).presheaf.map (homOfLE hUW).op
        (θ.inv.val.app (op (⊤ : (↑W : Scheme.{u}).Opens))
          (1 : Γ((↑W : Scheme.{u}), (⊤ : (↑W : Scheme.{u}).Opens))))) :
    ∃ (w₀ : Γ(inverseTautologicalTwist E, tautologicalChart E W s))
      (y : Γ(kernel (structureSheafUnit σ), tautologicalChart E W s)),
      (inverseTwistBaseChangeIso E Q e).inv.val.app (op W) w =
          Scheme.Modules.pullbackSection σ (inverseTautologicalTwist E)
            (tautologicalChart E W s) W
            (le_preimage_tautologicalChart E Q hσ e hqe W s hW eL hs) w₀ ∧
        (kernel.ι (structureSheafUnit σ)).val.app (op (tautologicalChart E W s)) y =
            Stacks.SheafOfModules.Invertible.sectionMulNegOne (bundle E).scheme.presheaf
              (bundle E).scheme.ringCatSheaf.2 (tautologicalTwist E (symPieces E))
              (op (tautologicalChart E W s))
              ((kernelTautologicalMap E Q).val.app (op (tautologicalChart E W s))
                (((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q)).val.map
                  (homOfLE (tautologicalChart_le E W s)).op
                  (unitSection (bundle E).toBase (kernel Q.q) W κ))) w₀ ∧
          (conormalCanonicalMap E Q hσ e hqe).val.app (op W)
              (tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op W) (kernel Q.q)
                (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
                  Q.L (-1)) κ w) =
            (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).inv.val.app (op W)
              (Scheme.Modules.pullbackSection σ (kernel (structureSheafUnit σ))
                (tautologicalChart E W s) W
                (le_preimage_tautologicalChart E Q hσ e hqe W s hW eL hs) y) := by
  exact exists_conormalCanonicalMap_val_app_tensorSectionsAt_chart_of_exists E Q hσ e hqe W s hW
    eL hs κ w
    (exists_pullbackSection_inverseTwistBaseChangeIso_inv_val_app_restrictIsoUnit E Q hσ e hqe
      W s hW eL hs θ hUW w hwθ)

/-! ### The factorization the target half consumes, at the tautological chart -/

section TautologicalChartFactor

variable {W : X.Opens} (hW : IsAffineOpen W) (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W)) (t : Γ(E, W))
  (ht : chartLinearForm Q W eL t = 1)

omit [IsImmersion σ] in
include hσ e hqe hW eL ht in
/-- **The tautological chart has `W` for its preimage under the section.** One inclusion is
`Stacks.ProjectiveBundleConormal.le_preimage_tautologicalChart`, the other is
`Stacks.ProjectiveBundleConormal.tautologicalChart_le` followed by
`Stacks.ProjectiveBundleConormal.preimage_toBase_preimage`.

This is the hypothesis `hW` of `Stacks.Conormal.restrictConormalIsoOfOpenFactor` at
`V := tautologicalChart E W t`, read backwards. Note that the chart is *not* `π⁻¹W` and yet has
the same preimage: the target identification may therefore be taken over it, which is what makes
the target half of clause 3 of [Stacks, Tag 0B3V] meet the source half. -/
theorem preimage_tautologicalChart :
    σ ⁻¹ᵁ tautologicalChart E W t = W :=
  le_antisymm
    (fun x hx => Eq.mp (congrArg (fun U : X.Opens => x ∈ U) (preimage_toBase_preimage E hσ W))
      (tautologicalChart_le E W t hx))
    (le_preimage_tautologicalChart E Q hσ e hqe W t hW eL ht)

omit [IsImmersion σ] in
include hσ e hqe in
/-- **The section, read over the chart, is the zero section of the affine bundle followed by the
chart of `Proj`.** This is
`Stacks.ProjectiveBundleConormal.chartSection_eq_isoSpec_comp_zeroSection` composed into
`Stacks.ProjectiveBundleConormal.chartSection_comp_chartMap`, with the open immersion of `π⁻¹W`
*not* split off — the form
`Stacks.ProjectiveBundleConormal.isoSpec_comp_zeroSection_comp_splitChart_comp_ι` produces. -/
theorem isoSpec_comp_zeroSection_comp_splitChartMap_comp_chartMap :
    hW.isoSpec.hom ≫
        zeroSection Γ(X, W) (LinearMap.ker (chartLinearForm Q W eL)) ≫
          splitChartMap (chartLinearForm Q W eL) t ht ≫ chartMap E (symPieces E) hW =
      W.ι ≫ σ :=
  calc hW.isoSpec.hom ≫
        zeroSection Γ(X, W) (LinearMap.ker (chartLinearForm Q W eL)) ≫
          splitChartMap (chartLinearForm Q W eL) t ht ≫ chartMap E (symPieces E) hW
      = (hW.isoSpec.hom ≫
          zeroSection Γ(X, W) (LinearMap.ker (chartLinearForm Q W eL)) ≫
            splitChartMap (chartLinearForm Q W eL) t ht) ≫ chartMap E (symPieces E) hW :=
        (congrArg (fun m => hW.isoSpec.hom ≫ m) (Category.assoc _ _ _).symm).trans
          (Category.assoc _ _ _).symm
    _ = chartSection E hW hσ ≫ chartMap E (symPieces E) hW :=
        congrArg (fun m => m ≫ chartMap E (symPieces E) hW)
          (chartSection_eq_isoSpec_comp_zeroSection E Q hσ e hqe hW eL t ht).symm
    _ = W.ι ≫ σ := chartSection_comp_chartMap E hW hσ

/-- **The affine chart of the frame lands inside the tautological chart**, as the range
containment `AlgebraicGeometry.IsOpenImmersion.lift` asks for. It is
`Stacks.ProjectiveBundleConormal.basicOpen_le_preimage_chartMap_tautologicalChart` at the points
of the image of `Stacks.ProjectiveBundleConormal.splitChartMap`, whose own image
`Stacks.ProjectiveBundleConormal.opensRange_splitChartMap` names. -/
theorem range_splitChartMap_comp_chartMap_subset :
    Set.range (splitChartMap (chartLinearForm Q W eL) t ht ≫
        chartMap E (symPieces E) hW).base ⊆
      Set.range (tautologicalChart E W t).ι.base := by
  rintro _ ⟨y, rfl⟩
  refine Eq.mpr (congrArg (fun S : Set (bundle E).scheme => _ ∈ S)
    (Scheme.Opens.range_ι (tautologicalChart E W t))) ?_
  refine basicOpen_le_preimage_chartMap_tautologicalChart E W t hW ?_
  exact Eq.mp (congrArg (fun U => (splitChartMap (chartLinearForm Q W eL) t ht).base y ∈ U)
    (opensRange_splitChartMap (chartLinearForm Q W eL) t ht)) ⟨y, rfl⟩

/-- **The affine bundle of `ker p`, as an open immersion into the tautological chart.** This is
the `j` of `Stacks.Conormal.restrictConormalIsoOfOpenFactor` at
`V := tautologicalChart E W t`: `Stacks.ProjectiveBundleConormal.splitChartMap` followed by the
chart of `Proj`, factored through the inclusion of the tautological chart. -/
def tautologicalChartLift :
    Spec (symRing Γ(X, W) ↥(LinearMap.ker (chartLinearForm Q W eL))) ⟶
      (tautologicalChart E W t).toScheme :=
  IsOpenImmersion.lift (tautologicalChart E W t).ι
    (splitChartMap (chartLinearForm Q W eL) t ht ≫ chartMap E (symPieces E) hW)
    (range_splitChartMap_comp_chartMap_subset E Q hW eL t ht)

/-- The lift is a factorization of the chart through the inclusion of the tautological chart. -/
theorem tautologicalChartLift_comp_ι :
    tautologicalChartLift E Q hW eL t ht ≫ (tautologicalChart E W t).ι =
      splitChartMap (chartLinearForm Q W eL) t ht ≫ chartMap E (symPieces E) hW :=
  IsOpenImmersion.lift_fac _ _ _

/-- **The lift is an open immersion**, its composite with the inclusion of the tautological chart
being one. -/
instance isOpenImmersion_tautologicalChartLift :
    IsOpenImmersion (tautologicalChartLift E Q hW eL t ht) :=
  haveI : IsOpenImmersion
      (tautologicalChartLift E Q hW eL t ht ≫ (tautologicalChart E W t).ι) :=
    Eq.mpr (congrArg (fun m : Spec (symRing Γ(X, W) ↥(LinearMap.ker (chartLinearForm Q W eL))) ⟶
        (bundle E).scheme => IsOpenImmersion m)
      (tautologicalChartLift_comp_ι E Q hW eL t ht)) inferInstance
  IsOpenImmersion.of_comp (tautologicalChartLift E Q hW eL t ht) (tautologicalChart E W t).ι

omit [IsImmersion σ] in
include hσ e hqe in
/-- **The factorization of `σ|_W` through the zero section of the affine bundle and the
tautological chart.** This is the hypothesis `hfac` of
`Stacks.Conormal.restrictConormalIsoOfOpenFactor` at `V := tautologicalChart E W t`,
`α := hW.isoSpec`, `g :=` the zero section and `j :=`
`Stacks.ProjectiveBundleConormal.tautologicalChartLift`. -/
theorem isoSpec_comp_zeroSection_comp_tautologicalChartLift_comp_ι :
    hW.isoSpec.hom ≫
        zeroSection Γ(X, W) (LinearMap.ker (chartLinearForm Q W eL)) ≫
          tautologicalChartLift E Q hW eL t ht ≫ (tautologicalChart E W t).ι =
      W.ι ≫ σ :=
  (congrArg
      (fun m => hW.isoSpec.hom ≫
        zeroSection Γ(X, W) (LinearMap.ker (chartLinearForm Q W eL)) ≫ m)
      (tautologicalChartLift_comp_ι E Q hW eL t ht)).trans
    (isoSpec_comp_zeroSection_comp_splitChartMap_comp_chartMap E Q hσ e hqe hW eL t ht)

/-- **The whole of the affine bundle lies over the tautological chart's self-preimage.** This is
the hypothesis `hP` of
`Stacks.ProjectiveBundleConormal.restrictConormalIsoOfOpenFactor_trans_zeroSection_hom_unit_toOpen`
at `V := tautologicalChart E W t`, which is what lets that statement be read at the open `⊤` of
`Spec (Sym_A (ker p))` — the only open at which
`Stacks.ProjectiveBundleConormal.conormalZeroSectionTildeIso_hom_unit_toOpen` can be stated. -/
theorem top_eq_preimage_tautologicalChartLift_preimage_ι :
    (⊤ : (Spec (symRing Γ(X, W) ↥(LinearMap.ker (chartLinearForm Q W eL)))).Opens) =
      tautologicalChartLift E Q hW eL t ht ⁻¹ᵁ
        ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t) :=
  ((congrArg (fun O : (tautologicalChart E W t).toScheme.Opens =>
          tautologicalChartLift E Q hW eL t ht ⁻¹ᵁ O)
        (tautologicalChart E W t).ι_preimage_self).trans
    (Scheme.Hom.preimage_top (tautologicalChartLift E Q hW eL t ht))).symm

end TautologicalChartFactor

end Stacks.ProjectiveBundleConormal

end
