module

public import StacksFrontier.AlgebraicGeometry.ConormalAffineCotangent.Sections
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.Locality
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.TensorSectionCalculus

/-!
# The ideal-sheaf lift of Tag 0B3V clause 3, read on sections

`Stacks.ProjectiveBundleConormal.idealSheafLift` factors the untwisted tautological map
`ṽ : (π^*ker q) ⊗ 𝒪(-1) ⟶ 𝒪_{𝐏(ℰ)}` through the ideal sheaf `ℐ(σ)` of the section, and
`Stacks.ProjectiveBundleConormal.idealSheafLift_comp_ι` is the only statement that pins it down.
**This file reads that pin on a section**, and adds the section-level formula for `ṽ` itself.

The pin is usable on sections because the inclusion of the ideal sheaf is
`CategoryTheory.Limits.kernel.ι`, hence injective on sections over every open
(`Stacks.Conormal.Locality.idealSheaf_section_injective`): a section of `ℐ(σ)` is *determined* by
its image in `𝒪_{𝐏(ℰ)}`, so naming the image of a section under `ṽ` names the section of `ℐ(σ)`
the lift produces.

**This has to happen on `𝐏(ℰ)` and not after pulling back along `σ`.** The clause's map is
`σ^*` of the lift, and `σ^*` does not preserve the mono: indeed `σ^*ṽ = 0` by
`Stacks.ProjectiveBundleConormal.pullback_kernelTautologicalMapTwisted_eq_zero`, so the pulled-back
pin `Stacks.ProjectiveBundleConormal.conormalCanonicalMap_comp_ι` says only that a composite
vanishes and carries no information about the clause's map at all. The route to the chart
computation therefore runs through this file — the lift on a section of `𝐏(ℰ)` — and then
transports along `AlgebraicGeometry.Scheme.Modules.pullbackSection_naturality`.

## Main results

* `Stacks.ProjectiveBundleConormal.kernelTautologicalMapTwisted_tensorSectionsAt`: **the untwisted
  tautological map on a product section.** On the section of `(π^*ker q) ⊗ 𝒪(-1)` determined by a
  section `z` of `π^*ker q` and a section `w` of `𝒪(-1)` it is the multiplication of `v z` and
  `w`.
* `Stacks.ProjectiveBundleConormal.idealSheafLift_val_app_ι`: the pin of the lift, on a section.
* `Stacks.ProjectiveBundleConormal.idealSheafLift_val_app_eq_of_ι`: **the pin is a
  determination.** A section of `ℐ(σ)` whose image in `𝒪_{𝐏(ℰ)}` is `ṽ z` *is* the value of the
  lift at `z`.

## Implementation notes

Nothing is rewritten. The pin on a section is `congrArg` of `idealSheafLift_comp_ι` with the
morphism variable's type written out — the application of a composite to a section is the
composite of the applications by definition, so no step of the composite has to be performed — and
the determination is `Stacks.Conormal.Locality.idealSheaf_section_injective` applied to it. See
the implementation notes of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartRatio` for why no `rw` occurs on
this layer.

The formula for `ṽ` is its definition — a whiskering followed by the evaluation pairing — with the
two factors read on sections by
`Stacks.ProjectiveBundleConormal.tensorSectionsAt_whiskerRight` and
`Stacks.ProjectiveBundleConormal.invertibleEvaluation_tensorSectionsAt`.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.ProjectiveBundleSplitting
open Stacks.SymGraded

universe u

namespace Stacks.ProjectiveBundleConormal

attribute [local instance] monoidalSheafTensor

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
  (Q : Stacks.Divisors.InvertibleQuotient X E)

/-- **The untwisted tautological map of [Stacks, Tag 0B3V] clause 3 on a product section.** On the
section of `(π^*ker q) ⊗ 𝒪(-1)` determined by a section `z` of `π^*ker q` and a section `w` of
`𝒪(-1)`, the map `ṽ` is the multiplication of the section `v z` of `𝒪(1)` with `w`, which is
`Stacks.SheafOfModules.Invertible.sectionMulNegOne`.

This is its definition, read on a section: the whiskering by
`Stacks.ProjectiveBundleConormal.tensorSectionsAt_whiskerRight` and the evaluation pairing by
`Stacks.ProjectiveBundleConormal.invertibleEvaluation_tensorSectionsAt`. -/
theorem kernelTautologicalMapTwisted_tensorSectionsAt (V : (bundle E).scheme.Opens)
    (z : ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q)).val.obj (op V))
    (w : (inverseTautologicalTwist E).val.obj (op V)) :
    (kernelTautologicalMapTwisted E Q).val.app (op V)
        (Stacks.SheafOfModules.tensorSectionsAt (bundle E).scheme.presheaf
          (bundle E).scheme.ringCatSheaf.2 (op V)
          ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q))
          (inverseTautologicalTwist E) z w) =
      Stacks.SheafOfModules.Invertible.sectionMulNegOne (bundle E).scheme.presheaf
        (bundle E).scheme.ringCatSheaf.2 (tautologicalTwist E (symPieces E)) (op V)
        ((kernelTautologicalMap E Q).val.app (op V) z) w :=
  (congrArg
      (fun y => (invertibleEvaluation (tautologicalTwist E (symPieces E))).hom.val.app (op V) y)
      (tensorSectionsAt_whiskerRight (kernelTautologicalMap E Q)
        (inverseTautologicalTwist E) V z w)).trans
    (invertibleEvaluation_tensorSectionsAt (tautologicalTwist E (symPieces E)) V
      ((kernelTautologicalMap E Q).val.app (op V) z) w)

variable {σ : X ⟶ (bundle E).scheme} (hσ : σ ≫ (bundle E).toBase = 𝟙 X)
  (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L)
  (hqe : (Scheme.Modules.pullbackId X).inv.app E ≫
    (Scheme.Modules.pullbackCongr hσ).inv.app E ≫
      (Scheme.Modules.pullbackComp σ (bundle E).toBase).inv.app E ≫
        (Scheme.Modules.pullback σ).map (tautologicalMap E (symPieces E)) ≫ e.hom = Q.q)

include hσ e hqe in
/-- **The pin of the ideal-sheaf lift, on a section.** The image in `𝒪_{𝐏(ℰ)}` of the section of
`ℐ(σ)` produced by the lift is the value of the untwisted tautological map. This is
`Stacks.ProjectiveBundleConormal.idealSheafLift_comp_ι` read on a section. -/
theorem idealSheafLift_val_app_ι (V : (bundle E).scheme.Opens)
    (z : ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q) ⊗
      inverseTautologicalTwist E).val.obj (op V)) :
    (kernel.ι (structureSheafUnit σ)).val.app (op V)
        ((idealSheafLift E Q hσ e hqe).val.app (op V) z) =
      (kernelTautologicalMapTwisted E Q).val.app (op V) z :=
  congrArg
    (fun ψ : (Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q) ⊗
        inverseTautologicalTwist E ⟶ 𝟙_ ((bundle E).scheme.Modules) => ψ.val.app (op V) z)
    (idealSheafLift_comp_ι E Q hσ e hqe)

include hσ e hqe in
/-- **The pin determines the lift on sections.** A section `w` of `ℐ(σ)` over `V` whose image in
`𝒪_{𝐏(ℰ)}` is the value of the untwisted tautological map at `z` is the value of the lift at `z`.

This is what makes `Stacks.ProjectiveBundleConormal.idealSheafLift_val_app_ι` a *computation* of
the lift and not merely a property of it: the inclusion of the ideal sheaf is
`CategoryTheory.Limits.kernel.ι`, hence injective on sections, by
`Stacks.Conormal.Locality.idealSheaf_section_injective`. -/
theorem idealSheafLift_val_app_eq_of_ι (V : (bundle E).scheme.Opens)
    (z : ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q) ⊗
      inverseTautologicalTwist E).val.obj (op V))
    (w : (kernel (structureSheafUnit σ)).val.obj (op V))
    (hw : (kernel.ι (structureSheafUnit σ)).val.app (op V) w =
      (kernelTautologicalMapTwisted E Q).val.app (op V) z) :
    (idealSheafLift E Q hσ e hqe).val.app (op V) z = w :=
  Stacks.Conormal.Locality.idealSheaf_section_injective σ V
    ((idealSheafLift_val_app_ι E Q hσ e hqe V z).trans hw.symm)

/-! ### The obligation `hy`: a section of the ideal sheaf over the value of `ṽ` -/

include hσ e hqe in
/-- **`ṽ` lands in the ideal sheaf, read as a scalar equation on sections.** The value of the
untwisted tautological map at a section of `(π^*ker q) ⊗ 𝒪(-1)` over `V` is a section of
`𝒪_{𝐏(ℰ)}` that `σ` sends to `0`.

This is `Stacks.ProjectiveBundleConormal.kernelTautologicalMapTwisted_comp_structureSheafUnit`
read on a section: the morphism `Stacks.ProjectiveBundleConormal.structureSheafUnit` is by
definition `CategoryTheory.SheafOfModules.unitToPushforwardObjUnit` of the structure-sheaf map,
and on sections over `V` that *is* `σ.app V` — the `rfl` recorded as
`Stacks.Conormal.AffineCotangent.Sections.structureMap_app_eq`. So no step of the composite has
to be performed and nothing is rewritten.

No `@[stacks 0B3V]` attribute is attached. This is one scalar equation feeding the chart
computation of the clause, not the clause's isomorphism assertion. -/
theorem app_kernelTautologicalMapTwisted_eq_zero (V : (bundle E).scheme.Opens)
    (z : ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q) ⊗
      inverseTautologicalTwist E).val.obj (op V)) :
    (σ.app V).hom ((kernelTautologicalMapTwisted E Q).val.app (op V) z) = 0 :=
  congr($(kernelTautologicalMapTwisted_comp_structureSheafUnit E Q hσ e hqe).val.app (op V) z)

include hσ e hqe in
/-- **The obligation `hy` of the chart computation is not an existence construction.** There *is*
a section `y` of the ideal sheaf `ℐ(σ)` over any open `V` of `𝐏(ℰ)` whose image in `𝒪_{𝐏(ℰ)}` is
the value of the untwisted tautological map at `z`.

This is the hypothesis `hy` of
`Stacks.ProjectiveBundleConormal.conormalCanonicalMap_val_app_tensorSectionsAt` discharged.
`Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff` carries **no hypothesis
on the morphism at all** — a section of `𝒪_{𝐏(ℰ)}` over `V` is the image of a section of the
ideal sheaf exactly when `σ` sends it to `0` — so the obligation reduces to the single scalar
vanishing equation `Stacks.ProjectiveBundleConormal.app_kernelTautologicalMapTwisted_eq_zero`,
and `V` stays arbitrary: no affineness, no chart, no trivialisation, no ratio computation.

By `Stacks.Conormal.Locality.idealSheaf_section_injective` the `y` produced here is the only one,
so it is `Stacks.ProjectiveBundleConormal.idealSheafLift` at `z`; the point of the statement is
that the chart computation may *obtain* it rather than carry it, which is what
`Stacks.ProjectiveBundleConormal.idealSheafLift_val_app_eq_of_ι` then turns back into a
computation of the lift.

No `@[stacks 0B3V]` attribute is attached: this is a step towards the clause's isomorphism
assertion — one hypothesis of one chart formula — and not the clause. -/
theorem exists_idealSheaf_section_kernelTautologicalMapTwisted (V : (bundle E).scheme.Opens)
    (z : ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q) ⊗
      inverseTautologicalTwist E).val.obj (op V)) :
    ∃ y : (kernel (structureSheafUnit σ)).val.obj (op V),
      (kernel.ι (structureSheafUnit σ)).val.app (op V) y =
        (kernelTautologicalMapTwisted E Q).val.app (op V) z :=
  (Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff σ V
      ((kernelTautologicalMapTwisted E Q).val.app (op V) z)).mpr
    (app_kernelTautologicalMapTwisted_eq_zero E Q hσ e hqe V z)

end Stacks.ProjectiveBundleConormal

end
