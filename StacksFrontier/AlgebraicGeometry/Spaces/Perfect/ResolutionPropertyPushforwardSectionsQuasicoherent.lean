module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyPushforwardSections

/-!
# The covering submodule of a direct image is quasi-coherent

`AlgebraicGeometry.Space.exists_finiteLocallyFree_epi_submodule_modulePushforward` turns finitely
many sections of a direct image `f_*ℱ` over an affine étale chart of the target into a submodule
`𝒢` of `f_*ℱ` containing them, a finite locally free `𝒪_Y`-module `ℰ` and an epimorphism
`ℰ ⟶ 𝒢`.  Its proof establishes along the way that `𝒢` is **quasi-coherent** — that is the only
reason the resolution property of `Y`, which speaks about quasi-coherent modules, may be applied
to `𝒢` at all — but its conclusion does not record it, and neither does the conclusion of
`AlgebraicGeometry.Space.exists_finiteLocallyFree_modulePullback_hom_of_hasResolutionProperty`.

A consumer cannot recover it: the submodule `𝒢` is produced by the étale extension property of
Stacks 0829 as a `AlgebraicGeometry.Space.ChartSubmodule` which is *existentially bound* inside
the proof, so nothing outside has access to the witness whose cartesian-on-affine-charts property
is what quasi-coherence of `𝒢` comes from.  Quasi-coherence of a submodule of a quasi-coherent
module is not automatic — a submodule of a quasi-coherent module need not be quasi-coherent —
so it cannot be re-derived from the data the conclusion does carry either.

This file therefore restates both results with one further existential component, the
quasi-coherence of `𝒢`, and re-runs the argument of the original proofs.  Nothing in
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyPushforwardSections` is changed:
its statements, its proofs and its `@[stacks 0GUU]` registration are left exactly as they are,
and the two theorems below are strictly stronger forms living beside them.

## Main results

* `AlgebraicGeometry.Space.exists_finiteLocallyFree_epi_quasicoherentSubmodule_modulePushforward`:
  **the strengthened form of
  `AlgebraicGeometry.Space.exists_finiteLocallyFree_epi_submodule_modulePushforward`** — same
  hypotheses, same conclusion, plus `𝒢` quasi-coherent.
* `AlgebraicGeometry.Space.exists_finiteLocallyFree_modulePullback_hom_quasicoherentSubmodule`:
  **the strengthened form of
  `AlgebraicGeometry.Space.exists_finiteLocallyFree_modulePullback_hom_of_hasResolutionProperty`**
  — same hypotheses, same conclusion, plus `𝒢` quasi-coherent.

## Implementation notes

**No hypothesis is added and no conclusion is dropped.**  The binders of both theorems are those
of the originals, verbatim, and each conclusion is the original's conjunction with one further
component.  In particular quasi-coherence of `𝒢` is *not* taken as an input: it is proved, from
`AlgebraicGeometry.Space.ChartSubmodule.isCartesianOnAffineCharts_toSubmodule` applied to the
chart submodule that `AlgebraicGeometry.Space.chartExtensionProperty_id` produces, exactly as the
original proof does.

**Why the argument is re-run rather than invoked.**  The pieces of the original proof that lead
to quasi-coherence — `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_qcqs`
for `f_*ℱ`, then `AlgebraicGeometry.Space.chartExtensionProperty_id` and
`AlgebraicGeometry.Space.ChartExtensionProperty.exists_forall_mem` for the chart submodule, then
`AlgebraicGeometry.Space.ChartSubmodule.isCartesianOnAffineCharts_toSubmodule` and
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts` — all speak about
that chart submodule, and it is not in the original's conclusion.  There is no way to reach it
from outside, so the four steps are repeated here.  The second theorem, by contrast, is *not*
re-run from scratch: its extra content over the first is the pullback of `ℰ` and the transpose
of `ℰ ⟶ f_*ℱ`, both of which are reached from the first theorem's output by the public
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_modulePullback` and
`AlgebraicGeometry.Space.modulePullbackAdjunction`, as the original does.

**No tag is claimed.**  Stacks 0GUU is registered on
`AlgebraicGeometry.Space.exists_finiteLocallyFree_modulePullback_hom_of_hasResolutionProperty`
and stays there; these are export forms of one step of a proof, not a tagged result.

**The module universe.**  As in the original, `AlgebraicGeometry.Space.modulePushforward` and
`AlgebraicGeometry.Space.modulePullback` exist only at the universe `u` of the schemes, so
everything is stated at `AlgebraicGeometry.Space.Modules.{u, u}` and the resolution property of
`Y` is used at `AlgebraicGeometry.Space.HasResolutionProperty.{u, u}`.

## References

* [Stacks Project, Tag 0GUU](https://stacks.math.columbia.edu/tag/0GUU)
* [Stacks Project, Tag 0GUT](https://stacks.math.columbia.edu/tag/0GUT)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The covering submodule of `f_*ℱ` is quasi-coherent.**  This is
`AlgebraicGeometry.Space.exists_finiteLocallyFree_epi_submodule_modulePushforward` with its
conclusion carrying one further component: the submodule `𝒢` of `f_*ℱ` it produces is
quasi-coherent.

The original proof establishes this — it is what lets the resolution property of `Y`, a statement
about quasi-coherent modules, be applied to `𝒢` — but discards it, and a consumer cannot recover
it, because the chart submodule from which it is read off is existentially bound inside that
proof.  The argument is therefore re-run: `f_*ℱ` is quasi-coherent by Stacks 03M9, hence
cartesian on affine charts; the étale extension property of Stacks 0829 encloses the given
sections in a chart submodule `D`; `D` is cartesian on affine charts by Descent, Proposition
03DX (2), which is quasi-coherence of the submodule it determines; and the resolution property of
`Y` covers that submodule by a finite locally free module. -/
theorem exists_finiteLocallyFree_epi_quasicoherentSubmodule_modulePushforward
    (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (hYres : HasResolutionProperty.{u, u} B S hS Y.1 Y.2)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    {α : Type*} (s : Finset α) (V : SmallEtale B S hS Y.1) (hV : IsAffine (chartScheme V))
    (σ : α → ((modulePushforward B S hS f).obj F).val.obj (op V)) :
    ∃ (G : ((modulePushforward B S hS f).obj F).Submodule)
      (E : Modules.{u, u} B S hS Y.1 Y.2)
      (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E)
      (φ : E ⟶ G.toSheafOfModules), Epi φ ∧ (∀ x ∈ s, σ x ∈ G.obj (op V)) ∧
        G.toSheafOfModules.IsQuasicoherentOnSite := by
  have hpush : ((modulePushforward B S hS f).obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS f hfqc hfqs F hF
  have hcart : IsCartesianOnAffineCharts ((modulePushforward B S hS f).obj F) :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 _ hpush
  obtain ⟨D, hD⟩ := (chartExtensionProperty_id hZ hYqc hYqs hcart).exists_forall_mem hcart s
    (fun _ => V) (fun _ => V.1.hom) (fun _ => Category.comp_id _) (fun _ => hV) σ
  have hqc : (D.toSubmodule _).toSheafOfModules.IsQuasicoherentOnSite :=
    (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS Y.1 Y.2 _).2
      (D.isCartesianOnAffineCharts_toSubmodule hcart)
  have : SheafOfModules.IsFiniteTypeOnSite (D.toSubmodule _).toSheafOfModules :=
    D.isFiniteTypeOnSite_toSubmodule hcart
  obtain ⟨E, hE, φ, hφ⟩ := hYres.exists_finiteLocallyFree_quotient
    (⟨(D.toSubmodule _).toSheafOfModules, hqc⟩ : QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2)
  exact ⟨D.toSubmodule _, E, hE, φ, hφ, (fun x hx => hD x hx), hqc⟩

/-- **The covering submodule of `f_*ℱ` is quasi-coherent, in the form which also carries the
pullback and the transposed map.**  This is
`AlgebraicGeometry.Space.exists_finiteLocallyFree_modulePullback_hom_of_hasResolutionProperty`
with its conclusion carrying one further component: the submodule `𝒢` of `f_*ℱ` it produces is
quasi-coherent.

The original records neither the quasi-coherence of `𝒢` nor any route to it.  This is the
previous theorem followed by the two steps the original performs on top of its own weaker input:
the pullback `f^*ℰ` is finite locally free by Stacks 03DL under pullback
(`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_modulePullback`, with the quasi-coherence of
`ℰ` from `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isFiniteLocallyFreeOnSite`), and
`ψ : f^*ℰ ⟶ ℱ` is the transpose of `φ ≫ 𝒢.ι` along `f^* ⊣ f_*`. -/
theorem exists_finiteLocallyFree_modulePullback_hom_quasicoherentSubmodule
    (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (hYres : HasResolutionProperty.{u, u} B S hS Y.1 Y.2)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    {α : Type*} (s : Finset α) (V : SmallEtale B S hS Y.1) (hV : IsAffine (chartScheme V))
    (σ : α → ((modulePushforward B S hS f).obj F).val.obj (op V)) :
    ∃ (G : ((modulePushforward B S hS f).obj F).Submodule)
      (E : Modules.{u, u} B S hS Y.1 Y.2)
      (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E)
      (φ : E ⟶ G.toSheafOfModules), Epi φ ∧ (∀ x ∈ s, σ x ∈ G.obj (op V)) ∧
        G.toSheafOfModules.IsQuasicoherentOnSite ∧
        SheafOfModules.IsFiniteLocallyFreeOnSite ((modulePullback B S hS f).obj E) ∧
        ∃ ψ : (modulePullback B S hS f).obj E ⟶ F,
          (modulePullbackAdjunction B S hS f).homEquiv E F ψ = φ ≫ G.ι := by
  obtain ⟨G, E, hE, φ, hφ, hmem, hqc⟩ :=
    exists_finiteLocallyFree_epi_quasicoherentSubmodule_modulePushforward hZ f hfqc hfqs hYqc hYqs
      hYres F hF s V hV σ
  refine ⟨G, E, hE, φ, hφ, hmem, hqc,
    isFiniteLocallyFreeOnSite_modulePullback B S hS f E
      (isQuasicoherentOnSite_of_isFiniteLocallyFreeOnSite E hE) hE,
    ((modulePullbackAdjunction B S hS f).homEquiv E F).symm (φ ≫ G.ι), ?_⟩
  exact Equiv.apply_symm_apply _ _

end AlgebraicGeometry.Space

end
