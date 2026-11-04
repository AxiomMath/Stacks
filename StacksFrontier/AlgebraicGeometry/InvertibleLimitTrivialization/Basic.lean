module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.PartOne.Basic

/-!
# The trivializing affine cover of an invertible module on a limit comes from a stage

Let `S = lim Sᵢ` be the limit of a cofiltered system of quasi-compact and quasi-separated
schemes with affine transition morphisms, and let `L` be an invertible `𝒪_S`-module. Then there
is an index `i`, a finite affine open cover `V` of `Sᵢ` — a cover of the *stage*, not merely a
family whose preimages cover `S` — such that `L` is sectionwise trivial on each
`c.π.app i ⁻¹ᵁ V k`.

This is the first step of the proof of [Stacks, Tag 0B8W] part (2) along the route the
repository has reduced that label to: `Stacks.InvertibleLimitDescentReduction` proves Tag 0B8W's
`invertible_descent` assertion equivalent to `RankOneLimitDescent`, and the Stacks source's own
proof of the finite-locally-free descent it rests on is the Zariski glueing for which the source
writes "we omit the details". The glueing runs over exactly the cover produced here.

## Main results

* `Stacks.InvertibleLimitTrivialization.exists_stage_affine_trivializing_cover`: the cover, for
  an invertible module.
* `Stacks.InvertibleLimitTrivialization.exists_stage_affine_trivializing_cover_of_rank_one`: the
  same at the hypothesis of `Stacks.InvertibleLimitDescentReduction.RankOneLimitDescent`, i.e.
  with the module finite locally free of rank one rather than invertible.

## Route: composing two available halves

Nothing new is proved here. The two halves are

* `Stacks.Tag01PWPartOne.exists_finite_affine_trivializing_cover` — a quasi-compact scheme
  carrying an invertible module is covered by **finitely many affine opens** on each of which the
  module is sectionwise trivial, as a `Stacks.SheafDescent.Trivialization`; and
* `AlgebraicGeometry.Scheme.exists_isOpenCover_and_isAffine_of_finite` in pinned Mathlib — a
  finite affine open cover of the limit is the preimage of an affine open cover of some stage.

Quasi-compactness of the limit, which the first half needs, is
`AlgebraicGeometry.Scheme.compactSpace_of_isLimit`. The trivialization is then transported along
the equality `W k = c.π.app i ⁻¹ᵁ V k` that the second half supplies, which is a `subst` and not
a transport of data.

## What this does and does not give

It gives the cover at the stage. It does **not** give the descended module: what remains of
`RankOneLimitDescent` is the transition data — the units comparing two trivializations over
`c.π.app i ⁻¹ᵁ (V k ⊓ V l)`, their descent to a common later stage together with the cocycle
condition, the glueing of a rank-one module at that stage (for which
`Stacks.AlgebraicGeometry.SchemeModuleGlue.ChartGlueData` is the engine), and the
identification of the pullback of the glued module with `L`. No Tag 0B8W or Tag 01ZR attribute is
attached here: neither statement below is an assertion of either tag.

## References

* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.InvertibleLimitTrivialization

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)

include hc in
/-- **The trivializing affine cover of an invertible module on a cofiltered limit of qcqs schemes
with affine transition morphisms comes from a stage.** There are an index `i`, a finite family of
affine opens of `D.obj i` covering `D.obj i`, and a sectionwise trivialization of `L` over the
preimage in the limit of each member.

Note the cover is a cover of the **stage**: `TopologicalSpace.IsOpenCover V` says
`⨆ k, V k = ⊤` in `D.obj i`, not merely that the preimages cover the limit. -/
theorem exists_stage_affine_trivializing_cover [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (L : c.pt.Modules) [Stacks.Ample.IsInvertibleModule c.pt L] :
    ∃ (i : I) (ι : Type u) (_ : Finite ι) (V : ι → (D.obj i).Opens),
      IsOpenCover V ∧ (∀ k, IsAffineOpen (V k)) ∧
        ∀ k, Nonempty (Stacks.SheafDescent.Trivialization c.pt.presheaf L.val
          (c.π.app i ⁻¹ᵁ V k)) := by
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  obtain ⟨ι, hι, W, hWaff, hWcov, htriv⟩ :=
    Stacks.Tag01PWPartOne.exists_finite_affine_trivializing_cover L
  obtain ⟨i, V, hV, hVprop⟩ := Scheme.exists_isOpenCover_and_isAffine_of_finite D c hc W
    (IsOpenCover.mk (top_le_iff.mp hWcov)) hWaff
  refine ⟨i, ι, hι, V, hV, fun k => (hVprop k).1, fun k => ?_⟩
  exact ((hVprop k).2 ▸ htriv k :)

include hc in
/-- **The same cover at the hypothesis of
`Stacks.InvertibleLimitDescentReduction.RankOneLimitDescent`.** That statement — the single input
the repository's reduction leaves owed by Tag 0B8W's `invertible_descent` label — hypothesises
that the module on the limit is finite locally free of rank one rather than invertible, and the
two are interchangeable by clause 1 of [Stacks, Tag 0B8M] on a scheme
(`Stacks.InvertibleRankOneScheme.isInvertibleModule_of_isFiniteLocallyFreeOfRank_one`, an
instance). -/
theorem exists_stage_affine_trivializing_cover_of_rank_one [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (L : c.pt.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (R := c.pt.ringCatSheaf) L 1) :
    ∃ (i : I) (ι : Type u) (_ : Finite ι) (V : ι → (D.obj i).Opens),
      IsOpenCover V ∧ (∀ k, IsAffineOpen (V k)) ∧
        ∀ k, Nonempty (Stacks.SheafDescent.Trivialization c.pt.presheaf L.val
          (c.π.app i ⁻¹ᵁ V k)) :=
  have := hL
  exists_stage_affine_trivializing_cover D c hc L

end Stacks.InvertibleLimitTrivialization

end
