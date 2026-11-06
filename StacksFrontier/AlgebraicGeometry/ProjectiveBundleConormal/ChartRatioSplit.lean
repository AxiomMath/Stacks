module

public import StacksFrontier.AlgebraicGeometry.ProjTwistChain.Sections
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartRatio
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartTwistProduct

/-!
# The tautological ratio of the chart, computed, and read in the affine bundle

`Stacks.ProjectiveBundleConormal.exists_tautologicalSectionOver_res_eq_smul` says that on the
chart `Stacks.ProjectiveBundleConormal.tautologicalChart E W s` of `𝐏(ℰ)` the degree-one section
attached to `m : Γ(ℰ, W)` is *some* function times the one attached to `s`, which is all the
scalar identity of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartTwistProduct` needs. **This file
identifies that function**, and carries the identification into the affine bundle on `ker p`.

Two crossings, in series.

* `Stacks.ProjectiveBundleConormal.appLE_chartMap_eq_awayToSection_of_res_eq_smul` carries the
  ratio across the open immersion `Stacks.ProjectiveBundleConormal.chartMap` and names it: it is
  the degree-zero fraction `ι m / ι s` on the standard open `D₊(ι s)` of the absolute
  `Proj(Sym_A M)`. That lemma lives in
  `StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartRatio`, where it needs no open of
  the bundle; here it is instantiated at the tautological chart, which is where a ratio exists.
* `Stacks.ProjectiveBundleConormal.appLE_splitChartMap_awayToSection` carries it on across
  `Stacks.ProjectiveBundleConormal.splitChartMap`, the identification of `D₊(ι s)` with the
  affine bundle `Spec (Sym_A(ker p))`. There the fraction becomes its value under
  `SymmetricAlgebra.splitAwayEquiv`, and for a *kernel* section that value is the degree-one
  generator: `ι k / ι s ↦ ι k` (`SymmetricAlgebra.splitAwayEquiv_mk_ι`).

The two together are
`Stacks.ProjectiveBundleConormal.exists_appLE_splitChartMap_comp_chartMap_eq_ι`: **the affine
coordinate of the chart named by a section of `ker q` is `ι k`.** With
`Stacks.ProjectiveBundleConormal.splitChartOrigin_mk_ι` — which says `ι k` vanishes at the origin
— that is the geometric content of clause 3 of [Stacks, Tag 0B3V] read in the affine bundle: the
point of `𝐀(ker p)` named by the section is its origin because every one of its affine
coordinates is a coordinate of the kernel.

## Main results

* `Stacks.ProjectiveBundleConormal.appLE_splitChartMap_awayToSection`: **the affine chart on
  sections.** `Stacks.ProjectiveBundleConormal.splitChartMap` carries a degree-zero fraction, read
  as a function on `D₊(ι s)`, to its image under
  `Stacks.ProjectiveBundleConormal.splitChartRingIso`.
* `Stacks.ProjectiveBundleConormal.appLE_splitChartMap_awayToSection_ι`: the same at `ι k / ι s`
  for `k ∈ ker p`, where the image is `ι k`.
* `Stacks.ProjectiveBundleConormal.exists_tautologicalSectionOver_res_eq_smul_appLE_eq`: **the
  ratio of the tautological chart, with the ratio computed** — the existence statement of
  `ChartTwistProduct` strengthened by the value of the ratio across `chartMap`.
* `Stacks.ProjectiveBundleConormal.exists_appLE_splitChartMap_comp_chartMap_eq_ι`: **the ratio of
  a kernel section, read in `Sym_A(ker p)`**: it is `ι k`.
* `Stacks.ProjectiveBundleConormal.top_le_splitChartMap_preimage_basicOpen`,
  `top_le_awayι_preimage_basicOpen` and
  `top_le_splitChartMap_comp_chartMap_preimage_tautologicalChart`: the three inclusions of opens
  the `appLE`s above are parametrised by, each the image of an open immersion read as a preimage.

## Implementation notes

**The chart layer is crossed at morphisms and at rings, never at a section of a sheaf of
modules.** `appLE_splitChartMap_awayToSection` splits `splitChartMap` into `Spec.map` of the chart
ring isomorphism followed by `AlgebraicGeometry.Proj.awayι`, uses
`AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE` on the ring maps and
`Stacks.AlgebraicGeometry.ProjTwistChain.appLE_awayι_awayToSection` — the statement that the
standard chart is the identity on degree-zero fractions — and then only the naturality
`AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality` of the global-sections comparison. No
`AlgebraicGeometry.Proj.basicOpenIsoSpec` is unfolded.

**The ratio is bound existentially, not named.** Both assembled statements return the ratio inside
an `∃`, as `exists_tautologicalSectionOver_res_eq_smul` does: the ratio is produced by the
invertibility of `𝒪(1)` and there is no term for it, while the two equations it satisfies — the
one on the bundle and its value across the chart — determine it, the chart being an open
immersion. This is the device recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartTwistProduct`: an object pinned by
equations about a bound variable costs the elaborator nothing, while the same content with the
composite written out does not elaborate.

**No tag is attached, and in particular no `@[stacks 0B3V]`.** Identifying one affine coordinate
is a step of clause 3, not the clause, and the whole `ProjectiveBundleConormal` directory carries
no `@[stacks …]` for that reason.

**What this corrects.** The "Not done here" of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartTwistProduct` records that the
identification of the ratio with `ι m / ι s` — the transport of
`Stacks.TwistPullbackRatio.degreeSection_res_eq` along
`Stacks.ProjectiveBundleConormal.chartTwistIso` and then across `chartMap` — is "still not done",
and that it would have to cross the open immersion `chartMap` to land on an open of `𝐏(ℰ)`. That
crossing is done here; what makes it cheap is that the transport is stated at an *opaque*
morphism into `Proj` and an *arbitrary* open of its target
(`Stacks.ProjectiveBundleConormal.appLE_eq_awayToSection_of_res_eq_smul`), so no chart definition
is ever unfolded. The note remains correct in its other half: clause 3 does not need this.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 01OA](https://stacks.math.columbia.edu/tag/01OA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.ProjectiveBundleSplitting
open Stacks.SymGraded

universe u

namespace Stacks.ProjectiveBundleConormal

/-! ### The affine chart of a split degree-one element, on sections -/

section Split

variable {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]
  (p : M →ₗ[A] A) (s : M) (hps : p s = 1)

/-- **The affine chart lands in the standard open it is the chart of.** The image of
`Stacks.ProjectiveBundleConormal.splitChartMap` is exactly `D₊(ι s)`
(`Stacks.ProjectiveBundleConormal.opensRange_splitChartMap`), so the preimage of that open is
everything; this is the inequality in the form
`AlgebraicGeometry.Scheme.Hom.appLE` asks for. -/
theorem top_le_splitChartMap_preimage_basicOpen :
    (⊤ : (Spec (symRing A (LinearMap.ker p))).Opens) ≤
      splitChartMap p s hps ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen (SymmetricAlgebra.grading A M)
          (SymmetricAlgebra.ι A M s) :=
  (opensRange_splitChartMap p s hps) ▸ (Scheme.Hom.preimage_opensRange _).ge

/-- **The standard chart of `Proj` lands in its own standard open**, the same inequality for
`AlgebraicGeometry.Proj.awayι`, whose image `AlgebraicGeometry.Proj.opensRange_awayι` names. -/
theorem top_le_awayι_preimage_basicOpen :
    (⊤ : (Spec (CommRingCat.of (HomogeneousLocalization.Away
        (SymmetricAlgebra.grading A M) (SymmetricAlgebra.ι A M s)))).Opens) ≤
      AlgebraicGeometry.Proj.awayι (SymmetricAlgebra.grading A M) (SymmetricAlgebra.ι A M s)
          (SymmetricAlgebra.ι_mem_grading_one s) Nat.one_pos ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen (SymmetricAlgebra.grading A M)
          (SymmetricAlgebra.ι A M s) :=
  (AlgebraicGeometry.Proj.opensRange_awayι (SymmetricAlgebra.grading A M)
    (SymmetricAlgebra.ι A M s) (SymmetricAlgebra.ι_mem_grading_one s) Nat.one_pos) ▸
    (Scheme.Hom.preimage_opensRange _).ge

/-- **The affine chart of a split degree-one element, on sections.** A degree-zero fraction `z`
in `ι s`, read as a function on `D₊(ι s)` through `AlgebraicGeometry.Proj.awayToSection`, pulls
back along `Stacks.ProjectiveBundleConormal.splitChartMap` to its image under the chart ring
isomorphism `Stacks.ProjectiveBundleConormal.splitChartRingIso`, i.e. under
`SymmetricAlgebra.splitAwayEquiv`.

So the affine coordinates of `𝐀(ker p) = Spec (Sym_A(ker p))` are the degree-zero fractions of
`Proj(Sym_A M)` away from `ι s`, which is what makes a computation of a ratio on `D₊(ι s)` a
computation in `Sym_A(ker p)`.

The chart is `Spec` of the ring isomorphism followed by `AlgebraicGeometry.Proj.awayι`, so
`AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE` splits the pullback in two:
`Stacks.AlgebraicGeometry.ProjTwistChain.appLE_awayι_awayToSection` says the second leg is the
identity on fractions, up to the global-sections comparison of the affine chart ring, and
`AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality` moves that comparison across the first. -/
theorem appLE_splitChartMap_awayToSection
    (z : HomogeneousLocalization.Away (SymmetricAlgebra.grading A M)
      (SymmetricAlgebra.ι A M s)) :
    ((splitChartMap p s hps).appLE
          (AlgebraicGeometry.Proj.basicOpen (SymmetricAlgebra.grading A M)
            (SymmetricAlgebra.ι A M s)) ⊤
          (top_le_splitChartMap_preimage_basicOpen p s hps)).hom
        ((AlgebraicGeometry.Proj.awayToSection (SymmetricAlgebra.grading A M)
          (SymmetricAlgebra.ι A M s)).hom z) =
      (Scheme.ΓSpecIso (symRing A (LinearMap.ker p))).inv.hom
        ((splitChartRingIso p s hps).hom.hom z) := by
  have hsplit := Scheme.Hom.appLE_comp_appLE
    (Spec.map (splitChartRingIso p s hps).hom)
    (AlgebraicGeometry.Proj.awayι (SymmetricAlgebra.grading A M) (SymmetricAlgebra.ι A M s)
      (SymmetricAlgebra.ι_mem_grading_one s) Nat.one_pos)
    (AlgebraicGeometry.Proj.basicOpen (SymmetricAlgebra.grading A M)
      (SymmetricAlgebra.ι A M s)) ⊤ ⊤
    (top_le_awayι_preimage_basicOpen s) le_top
  have hval := congrArg
    (fun φ : Γ(AlgebraicGeometry.Proj (SymmetricAlgebra.grading A M),
          AlgebraicGeometry.Proj.basicOpen (SymmetricAlgebra.grading A M)
            (SymmetricAlgebra.ι A M s)) ⟶
        Γ(Spec (symRing A (LinearMap.ker p)), ⊤) =>
      φ.hom ((AlgebraicGeometry.Proj.awayToSection (SymmetricAlgebra.grading A M)
        (SymmetricAlgebra.ι A M s)).hom z)) hsplit
  have hnat := congrArg
    (fun φ : CommRingCat.of (HomogeneousLocalization.Away (SymmetricAlgebra.grading A M)
          (SymmetricAlgebra.ι A M s)) ⟶ Γ(Spec (symRing A (LinearMap.ker p)), ⊤) => φ.hom z)
    (Scheme.ΓSpecIso_inv_naturality (splitChartRingIso p s hps).hom)
  refine hval.symm.trans ?_
  refine Eq.trans ?_ hnat.symm
  refine congrArg
    (fun w => (Scheme.Hom.appLE (Spec.map (splitChartRingIso p s hps).hom) ⊤ ⊤ le_top).hom w)
    (Stacks.AlgebraicGeometry.ProjTwistChain.appLE_awayι_awayToSection
      (𝒜 := SymmetricAlgebra.grading A M) Nat.one_pos (SymmetricAlgebra.ι_mem_grading_one s)
      (top_le_awayι_preimage_basicOpen s) z) |>.trans ?_
  exact congrArg
    (fun φ : Γ(Spec (CommRingCat.of (HomogeneousLocalization.Away
          (SymmetricAlgebra.grading A M) (SymmetricAlgebra.ι A M s))), ⊤) ⟶
        Γ(Spec (symRing A (LinearMap.ker p)), ⊤) =>
      φ.hom ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away
        (SymmetricAlgebra.grading A M) (SymmetricAlgebra.ι A M s)))).inv.hom z))
    (Scheme.Hom.appLE_top_top (Spec.map (splitChartRingIso p s hps).hom) le_top)

/-- **An affine coordinate of the chart is a degree-one generator.** For `k` in the kernel of the
linear form, the fraction `ι k / ι s` pulls back along
`Stacks.ProjectiveBundleConormal.splitChartMap` to `ι k`, the degree-one generator of
`Sym_A(ker p)` attached to `k`.

This is `Stacks.ProjectiveBundleConormal.appLE_splitChartMap_awayToSection` read against the
normalisation `SymmetricAlgebra.splitAwayEquiv_mk_ι` that pins the chart identification down. It
is the coordinate that `Stacks.ProjectiveBundleConormal.splitChartOrigin_mk_ι` says vanishes at
the origin of the affine bundle. -/
theorem appLE_splitChartMap_awayToSection_ι (k : LinearMap.ker p) :
    ((splitChartMap p s hps).appLE
          (AlgebraicGeometry.Proj.basicOpen (SymmetricAlgebra.grading A M)
            (SymmetricAlgebra.ι A M s)) ⊤
          (top_le_splitChartMap_preimage_basicOpen p s hps)).hom
        ((AlgebraicGeometry.Proj.awayToSection (SymmetricAlgebra.grading A M)
            (SymmetricAlgebra.ι A M s)).hom
          (HomogeneousLocalization.Away.mk (SymmetricAlgebra.grading A M)
            (SymmetricAlgebra.ι_mem_grading_one s) 1 (SymmetricAlgebra.ι A M (k : M))
            (SymmetricAlgebra.ι_mem_grading_smul _))) =
      (Scheme.ΓSpecIso (symRing A (LinearMap.ker p))).inv.hom
        (SymmetricAlgebra.ι A (LinearMap.ker p) k) :=
  (appLE_splitChartMap_awayToSection p s hps _).trans
    (congrArg (Scheme.ΓSpecIso (symRing A (LinearMap.ker p))).inv.hom
      (SymmetricAlgebra.splitAwayEquiv_mk_ι p s hps k))

end Split

/-! ### The ratio of the tautological chart, computed -/

section Chart

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
  (Q : Stacks.Divisors.InvertibleQuotient X E) {W : X.Opens} (hW : IsAffineOpen W)

/-- **The ratio of the tautological chart exists, and is `ι m / ι s`.** On
`Stacks.ProjectiveBundleConormal.tautologicalChart E W s` the degree-one section attached to `m`
is a function `g` times the one attached to `s`, and that function is carried by the chart
`Stacks.ProjectiveBundleConormal.chartMap` to the degree-zero fraction `ι m / ι s`.

This is `Stacks.ProjectiveBundleConormal.exists_tautologicalSectionOver_res_eq_smul` — which
produces the ratio from invertibility of `𝒪(1)` and says nothing about it — strengthened by
`Stacks.ProjectiveBundleConormal.appLE_chartMap_eq_awayToSection_of_res_eq_smul`. The ratio stays
bound: the two equations determine it, `chartMap` being an open immersion whose preimage of the
tautological chart is `D₊(ι s)`. -/
theorem exists_tautologicalSectionOver_res_eq_smul_appLE_eq (s m : Γ(E, W)) :
    ∃ g : Γ((bundle E).scheme, tautologicalChart E W s),
      (tautologicalTwist E (symPieces E)).presheaf.map
            (homOfLE (tautologicalChart_le E W s)).op (tautologicalSectionOver E W m) =
          ((tautologicalTwist E (symPieces E)).smul g).asHom.hom
            ((tautologicalTwist E (symPieces E)).presheaf.map
              (homOfLE (tautologicalChart_le E W s)).op (tautologicalSectionOver E W s)) ∧
        ((chartMap E (symPieces E) hW).appLE (tautologicalChart E W s)
            (AlgebraicGeometry.Proj.basicOpen (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
              (SymmetricAlgebra.ι Γ(X, W) Γ(E, W) s))
            (basicOpen_le_preimage_chartMap_tautologicalChart E W s hW)).hom g =
          (AlgebraicGeometry.Proj.awayToSection (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
                (SymmetricAlgebra.ι Γ(X, W) Γ(E, W) s)).hom
            (HomogeneousLocalization.Away.mk (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
              (SymmetricAlgebra.ι_mem_grading_one s) 1 (SymmetricAlgebra.ι Γ(X, W) Γ(E, W) m)
              (SymmetricAlgebra.ι_mem_grading_smul m)) :=
  let hex := exists_tautologicalSectionOver_res_eq_smul E W s m
  ⟨hex.choose, hex.choose_spec,
    appLE_chartMap_eq_awayToSection_of_res_eq_smul E hW s m (tautologicalChart_le E W s)
      (basicOpen_le_preimage_chartMap_tautologicalChart E W s hW) hex.choose hex.choose_spec⟩

/-- **The affine bundle on `ker p` lands in the tautological chart**, read through the two charts
in series: `Stacks.ProjectiveBundleConormal.splitChartMap` lands in `D₊(ι s)` and
`Stacks.ProjectiveBundleConormal.basicOpen_le_preimage_chartMap_tautologicalChart` carries that
open into `Stacks.ProjectiveBundleConormal.tautologicalChart E W s`. -/
theorem top_le_splitChartMap_comp_chartMap_preimage_tautologicalChart
    (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W)) (s : Γ(E, W))
    (hs : chartLinearForm Q W eL s = 1) :
    (⊤ : (Spec (symRing Γ(X, W) (LinearMap.ker (chartLinearForm Q W eL)))).Opens) ≤
      (splitChartMap (chartLinearForm Q W eL) s hs ≫ chartMap E (symPieces E) hW) ⁻¹ᵁ
        tautologicalChart E W s := fun y _ =>
  basicOpen_le_preimage_chartMap_tautologicalChart E W s hW
    (top_le_splitChartMap_preimage_basicOpen (chartLinearForm Q W eL) s hs (x := y) trivial)

/-- **The affine coordinate of the chart attached to a section of `ker q` is `ι k`.** Let `W` be
an affine open carrying a frame `eL` for `𝓛` and a section `s` of `ℰ` at which the chart's linear
form `p = eL ∘ q` takes the value `1`, and let `k` be a section of `ker q` over `W`. Then the
ratio of the degree-one section attached to `k` by the one attached to `s`, which exists on
`Stacks.ProjectiveBundleConormal.tautologicalChart E W s`, becomes `ι k` in `Sym_A(ker p)` once
pulled back along the two charts.

**This is the identification of the ratio that clause 3 of [Stacks, Tag 0B3V] turns on, carried
all the way into the affine bundle.** The point of `𝐀(ker p)` named by the section of `𝐏(ℰ)` has
every affine coordinate `ι k / ι s`, `k` a section of `ker q`, equal to a coordinate of the
kernel; `Stacks.ProjectiveBundleConormal.splitChartOrigin_mk_ι` is the other side — those
coordinates vanish at the origin — and
`Stacks.ProjectiveBundleConormal.chartHomEquiv_chartSection_mk_ι` is the same computation
performed along the section instead of on the chart.

The two crossings are composed by `AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE`, and the
identification `Stacks.ProjectiveBundleConormal.kernelSectionsKerEquiv` of `Γ(ker q, W)` with
`ker p` changes nothing but the type. -/
theorem exists_appLE_splitChartMap_comp_chartMap_eq_ι
    (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W)) (s : Γ(E, W))
    (hs : chartLinearForm Q W eL s = 1) (k : Γ(kernel Q.q, W)) :
    ∃ g : Γ((bundle E).scheme, tautologicalChart E W s),
      (tautologicalTwist E (symPieces E)).presheaf.map
            (homOfLE (tautologicalChart_le E W s)).op
            (tautologicalSectionOver E W ((kernel.ι Q.q).app W k)) =
          ((tautologicalTwist E (symPieces E)).smul g).asHom.hom
            ((tautologicalTwist E (symPieces E)).presheaf.map
              (homOfLE (tautologicalChart_le E W s)).op (tautologicalSectionOver E W s)) ∧
        ((splitChartMap (chartLinearForm Q W eL) s hs ≫
                chartMap E (symPieces E) hW).appLE (tautologicalChart E W s) ⊤
            (top_le_splitChartMap_comp_chartMap_preimage_tautologicalChart E Q hW eL s hs)).hom
            g =
          (Scheme.ΓSpecIso
                (symRing Γ(X, W) (LinearMap.ker (chartLinearForm Q W eL)))).inv.hom
            (SymmetricAlgebra.ι Γ(X, W) (LinearMap.ker (chartLinearForm Q W eL))
              (kernelSectionsKerEquiv Q W eL k)) := by
  obtain ⟨g, hg, happ⟩ := exists_tautologicalSectionOver_res_eq_smul_appLE_eq E hW s
    ((kernel.ι Q.q).app W k)
  refine ⟨g, hg, ?_⟩
  have hsplit := Scheme.Hom.appLE_comp_appLE
    (splitChartMap (chartLinearForm Q W eL) s hs) (chartMap E (symPieces E) hW)
    (tautologicalChart E W s)
    (AlgebraicGeometry.Proj.basicOpen (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
      (SymmetricAlgebra.ι Γ(X, W) Γ(E, W) s)) ⊤
    (basicOpen_le_preimage_chartMap_tautologicalChart E W s hW)
    (top_le_splitChartMap_preimage_basicOpen (chartLinearForm Q W eL) s hs)
  have hval := congrArg
    (fun φ : Γ((bundle E).scheme, tautologicalChart E W s) ⟶
        Γ(Spec (symRing Γ(X, W) (LinearMap.ker (chartLinearForm Q W eL))), ⊤) => φ.hom g)
    hsplit
  exact hval.symm.trans
    ((congrArg
        (fun w => ((splitChartMap (chartLinearForm Q W eL) s hs).appLE
            (AlgebraicGeometry.Proj.basicOpen (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
              (SymmetricAlgebra.ι Γ(X, W) Γ(E, W) s)) ⊤
            (top_le_splitChartMap_preimage_basicOpen (chartLinearForm Q W eL) s hs)).hom w)
        happ).trans
      (appLE_splitChartMap_awayToSection_ι (chartLinearForm Q W eL) s hs
        (kernelSectionsKerEquiv Q W eL k)))

end Chart

end Stacks.ProjectiveBundleConormal

end
