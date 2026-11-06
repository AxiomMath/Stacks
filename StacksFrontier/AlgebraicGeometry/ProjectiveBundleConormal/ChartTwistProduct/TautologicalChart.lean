module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartTwistProduct.ScalarIdentity

/-! # The tautological chart of `𝐏(ℰ)` and the hypothesis `hw` of Tag 0B3V clause 3

* the chart `tautologicalChart` on which the ratio exists, and the vanishing on it,
* sections of `𝓛` over the chart coming from `𝒪(1)` upstairs, and the hypothesis `hw`.
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

variable {σ : X ⟶ (bundle E).scheme} (hσ : σ ≫ (bundle E).toBase = 𝟙 X)
  (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L)
  (hqe : (Scheme.Modules.pullbackId X).inv.app E ≫
    (Scheme.Modules.pullbackCongr hσ).inv.app E ≫
      (Scheme.Modules.pullbackComp σ (bundle E).toBase).inv.app E ≫
        (Scheme.Modules.pullback σ).map (tautologicalMap E (symPieces E)) ≫ e.hom = Q.q)

/-! ### The chart on which the ratio exists, and the vanishing with no hypothesis left -/

section Chart

variable (W : X.Opens) (s : Γ(E, W))

/-- **The chart of `𝐏(ℰ)` cut out over `W` by a section `s` of `ℰ`**: the open of `π⁻¹W` on
which the degree-one section attached to `s` does not vanish, i.e. `π⁻¹W ∩ D₊(ι s)` read
upstairs on the bundle rather than through the chart of `Proj`. It is open by
`Stacks.SectionPowerOpen.isOpen_nonvanishingLocusOn`, the analogue over an open of the openness
clause of [Stacks, Tag 01CY].

This is the `V` every statement of this file is parametrised by, specialised: the hypotheses
`hV : V ≤ π⁻¹W` and `hWV : W ≤ σ⁻¹V` hold for it, and — what the parametrised statements cannot
supply — the degree-one section of `s` *generates* `𝒪(1)` on it, which is what produces the
ratio `g`.

It is not `π⁻¹W`: over the full preimage the only section of `𝒪(-1)` is `0`, as recorded in the
implementation notes of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.PullbackSourceSection`. -/
def tautologicalChart : (bundle E).scheme.Opens :=
  Stacks.SectionPowerOpen.nonvanishingOpenOn (tautologicalTwist E (symPieces E))
    ((bundle E).toBase ⁻¹ᵁ W) (tautologicalSectionOver E W s)

/-- **The chart lies over `W`.** A section can only fail to vanish inside its own domain. -/
theorem tautologicalChart_le : tautologicalChart E W s ≤ (bundle E).toBase ⁻¹ᵁ W :=
  Stacks.SectionPowerOpen.nonvanishingOpenOn_le (tautologicalTwist E (symPieces E))
    ((bundle E).toBase ⁻¹ᵁ W) (tautologicalSectionOver E W s)

/-- The points of the chart are the points of the nonvanishing locus, by definition. -/
theorem coe_tautologicalChart :
    ((tautologicalChart E W s : (bundle E).scheme.Opens) : Set (bundle E).scheme) =
      Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn
        (tautologicalTwist E (symPieces E)) ((bundle E).toBase ⁻¹ᵁ W)
        (tautologicalSectionOver E W s) := rfl

/-- **Every degree-one section over the chart is a function times the one attached to `s`.** On
`tautologicalChart E W s` the section `tautologicalSectionOver E W s` vanishes nowhere, hence
generates the sections of `𝒪(1)` there by
`Stacks.ProjectiveBundleConormal.exists_eq_smul_res_of_subset_nonvanishingLocusOn`; so the
restriction of the degree-one section attached to any `m : Γ(ℰ, W)` is a function on the chart
times it.

**This is the ratio `ι m / ι s` of the chart, obtained without the chart of `Proj`.** The
development's other route to it is
`Stacks.TwistPullbackRatio.degreeSection_res_eq` transported along
`Stacks.ProjectiveBundleConormal.chartTwistIso`, which would have to cross the open immersion
`chartMap` to land on an open of `𝐏(ℰ)`; nothing is needed here beyond invertibility of `𝒪(1)`,
because the *hypothesis* `hz` of
`Stacks.ProjectiveBundleConormal.kernelTautologicalMapTwisted_tensorSectionsAt_eq_mul` asks only
that the ratio exist, not that it be `ι m / ι s`. -/
theorem exists_tautologicalSectionOver_res_eq_smul (m : Γ(E, W)) :
    ∃ g : Γ((bundle E).scheme, tautologicalChart E W s),
      (tautologicalTwist E (symPieces E)).presheaf.map
            (homOfLE (tautologicalChart_le E W s)).op (tautologicalSectionOver E W m) =
        ((tautologicalTwist E (symPieces E)).smul g).asHom.hom
          ((tautologicalTwist E (symPieces E)).presheaf.map
            (homOfLE (tautologicalChart_le E W s)).op (tautologicalSectionOver E W s)) :=
  exists_eq_smul_res_of_subset_nonvanishingLocusOn (tautologicalTwist E (symPieces E))
    (tautologicalSectionOver E W s) (tautologicalChart E W s) (tautologicalChart_le E W s)
    (subset_of_eq (coe_tautologicalChart E W s))
    ((tautologicalTwist E (symPieces E)).presheaf.map
      (homOfLE (tautologicalChart_le E W s)).op (tautologicalSectionOver E W m))

/-- **The standard open of a frame lies inside the tautological chart**, read through the chart
`Stacks.ProjectiveBundleConormal.chartMap` of `𝐏(ℰ)` over `W`: every point of `D₊(ι s)` is
carried by that chart into `Stacks.ProjectiveBundleConormal.tautologicalChart E W s`.

This is the chain of `Stacks.ProjectiveBundleConormal.chartSection_preimage_basicOpen_eq_top`
read in the opposite direction, at an arbitrary point of `D₊(ι s)` instead of at a point of the
image of the section. The two inclusions it composes are in fact equalities; only this direction
is needed and only in `≤` form, so neither is stated.

**Why it is wanted.** The conormal computation of [Stacks, Tag 0B3V] clause 3 has to read the
*target* identification over an open `V` of `𝐏(ℰ)` meeting two demands at once. The affine chart
`Spec (Sym_A (ker p))` must map into `V` by an open immersion, so that
`Stacks.Conormal.restrictConormalIsoOfOpenFactor` applies with an open `P` equal to `⊤` — which
is forced, `Stacks.ProjectiveBundleConormal.conormalZeroSectionTildeIso_hom_unit_toOpen` being
unstatable at a variable open. And `𝒪(-1)` must be trivial on `V`, so that the *source*
identification
`Stacks.ProjectiveBundleConormal.exists_conormalCanonicalMap_val_app_tensorSectionsAt` applies.
The second demand rules out `π⁻¹W` outright — over the full preimage the only section of `𝒪(-1)`
is `0` — so `V` has to be the tautological chart, and the first demand is then exactly this
inclusion.

Four set identities and no new mathematics:
`Stacks.ProjectiveBundleConormal.basicOpen_eq_nonvanishingLocus_pullbackSection` identifies
`D₊(ι s)` with the nonvanishing locus of the pulled-back degree-one section over `⊤`,
`Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_top` and
`Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_res` move that to the nonvanishing locus
over `chartMap ⁻¹ π⁻¹W`, `Stacks.NonvanishingLocusRestrict.preimage_nonvanishingLocusOn` — which
is [Stacks, Tag 0H78] over an open — turns it into the preimage of the nonvanishing locus
downstairs, and `Stacks.ProjectiveBundleConormal.coe_tautologicalChart` names the latter. -/
theorem basicOpen_le_preimage_chartMap_tautologicalChart (hW : IsAffineOpen W) :
    AlgebraicGeometry.Proj.basicOpen (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
        (SymmetricAlgebra.ι Γ(X, W) Γ(E, W) s) ≤
      chartMap E (symPieces E) hW ⁻¹ᵁ tautologicalChart E W s := fun w hw => by
  have h1 := (Set.ext_iff.mp
    (basicOpen_eq_nonvanishingLocus_pullbackSection E (symPieces E) hW s) w).mp hw
  have h2 := (Set.ext_iff.mp (Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_top
    ((Scheme.Modules.pullback (chartMap E (symPieces E) hW)).obj
      (tautologicalTwist E (symPieces E)))
    (Scheme.Modules.pullbackSection (chartMap E (symPieces E) hW)
      (tautologicalTwist E (symPieces E)) ((bundle E).toBase ⁻¹ᵁ W) ⊤
      (top_le_chartMap_preimage E (symPieces E) hW) (tautologicalSectionOver E W s))) w).mpr h1
  have h3 := (Set.ext_iff.mp (Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_res
    ((Scheme.Modules.pullback (chartMap E (symPieces E) hW)).obj
      (tautologicalTwist E (symPieces E)))
    (top_le_chartMap_preimage E (symPieces E) hW)
    (unitSection (chartMap E (symPieces E) hW) (tautologicalTwist E (symPieces E))
      ((bundle E).toBase ⁻¹ᵁ W) (tautologicalSectionOver E W s))) w).mp h2
  exact subset_of_eq (coe_tautologicalChart E W s).symm
    ((Set.ext_iff.mp (Stacks.NonvanishingLocusRestrict.preimage_nonvanishingLocusOn
      (chartMap E (symPieces E) hW) (tautologicalTwist E (symPieces E))
      (tautologicalSectionOver E W s)) w).mpr h3.2)

include hσ e hqe in
/-- **The chart lies in the image of `σ`'s domain.** If `W` is affine and the chart's linear form
takes the value `1` at `s`, then `σ` carries the whole of `W` into
`Stacks.ProjectiveBundleConormal.tautologicalChart E W s`: the image `q(s)` spans by
`Stacks.ProjectiveBundleConormal.span_singleton_app_eq_top_of_chartLinearForm_eq_one`, and
`Stacks.ProjectiveBundleConormal.mem_nonvanishingLocusOn_tautologicalSection` is then exactly
the membership wanted. -/
theorem le_preimage_tautologicalChart (hW : IsAffineOpen W)
    (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W)) (hs : chartLinearForm Q W eL s = 1) :
    W ≤ σ ⁻¹ᵁ tautologicalChart E W s := fun _ hx =>
  mem_nonvanishingLocusOn_tautologicalSection E Q hσ e hqe W hW s
    (span_singleton_app_eq_top_of_chartLinearForm_eq_one Q W eL hs) hx

include hσ e hqe in
/-- **`σ` kills the value of the untwisted tautological map on a product section built from a
kernel section — with nothing left to assume.** On the chart
`Stacks.ProjectiveBundleConormal.tautologicalChart E W s`, for every section `k` of `ker q` over
`W` and every section `w` of `𝒪(-1)` over the chart, the function `ṽ(π^*k ⊗ w)` is pulled back
to `0` by `σ`.

This is
`Stacks.ProjectiveBundleConormal.appLE_kernelTautologicalMapTwisted_tensorSectionsAt_eq_zero`
with all three of its remaining hypotheses discharged: `hzk` by
`Stacks.ProjectiveBundleConormal.kernelTautologicalMap_res_unitSection`, `hz` by
`Stacks.ProjectiveBundleConormal.exists_tautologicalSectionOver_res_eq_smul` at
`m = ι k` — which is where the chart is used — and `hg₀` by naming `g₀` as the product itself.

So the condition for the product section to come from a section of `ℐ(σ)`, which is what
`Stacks.ProjectiveBundleConormal.exists_idealSheaf_section_kernelTautologicalMapTwisted` asks
for, holds on a chart that is produced rather than assumed. What clause 3 still needs beyond it
is recorded in this module's "Not done here". -/
theorem appLE_tautologicalChart_kernelTautologicalMapTwisted_eq_zero (hW : IsAffineOpen W)
    (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W)) (hs : chartLinearForm Q W eL s = 1)
    (k : Γ(kernel Q.q, W)) (w : Γ(inverseTautologicalTwist E, tautologicalChart E W s)) :
    σ.appLE (tautologicalChart E W s) W
        (le_preimage_tautologicalChart E Q hσ e hqe W s hW eL hs)
        ((kernelTautologicalMapTwisted E Q).val.app (op (tautologicalChart E W s))
          (tensorSectionsAt (bundle E).scheme.presheaf (bundle E).scheme.ringCatSheaf.2
            (op (tautologicalChart E W s))
            ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q))
            (inverseTautologicalTwist E)
            (((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q)).val.map
              (homOfLE (tautologicalChart_le E W s)).op
              (unitSection (bundle E).toBase (kernel Q.q) W k)) w)) = 0 := by
  obtain ⟨g, hg⟩ := exists_tautologicalSectionOver_res_eq_smul E W s
    ((kernel.ι Q.q).val.app (op W) k)
  exact appLE_kernelTautologicalMapTwisted_tensorSectionsAt_eq_zero E Q hσ e hqe eL s hs
    (tautologicalChart E W s) (tautologicalChart_le E W s)
    (le_preimage_tautologicalChart E Q hσ e hqe W s hW eL hs) k _ w g _
    (kernelTautologicalMap_res_unitSection E Q W (tautologicalChart E W s)
      (tautologicalChart_le E W s) k)
    ((kernelTautologicalMap_res_unitSection E Q W (tautologicalChart E W s)
      (tautologicalChart_le E W s) k).trans hg) rfl

/-! ### Every section of `𝓛` over the chart comes from a section of `𝒪(1)` upstairs -/

include hσ e hqe in
/-- **The map `b₀ ↦ e(σ^*b₀)` is onto the sections of `𝓛` over `W`.** On the chart
`Stacks.ProjectiveBundleConormal.tautologicalChart E W s`, every section `c` of `𝓛` over `W` is
`e` of the pullback along `σ` of some section of `𝒪(1)` over the chart.

This is the statement the downstairs hypothesis `hdown` of
`Stacks.ProjBundleInverseBaseChange.inverseTwistBaseChangeIso_inv_val_app` needs and that the
development did not have. In `hdown` *both* arguments of the pairing are fixed — one of them is
`e(σ^*b₀)` for the `b₀` that the upstairs hypothesis `hup` consumed — so no existence statement
about the pairing can supply it; what can is that the section of `𝓛` the pairing determines is in
the image of `b₀ ↦ e(σ^*b₀)`, which is exactly what is proved here.

The witness is `π^♯(eL c)` times the degree-one section of `s`, restricted to the chart. Three
existing facts and no new mathematics:
`Stacks.ProjectiveBundleConormal.pullbackSection_smul_appLE_toBase` carries the scalar through the
pullback — this is where `σ ≫ π = 𝟙 X` is used, and it is the only reason an arbitrary scalar is
available upstairs; `AlgebraicGeometry.Scheme.Modules.pullbackSection_res` removes the
restriction to the chart, the pullback being taken over `W` on both sides; and
`Stacks.ProjectiveBundleConormal.hom_pullbackSection_tautologicalMap` — the classifying
hypothesis `hqe` read on sections — identifies `e(σ^*(u s))` with `q(s)`. The frame then
finishes: `eL (q s) = 1` by `hs`, so `eL` of the result is `eL c`, and `eL` is injective.

**No `@[stacks 0B3V]` attribute is attached.** Surjectivity of one map on sections over one chart
is an input to clause 3, not the clause; what clause 3 still owes beyond it is recorded in this
module's "Not done here".

The witness is *named* rather than produced, in the variables-and-equation idiom, because the
upstairs hypothesis `hup` of
`Stacks.ProjBundleInverseBaseChange.inverseTwistBaseChangeIso_inv_val_app` asks that it generate
`𝒪(1)` on the chart, which an existential statement cannot say of it:
`Stacks.ProjectiveBundleConormal.exists_hom_pullbackSection_tautologicalChart_eq` is this result
with the witness forgotten again. -/
theorem hom_pullbackSection_smul_tautologicalSectionOver (hW : IsAffineOpen W)
    (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W)) (hs : chartLinearForm Q W eL s = 1) (c : Γ(Q.L, W))
    (b₀ : Γ(tautologicalTwist E (symPieces E), tautologicalChart E W s))
    (hb₀ : b₀ = (bundle E).toBase.appLE W (tautologicalChart E W s)
          (tautologicalChart_le E W s) (eL c) •
        (tautologicalTwist E (symPieces E)).presheaf.map
          (homOfLE (tautologicalChart_le E W s)).op (tautologicalSectionOver E W s)) :
    e.hom.val.app (op W)
        (Scheme.Modules.pullbackSection σ (tautologicalTwist E (symPieces E))
          (tautologicalChart E W s) W
          (le_preimage_tautologicalChart E Q hσ e hqe W s hW eL hs) b₀) = c := by
  have hV : tautologicalChart E W s ≤ (bundle E).toBase ⁻¹ᵁ W := tautologicalChart_le E W s
  have hWV : W ≤ σ ⁻¹ᵁ tautologicalChart E W s :=
    le_preimage_tautologicalChart E Q hσ e hqe W s hW eL hs
  have hbase : e.hom.val.app (op W)
        (Scheme.Modules.pullbackSection σ (tautologicalTwist E (symPieces E))
          (tautologicalChart E W s) W hWV
          ((tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hV).op
            (tautologicalSectionOver E W s))) =
      Q.q.val.app (op W) s :=
    (congrArg (e.hom.val.app (op W))
        (Scheme.Modules.pullbackSection_res σ (tautologicalTwist E (symPieces E)) hV W hWV
          (tautologicalSectionOver E W s))).trans
      (hom_pullbackSection_tautologicalMap E Q hσ e hqe W s)
  subst hb₀
  refine Eq.trans (congrArg (e.hom.val.app (op W))
    (pullbackSection_smul_appLE_toBase E hσ (tautologicalTwist E (symPieces E)) W
      (tautologicalChart E W s) hV hWV (eL c)
      ((tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hV).op
        (tautologicalSectionOver E W s)))) ?_
  refine Eq.trans ((e.hom.val.app (op W)).hom.map_smul (eL c) _) ?_
  refine Eq.trans (congrArg (fun y : Γ(Q.L, W) => (Q.L.smul (eL c)).asHom.hom y) hbase) ?_
  refine eL.injective ?_
  refine Eq.trans (eL.map_smul (eL c) (Q.q.val.app (op W) s)) ?_
  refine Eq.trans (congrArg (fun y : Γ(X, W) => eL c • y) hs) ?_
  simp

include hσ e hqe in
/-- **The map `b₀ ↦ e(σ^*b₀)` is onto the sections of `𝓛` over `W`.** On the chart
`Stacks.ProjectiveBundleConormal.tautologicalChart E W s`, every section `c` of `𝓛` over `W` is
`e` of the pullback along `σ` of some section of `𝒪(1)` over the chart —
`Stacks.ProjectiveBundleConormal.hom_pullbackSection_smul_tautologicalSectionOver` with its
witness forgotten.

This is the reachability statement the downstairs hypothesis `hdown` of
`Stacks.ProjBundleInverseBaseChange.inverseTwistBaseChangeIso_inv_val_app` needs: there both
arguments of the pairing are already determined — one of them is `e(σ^*b₀)` for the `b₀` that the
upstairs hypothesis `hup` consumed — so no existence statement *about the pairing* can supply it;
what can is that the section of `𝓛` the pairing determines is in the image of this map. A consumer
that also has to feed `hup` wants the witness itself and should use the named form. -/
theorem exists_hom_pullbackSection_tautologicalChart_eq (hW : IsAffineOpen W)
    (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W)) (hs : chartLinearForm Q W eL s = 1) (c : Γ(Q.L, W)) :
    ∃ b₀ : Γ(tautologicalTwist E (symPieces E), tautologicalChart E W s),
      e.hom.val.app (op W)
          (Scheme.Modules.pullbackSection σ (tautologicalTwist E (symPieces E))
            (tautologicalChart E W s) W
            (le_preimage_tautologicalChart E Q hσ e hqe W s hW eL hs) b₀) = c :=
  ⟨_, hom_pullbackSection_smul_tautologicalSectionOver E Q hσ e hqe W s hW eL hs c _ rfl⟩

/-! ### The hypothesis `hw` of the chart computation of Tag 0B3V clause 3 -/

section Hw

open Stacks.ProjBundleInverseBaseChange (negOneMulPairingIso'
  exists_tensorPairing_eq_one_of_forall_germ_notMem_maximalIdeal_smul_top_right
  exists_negOneMulIso_hom_tensorSectionsAt_eq_one inverseTwistBaseChangeIso_inv_val_app)

include hσ e hqe in
/-- **The hypothesis `hw` of
`Stacks.ProjectiveBundleConormal.exists_conormalCanonicalMap_val_app_tensorSectionsAt`, for a
section of `𝓛^{⊗ -1}` trivialising it on `W`.** On the chart
`Stacks.ProjectiveBundleConormal.tautologicalChart E W s` the base-change comparison of the
inverse twist carries `w` to the pullback along `σ` of a section of `𝒪(-1)` over the chart.

`Stacks.ProjBundleInverseBaseChange.inverseTwistBaseChangeIso_inv_val_app` reduces this to a pair
of scalar pairings, `hup` upstairs and `hdown` downstairs, sharing a section `b₀` of `𝒪(1)` over
the chart. Both are discharged here, and the order is forced — `hdown` first, because the section
`b₀` that `hup` needs is built out of what `hdown` produces:

* **`hdown`.** `w` generates, so
  `Stacks.ProjBundleInverseBaseChange`
  `.exists_tensorPairing_eq_one_of_forall_germ_notMem_maximalIdeal_smul_top_right`
  — the pairing existence of [Stacks, Tag 01CY] with the generator in the second factor — gives a
  section `c` of `𝓛` over `W` pairing with `w` to `1`. Read against
  `Stacks.ProjBundleInverseBaseChange.negOneMulPairingIso'`, which is the left trivialisation
  `𝓛 ⊗ 𝓛^{⊗ -1} ≅ 𝒪_X` with no braiding in the way, that pairing *is* `hdown`, up to replacing
  `c` by `e(σ^*b₀)`, which
  `Stacks.ProjectiveBundleConormal.hom_pullbackSection_smul_tautologicalSectionOver` does.
* **`hup`.** The `b₀` just named is `π^♯(eL c)` times the degree-one section of `s`, restricted to
  the chart. The scalar is a unit, because `eL c` is
  (`Stacks.ProjectiveBundleConormal.isUnit_linearEquiv_of_tensorPairing_eq_unitSection`) and `π^♯`
  is a ring map; the degree-one section of `s` generates at every point of the chart, the chart
  being its nonvanishing locus by `Stacks.ProjectiveBundleConormal.coe_tautologicalChart`; so `b₀`
  generates there too, by
  `Stacks.ProjectiveBundleConormal.notMem_maximalIdeal_smul_top_smul_of_isUnit`. That is exactly
  what `Stacks.ProjBundleInverseBaseChange.exists_negOneMulIso_hom_tensorSectionsAt_eq_one` asks
  before producing the `w₀` of `hup`.

The hypothesis on `w` is that it generate the sections of `𝓛^{⊗ -1}` over every open of `W` — the
form `Stacks.SheafOfModules.notMem_maximalIdeal_smul_top_of_forall_bijective_smul` converts to the
germ condition, and the form a trivialisation of the restriction supplies; see
`Stacks.ProjectiveBundleConormal`
`.exists_pullbackSection_inverseTwistBaseChangeIso_inv_val_app_restrictIsoUnit`,
where it is discharged. It cannot be dropped: `hdown` asks `w` for a pairing partner, and only a
generator has one.

**No `@[stacks 0B3V]` attribute is attached.** Clause 3 asserts that
`Stacks.ProjectiveBundleConormal.conormalCanonicalMap` is an isomorphism; this is one of the two
inputs that `Stacks.ProjectiveBundleConormal.exists_conormalCanonicalMap_val_app_tensorSectionsAt`
still carries, and the target identification is not touched — see this module's "Not done
here". -/
theorem exists_pullbackSection_inverseTwistBaseChangeIso_inv_val_app (hW : IsAffineOpen W)
    (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W)) (hs : chartLinearForm Q W eL s = 1)
    (w : Γ(Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1), W))
    (hw : ∀ (V : X.Opens) (hVW : V ≤ W), Function.Bijective fun d : Γ(X, V) =>
      d • (show X.Modules from Stacks.SheafOfModules.Invertible.tensorPower X.presheaf
        X.ringCatSheaf.2 Q.L (-1)).presheaf.map (homOfLE hVW).op w) :
    ∃ w₀ : Γ(inverseTautologicalTwist E, tautologicalChart E W s),
      (inverseTwistBaseChangeIso E Q e).inv.val.app (op W) w =
        Scheme.Modules.pullbackSection σ (inverseTautologicalTwist E) (tautologicalChart E W s) W
          (le_preimage_tautologicalChart E Q hσ e hqe W s hW eL hs) w₀ := by
  have hV : tautologicalChart E W s ≤ (bundle E).toBase ⁻¹ᵁ W := tautologicalChart_le E W s
  have hWV : W ≤ σ ⁻¹ᵁ tautologicalChart E W s :=
    le_preimage_tautologicalChart E Q hσ e hqe W s hW eL hs
  obtain ⟨c, hc⟩ := exists_tensorPairing_eq_one_of_forall_germ_notMem_maximalIdeal_smul_top_right
      (negOneMulPairingIso' (X := X.toRingedSpace) Q.L) W w
      (fun y hy => Stacks.SheafOfModules.notMem_maximalIdeal_smul_top_of_forall_bijective_smul
        (X := X.toRingedSpace)
        (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1))
        w (fun V hVW => hw V hVW) y hy)
  have hunit : IsUnit (eL c) :=
    isUnit_linearEquiv_of_tensorPairing_eq_unitSection Q.L _ _ W eL c w hc
  obtain ⟨b₀, hb₀def⟩ : ∃ b₀ : Γ(tautologicalTwist E (symPieces E), tautologicalChart E W s),
      b₀ = (bundle E).toBase.appLE W (tautologicalChart E W s) hV (eL c) •
        (tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hV).op
          (tautologicalSectionOver E W s) := ⟨_, rfl⟩
  obtain ⟨w₀, hup⟩ := exists_negOneMulIso_hom_tensorSectionsAt_eq_one
      (X := (bundle E).scheme.toRingedSpace) (tautologicalTwist E (symPieces E))
      (tautologicalChart E W s) b₀
      (fun y hy => notMem_maximalIdeal_smul_top_smul_of_isUnit
        (tautologicalTwist E (symPieces E)) hV (tautologicalSectionOver E W s)
        (fun z hz hmem => (subset_of_eq (coe_tautologicalChart E W s) hz).2
          ((Stacks.NonvanishingPullback.mem_maximalSmul_iff
            (tautologicalTwist E (symPieces E)) z _).mpr hmem))
        ((bundle E).toBase.appLE W (tautologicalChart E W s) hV (eL c))
        (IsUnit.map ((bundle E).toBase.appLE W (tautologicalChart E W s) hV).hom hunit)
        b₀ hb₀def y hy)
  refine ⟨w₀, inverseTwistBaseChangeIso_inv_val_app E Q e
    (tautologicalChart E W s) W hWV w₀ b₀ w hup ?_⟩
  exact Eq.trans (congrArg (fun z : Γ(Q.L, W) =>
      Stacks.SheafOfModules.tensorPairing (negOneMulPairingIso' (X := X.toRingedSpace) Q.L)
        W z w)
    (hom_pullbackSection_smul_tautologicalSectionOver E Q hσ e hqe W s hW eL hs c b₀ hb₀def)) hc

include hσ e hqe in
/-- **`hw` with nothing left to assume, for the generator a trivialisation of the restriction
names.** If `𝓛^{⊗ -1}` is trivial on `W` — which on a chart it is, by
`Stacks.ProjectiveBundleConormal.restrictInverseTwistIso` applied to a trivialisation of `𝓛` — then
the section `θ⁻¹(1)` it names, restricted to `W`, satisfies the generation hypothesis of
`Stacks.ProjectiveBundleConormal.exists_pullbackSection_inverseTwistBaseChangeIso_inv_val_app`:
its germ escapes `𝔪_y` at every point by
`Stacks.ProjectiveBundleConormal.notMem_maximalIdeal_smul_top_restrictIsoUnit_res`, and
`Stacks.SheafOfModules.bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top` turns that into
generation over every open of `W`.

The generator lives over `W.ι ''ᵁ ⊤`, which is `W` only up to
`AlgebraicGeometry.Scheme.Opens.ι_image_top`; the inequality is a parameter and `w` is a variable
named by `hw`, so a consumer holding either reading can instantiate. -/
theorem exists_pullbackSection_inverseTwistBaseChangeIso_inv_val_app_restrictIsoUnit
    (hW : IsAffineOpen W) (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W))
    (hs : chartLinearForm Q W eL s = 1)
    (θ : (Scheme.Modules.restrictFunctor W.ι).obj
        (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1)) ≅
      𝟙_ (↑W : Scheme.{u}).Modules)
    (hUW : W ≤ W.ι ''ᵁ (⊤ : (↑W : Scheme.{u}).Opens))
    (w : Γ(Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1), W))
    (hw : w = (show X.Modules from Stacks.SheafOfModules.Invertible.tensorPower X.presheaf
          X.ringCatSheaf.2 Q.L (-1)).presheaf.map (homOfLE hUW).op
        (θ.inv.val.app (op (⊤ : (↑W : Scheme.{u}).Opens))
          (1 : Γ((↑W : Scheme.{u}), (⊤ : (↑W : Scheme.{u}).Opens))))) :
    ∃ w₀ : Γ(inverseTautologicalTwist E, tautologicalChart E W s),
      (inverseTwistBaseChangeIso E Q e).inv.val.app (op W) w =
        Scheme.Modules.pullbackSection σ (inverseTautologicalTwist E) (tautologicalChart E W s) W
          (le_preimage_tautologicalChart E Q hσ e hqe W s hW eL hs) w₀ :=
  exists_pullbackSection_inverseTwistBaseChangeIso_inv_val_app E Q hσ e hqe W s hW eL hs w
    (fun V hVW => Stacks.SheafOfModules.bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top
      (X := X.toRingedSpace)
      (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1))
      w V hVW
      (fun y hy => notMem_maximalIdeal_smul_top_restrictIsoUnit_res _ W θ W hUW w hw y (hVW hy)))

include hσ e hqe in
/-- **`hw` with the section `w₀` it produces pinned**, which the two existence statements above
leave open. They determine `σ^*w₀`, hence `w₀` only modulo the ideal of the section, and that is
not enough for the chart computation of [Stacks, Tag 0B3V] clause 3: the source half pins its
section of `ℐ(σ)` by the product of `v(π^*κ)` with `w₀`
(`Stacks.ProjectiveBundleConormal.exists_conormalCanonicalMap_val_app_tensorSectionsAt`), so the
coordinate the target half asks for is only determined once the value of that product on the
*frame* section is known. Here it is `1`.

**The construction is the one that makes it `1`.** The `hup` of
`Stacks.ProjBundleInverseBaseChange.inverseTwistBaseChangeIso_inv_val_app` asks for a section
`b₀` of `𝒪(1)` over the chart generating there, and
`Stacks.ProjectiveBundleConormal.exists_pullbackSection_inverseTwistBaseChangeIso_inv_val_app`
takes for it `π^♯(eL c)` times the degree-one section of `s`, with `c` the pairing partner of
`w` — so the product of the degree-one section of `s` with the `w₀` it returns is the inverse of
`π^♯(eL c)` and not `1`. Taking `b₀` to be the degree-one section of `s` itself removes the
scalar; what that costs is that `hdown` is no longer automatic, since `e(σ^*b₀)` is then `q s`
(`Stacks.ProjectiveBundleConormal.hom_pullbackSection_smul_tautologicalSectionOver` at
`c := q s`, the scalar being `1` by `hs`), and the hypothesis `hpair` is exactly the pairing that
asks for. On a chart `hpair` holds for the generator a trivialisation of `𝓛` names, the frame
`eL` being the one that trivialisation induces.

Generation of `b₀` is `Stacks.ProjectiveBundleConormal.coe_tautologicalChart` — the chart *is*
the nonvanishing locus of that section — crossed to the `𝔪_y • ⊤` spelling by
`Stacks.NonvanishingPullback.mem_maximalSmul_iff`, through
`Stacks.ProjectiveBundleConormal.notMem_maximalIdeal_smul_top_smul_of_isUnit` at the unit `1`.
The pin is the `hup` the construction returns, carried to the
`Stacks.SheafOfModules.Invertible.sectionMulNegOne` spelling by
`Stacks.ProjectiveBundleConormal.sectionMulNegOne_eq_negOneMulIso`.

**No `@[stacks 0B3V]` attribute is attached**; see this module's "Not done here" for what clause
3 still owes. -/
theorem exists_pullbackSection_inverseTwistBaseChangeIso_inv_val_app_pinned (hW : IsAffineOpen W)
    (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W)) (hs : chartLinearForm Q W eL s = 1)
    (w : Γ(Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1), W))
    (hpair : Stacks.SheafOfModules.tensorPairing
        (negOneMulPairingIso' (X := X.toRingedSpace) Q.L) W (Q.q.app W s) w =
      Stacks.SheafOfModules.unitSection X.toRingedSpace W) :
    ∃ w₀ : Γ(inverseTautologicalTwist E, tautologicalChart E W s),
      (inverseTwistBaseChangeIso E Q e).inv.val.app (op W) w =
          Scheme.Modules.pullbackSection σ (inverseTautologicalTwist E)
            (tautologicalChart E W s) W
            (le_preimage_tautologicalChart E Q hσ e hqe W s hW eL hs) w₀ ∧
        Stacks.SheafOfModules.Invertible.sectionMulNegOne (bundle E).scheme.presheaf
            (bundle E).scheme.ringCatSheaf.2 (tautologicalTwist E (symPieces E))
            (op (tautologicalChart E W s))
            ((tautologicalTwist E (symPieces E)).presheaf.map
              (homOfLE (tautologicalChart_le E W s)).op (tautologicalSectionOver E W s)) w₀ =
          (1 : Γ((bundle E).scheme, tautologicalChart E W s)) := by
  have hV : tautologicalChart E W s ≤ (bundle E).toBase ⁻¹ᵁ W := tautologicalChart_le E W s
  have hWV : W ≤ σ ⁻¹ᵁ tautologicalChart E W s :=
    le_preimage_tautologicalChart E Q hσ e hqe W s hW eL hs
  have hr : (bundle E).toBase.appLE W (tautologicalChart E W s) hV (eL (Q.q.app W s)) = 1 :=
    (congrArg (fun z : Γ(X, W) =>
      (bundle E).toBase.appLE W (tautologicalChart E W s) hV z) hs).trans (map_one _)
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : Γ(tautologicalTwist E (symPieces E), tautologicalChart E W s),
      b₀ = (tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hV).op
        (tautologicalSectionOver E W s) := ⟨_, rfl⟩
  have hb₀smul : b₀ = (bundle E).toBase.appLE W (tautologicalChart E W s) hV
        (eL (Q.q.app W s)) •
      (tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hV).op
        (tautologicalSectionOver E W s) :=
    hb₀.trans (((congrArg (fun z : Γ((bundle E).scheme, tautologicalChart E W s) =>
      z • (tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hV).op
        (tautologicalSectionOver E W s)) hr).trans (one_smul _ _)).symm)
  obtain ⟨w₀, hup⟩ := exists_negOneMulIso_hom_tensorSectionsAt_eq_one
      (X := (bundle E).scheme.toRingedSpace) (tautologicalTwist E (symPieces E))
      (tautologicalChart E W s) b₀
      (fun y hy => notMem_maximalIdeal_smul_top_smul_of_isUnit
        (tautologicalTwist E (symPieces E)) hV (tautologicalSectionOver E W s)
        (fun z hz hmem => (subset_of_eq (coe_tautologicalChart E W s) hz).2
          ((Stacks.NonvanishingPullback.mem_maximalSmul_iff
            (tautologicalTwist E (symPieces E)) z _).mpr hmem))
        ((bundle E).toBase.appLE W (tautologicalChart E W s) hV (eL (Q.q.app W s)))
        (Eq.mp (congrArg IsUnit hr.symm) isUnit_one)
        b₀ hb₀smul y hy)
  refine ⟨w₀, inverseTwistBaseChangeIso_inv_val_app E Q e
    (tautologicalChart E W s) W hWV w₀ b₀ w hup
    (Eq.trans (congrArg (fun z : Γ(Q.L, W) =>
        Stacks.SheafOfModules.tensorPairing (negOneMulPairingIso' (X := X.toRingedSpace) Q.L)
          W z w)
      (hom_pullbackSection_smul_tautologicalSectionOver E Q hσ e hqe W s hW eL hs
        (Q.q.app W s) b₀ hb₀smul)) hpair), ?_⟩
  refine Eq.trans (congrArg (fun z : Γ(tautologicalTwist E (symPieces E),
      tautologicalChart E W s) =>
    Stacks.SheafOfModules.Invertible.sectionMulNegOne (bundle E).scheme.presheaf
      (bundle E).scheme.ringCatSheaf.2 (tautologicalTwist E (symPieces E))
      (op (tautologicalChart E W s)) z w₀) hb₀).symm ?_
  exact Eq.trans (sectionMulNegOne_eq_negOneMulIso (tautologicalTwist E (symPieces E))
    (tautologicalChart E W s) b₀ w₀) hup

end Hw

end Chart

end Stacks.ProjectiveBundleConormal

end
