module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartTwistProduct.TautologicalChart

/-! # Reindexing the chart data to a smaller base open, and the frame of a section

* restricting `unitSection`, `tautologicalSectionOver` and the ratio identity to `W ≤ U`,
* a frame around every point for a section of `ℰ` whose image pairs to `1`.
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

/-! ### Moving the chart data to a smaller base open -/

section Reindex

/-- **Pulling a section back along `π` is compatible with shrinking the open it lives on.** The
canonical section of `π^*ℰ` over `π⁻¹U` attached to `s : Γ(ℰ, U)` restricts, along `π⁻¹W ≤ π⁻¹U`,
to the one attached to `s|_W`.

This is naturality of the unit of `π^* ⊣ π_*` read on one section; it is the same step
`Stacks.Conormal.pullbackSection_restrict_source` performs for
`AlgebraicGeometry.Scheme.Modules.pullbackSection`, at the unit itself rather than at the unit
followed by a restriction. -/
theorem unitSection_res (U W : X.Opens) (hWU : W ≤ U) (s : Γ(E, U)) :
    ((Scheme.Modules.pullback (bundle E).toBase).obj E).val.map
        (homOfLE ((bundle E).toBase.preimage_mono hWU)).op
        (unitSection (bundle E).toBase E U s) =
      unitSection (bundle E).toBase E W (E.val.map (homOfLE hWU).op s) :=
  (PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction (bundle E).toBase).unit.app E).val
    (homOfLE hWU).op s).symm

/-- **The degree-one section attached to a section of `ℰ` is compatible with shrinking the base
open.** For `W ≤ U` the section `Stacks.ProjectiveBundleConormal.tautologicalSectionOver E U s` of
`𝒪(1)` over `π⁻¹U` restricts, along `π⁻¹W ≤ π⁻¹U`, to the one attached to `s|_W` over `π⁻¹W`.

The clause of [Stacks, Tag 0B3V] computing the conormal generator at a *given* `s` over a *given*
base open `U` is proved by shrinking `U` to an affine open carrying a frame, and this is what
carries its ratio hypothesis down to that smaller open: the ratio is an equation between
degree-one sections attached to sections of `ℰ` over `U`, and the chart over the smaller open is
cut out by the restricted section. Naturality of `u : π^*ℰ ⟶ 𝒪(1)` and `unitSection_res`, and
nothing else. -/
theorem tautologicalSectionOver_res (U W : X.Opens) (hWU : W ≤ U) (s : Γ(E, U)) :
    (tautologicalTwist E (symPieces E)).presheaf.map
        (homOfLE ((bundle E).toBase.preimage_mono hWU)).op
        (tautologicalSectionOver E U s) =
      tautologicalSectionOver E W (E.val.map (homOfLE hWU).op s) :=
  (PresheafOfModules.naturality_apply (tautologicalMap E (symPieces E)).val
      (homOfLE ((bundle E).toBase.preimage_mono hWU)).op
      (unitSection (bundle E).toBase E U s)).symm.trans
    (congrArg
      (fun z : Γ((Scheme.Modules.pullback (bundle E).toBase).obj E,
          (bundle E).toBase ⁻¹ᵁ W) =>
        (tautologicalMap E (symPieces E)).val.app (op ((bundle E).toBase ⁻¹ᵁ W)) z)
      (unitSection_res E U W hWU s))

/-- **A section of an invertible module that vanishes nowhere on an open determines the function
scaling it uniquely.** This is the injectivity half of
`Stacks.SheafOfModules.bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top`, stated at the
`Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn` hypothesis — the companion of
`Stacks.ProjectiveBundleConormal.exists_eq_smul_res_of_subset_nonvanishingLocusOn`, which is its
surjectivity half and the only half the development had. -/
theorem smul_res_injective_of_subset_nonvanishingLocusOn {Y : Scheme.{u}} (L : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y L] {U : Y.Opens} (t : Γ(L, U))
    (V : Y.Opens) (hVU : V ≤ U)
    (hV : (V : Set Y) ⊆ Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn L U t) :
    Function.Injective
      fun g : Γ(Y, V) => (L.smul g).hom (L.presheaf.map (homOfLE hVU).op t) :=
  (Stacks.SheafOfModules.bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top
    (X := Y.toRingedSpace) L t V hVU (fun y hy hmem => (hV hy).2
      ((Stacks.NonvanishingPullback.mem_maximalSmul_iff L y _).mpr hmem))).injective

/-- **Two ratios of the same pair of degree-one sections agree where they meet.** Let `sU` and
`mU` be sections of `ℰ` over `U`, let `f` be a function on an open `V ≤ π⁻¹U` with
`v(mU) = f · v(sU)` there, let `W ≤ U`, and let `g` be a function on the chart
`Stacks.ProjectiveBundleConormal.tautologicalChart E W (sU|_W)` with
`v(mU|_W) = g · v(sU|_W)` there. Then `f` and `g` agree on `V ⊓ chart`.

Neither `V` nor `W` is otherwise constrained, and the chart is the open on which the conclusion is
available at all: it is exactly where `v(sU|_W)` generates, so where the function scaling it is
determined. The `f` of [Stacks, Tag 0B3V]'s normalization clause is given on an arbitrary `V`,
while the chart computation produces its own ratio on its own chart; this is what identifies the
two, and it is the only place the clause uses that the chart is a nonvanishing locus.

`tautologicalSectionOver_res` reindexes the first equation at the smaller base open and
`smul_res_injective_of_subset_nonvanishingLocusOn` cancels the generator. -/
theorem res_eq_res_of_tautologicalSectionOver_eq_smul
    (U : X.Opens) (sU mU : Γ(E, U)) (W : X.Opens) (hWU : W ≤ U)
    (V : (bundle E).scheme.Opens) (hV : V ≤ (bundle E).toBase ⁻¹ᵁ U)
    (f : Γ((bundle E).scheme, V))
    (hf : (tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hV).op
          (tautologicalSectionOver E U mU) =
        ((tautologicalTwist E (symPieces E)).smul f).hom
          ((tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hV).op
            (tautologicalSectionOver E U sU)))
    (g : Γ((bundle E).scheme, tautologicalChart E W (E.val.map (homOfLE hWU).op sU)))
    (hg : (tautologicalTwist E (symPieces E)).presheaf.map
            (homOfLE (tautologicalChart_le E W (E.val.map (homOfLE hWU).op sU))).op
          (tautologicalSectionOver E W (E.val.map (homOfLE hWU).op mU)) =
        ((tautologicalTwist E (symPieces E)).smul g).hom
          ((tautologicalTwist E (symPieces E)).presheaf.map
            (homOfLE (tautologicalChart_le E W (E.val.map (homOfLE hWU).op sU))).op
            (tautologicalSectionOver E W (E.val.map (homOfLE hWU).op sU)))) :
    (bundle E).scheme.presheaf.map
        (homOfLE (inf_le_left :
          V ⊓ tautologicalChart E W (E.val.map (homOfLE hWU).op sU) ≤ V)).op f =
      (bundle E).scheme.presheaf.map
        (homOfLE (inf_le_right :
          V ⊓ tautologicalChart E W (E.val.map (homOfLE hWU).op sU) ≤
            tautologicalChart E W (E.val.map (homOfLE hWU).op sU))).op g := by
  have hPV : V ⊓ tautologicalChart E W (E.val.map (homOfLE hWU).op sU) ≤ V := inf_le_left
  have hPC : V ⊓ tautologicalChart E W (E.val.map (homOfLE hWU).op sU) ≤
      tautologicalChart E W (E.val.map (homOfLE hWU).op sU) := inf_le_right
  have hPW : V ⊓ tautologicalChart E W (E.val.map (homOfLE hWU).op sU) ≤
      (bundle E).toBase ⁻¹ᵁ W :=
    hPC.trans (tautologicalChart_le E W (E.val.map (homOfLE hWU).op sU))
  -- a degree-one section over `π⁻¹B`, restricted to the intersection and reindexed at `W`
  have down : ∀ (B : X.Opens) (hWB : W ≤ B) (T : (bundle E).scheme.Opens)
      (hT : T ≤ (bundle E).toBase ⁻¹ᵁ B)
      (hP : V ⊓ tautologicalChart E W (E.val.map (homOfLE hWU).op sU) ≤ T)
      (aB : Γ(E, B)) (aW : Γ(E, W)) (ha : E.val.map (homOfLE hWB).op aB = aW),
      (tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hP).op
          ((tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hT).op
            (tautologicalSectionOver E B aB)) =
        (tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hPW).op
          (tautologicalSectionOver E W aW) := by
    intro B hWB T hT hP aB aW ha
    refine Eq.trans (PresheafOfModules.map_comp_apply
      (M := (tautologicalTwist E (symPieces E)).val) (homOfLE hT).op (homOfLE hP).op _).symm ?_
    refine Eq.trans (PresheafOfModules.congr_map_apply
      (M := (tautologicalTwist E (symPieces E)).val)
      (f := (homOfLE hT).op ≫ (homOfLE hP).op)
      (g := (homOfLE ((bundle E).toBase.preimage_mono hWB)).op ≫ (homOfLE hPW).op)
      (Subsingleton.elim _ _) _) ?_
    refine Eq.trans (PresheafOfModules.map_comp_apply
      (M := (tautologicalTwist E (symPieces E)).val)
      (homOfLE ((bundle E).toBase.preimage_mono hWB)).op (homOfLE hPW).op _) ?_
    refine Eq.trans (congrArg
      (fun z : Γ(tautologicalTwist E (symPieces E), (bundle E).toBase ⁻¹ᵁ W) =>
        (tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hPW).op z)
      (tautologicalSectionOver_res E B W hWB aB)) ?_
    exact congrArg
      (fun z : Γ(E, W) =>
        (tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hPW).op
          (tautologicalSectionOver E W z)) ha
  -- the same for a ratio equation, the scalar restricted
  have move : ∀ (B : X.Opens) (hWB : W ≤ B) (T : (bundle E).scheme.Opens)
      (hT : T ≤ (bundle E).toBase ⁻¹ᵁ B)
      (hP : V ⊓ tautologicalChart E W (E.val.map (homOfLE hWU).op sU) ≤ T)
      (c : Γ((bundle E).scheme, T)) (aB bB : Γ(E, B))
      (ha : E.val.map (homOfLE hWB).op aB = E.val.map (homOfLE hWU).op mU)
      (hb : E.val.map (homOfLE hWB).op bB = E.val.map (homOfLE hWU).op sU),
      (tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hT).op
            (tautologicalSectionOver E B aB) =
          ((tautologicalTwist E (symPieces E)).smul c).hom
            ((tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hT).op
              (tautologicalSectionOver E B bB)) →
        (tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hPW).op
              (tautologicalSectionOver E W (E.val.map (homOfLE hWU).op mU)) =
          ((tautologicalTwist E (symPieces E)).smul
              ((bundle E).scheme.presheaf.map (homOfLE hP).op c)).hom
            ((tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hPW).op
              (tautologicalSectionOver E W (E.val.map (homOfLE hWU).op sU))) := by
    intro B hWB T hT hP c aB bB ha hb hc
    refine Eq.trans (down B hWB T hT hP aB _ ha).symm ?_
    refine Eq.trans (congrArg
      (fun z : Γ(tautologicalTwist E (symPieces E), T) =>
        (tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hP).op z) hc) ?_
    refine Eq.trans (map_smulₛₗ
      ((tautologicalTwist E (symPieces E)).val.restrictₛₗ (homOfLE hP).op) c _) ?_
    exact congrArg
      (fun z : Γ(tautologicalTwist E (symPieces E),
          V ⊓ tautologicalChart E W (E.val.map (homOfLE hWU).op sU)) =>
        ((tautologicalTwist E (symPieces E)).smul
          ((bundle E).scheme.presheaf.map (homOfLE hP).op c)).hom z)
      (down B hWB T hT hP bB _ hb)
  refine smul_res_injective_of_subset_nonvanishingLocusOn
    (tautologicalTwist E (symPieces E))
    (tautologicalSectionOver E W (E.val.map (homOfLE hWU).op sU)) _ hPW
    (fun y hy => subset_of_eq
      (coe_tautologicalChart E W (E.val.map (homOfLE hWU).op sU)) hy.2) ?_
  refine Eq.trans (move U hWU V hV hPV f mU sU rfl rfl hf).symm ?_
  exact move W le_rfl (tautologicalChart E W (E.val.map (homOfLE hWU).op sU))
    (tautologicalChart_le E W (E.val.map (homOfLE hWU).op sU)) hPC g
    (E.val.map (homOfLE hWU).op mU) (E.val.map (homOfLE hWU).op sU)
    (val_map_le_refl E W _) (val_map_le_refl E W _) hg

end Reindex

/-! ### The frame of a given section, from its pairing alone -/

section Frame

variable {X : Scheme.{u}} {E : X.Modules}

/-- **A section of `ℰ` whose image pairs to `1` carries a frame around every point of its
domain.** Let `q : ℰ ⟶ 𝓛` be an invertible quotient, let `s` be a section of `ℰ` over `U` and
suppose `q s` pairs to the unit section against some section `w` of a tensor inverse of `𝓛` over
`U`. Then every point of `U` has an affine open neighbourhood `W ≤ U` carrying a frame
`eL : Γ(𝓛, W) ≃ₗ Γ(X, W)` with `Stacks.ProjectiveBundleConormal.chartLinearForm` of `s|_W` equal
to `1`.

**This is the hypothesis the chart computation of [Stacks, Tag 0B3V] clause 3 asks for, produced
at a section that is given rather than chosen.**
`Stacks.ProjectiveBundleConormal.exists_affine_open_chartData` is the cover that clause's
isomorphism statement runs on, and it cannot serve here: it returns a section of its own choosing,
whereas the normalization clause fixes `s` in advance and asserts something about *that* ratio.

Three steps, all proved. An invertible module is trivial on an affine open inside any prescribed
open (`Stacks.Modules.exists_affineOpen_restrict_iso_unit_of_isInvertible`), and the
trivialisation names a frame `e₀` the same way
`Stacks.ProjectiveBundleConormal.exists_affine_open_splitting` reads one off. The pairing makes
`c ↦ c · (q s)` surjective over every smaller open
(`Stacks.SheafOfModules.bijective_smul_of_tensorPairing_eq_unitSection`) — this is the retraction
the pairing supplies — so `e₀ (q s|_W)` is a unit
(`Stacks.SheafOfModules.Invertible.isUnit_linearEquiv_of_surjective_smul`). Rescaling `e₀` by that
unit normalises the value to `1`; the frame is only asked to exist, so the rescaling costs
nothing. -/
theorem exists_isAffineOpen_chartLinearForm_eq_one
    (Q : Stacks.Divisors.InvertibleQuotient X E) (U : X.Opens) (s : Γ(E, U))
    (N : X.Modules)
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩).obj (Q.L)).obj (N)) ≅
      _root_.SheafOfModules.unit (structureSheafRing X.toRingedSpace))
    (w : N.val.obj (op U))
    (hw : Stacks.SheafOfModules.tensorPairing ψ U (Q.q.app U s) w =
      Stacks.SheafOfModules.unitSection X.toRingedSpace U)
    (x : X) (hx : x ∈ U) :
    ∃ (W : X.Opens) (hWU : W ≤ U), x ∈ W ∧ IsAffineOpen W ∧
      ∃ eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W),
        chartLinearForm Q W eL (E.val.map (homOfLE hWU).op s) = 1 := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property Q.L :=
    Q.invertible
  obtain ⟨W, hW, hxW, hWU, ⟨eW⟩⟩ :=
    Stacks.Modules.exists_affineOpen_restrict_iso_unit_of_isInvertible Q.L (W := U) hx
  let e₀ : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W) :=
    ((_root_.SheafOfModules.evaluation (X.ringCatSheaf.over W)
      (op (Over.mk (homOfLE (le_refl W))))).mapIso
        (Stacks.Modules.overIsoUnitOfRestrictIsoUnit Q.L W eW)).toLinearEquiv
  have hnat : Q.q.app W (E.val.map (homOfLE hWU).op s) =
      Q.L.val.map (homOfLE hWU).op (Q.q.app U s) :=
    NatTrans.naturality_apply Q.q.mapPresheaf (homOfLE hWU).op s
  obtain ⟨u, hu⟩ : IsUnit (e₀ (Q.q.app W (E.val.map (homOfLE hWU).op s))) := by
    rw [hnat]
    exact Stacks.SheafOfModules.Invertible.isUnit_linearEquiv_of_surjective_smul e₀
      (Stacks.SheafOfModules.bijective_smul_of_tensorPairing_eq_unitSection ψ U
        (Q.q.app U s) w hw W hWU).surjective
  refine ⟨W, hWU, hxW, hW, e₀.trans (LinearEquiv.smulOfUnit u⁻¹), ?_⟩
  show (u⁻¹ : Γ(X, W)ˣ) • e₀ (Q.q.app W (E.val.map (homOfLE hWU).op s)) = 1
  rw [← hu]
  exact u.inv_mul

end Frame

end Stacks.ProjectiveBundleConormal

end
