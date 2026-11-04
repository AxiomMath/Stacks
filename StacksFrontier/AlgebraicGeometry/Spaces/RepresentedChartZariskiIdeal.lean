module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.IdealSheafSpelling
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiIdealSubmodule
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiStalkOrdinary
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealSheafIsoInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction

/-!
# The Zariski restriction of the kernel ideal sheaf of a represented morphism

Let `B` be a big fppf site containing a scheme `S`, let `j : R ⟶ V` be a morphism of the big fppf
category over `S`, and let `𝓘` be `AlgebraicGeometry.Space.kernelIdealSheaf` of the morphism of
algebraic spaces `yoneda.obj R ⟶ yoneda.obj V` which `j` represents, the kernel of the structure
map `♯` of Stacks 03G8. The identity of `yoneda.obj V` is an étale scheme chart of it,
`AlgebraicGeometry.Space.selfChart`, whose scheme is the scheme underlying `V`, and
`AlgebraicGeometry.Space.chartZariskiIdealSheaf` restricts `𝓘` along that chart to a submodule of
`𝒪_V` on the small Zariski site of the scheme underlying `V`.

This file identifies that restriction with the scheme-level ideal sheaf of `j`: its ideal of
sections over an open `W` is `RingHom.ker` of the ring map which `j` induces on sections there,
and it is isomorphic to `Stacks.ClosedImmersion.idealSheaf` of the underlying morphism of schemes,
the categorical kernel of `𝒪_V ⟶ j_*𝒪_R`. When the morphism of schemes underlying `j` is a closed
immersion, `𝓘` is the defining ideal sheaf of Stacks 03MB of the closed subspace
`AlgebraicGeometry.Space.closedSubspaceRange` which `j` cuts out of `yoneda.obj V`, and the same
statements hold for that defining ideal sheaf.

## Main results

* `AlgebraicGeometry.Γ_map_topIso_inv_eq_zero_iff_of_isPullback` and
  `AlgebraicGeometry.mem_ker_Γ_map_iff_mem_ker_app_of_isPullback`: for any fibre product of an
  open immersion `W.ι` with `f`, the kernel of the global-sections map of the projection to `W`,
  pulled back along `AlgebraicGeometry.Scheme.Opens.topIso`, is the kernel of `f.app W`.
* `AlgebraicGeometry.Space.isPullback_representedChart_toScheme` and
  `AlgebraicGeometry.Space.isPullback_snd_openChart_selfChart`: the representability square of a
  represented morphism, read in schemes, and its instance at the chart cut out by a Zariski open
  of the representing scheme, where the leg to the chart is the open immersion.
* `AlgebraicGeometry.Space.openChartIdeal_kernelIdealSheaf_selfChart` and
  `AlgebraicGeometry.Space.chartZariskiIdealSheaf_selfChart_kernelIdealSheaf_obj_eq_ker`: the
  ideal which the open `W` inherits from `AlgebraicGeometry.Space.kernelIdealSheaf` of the
  represented morphism is `RingHom.ker (j.app W)`.
* `AlgebraicGeometry.Space.chartZariskiKernelIdealSheafSelfChartIsoIdealSheaf` and
  `AlgebraicGeometry.Space.chartZariskiKernelIdealSheafSelfChartIsoIdealSheaf_hom_comp_ι`: the
  Zariski restriction of the space-level kernel ideal sheaf is isomorphic to the scheme-level
  ideal sheaf of `j`, compatibly with the two inclusions into `𝒪_V`.
* `AlgebraicGeometry.Space.openChartIdeal_closedSubspaceRange_selfChart`,
  `AlgebraicGeometry.Space.chartZariskiIdealSheaf_selfChart_obj_eq_ker`,
  `AlgebraicGeometry.Space.chartZariskiIdealSheafSelfChartIsoIdealSheaf` and
  `AlgebraicGeometry.Space.chartZariskiIdealSheafSelfChartIsoIdealSheaf_hom_comp_ι`: the same
  statements for the defining ideal sheaf of the closed subspace cut out by a closed immersion
  `j`.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The scheme-level step -/

/-- **A regular function on an open `W` of `Y` is killed by the projection of any fibre product
of `W ⟶ Y` with `f : X ⟶ Y` exactly when it is killed by `f` on sections over `W`.** -/
theorem Γ_map_topIso_inv_eq_zero_iff_of_isPullback {X Y : Scheme.{u}} (f : X ⟶ Y) (W : Y.Opens)
    {Q : Scheme.{u}} (q : Q ⟶ W.toScheme) (p : Q ⟶ X) (hpb : IsPullback q p W.ι f)
    (r : Γ(Y, W)) :
    (Scheme.Γ.map q.op).hom (W.topIso.inv.hom r) = 0 ↔ (f.app W).hom r = 0 := by
  set e := hpb.isoIsPullback _ _ (isPullback_morphismRestrict f W) with he
  have hfac : e.hom ≫ (f ∣_ W) = q :=
    hpb.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict f W)
  set ψ : Γ(X, f ⁻¹ᵁ W) ≅ Γ(Q, ⊤) :=
    (f ⁻¹ᵁ W).topIso.symm ≪≫ Scheme.Γ.mapIso e.op with hψ
  have hsplit : Scheme.Γ.map q.op
      = Scheme.Γ.map (f ∣_ W).op ≫ Scheme.Γ.map e.hom.op := by
    rw [← hfac, op_comp, Scheme.Γ.map_comp]
  have hkey : W.topIso.inv ≫ Scheme.Γ.map q.op = f.app W ≫ ψ.hom :=
    (congrArg (fun z => W.topIso.inv ≫ z) hsplit).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ Scheme.Γ.map e.hom.op)
            (topIso_inv_comp_Γ_map_morphismRestrict f W)).trans
          (Category.assoc _ _ _)))
  have happ : (Scheme.Γ.map q.op).hom (W.topIso.inv.hom r) = ψ.hom.hom ((f.app W).hom r) :=
    congrArg (fun φ : Γ(Y, W) ⟶ Γ(Q, ⊤) => φ.hom r) hkey
  have hzero : ∀ x : Γ(X, f ⁻¹ᵁ W), ψ.hom.hom x = 0 → x = 0 := by
    intro x hx
    have hinv : ψ.inv.hom (ψ.hom.hom x) = x :=
      congrArg (fun φ : Γ(X, f ⁻¹ᵁ W) ⟶ Γ(X, f ⁻¹ᵁ W) => φ.hom x) ψ.hom_inv_id
    rw [← hinv, hx]
    exact map_zero _
  rw [happ]
  refine ⟨fun h0 => hzero _ h0, fun h0 => ?_⟩
  rw [h0]
  exact map_zero _

/-- `AlgebraicGeometry.Γ_map_topIso_inv_eq_zero_iff_of_isPullback` as an equivalence of
memberships in the two kernel ideals, with the transported function given as a separate argument
together with the equation that computes it. -/
theorem mem_ker_Γ_map_iff_mem_ker_app_of_isPullback {X Y : Scheme.{u}} (f : X ⟶ Y) (W : Y.Opens)
    {Q : Scheme.{u}} (q : Q ⟶ W.toScheme) (p : Q ⟶ X) (hpb : IsPullback q p W.ι f)
    (r : Γ(Y, W)) (a : Γ(W.toScheme, ⊤)) (ha : a = W.topIso.inv.hom r) :
    (a ∈ RingHom.ker (Scheme.Γ.map q.op).hom) ↔ r ∈ RingHom.ker (f.app W).hom := by
  have hleft : (a ∈ RingHom.ker (Scheme.Γ.map q.op).hom) ↔
      (Scheme.Γ.map q.op).hom a = 0 := RingHom.mem_ker
  have hright : (r ∈ RingHom.ker (f.app W).hom) ↔ (f.app W).hom r = 0 := RingHom.mem_ker
  exact hleft.trans
    (((congrArg (fun y => (Scheme.Γ.map q.op).hom y = 0) ha).to_iff).trans
      ((Γ_map_topIso_inv_eq_zero_iff_of_isPullback f W q p hpb r).trans hright.symm))

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The comparison of scalars at a chart is the comparison of `topIso` -/

/-- **The comparison of scalars of the chart sections identification is the inverse of
`AlgebraicGeometry.Scheme.Opens.topIso`, on elements.** -/
theorem chartSectionsRingHom_apply_eq_topIso_inv (X : AlgebraicSpaces B S hS)
    (A : SmallEtale B S hS X.1) (W : (chartScheme A).Opens) (r : Γ(chartScheme A, W)) :
    chartSectionsRingHom B S hS X A W r = W.topIso.inv.hom r :=
  (congrArg (fun y => W.topIso.inv.hom y)
      (openChartTopRingHom_chartSectionsRingHom B S hS X A W r)).symm.trans
    (W.topIso.hom_inv_id_apply _)

/-! ### The representability square at a Zariski open of the representing scheme -/

variable (V : BigFppfOver B S hS)

/-- **The morphism of schemes underlying the structure morphism of the étale chart which a
Zariski open of the representing scheme cuts out is the inclusion of that open.** -/
theorem toScheme_map_yonedaEquiv_openChart_selfChart
    (W : (chartScheme (selfChart B S hS V)).Opens) :
    (BigFppfOver.toScheme B S hS).map
        (yonedaEquiv (openChart B S hS (yoneda.obj V) (selfChart B S hS V) W).1.hom) =
      W.ι :=
  (congrArg (fun m => (BigFppfOver.toScheme B S hS).map m)
      (((congrArg (fun z => yonedaEquiv z)
            (Category.comp_id (yoneda.map (openSubHom V W)))).trans
        (yonedaEquiv_yoneda_map (openSubHom V W))))).trans
    (toScheme_map_openSubHom ..)

/-- **The representability square of a represented morphism, read in schemes.** -/
theorem isPullback_representedChart_toScheme {R : BigFppfOver B S hS} (j : R ⟶ V)
    (P : SmallEtale B S hS (yoneda.obj V)) :
    IsPullback
      ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_yoneda_map B S hS j).snd P.1.hom))
      ((BigFppfOver.toScheme B S hS).map
        (yonedaEquiv ((relativelyRepresentable_yoneda_map B S hS j).fst P.1.hom)))
      ((BigFppfOver.toScheme B S hS).map (yonedaEquiv P.1.hom))
      ((BigFppfOver.toScheme B S hS).map j) :=
  (isPullback_representedChart_schemes B S hS j
    (relativelyRepresentable_yoneda_map B S hS j) P).map B.inclusion

/-- **At the chart cut out by a Zariski open of the representing scheme, the cartesian projection
is a fibre product of that open with `j`**, the leg to the chart being the open immersion
`W.ι`. -/
theorem isPullback_snd_openChart_selfChart {R : BigFppfOver B S hS} (j : R ⟶ V)
    (W : (chartScheme (selfChart B S hS V)).Opens) :
    IsPullback
      ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_yoneda_map B S hS j).snd
          (openChart B S hS (yoneda.obj V) (selfChart B S hS V) W).1.hom))
      ((BigFppfOver.toScheme B S hS).map
        (yonedaEquiv ((relativelyRepresentable_yoneda_map B S hS j).fst
          (openChart B S hS (yoneda.obj V) (selfChart B S hS V) W).1.hom)))
      W.ι ((BigFppfOver.toScheme B S hS).map j) :=
  toScheme_map_yonedaEquiv_openChart_selfChart B S hS V W ▸
    isPullback_representedChart_toScheme B S hS V j
      (openChart B S hS (yoneda.obj V) (selfChart B S hS V) W)

/-! ### The sections of the Zariski restriction of the kernel ideal sheaf -/

variable {R : BigFppfOver B S hS} (j : R ⟶ V)

/-- **The ideal which a Zariski open `W` of the representing scheme inherits from the kernel
ideal sheaf of the represented morphism is the kernel of the ring map which `j` induces on
sections over `W`.** -/
theorem openChartIdeal_kernelIdealSheaf_selfChart
    (W : (chartScheme (selfChart B S hS V)).Opens) :
    openChartIdeal B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (kernelIdealSheaf B S hS (representedSpaceMap B S hS j))
        (selfChart B S hS V) W =
      RingHom.ker (((BigFppfOver.toScheme B S hS).map j).app W).hom := by
  have hchart : (kernelIdealSheaf B S hS (representedSpaceMap B S hS j)).obj
          (op (openChartOfComparison B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
            (selfChart B S hS V) W))
      = (kernelIdealSheaf B S hS (representedSpaceMap B S hS j)).obj
          (op (openChart B S hS (yoneda.obj V) (selfChart B S hS V) W)) :=
    chartSectionIdeal_openChartOfComparison B S hS
      ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
      (kernelIdealSheaf B S hS (representedSpaceMap B S hS j)) (selfChart B S hS V) W
  have hker : (kernelIdealSheaf B S hS (representedSpaceMap B S hS j)).obj
          (op (openChart B S hS (yoneda.obj V) (selfChart B S hS V) W))
      = RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          ((relativelyRepresentable_yoneda_map B S hS j).snd
            (openChart B S hS (yoneda.obj V) (selfChart B S hS V) W).1.hom)).op).hom := by
    rw [kernelIdealSheaf_obj, ker_structureSharp_eq B S hS (representedSpaceMap B S hS j)
      (relativelyRepresentable_yoneda_map B S hS j)
      (openChart B S hS (yoneda.obj V) (selfChart B S hS V) W),
      chartPullbackRingHom_chartBaseChangeArrow B S hS (representedSpaceMap B S hS j)
        (relativelyRepresentable_yoneda_map B S hS j)]
    rfl
  refine Submodule.ext fun r =>
    (mem_openChartIdeal_iff_chartSectionsRingHom_mem B S hS
        ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (kernelIdealSheaf B S hS (representedSpaceMap B S hS j))
        (selfChart B S hS V) W r).trans
      (((congrArg (fun I => chartSectionsRingHom B S hS
            ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ (selfChart B S hS V) W r ∈ I)
          (hchart.trans hker)).to_iff).trans
        (mem_ker_Γ_map_iff_mem_ker_app_of_isPullback _ _ _ _
          (isPullback_snd_openChart_selfChart B S hS V j W) r _
          (chartSectionsRingHom_apply_eq_topIso_inv B S hS
            ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
            (selfChart B S hS V) W r)))

/-- `AlgebraicGeometry.Space.openChartIdeal_kernelIdealSheaf_selfChart` read on the submodule of
`𝒪_V` which `AlgebraicGeometry.Space.chartZariskiIdealSheaf` builds: its ideal of sections over a
Zariski open `W` of the representing scheme is `RingHom.ker (j.app W)`. -/
theorem chartZariskiIdealSheaf_selfChart_kernelIdealSheaf_obj_eq_ker
    (W : (chartScheme (selfChart B S hS V)).Opens) :
    (chartZariskiIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (kernelIdealSheaf B S hS (representedSpaceMap B S hS j))
          (selfChart B S hS V)).toSubmodule.obj (op W) =
      RingHom.ker (((BigFppfOver.toScheme B S hS).map j).app W).hom :=
  openChartIdeal_kernelIdealSheaf_selfChart B S hS V j W

/-- **The Zariski restriction of the kernel ideal sheaf of the represented morphism is the
scheme-level ideal sheaf of `j`.** The submodule of `𝒪_V` to which
`AlgebraicGeometry.Space.chartZariskiIdealSheaf` restricts
`AlgebraicGeometry.Space.kernelIdealSheaf` of the represented morphism is isomorphic, as a sheaf
of `𝒪_V`-modules, to `Stacks.ClosedImmersion.idealSheaf` of the underlying morphism of schemes,
the categorical kernel of `𝒪_V ⟶ j_*𝒪_R`. -/
noncomputable def chartZariskiKernelIdealSheafSelfChartIsoIdealSheaf :
    (chartZariskiIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (kernelIdealSheaf B S hS (representedSpaceMap B S hS j))
        (selfChart B S hS V)).toSheafOfModules ≅
      Stacks.ClosedImmersion.idealSheaf
        ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom :=
  Stacks.Divisors.submoduleIsoIdealSheafOfKer _ _ fun W =>
    (chartZariskiIdealSheaf_selfChart_kernelIdealSheaf_obj_eq_ker B S hS V j W).symm

/-- The identification of the two ideal sheaves respects the inclusions into `𝒪_V`. -/
theorem chartZariskiKernelIdealSheafSelfChartIsoIdealSheaf_hom_comp_ι :
    (chartZariskiKernelIdealSheafSelfChartIsoIdealSheaf B S hS V j).hom ≫
        kernel.ι (Stacks.Divisors.structureModuleHom
          ((BigFppfOver.toScheme B S hS).map j)) =
      (chartZariskiIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (kernelIdealSheaf B S hS (representedSpaceMap B S hS j)) (selfChart B S hS V)).ι :=
  Stacks.Divisors.submoduleIsoIdealSheafOfKer_hom_comp_ι _ _ fun W =>
    (chartZariskiIdealSheaf_selfChart_kernelIdealSheaf_obj_eq_ker B S hS V j W).symm

/-! ### The closed case, where the kernel ideal sheaf is a defining ideal sheaf -/

variable (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j))

/-- **The ideal which a Zariski open `W` of the representing scheme inherits from the defining
ideal sheaf of the closed subspace cut out by `j` is the kernel of the ring map which `j` induces
on sections over `W`.** -/
theorem openChartIdeal_closedSubspaceRange_selfChart
    (W : (chartScheme (selfChart B S hS V)).Opens) :
    openChartIdeal B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (closedSubspaceRange B S hS j hj))
        (selfChart B S hS V) W =
      RingHom.ker (((BigFppfOver.toScheme B S hS).map j).app W).hom :=
  (congrArg (fun N : IdealSheaves B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V) =>
        openChartIdeal B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ N
          (selfChart B S hS V) W)
      (kernelIdealSheaf_representedSpaceMap B S hS j hj)).symm.trans
    (openChartIdeal_kernelIdealSheaf_selfChart B S hS V j W)

/-- `AlgebraicGeometry.Space.openChartIdeal_closedSubspaceRange_selfChart` read on the submodule
of `𝒪_V` which `AlgebraicGeometry.Space.chartZariskiIdealSheaf` builds: its ideal of sections
over a Zariski open `W` of the representing scheme is `RingHom.ker (j.app W)`. -/
theorem chartZariskiIdealSheaf_selfChart_obj_eq_ker
    (W : (chartScheme (selfChart B S hS V)).Opens) :
    (chartZariskiIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
            (closedSubspaceRange B S hS j hj))
          (selfChart B S hS V)).toSubmodule.obj (op W) =
      RingHom.ker (((BigFppfOver.toScheme B S hS).map j).app W).hom :=
  openChartIdeal_closedSubspaceRange_selfChart B S hS V j hj W

/-! ### The two ideal sheaves agree -/

/-- **The Zariski restriction of the space-level defining ideal sheaf is the scheme-level ideal
sheaf of `j`.**  The submodule of `𝒪_V` which
`AlgebraicGeometry.Space.chartZariskiIdealSheaf` restricts the defining ideal sheaf of Stacks
03MB of the closed subspace cut out by `j` to is isomorphic, as a sheaf of `𝒪_V`-modules, to
`Stacks.ClosedImmersion.idealSheaf` of the underlying morphism of schemes — the categorical
kernel of `𝒪_V ⟶ j_*𝒪_R`. -/
noncomputable def chartZariskiIdealSheafSelfChartIsoIdealSheaf :
    (chartZariskiIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (closedSubspaceRange B S hS j hj)) (selfChart B S hS V)).toSheafOfModules ≅
      Stacks.ClosedImmersion.idealSheaf
        ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom :=
  Stacks.Divisors.submoduleIsoIdealSheafOfKer _ _ fun W =>
    (chartZariskiIdealSheaf_selfChart_obj_eq_ker B S hS V j hj W).symm

/-- The identification of the two ideal sheaves respects the inclusions into `𝒪_V`. -/
theorem chartZariskiIdealSheafSelfChartIsoIdealSheaf_hom_comp_ι :
    (chartZariskiIdealSheafSelfChartIsoIdealSheaf B S hS V j hj).hom ≫
        kernel.ι (Stacks.Divisors.structureModuleHom
          ((BigFppfOver.toScheme B S hS).map j)) =
      (chartZariskiIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (closedSubspaceRange B S hS j hj)) (selfChart B S hS V)).ι :=
  Stacks.Divisors.submoduleIsoIdealSheafOfKer_hom_comp_ι _ _ fun W =>
    (chartZariskiIdealSheaf_selfChart_obj_eq_ker B S hS V j hj W).symm

end Space

end AlgebraicGeometry

end
