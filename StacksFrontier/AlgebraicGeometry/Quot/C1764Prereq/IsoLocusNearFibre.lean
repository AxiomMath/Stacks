module

public import StacksFrontier.AlgebraicGeometry.Quot.C1764Prereq.DualizingSheafOfComplex
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyBaseChangeFieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveLocusOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleMapClosedFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageTensorInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperMorphismSupport

/-!
# A map of invertible modules which is surjective on a fibre is an isomorphism nearby

Let `f : Y → T` be a family of curves, `σ : M ⟶ L` a map of invertible `𝒪_Y`-modules and `V` a
presentation of the fibre `Y_t` over a point `t ∈ T`. If the pullback of `σ` to `V` is surjective,
then `σ` is an isomorphism over the inverse image of an open neighbourhood `O` of `t`, in the form
used below: its pullback to the base change of the family to the open subscheme `O ⊆ T` is an
isomorphism.

The argument is the one of Stacks 09TP. The pullback of `σ` along a morphism `g : W ⟶ Y` is
surjective exactly when no point of `W` maps into `Supp(Coker σ)`, because pullback is right exact
and the support of a pullback is the inverse image of the support (Stacks 07TZ). The image of
`Supp(Coker σ)` in `T` is closed, the support being closed in the support of `L`, which is proper
over `T` (Stacks 0CZG). It misses `t`, since every point of `Y` over `t` comes from the fibre
`V` (Stacks 03H4). Over its complement `O` the pullback of `σ` is surjective, and a surjection of
invertible modules is an isomorphism.

This is the step of the genus one case of the proof of [Stacks, Tag 0E6Y] which spreads out the
triviality of `ω_{X/S}` from a fibre to a neighbourhood of it.

## Main results

* `AlgebraicGeometry.C1764Prereq.epi_modulePullback_map_iff_forall_not_mem`: the pullback of a
  map of quasi-coherent modules is surjective exactly when the points avoid the support of the
  cokernel.
* `AlgebraicGeometry.C1764Prereq.exists_opens_isIso_baseChange_of_epi_fibre`: the isomorphism
  over a neighbourhood of the fibre.

## References

* [Stacks Project, Tag 09TP](https://stacks.math.columbia.edu/tag/09TP)
* [Stacks Project, Tag 0CZG](https://stacks.math.columbia.edu/tag/0CZG)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 0E6Y](https://stacks.math.columbia.edu/tag/0E6Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace C1764Prereq

section Generic

variable {S : Scheme.{u}} {hS : B.Contains S}

/-- **Surjectivity of a pulled back map is read on the support of the cokernel.** For a map
`σ : M ⟶ L` of quasi-coherent `𝒪_X`-modules with `L` of finite type and a morphism `g : W ⟶ X`,
the pullback `g^*σ` is surjective exactly when no point of `W` maps into `Supp(Coker σ)`: pullback
is right exact, so `Coker(g^*σ) = g^*Coker σ`, whose support is `g⁻¹(Supp(Coker σ))`
(Stacks 07TZ), and a module vanishes exactly when its support is empty. -/
theorem epi_modulePullback_map_iff_forall_not_mem {X W : AlgebraicSpaces B S hS}
    {M L : Space.Modules.{u, u} B S hS X.1 X.2} (hMq : M.IsQuasicoherentOnSite)
    (hLq : L.IsQuasicoherentOnSite) (hLft : SheafOfModules.IsFiniteTypeOnSite L) (σ : M ⟶ L)
    (g : W ⟶ X) :
    Epi ((Space.modulePullback B S hS g).map σ) ↔
      ∀ w, Space.pointsMap B S hS W.1 g.hom w ∉
        Space.supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
          (cokernel σ : Space.Modules.{u, u} B S hS X.1 X.2)) := by
  have hCq : (cokernel σ).IsQuasicoherentOnSite :=
    @Space.isQuasicoherentOnSite_cokernel_unconditional B S hS X.1 X.2 M L hMq hLq σ
  have hCft := Space.isFiniteTypeOnSite_cokernel_of_isFiniteTypeOnSite B S hS X.1 X.2 σ hLft
  have hadj := Space.modulePullbackAdjunction B S hS g
  have := hadj.isLeftAdjoint
  have hpc : PreservesColimitsOfSize.{0, 0} (Space.modulePullback B S hS g) :=
    hadj.leftAdjoint_preservesColimits
  have e := PreservesCokernel.iso (Space.modulePullback B S hS g) σ
  rw [Preadditive.epi_iff_isZero_cokernel,
    show IsZero (cokernel ((Space.modulePullback B S hS g).map σ)) ↔
        IsZero ((Space.modulePullback B S hS g).obj (cokernel σ)) from
      ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩,
    ← Space.supportOfSheaf_eq_empty_iff_isZero,
    Space.supportOfSheaf_modulePullback_eq B S hS g _ hCq hCft, Set.eq_empty_iff_forall_notMem]
  rfl

end Generic

/-- **A map of invertible modules surjective on a fibre is an isomorphism over a neighbourhood of
the fibre.** Let `f : Y → T` be a family of curves, `σ : M ⟶ L` a map of invertible
`𝒪_Y`-modules and `V` a presentation of the fibre `Y_t`. If the pullback of `σ` to `V` is
surjective, then there is an open `O ∋ t` of `T` over which `σ` is an isomorphism: the support of
`Coker σ` is closed with closed image in `T` (Stacks 0CZG) missing `t` (Stacks 07TZ), and a
surjection of invertible modules is an isomorphism. -/
theorem exists_opens_isIso_baseChange_of_epi_fibre (Y : CurveFamily B hZ)
    {M L : Space.Modules.{u, u} B integerBase hZ Y.total.1 Y.total.2}
    (hM : Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ Y.total.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ Y.total.1 Y.total.2).O)).property M)
    (hL : Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ Y.total.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ Y.total.1 Y.total.2).O)).property L)
    (σ : M ⟶ L) (t : (BigFppfOver.toScheme B integerBase hZ).obj Y.base)
    {V : BigFppfOver B integerBase hZ} {v : V ⟶ CurveFamily.residuePoint B hZ Y t}
    {q : yoneda.obj V ⟶ Y.total.obj} (hq : CurveFamily.IsFibrePresentation B hZ Y t v q)
    (hσ : Epi ((Space.modulePullback B integerBase hZ
      (ObjectProperty.homMk q : schemeSpace V ⟶ Y.total)).map σ)) :
    ∃ O : ((BigFppfOver.toScheme B integerBase hZ).obj Y.base).Opens, t ∈ O ∧
      IsIso ((Space.modulePullback B integerBase hZ
        (Y.baseChangeHom (Space.openSubHom Y.base O)).totalMap).map σ) := by
  classical
  have hLa := Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL
  have hMq : M.IsQuasicoherentOnSite := Space.isQuasicoherentOnSite_of_isInvertible B integerBase
    hZ Y.total M (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ M hM)
  have hLq : L.IsQuasicoherentOnSite :=
    Space.isQuasicoherentOnSite_of_isInvertible B integerBase hZ Y.total L hLa
  have hLft : SheafOfModules.IsFiniteTypeOnSite L := by
    have : L.IsFinitePresentationOnSite :=
      SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite
        (Space.isFiniteLocallyFreeOfRank_one_of_isInvertible B integerBase hZ Y.total L
          hLa).isFiniteLocallyFreeOnSite
    infer_instance
  let D : Space.ModuleMapSituation.{u, u} B integerBase hZ :=
    ⟨Y.total, schemeSpace Y.base, Y.toBase, M, L, hMq, hLq, σ⟩
  have hlft : Space.IsLocallyOfFiniteType B integerBase hZ Y.toBase.hom :=
    Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B integerBase hZ
      Y.finitePresentation.1
  have hcl : IsClosed (Space.pointsToScheme B integerBase hZ Y.base '' D.cokernelSupportImage) :=
    (Space.isClosed_pointTopology_yoneda_iff_isClosed_image B integerBase hZ Y.base _).1 <|
      D.isClosed_cokernelSupportImage hlft hLft <| Space.hasProperSupport_toSheaf_of_isProper B
        integerBase hZ Y.total.2 (schemeSpace Y.base).2 Y.toBase.hom hlft Y.proper L
  let O : ((BigFppfOver.toScheme B integerBase hZ).obj Y.base).Opens := ⟨_, hcl.isOpen_compl⟩
  refine ⟨O, ?_, ?_⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, hxt⟩
    let r₀ : (BigFppfOver.toScheme B integerBase hZ).obj (CurveFamily.residuePoint B hZ Y t) :=
      IsLocalRing.closedPoint _
    obtain ⟨r, hr⟩ := Space.surjective_pointsToScheme B integerBase hZ _ r₀
    have hrx : Space.pointsMap B integerBase hZ _ Y.toBase.hom x =
        Space.pointsMap B integerBase hZ _
          (yoneda.map (CurveFamily.residuePointMap B hZ Y t)) r :=
      Space.injective_pointsToScheme B integerBase hZ Y.base <| by
        rw [Space.pointsToScheme_pointsMap_yoneda, hr, hxt]
        exact (Scheme.fromSpecResidueField_apply _ _).symm
    obtain ⟨w, hw, -⟩ := Space.exists_points_of_isPullback B integerBase hZ hq x r hrx
    exact (epi_modulePullback_map_iff_forall_not_mem hMq hLq hLft σ
      (ObjectProperty.homMk q : schemeSpace V ⟶ Y.total)).1 hσ w (hw ▸ hx)
  · have := (epi_modulePullback_map_iff_forall_not_mem hMq hLq hLft σ
      (Y.baseChangeHom (Space.openSubHom Y.base O)).totalMap).2 fun w hw => by
        have hc := Space.pointsMap_apply_comm B integerBase hZ
          (congrArg (fun k => k.hom) (Y.baseChangeHom (Space.openSubHom Y.base O)).cartesian.w) w
        have hmem : Space.pointsToScheme B integerBase hZ Y.base
            (Space.pointsMap B integerBase hZ _ (yoneda.map (Space.openSubHom Y.base O))
              (Space.pointsMap B integerBase hZ _
                (Y.baseChange (Space.openSubHom Y.base O)).toBase.hom w)) ∈ O := by
          rw [Space.pointsToScheme_pointsMap_yoneda, Space.toScheme_map_openSubHom]
          exact (Set.ext_iff.1 O.range_ι _).1 ⟨_, rfl⟩
        exact hmem ⟨_, ⟨_, hw, rfl⟩, congrArg (Space.pointsToScheme B integerBase hZ Y.base) hc⟩
    exact Space.isIso_of_epi_of_isInvertibleModule
      (Space.stacksIsInvertible_modulePullback_obj B integerBase hZ _ M)
      (Space.stacksIsInvertible_modulePullback_obj B integerBase hZ _ L) _

end C1764Prereq

end AlgebraicGeometry
