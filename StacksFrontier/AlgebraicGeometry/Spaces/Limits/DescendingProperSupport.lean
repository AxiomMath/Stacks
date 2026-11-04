module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingProperness
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType

/-!
# Properness of the support of a module descends to a stage of a limit of bases

Let `B = lim B_i` be a directed limit of algebraic spaces over a scheme `S` with affine
transition morphisms, let `f₀ : X₀ ⟶ Y₀` be a morphism of quasi-compact quasi-separated
algebraic spaces over `B₀` which is locally of finite type, and let `f_i : X_i ⟶ Y_i` and
`f : X ⟶ Y` be its base changes to a stage `B_i` and to the limit `B`; this is the situation of
Stacks 084W, carried by `AlgebraicGeometry.Space.MorphismDescentSystem`. Let `F₀` be a
quasi-coherent `𝒪_{X₀}`-module of finite type, with pullbacks `F_i` to `X_i` and `F` to `X`. If
the scheme-theoretic support of `F` is proper over `Y`, then the scheme-theoretic support of
`F_i` is proper over `Y_i` for some `i ≥ 0`.

The proof is the one of the source: replace `X₀` by the scheme-theoretic support `Z₀` of `F₀`.
The base change of `Z₀` to `X_i`, respectively to `X`, is a closed subspace whose points are the
points of the support of `F_i`, respectively of `F`, by Stacks 07TZ; since properness of a closed
subspace over the base depends only on its set of points (Stacks 0CZC), the statement becomes
Stacks 08K1 for the base changes of `Z₀ ⟶ Y₀`.

## Main results

* `AlgebraicGeometry.Space.MorphismDescentSystem.exists_isProper_schemeTheoreticSupport_mapAt`:
  **Stacks 08K2**.
* `AlgebraicGeometry.Space.MorphismDescentSystem.exists_hasProperSupport_mapAt`: the same
  statement for the support as a closed set of points proper over the base (Stacks 0CZD), which
  is the form in which the stack of coherent sheaves with proper support of Stacks 08KB records
  properness.

## References

* [Stacks Project, Tag 08K2](https://stacks.math.columbia.edu/tag/08K2)
* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
* [Stacks Project, Tag 08K1](https://stacks.math.columbia.edu/tag/08K1)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 07U1](https://stacks.math.columbia.edu/tag/07U1)
* [Stacks Project, Tag 0CZC](https://stacks.math.columbia.edu/tag/0CZC)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.MorphismDescentSystem

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

/-- The descent system obtained by replacing the source `X₀` by a closed subspace `Z₀` of it. -/
noncomputable def restrictSource (D : MorphismDescentSystem B S hS hZ I) (Z₀ : Subfunctor D.source₀)
    (hZ₀ : IsClosedSubspace B S hS Z₀) : MorphismDescentSystem B S hS hZ I :=
  { D with
    source₀ := Z₀.toFunctor
    sourceToBase := Z₀.ι ≫ D.sourceToBase
    map₀ := Z₀.ι ≫ D.map₀
    map₀_over := by rw [Category.assoc, D.map₀_over]
    source₀_isAlgebraicSpace := hZ₀.1
    source₀_quasiCompact :=
      isQuasiCompactSpace_of_isClosedImmersion B S hS D.source₀_quasiCompact Z₀.ι hZ₀.2
    source₀_quasiSeparated :=
      isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hZ₀.1 D.source₀_quasiSeparated
        (isQuasiSeparated_of_isSeparated B S hS
          (isSeparated_of_isClosedImmersion B S hS Z₀.ι hZ₀.2)) }

/-- The pullback of a quasi-coherent module of finite type is quasi-coherent of finite type. -/
private theorem modulePullback_isQuasicoherent_isFiniteType {X₀ X' : AlgebraicSpaces B S hS}
    (π : X' ⟶ X₀) (F₀ : Modules.{u, u} B S hS X₀.1 X₀.2) (hF₀ : F₀.IsQuasicoherentOnSite)
    (hF₀ft : SheafOfModules.IsFiniteTypeOnSite F₀) :
    ((modulePullback B S hS π).obj F₀).IsQuasicoherentOnSite ∧
      SheafOfModules.IsFiniteTypeOnSite ((modulePullback B S hS π).obj F₀) ∧
        PresheafOfModules.IsFiniteType (smallEtaleRingedSite B S hS X'.1 X'.2).J
          ((modulePullback B S hS π).obj F₀).val :=
  ⟨isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS π F₀ hF₀,
    isFiniteTypeOnSite_modulePullback B S hS π F₀ hF₀ft,
    Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite _
      (isFiniteTypeOnSite_modulePullback B S hS π F₀ hF₀ft)⟩

/-- Over any base change `b : B' ⟶ B₀`, properness over `B' ×_{B₀} Y₀` of the scheme-theoretic
support of the pullback of `F₀` to `B' ×_{B₀} X₀` is properness of the base change of
`Z₀ ⟶ Y₀`, for `Z₀` the scheme-theoretic support of `F₀`. -/
theorem isProper_schemeTheoreticSupport_comp_iff (D : MorphismDescentSystem B S hS hZ I)
    (F₀ : Modules.{u, u} B S hS D.source₀ D.source₀_isAlgebraicSpace)
    (hF₀ : F₀.IsQuasicoherentOnSite) (hF₀ft : SheafOfModules.IsFiniteTypeOnSite F₀)
    (ft : IsLocallyOfFiniteType B S hS D.map₀)
    (hZ₀ : IsClosedSubspace B S hS
      (schemeTheoreticSupport B S hS ⟨D.source₀, D.source₀_isAlgebraicSpace⟩ F₀))
    {B' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (b : B' ⟶ D.base.obj (op D.initial))
    (hX' : IsAlgebraicSpace B S hS (pullback b D.sourceToBase))
    (hY' : IsAlgebraicSpace B S hS (pullback b D.targetToBase))
    (h : pullback.fst b D.sourceToBase ≫ b =
      (pullback.snd b D.sourceToBase ≫ D.map₀) ≫ D.targetToBase)
    (h' : pullback.fst b ((schemeTheoreticSupport B S hS ⟨D.source₀, D.source₀_isAlgebraicSpace⟩
        F₀).ι ≫ D.sourceToBase) ≫ b =
      (pullback.snd b ((schemeTheoreticSupport B S hS ⟨D.source₀, D.source₀_isAlgebraicSpace⟩
        F₀).ι ≫ D.sourceToBase) ≫ (schemeTheoreticSupport B S hS
          ⟨D.source₀, D.source₀_isAlgebraicSpace⟩ F₀).ι ≫ D.map₀) ≫ D.targetToBase) :
    IsProper B S hS ((schemeTheoreticSupport B S hS ⟨pullback b D.sourceToBase, hX'⟩
        ((modulePullback B S hS (ObjectProperty.homMk (pullback.snd b D.sourceToBase) :
          (⟨pullback b D.sourceToBase, hX'⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨D.source₀, D.source₀_isAlgebraicSpace⟩)).obj F₀)).ι ≫
        pullback.lift (pullback.fst b D.sourceToBase)
          (pullback.snd b D.sourceToBase ≫ D.map₀) h) ↔
      IsProper B S hS (pullback.lift
        (pullback.fst b ((schemeTheoreticSupport B S hS ⟨D.source₀, D.source₀_isAlgebraicSpace⟩
          F₀).ι ≫ D.sourceToBase))
        (pullback.snd b ((schemeTheoreticSupport B S hS ⟨D.source₀, D.source₀_isAlgebraicSpace⟩
          F₀).ι ≫ D.sourceToBase) ≫ (schemeTheoreticSupport B S hS
            ⟨D.source₀, D.source₀_isAlgebraicSpace⟩ F₀).ι ≫ D.map₀) h') := by
  set X₀ : AlgebraicSpaces B S hS := ⟨D.source₀, D.source₀_isAlgebraicSpace⟩
  set X' : AlgebraicSpaces B S hS := ⟨pullback b D.sourceToBase, hX'⟩
  set π : X' ⟶ X₀ := ObjectProperty.homMk (pullback.snd b D.sourceToBase)
  set Z₀ := schemeTheoreticSupport B S hS X₀ F₀
  set F' := (modulePullback B S hS π).obj F₀
  set m := pullback.lift (pullback.fst b D.sourceToBase) (pullback.snd b D.sourceToBase ≫ D.map₀) h
  obtain ⟨hF', hF'ft, hF'pft⟩ := modulePullback_isQuasicoherent_isFiniteType π F₀ hF₀ hF₀ft
  -- the support of `F'` and its two closed subspaces
  set T := supportOfSheaf B S hS X'.1 ((SheafOfModules.toSheaf _).obj F')
  have hT : IsClosed T := @isClosed_supportOfSheaf_of_isFiniteTypeOnSite _ _ _ _ _ _ hF'ft
  have hmft : IsLocallyOfFiniteType B S hS m :=
    isLocallyOfFiniteType_baseChange_of_isPullback hX' D.source₀_isAlgebraicSpace hY'
      D.target₀_isAlgebraicSpace (isPullback_pullback_lift_snd b h D.map₀_over) ft
  obtain ⟨hZ', -⟩ := exists_isClosedSubspace_schemeTheoreticSupport B S hS X' F' hF' hF'pft
  have hZ'T : Set.range (pointsMap B S hS (schemeTheoreticSupport B S hS X' F').toFunctor
      (schemeTheoreticSupport B S hS X' F').ι) = T :=
    (supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport B S hS X' F' hF' hF'ft).symm
  set P := Z₀.preimage π.hom
  have hP : IsClosedSubspace B S hS P :=
    isClosedSubspace_preimage B S hS π.hom Z₀ D.source₀_isAlgebraicSpace hX' hZ₀
  have hPT : Set.range (pointsMap B S hS P.toFunctor P.ι) = T := by
    rw [range_pointsMap_ι_preimage B S hS hX' D.source₀_isAlgebraicSpace π.hom Z₀ hZ₀.1,
      ← supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport B S hS X₀ F₀ hF₀ hF₀ft]
    exact (supportOfSheaf_modulePullback_eq B S hS π F₀ hF₀ hF₀ft).symm
  -- the base change of `Z₀` is `P`
  set k := pullback.lift (pullback.fst b (Z₀.ι ≫ D.sourceToBase))
    (pullback.snd b (Z₀.ι ≫ D.sourceToBase) ≫ Z₀.ι)
    (by rw [Category.assoc, pullback.condition])
  have hk : IsPullback (pullback.snd b (Z₀.ι ≫ D.sourceToBase)) k Z₀.ι
      (pullback.snd b D.sourceToBase) :=
    isPullback_pullback_lift_snd b _ rfl
  have hsqP : IsPullback (Z₀.fromPreimage π.hom) P.ι Z₀.ι π.hom :=
    Subfunctor.isPullback_preimage π.hom Z₀
  let e := hk.flip.isoIsPullback _ _ hsqP.flip
  have hkm : k ≫ m = pullback.lift (pullback.fst b (Z₀.ι ≫ D.sourceToBase))
      (pullback.snd b (Z₀.ι ≫ D.sourceToBase) ≫ Z₀.ι ≫ D.map₀) h' := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_snd_assoc, k, m]
  rw [← hkm, ← hk.flip.isoIsPullback_hom_fst _ _ hsqP.flip, Category.assoc,
    isProper_isIso_comp_iff B S hS e.hom (P.ι ≫ m)]
  exact ⟨(isProper_ι_comp_of_isProper_ι_comp B S hS hX' hY' m hmft T hT _ hZ' hZ'T · P hP hPT),
    (isProper_ι_comp_of_isProper_ι_comp B S hS hX' hY' m hmft T hT P hP hPT · _ hZ' hZ'T)⟩

/- This proves Stacks 08K2 at the tag's full statement; no attribute is attached here. -/
/-- **Properness of the support descends to a stage of a limit of bases** (Stacks 08K2). In the
situation of Stacks 084W, let `F₀` be a quasi-coherent `𝒪_{X₀}`-module of finite type, with
pullbacks `F_i` to `X_i` and `F` to `X`. If `f₀` is locally of finite type and the
scheme-theoretic support of `F` is proper over `Y`, then the scheme-theoretic support of `F_i`
is proper over `Y_i` for some stage `i ≥ 0`. This proves Stacks 08K2. -/
theorem exists_isProper_schemeTheoreticSupport_mapAt (D : MorphismDescentSystem B S hS hZ I)
    (F₀ : Modules.{u, u} B S hS D.source₀ D.source₀_isAlgebraicSpace)
    [F₀.IsQuasicoherentOnSite] [SheafOfModules.IsFiniteTypeOnSite F₀]
    (ft : IsLocallyOfFiniteType B S hS D.map₀)
    (proper : IsProper B S hS ((schemeTheoreticSupport B S hS
      ⟨D.sourceLimit, D.sourceLimit_isAlgebraicSpace⟩
      ((modulePullback B S hS (ObjectProperty.homMk
        (pullback.snd (limit.π D.base (op D.initial)) D.sourceToBase) :
          (⟨D.sourceLimit, D.sourceLimit_isAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨D.source₀, D.source₀_isAlgebraicSpace⟩)).obj F₀)).ι ≫ D.mapLimit)) :
    ∃ (i : I) (hi : D.initial ≤ i), IsProper B S hS ((schemeTheoreticSupport B S hS
      ⟨D.sourceAt i hi, D.sourceAt_isAlgebraicSpace i hi⟩
      ((modulePullback B S hS (ObjectProperty.homMk
        (pullback.snd (D.baseAtToInitial i hi) D.sourceToBase) :
          (⟨D.sourceAt i hi, D.sourceAt_isAlgebraicSpace i hi⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨D.source₀, D.source₀_isAlgebraicSpace⟩)).obj F₀)).ι ≫ D.mapAt i hi) := by
  have hF₀ : F₀.IsQuasicoherentOnSite := inferInstance
  have hF₀ft : SheafOfModules.IsFiniteTypeOnSite F₀ := inferInstance
  obtain ⟨hZ₀, -⟩ := exists_isClosedSubspace_schemeTheoreticSupport B S hS
    ⟨D.source₀, D.source₀_isAlgebraicSpace⟩ F₀ hF₀
    (Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite F₀ hF₀ft)
  set Z₀ := schemeTheoreticSupport B S hS ⟨D.source₀, D.source₀_isAlgebraicSpace⟩ F₀
  set D' := D.restrictSource Z₀ hZ₀
  have hft' : IsLocallyOfFiniteType B S hS D'.map₀ :=
    isLocallyOfFiniteType_comp B S hS hZ₀.1 D.source₀_isAlgebraicSpace
      D.target₀_isAlgebraicSpace Z₀.ι D.map₀
      (isLocallyOfFiniteType_of_isClosedImmersion B S hS Z₀.ι hZ₀.2) ft
  have hlim : IsProper B S hS D'.mapLimit :=
    (isProper_schemeTheoreticSupport_comp_iff D F₀ hF₀ hF₀ft ft hZ₀
      (limit.π D.base (op D.initial)) D.sourceLimit_isAlgebraicSpace
      D.targetLimit_isAlgebraicSpace _ _).mp proper
  obtain ⟨i, hi, hprop⟩ := D'.exists_isProper_mapAt hlim hft'
  exact ⟨i, hi, (isProper_schemeTheoreticSupport_comp_iff D F₀ hF₀ hF₀ft ft hZ₀
    (D.baseAtToInitial i hi) (D.sourceAt_isAlgebraicSpace i hi)
    (D.targetAt_isAlgebraicSpace i hi) _ _).mpr hprop⟩

/-- **Stacks 08K2, for the support as a closed set of points.** In the situation of Stacks 084W,
let `F₀` be a quasi-coherent `𝒪_{X₀}`-module of finite type, with pullbacks `F_i` to `X_i` and `F`
to `X`. If `f₀` is locally of finite type and the support of `F` is a closed subset proper over `Y`
(Stacks 0CZD), then the support of `F_i` is a closed subset proper over `Y_i` for some stage
`i ≥ 0`.

This is
`AlgebraicGeometry.Space.MorphismDescentSystem.exists_isProper_schemeTheoreticSupport_mapAt`
read through `AlgebraicGeometry.Space.hasProperSupport_tfae`: properness over the base of the
support of a quasi-coherent module of finite type is properness of its scheme-theoretic support. -/
theorem exists_hasProperSupport_mapAt (D : MorphismDescentSystem B S hS hZ I)
    (F₀ : Modules.{u, u} B S hS D.source₀ D.source₀_isAlgebraicSpace)
    [F₀.IsQuasicoherentOnSite] [SheafOfModules.IsFiniteTypeOnSite F₀]
    (ft : IsLocallyOfFiniteType B S hS D.map₀) (ftLimit : IsLocallyOfFiniteType B S hS D.mapLimit)
    (proper : HasProperSupport B S hS D.sourceLimit_isAlgebraicSpace D.targetLimit_isAlgebraicSpace
      D.mapLimit ftLimit ((SheafOfModules.toSheaf _).obj
        ((modulePullback B S hS (ObjectProperty.homMk
          (pullback.snd (limit.π D.base (op D.initial)) D.sourceToBase) :
            (⟨D.sourceLimit, D.sourceLimit_isAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.source₀, D.source₀_isAlgebraicSpace⟩)).obj F₀))) :
    ∃ (i : I) (hi : D.initial ≤ i) (ftAt : IsLocallyOfFiniteType B S hS (D.mapAt i hi)),
      HasProperSupport B S hS (D.sourceAt_isAlgebraicSpace i hi)
        (D.targetAt_isAlgebraicSpace i hi) (D.mapAt i hi) ftAt ((SheafOfModules.toSheaf _).obj
          ((modulePullback B S hS (ObjectProperty.homMk
            (pullback.snd (D.baseAtToInitial i hi) D.sourceToBase) :
              (⟨D.sourceAt i hi, D.sourceAt_isAlgebraicSpace i hi⟩ : AlgebraicSpaces B S hS) ⟶
                ⟨D.source₀, D.source₀_isAlgebraicSpace⟩)).obj F₀)) := by
  have hF₀ : F₀.IsQuasicoherentOnSite := inferInstance
  have hF₀ft : SheafOfModules.IsFiniteTypeOnSite F₀ := inferInstance
  obtain ⟨hq, hft, hpft⟩ := modulePullback_isQuasicoherent_isFiniteType (ObjectProperty.homMk
    (pullback.snd (limit.π D.base (op D.initial)) D.sourceToBase) :
      (⟨D.sourceLimit, D.sourceLimit_isAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨D.source₀, D.source₀_isAlgebraicSpace⟩) F₀ hF₀ hF₀ft
  obtain ⟨i, hi, hprop⟩ := D.exists_isProper_schemeTheoreticSupport_mapAt F₀ ft
    (((hasProperSupport_tfae B S hS ⟨D.sourceLimit, D.sourceLimit_isAlgebraicSpace⟩
      ⟨D.targetLimit, D.targetLimit_isAlgebraicSpace⟩ D.mapLimit ftLimit _ hq hft hpft).out 1 2).mp
      proper)
  have ftAt : IsLocallyOfFiniteType B S hS (D.mapAt i hi) :=
    isLocallyOfFiniteType_baseChange_of_isPullback (D.sourceAt_isAlgebraicSpace i hi)
      D.source₀_isAlgebraicSpace (D.targetAt_isAlgebraicSpace i hi) D.target₀_isAlgebraicSpace
      (isPullback_pullback_lift_snd _ _ D.map₀_over) ft
  obtain ⟨hq', hft', hpft'⟩ := modulePullback_isQuasicoherent_isFiniteType (ObjectProperty.homMk
    (pullback.snd (D.baseAtToInitial i hi) D.sourceToBase) :
      (⟨D.sourceAt i hi, D.sourceAt_isAlgebraicSpace i hi⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨D.source₀, D.source₀_isAlgebraicSpace⟩) F₀ hF₀ hF₀ft
  exact ⟨i, hi, ftAt, ((hasProperSupport_tfae B S hS
    ⟨D.sourceAt i hi, D.sourceAt_isAlgebraicSpace i hi⟩
    ⟨D.targetAt i hi, D.targetAt_isAlgebraicSpace i hi⟩ (D.mapAt i hi) ftAt _ hq' hft'
    hpft').out 2 1).mp hprop⟩

end AlgebraicGeometry.Space.MorphismDescentSystem

end
