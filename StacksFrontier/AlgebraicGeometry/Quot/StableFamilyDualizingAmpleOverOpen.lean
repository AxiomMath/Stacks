module

public import StacksFrontier.AlgebraicGeometry.Quot.StableFamilyDualizingAmpleOfGenus
public import StacksFrontier.AlgebraicGeometry.Quot.StableFamilyDualizingAmpleFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspacePushforwardCech

/-!
# Ampleness near a point of a module living over an open of the base (towards Stacks 0E74)

Let `f : X → S` be a prestable family of curves of genus `g ≥ 2`, `U ⊆ S` an open and
`X₁ = f⁻¹(U)`, presented by a cartesian square over `U ⊆ S`. Let `ω` be an invertible module on
`X₁` which restricts on every fibre `X_s`, `s ∈ U`, to the dualizing sheaf of the fibre. This is
the situation of the relative dualizing sheaf `ω_{f⁻¹(U)/U}` over an affine open `U` (the third
remark after Stacks 0E5X and Stacks 0E6Q). The argument of Stacks 0E74 runs over `U`: there is
an open `U' ⊆ U`, the locus of Stacks 0D3D where `ω` is ample, such that

* a morphism `T ⟶ U` lands in `U'` exactly when the pullback of `ω` to `X₁ ×_U T` is ample
  relative to `T`;
* a point `s ∈ U` lies in `U'` exactly when the fibre `X_s` has no rational tail and no
  rational bridge.

## Main results

* `AlgebraicGeometry.CurveFamily.exists_opens_isRelativelyAmple_iff_of_isPullback_openSub`: the
  open `U'` above.

## Implementation notes

**Unregistered helper** (for Stacks 0E74). This is the argument of
`CurveFamily.hasNoRationalTailNoRationalBridge_iff_exists_isRelativelyAmple_of_openAmpleLocus`
with `ω` defined only over `U`: the morphism `Spec κ(s) ⟶ S` of a point `s ∈ U` factors through
`U` (`AlgebraicGeometry.Space.openSubLift`), a presentation of the fibre `X_s` factors through
`X₁`, and Stacks 0D3D is applied to `X₁ ⟶ U`. The fibres are those of `X` over the residue
fields of `S`, so no comparison of residue fields of `U` and `S` is needed.

## References

* [Stacks Project, Tag 0E74](https://stacks.math.columbia.edu/tag/0E74)
* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The argument of Stacks 0E74 over an open of the base.** Let `f : X → S` be a prestable
family of curves whose fibres have genus `g ≥ 2`, `U ⊆ S` an open, `X₁ = f⁻¹(U)` presented by a
cartesian square over `U ⊆ S`, and `ω` an invertible module on `X₁` which restricts on the fibre
`X_s` of every point `s ∈ U` to the dualizing sheaf of the fibre. There is an open `U' ⊆ U` such
that

1. a morphism `t : T ⟶ U` of the site lands in `U'` exactly when the pullback of `ω` to a base
   change `X₁ ×_U T` is ample relative to `T`;
2. a point `s ∈ U` lies in `U'` exactly when the fibre `X_s` (presented by a scheme of the site)
   has no rational tail and no rational bridge. -/
theorem exists_opens_isRelativelyAmple_iff_of_isPullback_openSub
    (X : CurveFamily B hZ) (hX : IsPrestableCurveFamily B hZ X) (g : ℕ)
    (hgen : X.HasFibreGenus B hZ g) (hg : 2 ≤ g)
    (U : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens)
    {X₁ : AlgebraicSpaces B integerBase hZ} {p₁ : X₁ ⟶ X.total}
    {f₁ : X₁ ⟶ schemeSpace (Space.openSub X.base U)}
    (h₁ : IsPullback p₁ f₁ X.toBase (schemeSpaceMap (Space.openSubHom X.base U)))
    (ω : Space.Modules.{u, u} B integerBase hZ X₁.obj X₁.property)
    (hωinv : Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ X₁.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ X₁.1 X₁.2).O)).property ω)
    (hω : ∀ s ∈ U, ∀ (V : BigFppfOver B integerBase hZ) (v : V ⟶ residuePoint B hZ X s)
      (q : yoneda.obj V ⟶ X.total.obj) (h : IsFibrePresentation B hZ X s v q)
      (q₁ : yoneda.obj V ⟶ X₁.obj), q₁ ≫ p₁.hom = q →
        haveI := h.isProper
        Nonempty (Space.baseChangeModule B integerBase hZ ω V q₁ ≅
          Stacks.Duality.dualizingSheafOverField (fibreMap B hZ X s v))) :
    ∃ U' : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens, U' ≤ U ∧
      (∀ ⦃T : BigFppfOver B integerBase hZ⦄ (t : T ⟶ Space.openSub X.base U)
        ⦃X' : AlgebraicSpaces B integerBase hZ⦄ (p : X' ⟶ X₁) (f' : X' ⟶ schemeSpace T),
        IsPullback p f' f₁ (schemeSpaceMap t) →
          ((∀ y, (BigFppfOver.toScheme B integerBase hZ).map
              (t ≫ Space.openSubHom X.base U) y ∈ U') ↔
            Space.IsRelativelyAmple B integerBase hZ f'
              ((Space.modulePullback B integerBase hZ p).obj ω))) ∧
      ∀ s ∈ U,
        ((∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ X.residuePoint B hZ s)
            (q : yoneda.obj V ⟶ X.total.obj),
            X.IsFibrePresentation B hZ s v q ∧
              HasNoRationalTailNoRationalBridge
                (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s)
                (X.fibreMap B hZ s v)) ↔ s ∈ U') := by
  have hf₁ : Space.IsProper B integerBase hZ f₁.hom :=
    (Space.isProper_isStableUnderBaseChange B integerBase hZ).of_isPullback h₁ X.proper
  obtain ⟨W, hW, hiff⟩ := openAmpleLocus B hZ hf₁ hωinv
  let W' := Space.opensOfOpenSubspace B integerBase hZ (Space.openSub X.base U) W hW
  -- Membership of a morphism of the site in `W`, read on its image.
  have hmem : ∀ {T : BigFppfOver B integerBase hZ} (x : T ⟶ Space.openSub X.base U),
      (∃ l : (schemeSpace T).1 ⟶ W.toFunctor, l ≫ W.ι = (schemeSpaceMap x).hom) ↔
        ∀ y, ((BigFppfOver.toScheme B integerBase hZ).map x) y ∈ W' := by
    intro T x
    refine (Space.FinitePartUniversalOpen.exists_lift_iff_mem
      (X := yoneda.obj (Space.openSub X.base U)) W T (yoneda.map x)).trans ?_
    rw [yonedaEquiv_yoneda_map]
    exact Space.mem_iff_of_isOpenSubspace B integerBase hZ _ W hW x
  -- Membership in the image of `W'` in `S`.
  have hι : ∀ {T : BigFppfOver B integerBase hZ} (t : T ⟶ Space.openSub X.base U) y,
      (BigFppfOver.toScheme B integerBase hZ).map (t ≫ Space.openSubHom X.base U) y ∈
          U.ι ''ᵁ W' ↔
        (BigFppfOver.toScheme B integerBase hZ).map t y ∈ W' := by
    intro T t y
    rw [Functor.map_comp, Space.toScheme_map_openSubHom]
    have e := U.ι.preimage_image_eq W'
    exact ⟨fun h => by rwa [← e], fun h => by rwa [← e] at h⟩
  have hr : ∀ (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) y,
      ((BigFppfOver.toScheme B integerBase hZ).map (X.residuePointMap B hZ s)) y = s :=
    fun _ _ => Scheme.fromSpecResidueField_apply _ _
  -- The residue point of `s ∈ U` lifts to `U`.
  have hex : ∀ s ∈ U, ∃ rU : X.residuePoint B hZ s ⟶ Space.openSub X.base U,
      rU ≫ Space.openSubHom X.base U = X.residuePointMap B hZ s := fun s hs =>
    ⟨_, Space.openSubLift_comp_openSubHom X.base U (X.residuePointMap B hZ s)
      (fun y => (hr s y).symm ▸ hs)⟩
  have hpb := AlgebraicSpaces.isPullback_hom B integerBase hZ h₁
  -- On a presentation of `X_s`, `s ∈ U`: (1) holds exactly when `s` lies in the image of `W'`.
  have hfib : ∀ s (hs : s ∈ U) (rU : X.residuePoint B hZ s ⟶ Space.openSub X.base U)
      (hrU : rU ≫ Space.openSubHom X.base U = X.residuePointMap B hZ s),
      ((∀ y, (BigFppfOver.toScheme B integerBase hZ).map rU y ∈ W') ↔ s ∈ U.ι ''ᵁ W') ∧
      ∀ {V : BigFppfOver B integerBase hZ} (v : V ⟶ X.residuePoint B hZ s)
        (q : yoneda.obj V ⟶ X.total.obj), X.IsFibrePresentation B hZ s v q →
        (HasNoRationalTailNoRationalBridge
            (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s)
            (X.fibreMap B hZ s v) ↔ s ∈ U.ι ''ᵁ W') := by
    intro s hs rU hrU
    have hpt : ∀ y, ((BigFppfOver.toScheme B integerBase hZ).map rU y ∈ W' ↔
        s ∈ U.ι ''ᵁ W') := fun y => by
      rw [← hι rU y, hrU, hr s y]
    obtain ⟨y₀⟩ : Nonempty ((BigFppfOver.toScheme B integerBase hZ).obj
        (X.residuePoint B hZ s)) := inferInstanceAs (Nonempty (Spec _))
    have hall : (∀ y, (BigFppfOver.toScheme B integerBase hZ).map rU y ∈ W') ↔
        s ∈ U.ι ''ᵁ W' :=
      ⟨fun h => (hpt y₀).1 (h y₀), fun h y => (hpt y).2 h⟩
    refine ⟨hall, fun {V} v q h => ?_⟩
    have hy : yoneda.map rU ≫ yoneda.map (Space.openSubHom X.base U) =
        yoneda.map (X.residuePointMap B hZ s) :=
      (yoneda.map_comp _ _).symm.trans (congrArg yoneda.map hrU)
    have hc : q ≫ X.toBase.hom = (yoneda.map v ≫ yoneda.map rU) ≫
        (schemeSpaceMap (Space.openSubHom X.base U)).hom :=
      h.w.trans ((congrArg (yoneda.map v ≫ ·) hy).symm.trans (Category.assoc _ _ _).symm)
    let q₁ := hpb.lift q (yoneda.map v ≫ yoneda.map rU) hc
    have hq₁ : q₁ ≫ p₁.hom = q := hpb.lift_fst _ _ _
    have hq₁' : q₁ ≫ f₁.hom = yoneda.map v ≫ yoneda.map rU := hpb.lift_snd _ _ _
    have hV₁ : IsPullback q₁ (yoneda.map v) f₁.hom (yoneda.map rU) := by
      refine IsPullback.of_right ?_ hq₁' hpb
      rw [hq₁]
      exact (congrArg (IsPullback q (yoneda.map v) X.toBase.hom) hy).mpr h
    have hsq : IsPullback (ObjectProperty.homMk q₁ : schemeSpace V ⟶ X₁) (schemeSpaceMap v) f₁
        (schemeSpaceMap rU) :=
      Space.isPullback_homMk B integerBase hZ X₁.property
        (isAlgebraicSpace_yoneda B integerBase hZ _) (isAlgebraicSpace_yoneda B integerBase hZ _)
        (isAlgebraicSpace_yoneda B integerBase hZ _) hV₁
    have := h.isProper
    obtain ⟨e⟩ := hω s hs V v q h q₁ hq₁
    let : ((BigFppfOver.toScheme B integerBase hZ).obj V).Over
        (Spec (.of (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s))) :=
      ⟨X.fibreMap B hZ s v⟩
    have : IsProper (((BigFppfOver.toScheme B integerBase hZ).obj V) ↘
        Spec (.of (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s))) :=
      h.isProper
    obtain ⟨hnod, hdim, hbij⟩ := prestableFibreReading B hZ X hX s V v q h
    have : IsIso (X.fibreMap B hZ s v).appTop :=
      (ConcreteCategory.isIso_iff_bijective _).2 hbij
    have : IsIso ((Scheme.ΓSpecIso (.of (((BigFppfOver.toScheme B integerBase hZ).obj
        X.base).residueField s))).inv ≫ (((BigFppfOver.toScheme B integerBase hZ).obj V) ↘
          Spec (.of (((BigFppfOver.toScheme B integerBase hZ).obj
            X.base).residueField s))).appTop) :=
      inferInstanceAs (IsIso ((Scheme.ΓSpecIso _).inv ≫ (X.fibreMap B hZ s v).appTop))
    have hgV : 2 ≤ genus (X.fibreMap B hZ s v) := hgen s V v q h ▸ hg
    refine Iff.trans ?_ ((hiff (schemeSpaceMap rU) _ _ hsq).symm.trans ((hmem rU).trans hall))
    refine Iff.trans ?_ (isRelativelyAmple_fibre_iff_of_iso hωinv q₁ e).symm
    refine Iff.trans ?_ ((forall_not_isRationalTail_and_isRationalBridge_iff_isAmple hdim hnod
      hgV).trans ⟨fun hamp => ⟨_, hamp⟩, fun ⟨_, hamp⟩ => hamp⟩)
    exact and_congr_right fun _ => ⟨fun hb => hb inferInstance, fun hb _ => hb⟩
  refine ⟨U.ι ''ᵁ W', (U.ι.image_le_opensRange W').trans_eq U.opensRange_ι, ?_, ?_⟩
  · intro T t X' p f' sq
    exact (forall_congr' (hι t)).trans ((hmem t).symm.trans (hiff (schemeSpaceMap t) p f' sq))
  · intro s hs
    obtain ⟨rU, hrU⟩ := hex s hs
    refine ⟨fun ⟨V, v, q, h, hno⟩ => ((hfib s hs rU hrU).2 v q h).1 hno, fun hsW => ?_⟩
    have sq₀ := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ f₁ (schemeSpaceMap rU)
    obtain ⟨V, v, q', hsq'⟩ := ((hiff _ _ _ sq₀).1 ((hmem rU).2 ((hfib s hs rU hrU).1.2 hsW))).1
      (𝟙 (yoneda.obj (X.residuePoint B hZ s)))
    have hpres :=
      (hsq'.paste_horiz (AlgebraicSpaces.isPullback_hom B integerBase hZ sq₀)).paste_horiz hpb
    have e : (𝟙 (yoneda.obj (X.residuePoint B hZ s)) ≫ (schemeSpaceMap rU).hom) ≫
        (schemeSpaceMap (Space.openSubHom X.base U)).hom =
          yoneda.map (X.residuePointMap B hZ s) :=
      (congrArg (· ≫ (schemeSpaceMap (Space.openSubHom X.base U)).hom)
        (Category.id_comp (schemeSpaceMap rU).hom)).trans
        ((yoneda.map_comp _ _).symm.trans (congrArg yoneda.map hrU))
    have hpres' : X.IsFibrePresentation B hZ s v
        ((q' ≫ pullback.fst f₁.hom (yoneda.map rU)) ≫ p₁.hom) :=
      (congrArg (IsPullback ((q' ≫ pullback.fst f₁.hom (yoneda.map rU)) ≫ p₁.hom)
        (yoneda.map v) X.toBase.hom) e).mp hpres
    exact ⟨V, v, _, hpres', ((hfib s hs rU hrU).2 v _ hpres').2 hsW⟩

end CurveFamily

end AlgebraicGeometry

end
