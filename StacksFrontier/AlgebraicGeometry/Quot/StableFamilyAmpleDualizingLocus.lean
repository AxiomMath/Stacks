module

public import StacksFrontier.AlgebraicGeometry.Quot.StableFamilyDualizingAmple
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.AmpleNoRationalBridge

/-!
# Ampleness of `ω_{X/S}` near a point, with the fibrewise step proved (towards Stacks 0E74)

`AlgebraicGeometry.CurveFamily.hasNoRationalTailNoRationalBridge_iff_exists_isRelativelyAmple_of`
proves the argument of Stacks 0E74 for a prestable family of curves `X → S` of genus `g ≥ 2`
from inputs of the shapes of Stacks 0E3P, 0E63, 0E64, 0D3D and of the fibre reading of
prestability. Here the fibrewise inputs (Stacks 0E3P, 0E63, 0E64 and 0B5Y) are replaced by
`AlgebraicGeometry.forall_not_isRationalTail_and_isRationalBridge_iff_isAmple`, which proves them.

## Main results

* `CurveFamily.hasNoRationalTailNoRationalBridge_iff_exists_isRelativelyAmple_of_openAmpleLocus`:
  the argument of Stacks 0E74, both directions, from `AlgebraicGeometry.OpenAmpleLocus` and
  `AlgebraicGeometry.PrestableFibreReading` alone.

## Implementation notes

The definitions (the residue point, presentations of a fibre, the genus and dualizing conditions
on fibres, and the two input shapes) and the fibrewise ampleness criterion
`AlgebraicGeometry.CurveFamily.isRelativelyAmple_fibre_iff` are those used by
`AlgebraicGeometry.CurveFamily.hasNoRationalTailNoRationalBridge_iff_exists_isRelativelyAmple_of`;
the proof is the one given there, with the fibrewise step read off
`AlgebraicGeometry.forall_not_isRationalTail_and_isRationalBridge_iff_isAmple`.

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

/-- **The argument of Stacks 0E74, from its inputs.** Let `f : X → S` be a prestable family of
curves whose fibres have genus `g ≥ 2`, let `ω` be an invertible module on `X` restricting on
every fibre to its dualizing sheaf (the relative dualizing sheaf `ω_{X/S}`), and let `s ∈ S`.
The following are equivalent:

1. the fibre `X_s` (presented by a scheme of the site) has no rational tail and no rational
   bridge;
2. there is an open `U ∋ s` of `S` such that `ω` is ample on `f⁻¹(U)` relative to `U`: on every
   base change of `f` along `U ⊆ S` the pullback of `ω` is relatively ample.

As in the source: given (2), `ω_{X_s}` is ample, which excludes rational tails and bridges by
Stacks 0E63, 0E64 and 0B5Y; given (1), `ω_{X_s}` is ample by Stacks 0E3Q, and Stacks 0D3D spreads
ampleness from the fibre to a neighbourhood
(`AlgebraicGeometry.forall_not_isRationalTail_and_isRationalBridge_iff_isAmple`
is the fibrewise step). The inputs `h0D3D` and `hpre` are described in the module docstring. -/
theorem hasNoRationalTailNoRationalBridge_iff_exists_isRelativelyAmple_of_openAmpleLocus
    (h0D3D : OpenAmpleLocus B hZ) (hpre : PrestableFibreReading B hZ)
    (X : CurveFamily B hZ) (hX : IsPrestableCurveFamily B hZ X) (g : ℕ)
    (hgen : X.HasFibreGenus B hZ g) (hg : 2 ≤ g)
    (ω : Space.Modules.{u, u} B integerBase hZ X.total.obj X.total.property)
    (hωinv : Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ X.total.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ X.total.1 X.total.2).O)).property ω)
    (hω : X.IsDualizingOnFibres B hZ ω)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) :
    (∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ X.residuePoint B hZ s)
        (q : yoneda.obj V ⟶ X.total.obj),
        X.IsFibrePresentation B hZ s v q ∧
          HasNoRationalTailNoRationalBridge
            (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s)
            (X.fibreMap B hZ s v)) ↔
      ∃ U : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens, s ∈ U ∧
        ∀ ⦃X₁ : AlgebraicSpaces B integerBase hZ⦄ (p₁ : X₁ ⟶ X.total)
          (f₁ : X₁ ⟶ schemeSpace (Space.openSub X.base U)),
          IsPullback p₁ f₁ X.toBase (schemeSpaceMap (Space.openSubHom X.base U)) →
            Space.IsRelativelyAmple B integerBase hZ f₁
              ((Space.modulePullback B integerBase hZ p₁).obj ω) := by
  obtain ⟨W, hW, hiff⟩ := h0D3D X.proper hωinv
  let K := X.residuePoint B hZ s
  let r := X.residuePointMap B hZ s
  have hfib : ∀ {V : BigFppfOver B integerBase hZ} (v : V ⟶ K) (q : yoneda.obj V ⟶ X.total.obj),
      X.IsFibrePresentation B hZ s v q →
      (HasNoRationalTailNoRationalBridge
          (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s)
          (X.fibreMap B hZ s v) ↔
        ∃ l : (schemeSpace K).1 ⟶ W.toFunctor, l ≫ W.ι = (schemeSpaceMap r).hom) := by
    intro V v q h
    let : ((BigFppfOver.toScheme B integerBase hZ).obj V).Over
        (Spec (.of (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s))) :=
      ⟨X.fibreMap B hZ s v⟩
    have : IsProper (((BigFppfOver.toScheme B integerBase hZ).obj V) ↘
        Spec (.of (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s))) :=
      h.isProper
    obtain ⟨hnod, hdim, hbij⟩ := hpre X hX s V v q h
    have : IsIso (X.fibreMap B hZ s v).appTop :=
      (ConcreteCategory.isIso_iff_bijective _).2 hbij
    have : IsIso ((Scheme.ΓSpecIso (.of (((BigFppfOver.toScheme B integerBase hZ).obj
        X.base).residueField s))).inv ≫ (((BigFppfOver.toScheme B integerBase hZ).obj V) ↘
          Spec (.of (((BigFppfOver.toScheme B integerBase hZ).obj
            X.base).residueField s))).appTop) :=
      inferInstanceAs (IsIso ((Scheme.ΓSpecIso _).inv ≫ (X.fibreMap B hZ s v).appTop))
    have hgV : 2 ≤ genus (X.fibreMap B hZ s v) := hgen s V v q h ▸ hg
    have hsq : IsPullback (ObjectProperty.homMk q : schemeSpace V ⟶ X.total) (schemeSpaceMap v)
        X.toBase (schemeSpaceMap r) :=
      Space.isPullback_homMk B integerBase hZ X.total.property
        (isAlgebraicSpace_yoneda B integerBase hZ _) (isAlgebraicSpace_yoneda B integerBase hZ _)
        (isAlgebraicSpace_yoneda B integerBase hZ _) h
    refine Iff.trans ?_ (hiff (schemeSpaceMap r) _ _ hsq).symm
    refine Iff.trans ?_ (isRelativelyAmple_fibre_iff hωinv hω h).symm
    refine Iff.trans ?_ ((forall_not_isRationalTail_and_isRationalBridge_iff_isAmple hdim hnod
      hgV).trans ⟨fun hamp => ⟨_, hamp⟩, fun ⟨_, hamp⟩ => hamp⟩)
    exact and_congr_right fun _ => ⟨fun hb => hb inferInstance, fun hb _ => hb⟩
  have hmem : ∀ {T : BigFppfOver B integerBase hZ} (x : T ⟶ X.base),
      (∃ l : (schemeSpace T).1 ⟶ W.toFunctor, l ≫ W.ι = (schemeSpaceMap x).hom) ↔
        ∀ y, ((BigFppfOver.toScheme B integerBase hZ).map x) y ∈
          Space.opensOfOpenSubspace B integerBase hZ X.base W hW := by
    intro T x
    refine (Space.FinitePartUniversalOpen.exists_lift_iff_mem (X := yoneda.obj X.base) W T
      (yoneda.map x)).trans ?_
    rw [yonedaEquiv_yoneda_map]
    exact Space.mem_iff_of_isOpenSubspace B integerBase hZ X.base W hW x
  have hr : ∀ y, ((BigFppfOver.toScheme B integerBase hZ).map r) y = s := fun y =>
    Scheme.fromSpecResidueField_apply _ _
  have hι : ∀ (U : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens) y,
      ((BigFppfOver.toScheme B integerBase hZ).map (Space.openSubHom X.base U)) y ∈ U := by
    intro U y
    rw [Space.toScheme_map_openSubHom]
    have hy := Set.mem_range_self (f := U.ι) y
    rwa [Scheme.Opens.range_ι] at hy
  constructor
  · rintro ⟨V, v, q, h, hno⟩
    obtain ⟨y⟩ : Nonempty ((BigFppfOver.toScheme B integerBase hZ).obj K) :=
      inferInstanceAs (Nonempty (Spec _))
    have hs := (hmem r).1 ((hfib v q h).1 hno) y
    rw [hr] at hs
    exact ⟨Space.opensOfOpenSubspace B integerBase hZ X.base W hW, hs, fun X₁ p₁ f₁ hsq =>
      (hiff _ p₁ f₁ hsq).1 ((hmem (Space.openSubHom X.base _)).2 (hι _))⟩
  · rintro ⟨U, hsU, hamp⟩
    have sq₁ := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase
      (schemeSpaceMap (Space.openSubHom X.base U))
    have hUW := (hmem (Space.openSubHom X.base U)).1 ((hiff _ _ _ sq₁).2 (hamp _ _ sq₁))
    have hsW : s ∈ Space.opensOfOpenSubspace B integerBase hZ X.base W hW := by
      simp only [Space.toScheme_map_openSubHom] at hUW
      exact hUW ⟨s, hsU⟩
    have hrW : ∃ l : (schemeSpace K).1 ⟶ W.toFunctor, l ≫ W.ι = (schemeSpaceMap r).hom :=
      (hmem r).2 fun y => (hr y).symm ▸ hsW
    have sq₀ := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase
      (schemeSpaceMap r)
    obtain ⟨V, v, q', hsq'⟩ := ((hiff _ _ _ sq₀).1 hrW).1 (𝟙 (yoneda.obj K))
    have h : X.IsFibrePresentation B hZ s v (q' ≫ pullback.fst X.toBase.hom (yoneda.map r)) := by
      have := hsq'.paste_horiz (AlgebraicSpaces.isPullback_hom B integerBase hZ sq₀)
      have e : 𝟙 (yoneda.obj K) ≫ (schemeSpaceMap r).hom = yoneda.map r :=
        Category.id_comp (yoneda.map r)
      exact cast (congrArg (fun t : yoneda.obj K ⟶ yoneda.obj X.base =>
        IsPullback (q' ≫ pullback.fst X.toBase.hom (yoneda.map r)) (yoneda.map v) X.toBase.hom t)
          e) this
    exact ⟨V, v, _, h, (hfib v _ h).2 hrW⟩

end CurveFamily

end AlgebraicGeometry

end
