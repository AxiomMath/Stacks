module

public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesStable
public import StacksFrontier.AlgebraicGeometry.Quot.StableCurveFamilyOfSchemes

/-!
# The fibres of a stable family of curves given by a morphism of schemes

Let `p : X ⟶ S` be a morphism of schemes which is a stable family of curves
(`AlgebraicGeometry.IsStableFamilyOfSchemes`), and let `s ∈ S`. The fibre of `p` over `s` is
presented by a scheme `V` with a cartesian square over `Spec κ(s) ⟶ S`, such that `V` is proper
over `κ(s)`, has genus at least two, no rational tail and no rational bridge
(Stacks 0E75), and `H⁰(V, 𝒪_V) = κ(s)`. This reads the definition of stability at the
field-valued point `Spec κ(s) ⟶ S` of the base.

## Main results

* `AlgebraicGeometry.IsStableFamilyOfSchemes.exists_isPullback_fiber`: the presentation of the
  fibre over `s`.

## References

* [Stacks Project, Tag 0E75](https://stacks.math.columbia.edu/tag/0E75)
* [Stacks Project, Tag 0E97](https://stacks.math.columbia.edu/tag/0E97)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The fibre of a stable family of schemes over a point of the base.** For a stable family of
curves `p : X ⟶ S` and `s ∈ S` there is a cartesian square `V ⟶ X`, `g : V ⟶ Spec κ(s)` over
`p` and `Spec κ(s) ⟶ S` such that `g` has genus at least two, no rational tail and no rational
bridge, and `H⁰(V, 𝒪_V) = κ(s)`. -/
theorem IsStableFamilyOfSchemes.exists_isPullback_fiber {X S : Scheme.{u}} {p : X ⟶ S}
    {hS : B.Contains S} (h : IsStableFamilyOfSchemes B hZ p hS) (s : S) :
    ∃ (V : Scheme.{u}) (j : V ⟶ X) (g : V ⟶ Spec (.of (S.residueField s))),
      IsPullback j g p (S.fromSpecResidueField s) ∧
      HasGenusTwoNoRationalTailNoRationalBridge (S.residueField s) g ∧
      IsIso ((Scheme.ΓSpecIso (.of (S.residueField s))).inv ≫ g.appTop) := by
  obtain ⟨hflat, hproper, hlfp, hfib, hstab⟩ := h
  have hκ : B.Contains (Spec (.of (S.residueField s))) := B.residueField_spec_contains hS s
  let F := curveFamilyOfFiberDimensionLE B hZ
    (integerSiteMap B hZ (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact p hS) hS p)
    hflat hproper hlfp hfib
  let pt : Space.FieldValuedPoint B integerBase hZ (schemeSpace F.base).obj :=
    { carrier := S.residueField s
      contained := hκ
      toBase := specULiftZIsTerminal.from _
      value := integerSiteMap B hZ hκ hS (S.fromSpecResidueField s) }
  obtain ⟨V, v, q, hq, hgen⟩ := hstab.2 pt
  have hval : yonedaEquiv.symm pt.value = yoneda.map pt.value :=
    yonedaEquiv.symm_apply_eq.mpr (yonedaEquiv_yoneda_map _).symm
  rw [hval] at hq
  have hsq : IsPullback (ObjectProperty.homMk q : schemeSpace V ⟶ F.total)
      (schemeSpaceMap v) F.toBase (schemeSpaceMap pt.value) :=
    IsPullback.of_map (ObjectProperty.ι _) ((ObjectProperty.ι _).map_injective hq.w) hq
  let q' := Yoneda.fullyFaithful.preimage q
  have hq' : yoneda.map q' = q := Yoneda.fullyFaithful.map_preimage q
  rw [← hq'] at hq
  have hsite : IsPullback q' v
      (integerSiteMap B hZ (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact p hS) hS p)
      pt.value :=
    IsPullback.of_map yoneda (Yoneda.fullyFaithful.map_injective (by
      rw [Functor.map_comp]
      exact hq.w)) hq
  have hsch := hsite.map (BigFppfOver.toScheme B integerBase hZ)
  exact ⟨_, (BigFppfOver.toScheme B integerBase hZ).map q',
    (BigFppfOver.toScheme B integerBase hZ).map v, hsch, hgen,
    CurveFamily.isIso_appTop_of_isPullback_fieldValuedPoint hstab.1.2 hsq⟩

end AlgebraicGeometry

end
