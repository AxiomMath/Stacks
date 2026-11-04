module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableNearFibre
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelUnique
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.DualizingAmple

/-!
# The stable model étale locally near a point

Let `X ⟶ S` be a prestable family of curves of genus `g ≥ 2` and `h : X_U ⟶ Y` a morphism to a
family of curves over an étale neighbourhood `U` of a point, whose fibres over a point `u` of `U`
are stable contractions (this is the output of Stacks 0E7C applied to the stable contraction of the
fibre, Stacks 0E7Q). Then over an étale neighbourhood of `u`, `h` is a stable model of `X`: this
is the local step of the proof of Stacks 0E8A, which combines Stacks 0E88 (condition (1) near the
fibre), the openness of the stable locus (Stacks 0E76) and the fibrewise characterization of
stable contractions.

## Main results

* `AlgebraicGeometry.C1590Private.fibreAcyclicAt_of_isStableContraction`: the fibre hypothesis of
  Stacks 0E88 at `u`.
* `AlgebraicGeometry.C1590Private.hasStableFibresAt_of_isStableContraction`: the fibres of `Y`
  over `u` are stable curves.

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 0E88](https://stacks.math.columbia.edu/tag/0E88)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 2000] HasDerivedCategory.standard

namespace AlgebraicGeometry.C1590Private

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- The fibres over `u` of a morphism `h : A ⟶ Y.total`, at every presentation, are stable
contractions. -/
def FibresStableContractionsAt {A : AlgebraicSpaces B integerBase hZ} (Y : CurveFamily B hZ)
    (pA : A ⟶ schemeSpace Y.base) (h : A ⟶ Y.total)
    (u : (BigFppfOver.toScheme B integerBase hZ).obj Y.base) : Prop :=
  ∀ Q : Space.FieldValuedPoint B integerBase hZ (schemeSpace Y.base).obj,
    (∀ x, (BigFppfOver.toScheme B integerBase hZ).map Q.value x = u) →
    ∀ ⦃V W : BigFppfOver B integerBase hZ⦄ (v : V ⟶ Q.siteObject) (w : W ⟶ Q.siteObject)
      (q : yoneda.obj V ⟶ A.obj) (r : yoneda.obj W ⟶ Y.total.obj) (m : V ⟶ W),
      IsPullback q (yoneda.map v) pA.hom (yonedaEquiv.symm Q.value) →
      IsPullback r (yoneda.map w) Y.toBase.hom (yonedaEquiv.symm Q.value) →
      m ≫ w = v → yoneda.map m ≫ r = q ≫ h.hom →
        Stacks.Curves.StableModel.IsStableContraction
          ((BigFppfOver.toScheme B integerBase hZ).map v)
          ((BigFppfOver.toScheme B integerBase hZ).map w)
          ((BigFppfOver.toScheme B integerBase hZ).map m)

/-- **The fibre hypothesis of Stacks 0E88** at a point over which the fibres are stable
contractions of the fibres of a prestable family. -/
theorem fibreAcyclicAt_of_isStableContraction {X Y : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X) (t : Y.base ⟶ X.base)
    {A : AlgebraicSpaces B integerBase hZ} (iA : A ⟶ X.total) (pA : A ⟶ schemeSpace Y.base)
    (hsq : IsPullback iA pA X.toBase (schemeSpaceMap t)) (h : A ⟶ Y.total)
    (hh : h ≫ Y.toBase = pA) (u : (BigFppfOver.toScheme B integerBase hZ).obj Y.base)
    (hfib : FibresStableContractionsAt Y pA h u) : FibreAcyclicAt h Y.toBase u := by
  intro P hP V W v w q r m hq hr hmw hmr
  rw [hh] at hq
  have hc := hfib P hP v w q r m hq hr hmw hmr
  have hX' := CurveFamily.isPrestableCurveFamily_of_hom
    (curveFamilyOfIsPullbackHom X t iA pA hsq) hX
  have hq' : IsPullback q (yoneda.map v) (curveFamilyOfIsPullback X t iA pA hsq).toBase.hom
      (yonedaEquiv.symm P.value) := by
    rw [curveFamilyOfIsPullback_toBase]
    exact hq
  obtain ⟨-, hdim, -, -⟩ := fibre_properties_of_isPrestableCurveFamily hX' P v q hq'
  exact ⟨hdim.le, (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ 1 _).1
    hc.isZero_rightDerived_one, hc.isIso_unitToPushforwardObjUnit⟩

/-- **The fibres of `Y` over `u` are stable curves**, when they are targets of stable contractions
of the fibres of a prestable family with fibres of genus `g ≥ 2`. -/
theorem hasStableFibresAt_of_isStableContraction {g : ℕ} {X Y : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X) (hgen : X.HasFibresOfGenus g) (hg : 2 ≤ g)
    (t : Y.base ⟶ X.base) {A : AlgebraicSpaces B integerBase hZ} (iA : A ⟶ X.total)
    (pA : A ⟶ schemeSpace Y.base) (hsq : IsPullback iA pA X.toBase (schemeSpaceMap t))
    (h : A ⟶ Y.total) (hh : h ≫ Y.toBase = pA)
    (u : (BigFppfOver.toScheme B integerBase hZ).obj Y.base)
    (hfib : FibresStableContractionsAt Y pA h u) : HasStableFibresAt Y u := by
  intro Q hQ W w r hr
  let X' := curveFamilyOfIsPullback X t iA pA hsq
  have hX' := CurveFamily.isPrestableCurveFamily_of_hom
    (curveFamilyOfIsPullbackHom X t iA pA hsq) hX
  have hgen' := hgen.of_hom (curveFamilyOfIsPullbackHom X t iA pA hsq)
  obtain ⟨V, v, q₀, hq⟩ := exists_presentation_of_fieldValuedPoint X' Q
  let q : yoneda.obj V ⟶ A.obj := q₀
  have hqA : IsPullback q (yoneda.map v) pA.hom (yonedaEquiv.symm Q.value) := hq
  let l : yoneda.obj V ⟶ yoneda.obj W := hr.lift (q ≫ h.hom) (yoneda.map v) (by
    rw [Category.assoc, ← hqA.w]
    exact congrArg (q ≫ ·) (congrArg (fun k => k.hom) hh))
  let m : V ⟶ W := Yoneda.fullyFaithful.preimage l
  have hml : yoneda.map m = l := Yoneda.fullyFaithful.map_preimage l
  have hmw : m ≫ w = v := Yoneda.fullyFaithful.map_injective (by
    rw [Functor.map_comp, hml]
    exact hr.lift_snd _ _ _)
  have hmr : yoneda.map m ≫ r = q ≫ h.hom := by
    rw [hml]
    exact hr.lift_fst _ _ _
  have hc := hfib Q hQ v w q r m hqA hr hmw hmr
  obtain ⟨hprop, hdim, hH0, -⟩ := fibre_properties_of_isPrestableCurveFamily hX' Q v q₀ hq
  have := hprop
  have := hH0
  have hgV : genus ((BigFppfOver.toScheme B integerBase hZ).map v) = g :=
    (hgen' Q).genus_eq v q₀ hq
  exact IsStableContraction.isStableCurveOver hc hdim (hgV ▸ hg)

/-- **Ampleness of the dualizing sheaf is invariant under isomorphism over the field.** If
`e : W ≅ W₀` lies over `Spec K`, `W` is a proper nodal curve of dimension one with `H⁰ = K`, and
`ω_{W₀}` is invertible and ample, then so is `ω_W`: it is the pullback of `ω_{W₀}` along `e`
(base change of the dualizing sheaf along the identity of `K`, Stacks 0E32). -/
theorem isAmple_dualizingSheafOverField_of_iso {K : Type u} [Field K] {W W₀ : Scheme.{u}}
    (g : W ⟶ Spec (.of K)) (g₀ : W₀ ⟶ Spec (.of K)) [IsProper g] [IsProper g₀]
    (hdim : topologicalKrullDim W = 1) [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop)]
    (hnodal : letI : W.Over (Spec (.of K)) := ⟨g⟩; Stacks.Curves.HasAtWorstNodalSingularities K W)
    (e : W ≅ W₀) (he : e.hom ≫ g₀ = g)
    (h₀ : ∃ _ : AlgebraicGeometry.SheafOfModules.IsInvertible W₀.toRingedSpace.presheaf
        (structureSheafRing W₀.toRingedSpace).property (Stacks.Duality.dualizingSheafOverField g₀),
      Scheme.Modules.IsAmple W₀ (Stacks.Duality.dualizingSheafOverField g₀)) :
    ∃ _ : AlgebraicGeometry.SheafOfModules.IsInvertible W.toRingedSpace.presheaf
        (structureSheafRing W.toRingedSpace).property (Stacks.Duality.dualizingSheafOverField g),
      Scheme.Modules.IsAmple W (Stacks.Duality.dualizingSheafOverField g) := by
  obtain ⟨hω₀, hL₀⟩ := h₀
  have hid : Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (.of K)) := by
    rw [show CommRingCat.ofHom (algebraMap K K) = 𝟙 _ from rfl, Spec.map_id]
  have hsq : IsPullback e.hom g g₀ (Spec.map (CommRingCat.ofHom (algebraMap K K))) := by
    rw [hid]
    exact IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩
  let eW := Stacks.Duality.dualizingSheafOverFieldBaseChangeIso g₀ e.hom g hsq
  let : AlgebraicGeometry.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
      ((Scheme.Modules.pullback e.hom).obj (Stacks.Duality.dualizingSheafOverField g₀)) :=
    Stacks.Modules.isInvertible_pullback _ _
  let : W.Over (Spec (.of K)) := ⟨g⟩
  have : IsProper (W ↘ Spec (.of K)) := inferInstanceAs (IsProper g)
  have : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ (W ↘ Spec (.of K)).appTop) :=
    inferInstanceAs (IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop))
  have : ConnectedSpace W := connectedSpace_of_isIso_globalSections K g
  have hω : AlgebraicGeometry.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField g) :=
    isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities K W hdim hnodal
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace g
  exact ⟨hω, Scheme.Modules.isAmple_of_iso eW
    (Scheme.Modules.isAmple_pullback_of_isAffineHom e.hom _ hL₀)⟩

end AlgebraicGeometry.C1590Private

end
