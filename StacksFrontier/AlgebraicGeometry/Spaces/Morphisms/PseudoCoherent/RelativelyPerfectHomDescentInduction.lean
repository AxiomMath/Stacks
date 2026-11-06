module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectHomDescentMayerVietoris
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactQuasiSeparatedOverAffine

/-!
# The two inductions of the proof of Stacks 0DKV

In Situation 0DKU fix `K₀, L₀ ∈ D(𝒪_{X₀})`.  For an étale morphism `w : W ⟶ X₀` write
`w_!(w^*K₀)` for the object `AlgebraicGeometry.Space.RelativeDescentSituation.extendRestrictObj`
of `D(𝒪_{X₀})`.  The source proves Stacks 0DKV by the induction principle of Stacks 08GP, run
twice: first over the quasi-compact quasi-separated objects of `(Y₀)_{spaces, étale}`, which
reduces to `Y₀` affine, and then over those of `(X₀)_{spaces, étale}`, which reduces to `X₀`
affine.  The Mayer–Vietoris step of both inductions is
`AlgebraicGeometry.Space.RelativeDescentSituation.shiftedHomDescent_extendRestrict_of_eds`.

This file runs the two inductions.  The conclusion is that the tag holds for `(K₀, L₀)` at every
shift of `K₀` as soon as it holds for `(u_!(u^*K₀), L₀)` at every shift, for every étale
`u : U ⟶ X₀` with `U` affine such that `U ⟶ Y₀` factors through an étale morphism from an
affine algebraic space.

## Main results

* `AlgebraicGeometry.Space.RelativeDescentSituation.shiftedHomDescent_extendRestrict_of_qcqs`:
  the induction over the étale objects of a quasi-compact quasi-separated algebraic space
  étale over `X₀`.
* `AlgebraicGeometry.Space.RelativeDescentSituation.shiftedHomDescent_of_affine`: the
  induction over the étale objects of `Y₀`, followed by the previous one.

## Implementation notes

The induction over `Y₀` is run on the property of an étale `g : W ⟶ Y₀` that the tag holds for
`v_!(v^*K₀)` for *every* étale `v : X' ⟶ X₀` sitting in a cartesian square over `g` and
`p₀ : X₀ ⟶ Y₀`.  Quantifying over all cartesian squares makes the property independent of the
choice of fibre product, so the base change of an elementary distinguished square of `Y₀`
(Stacks 08GN) can be read with the fibre products it comes with.

## References

* [Stacks Project, Tag 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 08GN](https://stacks.math.columbia.edu/tag/08GN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_RelativelyPerfectHomDescentInduction
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_RelativelyPerfectHomDescentInduction
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

namespace RelativeDescentSituation

/- The conclusion of Stacks 0DKV,
`AlgebraicGeometry.Space.RelativeDescentSituation.HomDescent`, and the derived pullback
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback` it is built from are stated for the
standard model of the derived category, so the declarations below are stated at it too. -/
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  {D : RelativeDescentSituation B S hS hZ I} (P : DerivedPullbackComposition B S hS)

/-- The object `w_!(w^*K₀)` depends only on the morphism `w`. -/
theorem shiftedHomDescent_extendRestrict_congr {W : AlgebraicSpaces B S hS}
    {w w' : W ⟶ D.initialSource} (hw : IsEtale B S hS w.hom) (hw' : IsEtale B S hS w'.hom)
    (h : w = w') {K₀ L₀ : D.InitialDerived}
    (hK : D.ShiftedHomDescent P (D.extendRestrictObj w hw K₀) L₀) :
    D.ShiftedHomDescent P (D.extendRestrictObj w' hw' K₀) L₀ := by
  subst h
  exact hK

/-- **The induction over the étale objects of a quasi-compact quasi-separated algebraic space
étale over `X₀`.**  Let `v : X' ⟶ X₀` be étale with `X'` quasi-compact and quasi-separated.  If
the conclusion of Stacks 0DKV holds at every shift for `(h ≫ v)_!((h ≫ v)^*K₀)` against `L₀`
for every étale `h : U ⟶ X'` with `U` affine, then it holds for `v_!(v^*K₀)`. -/
theorem shiftedHomDescent_extendRestrict_of_qcqs (K₀ L₀ : D.InitialDerived)
    {X' : AlgebraicSpaces B S hS} (v : X' ⟶ D.initialSource) (hv : IsEtale B S hS v.hom)
    (hX'qc : IsQuasiCompactSpace B S hS X'.1) (hX'qs : IsAbsolutelyQuasiSeparated B S hS hZ X'.1)
    (hleaf : ∀ {U : AlgebraicSpaces B S hS} (h : U ⟶ X') (hh : IsEtale B S hS h.hom),
      IsAffineSpace B S hS U.1 →
        D.ShiftedHomDescent P (D.extendRestrictObj (h ≫ v) (isEtale_comp B S hS hh hv) K₀) L₀) :
    D.ShiftedHomDescent P (D.extendRestrictObj v hv K₀) L₀ := by
  let Q : (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → (Y ⟶ X'.1) → Prop := fun Y g ↦
    ∀ (hY : IsAlgebraicSpace B S hS Y) (hg : IsEtale B S hS g),
      D.ShiftedHomDescent P (D.extendRestrictObj
        ((ObjectProperty.homMk g : (⟨Y, hY⟩ : AlgebraicSpaces B S hS) ⟶ X') ≫ v)
        (isEtale_comp B S hS hg hv) K₀) L₀
  have key : Q X'.1 (𝟙 X'.1) := by
    refine qcqs_induction_on_self B S hS hZ X' hX'qc hX'qs Q ?_ ?_
    · intro V hV hY hg
      exact hleaf (U := ⟨V.1.left.1, hY⟩) (ObjectProperty.homMk V.1.hom.hom) hg hV
    · intro W V U f hf hsq _ _ _ _ hPU hPV hPP hY hg
      have hWg := isEtale_comp B S hS (isEtale_edsOpenHom B S hS hsq) hg
      refine shiftedHomDescent_extendRestrict_of_eds P (W := W.1.left)
        (ObjectProperty.homMk W.1.hom.hom ≫ v) (isEtale_comp B S hS hg hv) hsq K₀ L₀ ?_ ?_ ?_
      · exact shiftedHomDescent_extendRestrict_congr P _ _ rfl
          (hPU hsq.isOpenSubspace.1 hWg)
      · refine shiftedHomDescent_extendRestrict_congr P _ _ ?_
          (hPV hsq.isAlgebraicSpace V.2)
        ext1
        exact hf.symm =≫ v.hom
      · exact shiftedHomDescent_extendRestrict_congr P _ _ rfl
          (hPP (edsInter B S hS hsq).2
            (isEtale_comp B S hS (isEtale_edsFst B S hS hsq) hWg))
  exact shiftedHomDescent_extendRestrict_congr P _ _ (Category.id_comp v) (key X'.2
    (isEtale_id B S hS X'.1))

/-- For `U ⊆ W`, `f : V ⟶ W` and `p : X' ⟶ W`, the comparison from the intersection of the base
change of `(U, f)` along `p` to the intersection `U ×_W V`. -/
def pullbackPreimageιLift {W V X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : Subfunctor W)
    (f : V ⟶ W) (p : X' ⟶ W) :
    pullback (U.preimage p).ι (pullback.snd f p) ⟶ pullback U.ι f :=
  pullback.lift (pullback.fst (U.preimage p).ι (pullback.snd f p) ≫ U.fromPreimage p)
    (pullback.snd (U.preimage p).ι (pullback.snd f p) ≫ pullback.fst f p) (by
      simp only [Category.assoc]
      rw [(Subfunctor.isPullback_preimage p U).w, ← Category.assoc, pullback.condition,
        Category.assoc, ← pullback.condition])

/-- The intersection of the base change along `p : X' ⟶ W` of an elementary distinguished
square `(U ⊆ W, f : V ⟶ W)` is the base change along `p` of its intersection `U ×_W V`. -/
theorem isPullback_pullbackPreimageιLift {W V X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : Subfunctor W) (f : V ⟶ W) (p : X' ⟶ W) :
    IsPullback (pullbackPreimageιLift U f p)
      (pullback.fst (U.preimage p).ι (pullback.snd f p) ≫ (U.preimage p).ι)
      (pullback.fst U.ι f ≫ U.ι) p := by
  have hAB := (IsPullback.of_hasPullback (U.preimage p).ι (pullback.snd f p)).paste_horiz
    (Subfunctor.isPullback_preimage p U)
  rw [← pullback.condition] at hAB
  have hTop := IsPullback.of_right (h₁₁ := pullbackPreimageιLift U f p)
    (by rw [pullbackPreimageιLift, pullback.lift_fst]; exact hAB)
    (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback U.ι f)
  have h := hTop.paste_vert (IsPullback.of_hasPullback f p)
  rwa [← pullback.condition, ← pullback.condition] at h

/-- **The induction over the étale objects of `Y₀`, then over those of `X₀`.**  If the
conclusion of Stacks 0DKV holds at every shift for `(u_!(u^*K₀), L₀)` for every étale
`u : U ⟶ X₀` with `U` affine whose composite `U ⟶ Y₀` factors through an étale morphism from
an affine algebraic space, then it holds for `(K₀, L₀)` at every shift. -/
theorem shiftedHomDescent_of_affine (K₀ L₀ : D.InitialDerived)
    (hleaf : ∀ {U : AlgebraicSpaces B S hS} (u : U ⟶ D.initialSource)
      (hu : IsEtale B S hS u.hom), IsAffineSpace B S hS U.1 →
      ∀ {V : AlgebraicSpaces B S hS} (g : V ⟶ D.initialTarget) (t : U.1 ⟶ V.1),
        IsAffineSpace B S hS V.1 → IsEtale B S hS g.hom → t ≫ g.hom = u.hom ≫ D.p₀ →
          D.ShiftedHomDescent P (D.extendRestrictObj u hu K₀) L₀) :
    D.ShiftedHomDescent P K₀ L₀ := by
  let Q : (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → (Y ⟶ D.initialTarget.1) → Prop := fun Y g ↦
    ∀ (X' : AlgebraicSpaces B S hS) (v : X' ⟶ D.initialSource) (hv : IsEtale B S hS v.hom)
      (v' : X'.1 ⟶ Y), IsPullback v' v.hom g D.p₀ →
        D.ShiftedHomDescent P (D.extendRestrictObj v hv K₀) L₀
  have hid : IsEtale B S hS (𝟙 D.initialSource : D.initialSource ⟶ D.initialSource).hom :=
    isEtale_id B S hS _
  refine shiftedHomDescent_of_extendRestrict_id P hid ?_
  suffices key : Q D.initialTarget.1 (𝟙 _) from
    key D.initialSource (𝟙 _) hid D.p₀ (IsPullback.of_vert_isIso ⟨by simp⟩)
  refine qcqs_induction_on_self B S hS hZ D.initialTarget (D.stage_isQuasiCompact D.i₀)
    (D.stage_isQuasiSeparated D.i₀) Q ?_ ?_
  · -- the affine objects of `Y₀`: the inner induction
    intro V hV X' v hv v' sq
    have hv'qc : IsQuasiCompact B S hS v' :=
      isQuasiCompact_of_isPullback B S hS sq.flip D.initial_isFinitePresentation.2.1
    have hv'qs : IsQuasiSeparated B S hS v' :=
      isQuasiSeparated_of_isPullback B S hS sq.flip D.initial_isFinitePresentation.2.2
    refine shiftedHomDescent_extendRestrict_of_qcqs P K₀ L₀ v hv
      (isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS v' hV hv'qc)
      (isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_isAffineSpace B S hS hZ v' X'.2 hV
        hv'qs) fun h hh hU ↦ ?_
    refine hleaf (h ≫ v) (isEtale_comp B S hS hh hv) hU (V := V.1.left)
      (ObjectProperty.homMk V.1.hom.hom) (h.hom ≫ v') hV V.2 ?_
    show (h.hom ≫ v') ≫ V.1.hom.hom = (h.hom ≫ v.hom) ≫ D.p₀
    rw [Category.assoc, Category.assoc, sq.w]
  · -- the Mayer–Vietoris step, through the base change of the square along `v'`
    intro W V U f hf hsq _ _ _ _ hPU hPV hPP X' v hv v' sq
    have hsq' := isElementaryDistinguishedSquare_preimage B S hS W.1.left.2 X'.2 U f hsq v'
    refine shiftedHomDescent_extendRestrict_of_eds P (W := X') v hv hsq' K₀ L₀ ?_ ?_ ?_
    · exact hPU (edsOpen B S hS hsq') _ _ (U.fromPreimage v')
        ((Subfunctor.isPullback_preimage v' U).paste_vert sq)
    · refine hPV (edsEtale B S hS hsq') _ _ (pullback.fst f v') ?_
      have h := (IsPullback.of_hasPullback f v').paste_vert sq
      rwa [hf] at h
    · refine hPP (edsInter B S hS hsq') _ _ (pullbackPreimageιLift U f v') ?_
      have h := (isPullback_pullbackPreimageιLift U f v').paste_vert sq
      simp only [Category.assoc] at h
      exact h

end RelativeDescentSituation

end AlgebraicGeometry.Space

end
