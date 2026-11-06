module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesAffineCaseSections
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineOver
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.IsomorphismFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffineBaseChangeIso
import StacksFrontier.AlgebraicGeometry.Pushout.QuasiFiniteFunctoriality
import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringBaseChange
import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.EtalePhCoverings

/-!
# Recognising a base change of an affine scheme on affine étale charts

Let `X` be represented by an affine object `Z` of the big fppf site, `T ⟶ Z` a morphism from an
affine object, `q : Q ⟶ X` a morphism of algebraic spaces, and `g : Q' ⟶ Q` an affine morphism
with a morphism `a : Q' ⟶ T` over `X`.  If over every affine étale chart `W` of `Q` the map
`Γ(W) ⊗_{Γ(Z)} Γ(T) ⟶ Γ(W ×_Q Q')`, `w ⊗ t ↦ w · a^*(t)`, is bijective, then
`Q' ⟶ Q ×_X T` is an isomorphism: over `W` it is the morphism of affine schemes
`W ×_Q Q' ⟶ W ×_Z T` inducing that map on global functions, and the affine étale charts cover `Q`.

## Main results

* `AlgebraicGeometry.Space.isIso_pullbackLift_of_bijective_tensor`.
* `AlgebraicGeometry.Space.isPullback_baseChangeChart_of_bijective_tensor`: over an affine étale
  chart `W` of `Q`, the chart `W ×_Q Q'` is the fibre product `T ×_X W`.
* `CommRingCat.isPushout_of_tensorAddEquiv`: a square of rings is a pushout once an additive
  bijection `A ⊗[R] B ≃ C` sends `a ⊗ b` to `i a * j b`.
* `CategoryTheory.Limits.isIso_pullback_snd_lift_of_isPullback`: the base change of
  `Q' ⟶ T ×_X Q` along `W ×_Q (T ×_X Q) ⟶ T ×_X Q` is invertible once `W ×_Q Q'` is `T ×_X W`.

## References

* [Stacks Project, Tag 0AF4](https://stacks.math.columbia.edu/tag/0AF4)
* [Stacks Project, Tag 041Y](https://stacks.math.columbia.edu/tag/041Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-- **A commutative square of commutative rings is a pushout as soon as some additive bijection
`A ⊗[R] B ≃ C` sends `a ⊗ b` to `i a * j b`.**  Such a bijection agrees with the canonical ring map
`a ⊗ b ↦ i a * j b` on pure tensors, hence everywhere, which is therefore a ring isomorphism. -/
theorem _root_.CommRingCat.isPushout_of_tensorAddEquiv {R A B C : CommRingCat.{u}}
    (f : R ⟶ A) (g : R ⟶ B) (i : A ⟶ C) (j : B ⟶ C) (w : f ≫ i = g ≫ j)
    (e : letI := f.hom.toAlgebra; letI := g.hom.toAlgebra; TensorProduct R A B ≃+ C)
    (he : letI := f.hom.toAlgebra; letI := g.hom.toAlgebra;
      ∀ a b, e (a ⊗ₜ b) = i a * j b) :
    IsPushout f g i j := by
  let := f.hom.toAlgebra
  let := g.hom.toAlgebra
  let : Algebra R C := (f ≫ i).hom.toAlgebra
  let iA : A →ₐ[R] C := { i.hom with commutes' := fun _ => rfl }
  let jB : B →ₐ[R] C :=
    { j.hom with commutes' := fun r => (congrArg (fun k => k.hom r) w).symm }
  let φ := Algebra.TensorProduct.productMap iA jB
  have hφ : ∀ x, φ x = e x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a b =>
      rw [he]
      exact Algebra.TensorProduct.productMap_apply_tmul iA jB a b
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hbij : Function.Bijective φ := by
    rw [show (φ : TensorProduct R A B → C) = e from funext hφ]
    exact e.bijective
  let ψ : TensorProduct R A B ≃+* C := RingEquiv.ofBijective φ.toRingHom hbij
  refine (CommRingCat.isPushout_tensorProduct R A B).of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ψ.toCommRingCatIso rfl rfl ?_ ?_
  · ext a
    change φ (a ⊗ₜ 1) = i a
    rw [Algebra.TensorProduct.productMap_apply_tmul]
    change i a * j 1 = i a
    rw [map_one, mul_one]
  · ext b
    change φ (1 ⊗ₜ b) = j b
    rw [Algebra.TensorProduct.productMap_apply_tmul]
    change i 1 * j b = j b
    rw [map_one, one_mul]

/-- **Recognising the base change of a cartesian square.**  Let `L : Q' ⟶ T ×_X Q` be the
morphism induced by `a : Q' ⟶ T` and `g : Q' ⟶ Q`, and let `E = Q' ×_Q W` be a fibre product
along `w : W ⟶ Q`.  If `E` with its maps `eQ ≫ a` and `eW` is also a fibre product of `T` and
`W` over `X`, then the base change of `L` along `W ×_Q (T ×_X Q) ⟶ T ×_X Q` is an
isomorphism. -/
theorem _root_.CategoryTheory.Limits.isIso_pullback_snd_lift_of_isPullback {C : Type*}
    [Category C] [HasPullbacks C] {Xo Qo Q'o To Wo Eo : C} (h₀ : To ⟶ Xo) (q : Qo ⟶ Xo)
    (g : Q'o ⟶ Qo) (a : Q'o ⟶ To) (ha : a ≫ h₀ = g ≫ q) (w : Wo ⟶ Qo) (eQ : Eo ⟶ Q'o)
    (eW : Eo ⟶ Wo) (hA : IsPullback eQ eW g w) (hD : IsPullback (eQ ≫ a) eW h₀ (w ≫ q)) :
    IsIso (pullback.snd (pullback.lift a g ha) (pullback.snd w (pullback.snd h₀ q))) := by
  let L := pullback.lift a g ha
  let s := pullback.snd h₀ q
  have hLs : L ≫ s = g := pullback.lift_snd _ _ _
  have hLf : L ≫ pullback.fst h₀ q = a := pullback.lift_fst _ _ _
  let c : Eo ⟶ pullback w s := pullback.lift eW (eQ ≫ L) (by
    rw [Category.assoc, hLs, hA.w])
  have hcf : c ≫ pullback.fst w s = eW := pullback.lift_fst _ _ _
  have hcs : c ≫ pullback.snd w s = eQ ≫ L := pullback.lift_snd _ _ _
  have hpaste : IsPullback (pullback.snd w s ≫ pullback.fst h₀ q) (pullback.fst w s) h₀
      (w ≫ q) :=
    (IsPullback.of_hasPullback w s).flip.paste_horiz (IsPullback.of_hasPullback h₀ q)
  have hc : IsIso c := by
    have hceq : c = (hD.isoIsPullback _ _ hpaste).hom := by
      apply hpaste.hom_ext
      · rw [IsPullback.isoIsPullback_hom_fst, ← Category.assoc, hcs, Category.assoc, hLf]
      · rw [IsPullback.isoIsPullback_hom_snd, hcf]
    rw [hceq]
    infer_instance
  have hout : IsPullback eQ (c ≫ pullback.fst w s) (L ≫ s) w := by rwa [hcf, hLs]
  have htop : IsPullback eQ c L (pullback.snd w s) :=
    hout.of_bot hcs.symm (IsPullback.of_hasPullback w s).flip
  have hsnd : pullback.snd L (pullback.snd w s) = htop.isoPullback.inv ≫ c := by
    rw [Iso.eq_inv_comp, IsPullback.isoPullback_hom_snd]
  rw [hsnd]
  infer_instance

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Q Q' : AlgebraicSpaces B S hS}

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_FormalGlueingSpacesAffineCaseGeometry :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Shortcut for limits of cospans of presheaves on the big fppf site. -/
local instance (priority := high) hasPullback_presheaf_FormalGlueingSpacesAffineCaseGeometry
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Over an affine étale chart `W` of `Q`, the base-changed chart `E = W ×_Q Q'` is the fibre
product `T ×_X W`.**  The four schemes are affine and the square of their rings of global
functions is a pushout, the tensor map being bijective by hypothesis; so the square of schemes
is cartesian, and so is its image under the Yoneda embedding. -/
theorem isPullback_baseChangeChart_of_bijective_tensor (q : Q ⟶ X) (g : Q' ⟶ Q)
    (hg : IsAffineHom B S hS g.hom) (Z₀ : SmallEtale B S hS X.1) [IsIso Z₀.1.hom]
    [IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀)]
    {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (τ : T ⟶ (SmallEtale.toOver B S hS X.1).obj Z₀) (a : Q' ⟶ schemeSpace T)
    (ha : a.hom ≫ yoneda.map τ ≫ Z₀.1.hom = g.hom ≫ q.hom)
    (hμ : ∀ (W : SmallEtale B S hS Q.1)
      (_ : IsAffine ((SmallEtale.toOver B S hS Q.1 ⋙ BigFppfOver.toScheme B S hS).obj W)),
      letI : Algebra (chartRing B S hS X.1 X.2 Z₀)
          (chartRing B S hS Q.1 Q.2 W) :=
        chartDiagramAlgebra B S hS q (isoChartDiagram B S hS q Z₀ W)
      letI : Algebra (chartRing B S hS X.1 X.2 Z₀)
          Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op).hom.toAlgebra
      ∃ e : TensorProduct (chartRing B S hS X.1 X.2 Z₀)
          (chartRing B S hS Q.1 Q.2 W) Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) ≃+
          chartRing B S hS Q'.1 Q'.2
            ((smallBaseChange B S hS g (relativelyRepresentable_of_isAffineHom B S hS g hg)).obj W),
        ∀ w t, e (w ⊗ₜ t) =
          (show (structureSheaf B S hS Q'.1 Q'.2).obj.obj
              (op ((smallBaseChange B S hS g
                (relativelyRepresentable_of_isAffineHom B S hS g hg)).obj W)) from
            chartDiagramRestrict B S hS g
              (smallBaseChangeDiagram g (relativelyRepresentable_of_isAffineHom B S hS g hg) W) w) *
            (show (structureSheaf B S hS Q'.1 Q'.2).obj.obj
                (op ((smallBaseChange B S hS g
                  (relativelyRepresentable_of_isAffineHom B S hS g hg)).obj W)) from
              (pullbackToGlobalFunctions B S hS Q' T a t).1
                (op ((smallBaseChange B S hS g
                  (relativelyRepresentable_of_isAffineHom B S hS g hg)).obj W))))
    (W : SmallEtale B S hS Q.1)
    (hW : IsAffine ((SmallEtale.toOver B S hS Q.1 ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    IsPullback (((smallBaseChange B S hS g
        (relativelyRepresentable_of_isAffineHom B S hS g hg)).obj W).1.hom ≫ a.hom)
      (yoneda.map ((relativelyRepresentable_of_isAffineHom B S hS g hg).snd W.1.hom))
      (yoneda.map τ ≫ Z₀.1.hom) (W.1.hom ≫ q.hom) := by
  let hrep := relativelyRepresentable_of_isAffineHom B S hS g hg
  let E := (smallBaseChange B S hS g hrep).obj W
  let F := BigFppfOver.toScheme B S hS
  let gW := (isoChartDiagram B S hS q Z₀ W).g
  let sE := hrep.snd W.1.hom
  let aE : (SmallEtale.toOver B S hS Q'.1).obj E ⟶ T := yoneda.preimage (E.1.hom ≫ a.hom)
  have haE : yoneda.map aE = E.1.hom ≫ a.hom := Functor.map_preimage _ _
  have hgW : yoneda.map gW ≫ Z₀.1.hom = W.1.hom ≫ q.hom :=
    (isoChartDiagram B S hS q Z₀ W).comm.symm
  have hwE : E.1.hom ≫ g.hom = yoneda.map sE ≫ W.1.hom := hrep.w W.1.hom
  have hw : sE ≫ gW = aE ≫ τ := by
    apply yoneda.map_injective
    have : Mono Z₀.1.hom := IsIso.mono_of_iso _
    rw [← cancel_mono Z₀.1.hom]
    have h1 : yoneda.map (sE ≫ gW) ≫ Z₀.1.hom = E.1.hom ≫ g.hom ≫ q.hom := by
      rw [Functor.map_comp, Category.assoc, hgW, ← Category.assoc, ← hwE]
      exact Category.assoc _ _ _
    have h2 : yoneda.map (aE ≫ τ) ≫ Z₀.1.hom = E.1.hom ≫ g.hom ≫ q.hom := by
      rw [Functor.map_comp, Category.assoc, haE]
      exact (Category.assoc _ _ _).trans (congrArg (E.1.hom ≫ ·) ha)
    exact h1.trans h2.symm
  have : IsAffine (F.obj ((SmallEtale.toOver B S hS Q'.1).obj E)) :=
    isAffine_smallBaseChange_obj B S hS g hrep hg W hW
  have : IsAffine (F.obj ((SmallEtale.toOver B S hS Q.1).obj W)) := hW
  have : IsAffine (F.obj ((SmallEtale.toOver B S hS X.1).obj Z₀)) :=
    inferInstanceAs (IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ F).obj Z₀))
  have hpush : IsPushout (F.map gW).appTop (F.map τ).appTop (F.map sE).appTop
      (F.map aE).appTop := by
    obtain ⟨e, he⟩ := hμ W hW
    exact CommRingCat.isPushout_of_tensorAddEquiv _ _ _ _
      (congrArg (fun k => (F.map k).appTop) hw) e he
  have : IsAffine (F.obj T) := ‹IsAffine ((BigFppfOver.toScheme B S hS).obj T)›
  have : IsAffine (F.obj W.1.left) := hW
  have : IsAffine (F.obj Z₀.1.left) :=
    inferInstanceAs (IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ F).obj Z₀))
  have : IsAffine (F.obj (hrep.pullback W.1.hom)) :=
    isAffine_smallBaseChange_obj B S hS g hrep hg W hW
  have hsq : IsPullback (F.map aE) (F.map sE) (F.map τ) (F.map gW) :=
    isPullback_of_isPushout_appTop hpush.flip
  have hy := (IsPullback.of_map_of_faithful F hsq).map yoneda
  rw [haE] at hy
  exact hy.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso Z₀.1.hom)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    (Category.id_comp _).symm (hgW.trans (Category.id_comp _).symm)

/-- **A morphism to a fibre product of algebraic spaces is an isomorphism once it is one after
base change along an fpqc covering.**  Let `L : Q' ⟶ Y ×_X Q` be induced by `a : Q' ⟶ Y` and
`g : Q' ⟶ Q`; if its base change along `W_p ×_Q (Y ×_X Q) ⟶ Y ×_X Q` is invertible for an fpqc
covering `W_p ⟶ Q`, then so is `L`. -/
private theorem isIso_pullbackLift_of_isFpqcCovering {Y : AlgebraicSpaces B S hS} (h : Y ⟶ X)
    (q : Q ⟶ X) (g : Q' ⟶ Q) (a : Q' ⟶ Y) (ha : a.hom ≫ h.hom = g.hom ≫ q.hom) {ι : Type u}
    {Wsp : ι → AlgebraicSpaces B S hS} (wι : ∀ p, Wsp p ⟶ Q)
    (hcovW : IsFpqcCovering B S hS (fun p => (wι p).hom))
    (hloc : ∀ p, IsIso (pullback.snd (pullback.lift a.hom g.hom ha)
      (pullback.snd (wι p).hom (pullback.snd h.hom q.hom)))) :
    IsIso (pullback.lift a.hom g.hom ha : Q'.1 ⟶ pullback h.hom q.hom) := by
  let P' := AlgebraicSpaces.fiberProduct B S hS h q
  let sndP : P' ⟶ Q := ObjectProperty.homMk (pullback.snd h.hom q.hom)
  let L : Q' ⟶ P' := ObjectProperty.homMk (pullback.lift a.hom g.hom ha)
  let Pi : ι → AlgebraicSpaces B S hS := fun p => AlgebraicSpaces.fiberProduct B S hS (wι p) sndP
  let qi : ∀ p, Pi p ⟶ P' := fun p => ObjectProperty.homMk (pullback.snd (wι p).hom sndP.hom)
  let K := Topology.precoverage.{u, u} .fpqc B S hS
  let 𝒰 : K.ZeroHypercover P' :=
    { I₀ := ι
      X := Pi
      f := qi
      mem₀ := ⟨ι, Pi, qi, rfl, P'.property, fun p => (Pi p).property,
        isFpqcCovering_pullback B S hS wι sndP hcovW⟩ }
  have hL : IsIso L := by
    have : (MorphismProperty.isomorphisms (AlgebraicSpaces B S hS)).IsLocalAtTarget K :=
      isomorphisms_isLocalAtTarget_fpqc B S hS
    apply MorphismProperty.IsLocalAtTarget.of_zeroHypercover
      (P := MorphismProperty.isomorphisms (AlgebraicSpaces B S hS)) 𝒰
    intro p
    have hp := AlgebraicSpaces.isPullback_fiberProduct B S hS L (qi p)
    let hpSnd : AlgebraicSpaces.fiberProduct B S hS L (qi p) ⟶ Pi p :=
      ObjectProperty.homMk (pullback.snd L.hom (qi p).hom)
    have hfp : IsIso hpSnd := by
      have : IsIso ((ObjectProperty.ι _).map hpSnd) := hloc p
      exact isIso_of_reflects_iso hpSnd (ObjectProperty.ι _)
    have : IsIso (hp.isoPullback.hom ≫ pullback.snd L (qi p)) := by
      rwa [hp.isoPullback_hom_snd]
    exact IsIso.of_isIso_comp_left hp.isoPullback.hom (pullback.snd L (qi p))
  exact Functor.map_isIso (ObjectProperty.ι _) L

/-- **A morphism to a base change of an affine scheme, recognised on affine étale charts.**  If
over every affine étale chart `W` of `Q` the map `Γ(W) ⊗_{Γ(Z₀)} Γ(T) ⟶ Γ(W ×_Q Q')`,
`w ⊗ t ↦ w · a^*(t)`, is bijective, then `Q' ⟶ T ×_X Q` is an isomorphism. -/
theorem isIso_pullbackLift_of_bijective_tensor (q : Q ⟶ X) (g : Q' ⟶ Q)
    (hg : IsAffineHom B S hS g.hom) (Z₀ : SmallEtale B S hS X.1) [IsIso Z₀.1.hom]
    [IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀)]
    {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (τ : T ⟶ (SmallEtale.toOver B S hS X.1).obj Z₀) (a : Q' ⟶ schemeSpace T)
    (ha : a.hom ≫ yoneda.map τ ≫ Z₀.1.hom = g.hom ≫ q.hom)
    (hμ : ∀ (W : SmallEtale B S hS Q.1)
      (_ : IsAffine ((SmallEtale.toOver B S hS Q.1 ⋙ BigFppfOver.toScheme B S hS).obj W)),
      letI : Algebra (chartRing B S hS X.1 X.2 Z₀)
          (chartRing B S hS Q.1 Q.2 W) :=
        chartDiagramAlgebra B S hS q (isoChartDiagram B S hS q Z₀ W)
      letI : Algebra (chartRing B S hS X.1 X.2 Z₀)
          Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op).hom.toAlgebra
      ∃ e : TensorProduct (chartRing B S hS X.1 X.2 Z₀)
          (chartRing B S hS Q.1 Q.2 W) Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) ≃+
          chartRing B S hS Q'.1 Q'.2
            ((smallBaseChange B S hS g (relativelyRepresentable_of_isAffineHom B S hS g hg)).obj W),
        ∀ w t, e (w ⊗ₜ t) =
          (show (structureSheaf B S hS Q'.1 Q'.2).obj.obj
              (op ((smallBaseChange B S hS g
                (relativelyRepresentable_of_isAffineHom B S hS g hg)).obj W)) from
            chartDiagramRestrict B S hS g
              (smallBaseChangeDiagram g (relativelyRepresentable_of_isAffineHom B S hS g hg) W) w) *
            (show (structureSheaf B S hS Q'.1 Q'.2).obj.obj
                (op ((smallBaseChange B S hS g
                  (relativelyRepresentable_of_isAffineHom B S hS g hg)).obj W)) from
              (pullbackToGlobalFunctions B S hS Q' T a t).1
                (op ((smallBaseChange B S hS g
                  (relativelyRepresentable_of_isAffineHom B S hS g hg)).obj W)))) :
    IsIso (pullback.lift a.hom g.hom ha : Q'.1 ⟶ pullback (yoneda.map τ ≫ Z₀.1.hom) q.hom) := by
  let hrep := relativelyRepresentable_of_isAffineHom B S hS g hg
  let h₀ : yoneda.obj T ⟶ X.1 := yoneda.map τ ≫ Z₀.1.hom
  obtain ⟨U, f, hfs, hfe⟩ := Q.property.exists_atlas
  obtain ⟨I, V, π, hVaff, hVcov⟩ := exists_affine_isEtaleCovering_yoneda B S hS U
  have hcomp := isFppfCovering_comp B S hS PUnit.{u + 1} (fun _ => I) (fun _ => yoneda.obj U)
    (fun _ i => yoneda.obj (V i)) (fun _ => f) (fun _ i => yoneda.map (π i))
    (isFppfCovering_atlas B S hS Q.property hfs hfe)
    (fun _ => isFppfCovering_of_isEtaleCovering B S hS hVcov)
  have hπ : ∀ i, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (π i) := fun i =>
    (presheaf_yoneda_map_etale_iff B S hS (π i)).1
      ((isEtale_iff_presheaf_of_yoneda B S hS _).1 (hVcov.etale i))
  let Wc : (Σ _ : PUnit.{u + 1}, I) → SmallEtale B S hS Q.1 := fun p =>
    chartFromEtaleHom B S hS Q (V p.2) (yoneda.map (π p.2) ≫ f)
      (chart_preimage_etale B S hS Q f hfe (π p.2) (hπ p.2))
  let wι : ∀ p : (Σ _ : PUnit.{u + 1}, I), representedAlgebraicSpace B S hS (V p.2) ⟶ Q :=
    fun p => ObjectProperty.homMk (Wc p).1.hom
  exact isIso_pullbackLift_of_isFpqcCovering B S hS (Y := schemeSpace T) (ObjectProperty.homMk h₀)
    q g a ha wι (isFpqcCovering_of_isFppfCovering B S hS _ _ hcomp) fun p =>
    isIso_pullback_snd_lift_of_isPullback h₀ q.hom g.hom a.hom ha (Wc p).1.hom
      ((smallBaseChange B S hS g hrep).obj (Wc p)).1.hom
      (yoneda.map (hrep.snd (Wc p).1.hom)) (hrep.isPullback (Wc p).1.hom)
      (isPullback_baseChangeChart_of_bijective_tensor B S hS q g hg Z₀ τ a ha hμ (Wc p)
        (hVaff p.2))

end AlgebraicGeometry.Space
