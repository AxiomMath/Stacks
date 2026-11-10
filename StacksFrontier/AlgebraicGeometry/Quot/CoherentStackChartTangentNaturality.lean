module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackChartTangentIdentification

/-!
# Naturality of the tangent identification over a chart, from the pullback of differences

Let `x = (Spec A, ℱ)` be an object of `Coh_{X/B}` over a chart, with `Y` final and `X → B` flat,
and `f : M ⟶ N` a map of modules. A tangent vector at `M` is a class of lifts of `x` to `A[M]`,
and its image under `f` is the class of its pullback along `Spec A[N] ⟶ Spec A[M]`
(`Deformation.Artin.TangentFunctorData.liftEquiv_natural`). Reading lifts of `x` as lifts of
`ℱ` (`AlgebraicGeometry.Space.CoherentSituation.fiberLiftClass_naturality`), the tangent
identification `T_x(M) ≃ Ext¹_{X_A}(ℱ, ℱ ⊗ f^*M̃)`
(`AlgebraicGeometry.Space.CoherentSituation.chartTangentEquiv`) is natural in `M` as soon as the
difference from the trivial lift is natural along `Spec A[N] ⟶ Spec A[M]`
(`AlgebraicGeometry.Space.CoherentSituation.TangentLiftDifferencePullback`): the coefficient map
of `Spec A[N] ⟶ Spec A[M]` is `f` on `Ext¹_{X_A}(ℱ, ℱ ⊗ f^*(-)~)`
(`AlgebraicGeometry.Space.CoherentSituation.tangentExtTransport_comp_mk₀`).

This is the naturality of the tangent spaces used in the second proof of Stacks 08WA.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.tangentExtTransport_thickeningLiftDifference_pullback`:
  the transported difference is natural, for any `Ext` structures.
* `AlgebraicGeometry.Space.CoherentSituation.tangentLiftDifference_pullback`.
* `AlgebraicGeometry.Space.CoherentSituation.chartTangentEquiv_map_of_tangentLiftDifferencePullback`
  states that the tangent identification is natural along a map of modules.

## Implementation notes

The `Ext` structures are carried as variables in
`AlgebraicGeometry.Space.CoherentSituation.tangentExtTransport_thickeningLiftDifference_pullback`
and instantiated once. The body of
`AlgebraicGeometry.Space.CoherentSituation.TangentLiftDifferencePullback`, being that of a
definition, carries its nested proofs as auxiliary lemmas whose statements are beta-reduced; they
agree with the spelling of a theorem statement up to beta-reduction and proof irrelevance, which
`with_reducible` checks at once, while the default transparency unfolds the test schemes first
(1.2 million heartbeats).

## References

* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Deformation.ToposThickening

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  (hY : IsTerminal D.Y)
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  {x : CoherentObject D}
  (hx : (coherentCFG D).val.p.obj x = Deformation.Artin.algebraOver A B S hS toS hA)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)] (hflat : IsFlat B S hS D.f.hom)

/-- `AlgebraicGeometry.Space.CoherentSituation.tangentLiftDifference` is the difference from the
trivial lift followed by the transport of `Ext` classes, with the `Ext` structures of its
definition. -/
theorem tangentLiftDifference_eq_trans (M : Deformation.Artin.SiteModule A B) :
    tangentLiftDifference hY hx M hflat =
      haveI := HasExt.standard (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap (D.thickeningTestMap hY x hx
            (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA)
              M)))).toToposHom).obj
            (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O)))
      haveI := HasExt.standard (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space
          (D.thickeningTestScheme hY
            (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M)))).O))
      haveI := HasExt.standard (Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2)
      letI : HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O)) :=
        inferInstanceAs (HasExt.{u + 1} (Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2))
      (thickeningLiftDifference _ (thickeningTestRetraction hY hx M)
        (thickeningTestMap_comp_thickeningTestRetraction hY hx M)
        (D.isFirstOrderThickening_thickeningTestMap hY x hx
          (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))
        (D.isFlat_projection_of_isFlat hflat _)).trans (tangentExtTransport hY hx M) :=
  rfl

section Generic

variable {M N : Deformation.Artin.SiteModule A B} (f : M ⟶ N)
  {hePM : HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap (D.thickeningTestMap hY x hx
        (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M)))).toToposHom).obj
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O)))}
  {heTM : HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space
      (D.thickeningTestScheme hY
        (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M)))).O))}
  {hePN : HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap (D.thickeningTestMap hY x hx
        (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N)))).toToposHom).obj
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O)))}
  {heTN : HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space
      (D.thickeningTestScheme hY
        (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N)))).O))}
  {heX : HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O))}
  {heMod : HasExt.{u + 1} (Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2)}

/-- **The transported difference is natural along `Spec A[N] ⟶ Spec A[M]`**, for any `Ext`
structures, as soon as the difference from the trivial lift is: the coefficient map of
`Spec A[N] ⟶ Spec A[M]` is `f` on `Ext¹_{X_A}(ℱ, ℱ ⊗ f^*(-)~)`
(`AlgebraicGeometry.Space.CoherentSituation.tangentExtTransport_comp_mk₀`). -/
theorem tangentExtTransport_thickeningLiftDifference_pullback
    (c : D.ThickeningLiftClass x (D.thickeningTestMap hY x hx
      (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M)))
    (hc : thickeningLiftDifference _ (thickeningTestRetraction hY hx N)
        (thickeningTestMap_comp_thickeningTestRetraction hY hx N)
        (D.isFirstOrderThickening_thickeningTestMap hY x hx
          (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N))
        (D.isFlat_projection_of_isFlat hflat _)
        (ThickeningLiftClass.pullback (D.thickeningTestSchemeMap hY
            (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
              (hA := hA) f))
          (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY
            (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
              (hA := hA) f)) c) =
      (thickeningLiftDifference _ (thickeningTestRetraction hY hx M)
          (thickeningTestMap_comp_thickeningTestRetraction hY hx M)
          (D.isFirstOrderThickening_thickeningTestMap hY x hx
            (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))
          (D.isFlat_projection_of_isFlat hflat _) c).comp
        (Abelian.Ext.mk₀ (thickeningCoefficientMap
          (D.thickeningTestSchemeMap hY (Deformation.Artin.squareZeroModuleThickeningHom (S := S)
            (hS := hS) (toS := toS) (hA := hA) f))
          (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY
            (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
              (hA := hA) f))
          (D.isFirstOrderThickening_thickeningTestMap hY x hx
            (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))
          (D.isFirstOrderThickening_thickeningTestMap hY x hx
            (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N))))
        (add_zero 1)) :
    tangentExtTransport hY hx N (thickeningLiftDifference _ (thickeningTestRetraction hY hx N)
        (thickeningTestMap_comp_thickeningTestRetraction hY hx N)
        (D.isFirstOrderThickening_thickeningTestMap hY x hx
          (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N))
        (D.isFlat_projection_of_isFlat hflat _)
        (ThickeningLiftClass.pullback (D.thickeningTestSchemeMap hY
            (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
              (hA := hA) f))
          (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY
            (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
              (hA := hA) f)) c)) =
      D.extGroupMap x (D.chartRingEquiv x hx) f.hom 1
        (tangentExtTransport hY hx M (thickeningLiftDifference _ (thickeningTestRetraction hY hx M)
          (thickeningTestMap_comp_thickeningTestRetraction hY hx M)
          (D.isFirstOrderThickening_thickeningTestMap hY x hx
            (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))
          (D.isFlat_projection_of_isFlat hflat _) c)) := by
  rw [hc]
  exact tangentExtTransport_comp_mk₀ hY hx f _

end Generic

/-- **The difference from the trivial lift is natural along `Spec A[N] ⟶ Spec A[M]`**: for a map
`f : M ⟶ N`, the difference of the pullback of a class of lifts across `Spec A ⊂ Spec A[M]` is
the difference of the class followed by the coefficient map of `Spec A[N] ⟶ Spec A[M]`, with the
`Ext` groups of `AlgebraicGeometry.Space.CoherentSituation.tangentLiftDifference`. -/
def TangentLiftDifferencePullback {M N : Deformation.Artin.SiteModule A B} (f : M ⟶ N) : Prop :=
  haveI := HasExt.standard (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap (D.thickeningTestMap hY x hx
        (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M)))).toToposHom).obj
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O)))
  haveI := HasExt.standard (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space
      (D.thickeningTestScheme hY
        (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M)))).O))
  haveI := HasExt.standard (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap (D.thickeningTestMap hY x hx
        (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N)))).toToposHom).obj
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O)))
  haveI := HasExt.standard (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space
      (D.thickeningTestScheme hY
        (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N)))).O))
  haveI := HasExt.standard (Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2)
  letI : HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O)) :=
    inferInstanceAs (HasExt.{u + 1} (Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2))
  ∀ c : D.ThickeningLiftClass x (D.thickeningTestMap hY x hx
      (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M)),
    thickeningLiftDifference _ (thickeningTestRetraction hY hx N)
        (thickeningTestMap_comp_thickeningTestRetraction hY hx N)
        (D.isFirstOrderThickening_thickeningTestMap hY x hx
          (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N))
        (D.isFlat_projection_of_isFlat hflat _)
        (ThickeningLiftClass.pullback (D.thickeningTestSchemeMap hY
            (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
              (hA := hA) f))
          (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY
            (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
              (hA := hA) f)) c) =
      (thickeningLiftDifference _ (thickeningTestRetraction hY hx M)
          (thickeningTestMap_comp_thickeningTestRetraction hY hx M)
          (D.isFirstOrderThickening_thickeningTestMap hY x hx
            (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))
          (D.isFlat_projection_of_isFlat hflat _) c).comp
        (Abelian.Ext.mk₀ (thickeningCoefficientMap
          (D.thickeningTestSchemeMap hY (Deformation.Artin.squareZeroModuleThickeningHom (S := S)
            (hS := hS) (toS := toS) (hA := hA) f))
          (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY
            (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
              (hA := hA) f))
          (D.isFirstOrderThickening_thickeningTestMap hY x hx
            (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))
          (D.isFirstOrderThickening_thickeningTestMap hY x hx
            (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N))))
        (add_zero 1)

/-- **The tangent difference is natural along `Spec A[N] ⟶ Spec A[M]`** as soon as the
difference from the trivial lift is. -/
theorem tangentLiftDifference_pullback {M N : Deformation.Artin.SiteModule A B} (f : M ⟶ N)
    (hdiff : TangentLiftDifferencePullback hY hx hflat f)
    (c : D.ThickeningLiftClass x (D.thickeningTestMap hY x hx
      (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))) :
    tangentLiftDifference hY hx N hflat
        (ThickeningLiftClass.pullback (D.thickeningTestSchemeMap hY
            (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
              (hA := hA) f))
          (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY
            (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
              (hA := hA) f)) c) =
      D.extGroupMap x (D.chartRingEquiv x hx) f.hom 1 (tangentLiftDifference hY hx M hflat c) := by
  rw [tangentLiftDifference_eq_trans, tangentLiftDifference_eq_trans, Equiv.trans_apply,
    Equiv.trans_apply]
  delta TangentLiftDifferencePullback at hdiff
  have h := tangentExtTransport_thickeningLiftDifference_pullback hY hx hflat f
    (heMod := (HasExt.standard _ : HasExt.{u + 1} (Modules.{u, u} B S hS (D.space x.T).1
      (D.space x.T).2))) c (by with_reducible exact hdiff c)
  with_reducible exact h

variable (hRS : Deformation.Artin.SatisfiesRSStar B S hS (coherentCFG D).val.p (coherentCFG D).2)

/-- **The tangent identification is natural along a map of modules**, given the naturality of the
difference from the trivial lift along `Spec A[N] ⟶ Spec A[M]`: the image of a tangent vector
under `f : M ⟶ N` goes to its class in `Ext¹_{X_A}(ℱ, ℱ ⊗ f^*M̃)` followed by `f`. -/
theorem chartTangentEquiv_map_of_tangentLiftDifferencePullback
    {M N : Deformation.Artin.SiteModule A B}
    (f : M ⟶ N) (hdiff : TangentLiftDifferencePullback hY hx hflat f)
    (t : (Deformation.Artin.tangentFunctor A B S hS toS hA (coherentCFG D).val.p x hx
      (coherentCFG D).2 hRS).functor.obj M) :
    chartTangentEquiv hY hx N hflat hRS
        ((Deformation.Artin.tangentFunctor A B S hS toS hA (coherentCFG D).val.p x hx
          (coherentCFG D).2 hRS).functor.map f t) =
      D.extGroupMap x (D.chartRingEquiv x hx) f.hom 1 (chartTangentEquiv hY hx M hflat hRS t) := by
  obtain ⟨a', b', ha, hb, φ, hφ, hw⟩ := (Deformation.Artin.tangentFunctor A B S hS toS hA
    (coherentCFG D).val.p x hx (coherentCFG D).2 hRS).liftEquiv_natural f t
  have hg : (eqToHom hx ≫ Deformation.Artin.squareZeroArrow A B S hS toS hA N) ≫
      Deformation.Artin.squareZeroOverMap A B S hS toS f =
        eqToHom hx ≫ Deformation.Artin.squareZeroArrow A B S hS toS hA M := by
    rw [Category.assoc, Deformation.Artin.squareZeroArrow_naturality]
  have hnat := fiberLiftClass_naturality hY (Deformation.Artin.squareZeroOverMap A B S hS toS f)
    hg a' b' φ hφ.toIsHomLift hw
  rw [chartTangentEquiv, chartTangentEquiv]
  simp only [Equiv.trans_apply]
  rw [← ha, ← hb]
  change tangentLiftDifference hY hx N hflat (D.fiberLiftClass hY (Quotient.mk _ b')) =
    D.extGroupMap x (D.chartRingEquiv x hx) f.hom 1
      (tangentLiftDifference hY hx M hflat (D.fiberLiftClass hY (Quotient.mk _ a')))
  exact (congrArg (tangentLiftDifference hY hx N hflat) hnat).trans
    (tangentLiftDifference_pullback hY hx hflat f hdiff _)

end AlgebraicGeometry.Space.CoherentSituation

end
