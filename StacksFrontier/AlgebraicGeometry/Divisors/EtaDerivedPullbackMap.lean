module

public import StacksFrontier.AlgebraicGeometry.Divisors.EtaDerivedPullbackComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffinePullbackComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatIdealTorsionFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IdealGeneratedByNonzerodivisor
public import StacksFrontier.Topology.Sheaves.Modules.TensorAndDuals.FlatPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.KFlatResolvingDatum
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaDerivedPullbackCore
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaGoodBaseChange.Comparison
public import StacksCore.Tactic.StacksAttribute

/-!
# The comparison of derived décalage with an arbitrary derived pullback

Let `h : Y ⟶ X` be a morphism of schemes, let `D ⊆ X` be an effective Cartier divisor with ideal
sheaf `I = ℐ_D` and suppose the pullback `E = h^{-1}D` is defined, with ideal sheaf `J = ℐ_E`.
This file constructs the canonical comparison

`φ : Lh^*(Lη_I M) ⟶ Lη_J(Lh^* M)`

in `D(𝒪_Y)`, with no flatness hypothesis on `h`, at an object `M = [G^•]` of `D(𝒪_X)` presented
by a K-flat complex `G^•` of `I`-torsion-free `𝒪_X`-modules whose termwise pullback is
`h^*I`-torsion-free. It is the composite of

* `Lh^*` applied to the identification `Lη_I [G^•] ≅ [η_I G^•]` of Stacks 0F8Q;
* the canonical comparison `Lh^*[η_I G^•] ⟶ [h^*η_I G^•]` of the left derived pullback with the
  termwise pullback (Stacks 06YJ);
* the chain-level comparison `h^*(η_I G^•) ⟶ η_{h^*I}(h^* G^•)`, which needs no flatness;
* the identification `[η_{h^*I}(h^*G^•)] ≅ Lη_{h^*I}[h^*G^•]` of Stacks 0F8Q and the transport of
  `Lη_{h^*I}` to `Lη_J` along `h^*ℐ_D ≅ ℐ_E`;
* `Lη_J` applied to `[h^*G^•] ≅ Lh^*[G^•]`, the inverse of the comparison of Stacks 06YJ, which
  is invertible because `G^•` is K-flat.

When `h` is flat, the comparison `Stacks.Divisors.Eta.derivedEtaPullbackComparison` is an
isomorphism. Stacks 0F9X asserts that `Lh^*(Lη_I M) ≅ Lη_J(Lh^* M)` when `(X, D, M)` is a good
triple, for an arbitrary `h`; that is
`AlgebraicGeometry.ComplexAndDivisorSituation.nonempty_derivedPullback_derivedEta_iso`.

## Main definitions

* `Stacks.Divisors.Eta.derivedEtaPullbackMap` — the comparison `φ`.

## Main results

* `Stacks.Divisors.Eta.hasTorsionFreeResolutions_pullbackIdealIncl_of_isPullbackDefined` — termwise
  `h^*ℐ_D`-torsion-free resolutions exist, the inclusion `h^*ℐ_D ⟶ 𝒪_Y` being a monomorphism with
  no flatness (`Stacks.Divisors.Eta.mono_pullbackIdealIncl_of_isPullbackDefined`).
* `Stacks.Divisors.Eta.isIdealTorsionFree_pullback_of_isFlat` — the pullback of a flat module is
  `h^*ℐ_D`-torsion-free, which supplies the hypothesis on the termwise pullback.
* `Stacks.Divisors.Eta.exists_kFlat_torsionFreeComplex_iso` — every object of `D(𝒪_X)` is
  presented by a K-flat complex of flat, hence `ℐ_D`-torsion-free, modules; so the comparison is
  available at every object.

## References

* [Stacks Project, Tag 0F9X](https://stacks.math.columbia.edu/tag/0F9X)
* [Stacks Project, Tag 0F8Q](https://stacks.math.columbia.edu/tag/0F8Q)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 06YF](https://stacks.math.columbia.edu/tag/06YF)
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf
  Stacks.SheafOfModules.Tensor.ringSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.RingedSpace (pullbackFunctor)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Divisors.Eta

variable {X Y : Scheme.{u}} (h : Y ⟶ X) (D : X.IdealSheafData)
  [Stacks.Divisors.IsEffectiveCartierDivisor D]

/-- **Termwise `h^*ℐ_D`-torsion-free resolutions exist when `h^{-1}D` is defined.** The pullback
of an invertible sheaf is invertible and `h^*ℐ_D ⟶ 𝒪_Y` is a monomorphism, so
`Stacks.IdealTorsion.Eta.hasTorsionFreeResolutions_of_isInvertible` applies. -/
theorem hasTorsionFreeResolutions_pullbackIdealIncl_of_isPullbackDefined
    (hD : Stacks.Divisors.IsPullbackDefined h D) :
    Stacks.IdealTorsion.Eta.HasTorsionFreeResolutions Y.toRingedSpace
      (Stacks.IdealTorsion.Eta.pullbackIdealIncl h.toLRSHom.toShHom (idealSheaf D)
        (idealSheafι D)) :=
  Stacks.IdealTorsion.Eta.hasTorsionFreeResolutions_of_isInvertible Y.toRingedSpace _ _
    (mono_pullbackIdealIncl_of_isPullbackDefined h D hD)
    (Stacks.IdealTorsion.Eta.isInvertible_pullbackIdeal h.toLRSHom.toShHom (idealSheaf D))

/-- **The pullback of a flat module is `h^*ℐ_D`-torsion-free when `h^{-1}D` is defined.** The
pullback of a flat module is flat (Stacks 0H97), the ideal `h^*ℐ_D ⊆ 𝒪_Y` is invertible, hence
locally generated by a nonzerodivisor, and a flat module has no torsion for such an ideal. -/
theorem isIdealTorsionFree_pullback_of_isFlat (hD : Stacks.Divisors.IsPullbackDefined h D)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.toRingedSpace.sheaf) F) :
    Stacks.IdealTorsion.IsIdealTorsionFree Y.toRingedSpace
      (Stacks.IdealTorsion.Eta.pullbackIdealIncl h.toLRSHom.toShHom (idealSheaf D)
        (idealSheafι D)) ((pullbackFunctor h.toLRSHom.toShHom).obj F) :=
  isIdealTorsionFree_pullbackIdealIncl_of_isFlat h D hD F hF

/-- **Every object of `D(𝒪_X)` is presented by a K-flat complex of flat modules, and such a
complex consists of `ℐ_D`-torsion-free modules.** The K-flat resolution is Stacks 06YF; flat
modules have no torsion for the invertible ideal `ℐ_D`. This is the presentation the comparison
`Stacks.Divisors.Eta.derivedEtaPullbackMap` is written at. -/
theorem exists_kFlat_torsionFreeComplex_iso
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    ∃ K : CochainComplex
      (Stacks.IdealTorsion.Eta.TorsionFreeModule X.toRingedSpace (idealSheafι D)) ℤ,
      Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex X.toRingedSpace
        ((Stacks.IdealTorsion.Eta.torsionFreeComplex X.toRingedSpace (idealSheafι D)).obj K) ∧
      (∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
        (O := X.toRingedSpace.sheaf)
        (((Stacks.IdealTorsion.Eta.torsionFreeComplex X.toRingedSpace (idealSheafι D)).obj K).X
          n)) ∧
      Nonempty (DerivedCategory.Q.obj
        ((Stacks.IdealTorsion.Eta.torsionFreeComplex X.toRingedSpace (idealSheafι D)).obj K) ≅
          M) := by
  obtain ⟨P, g, hKF, hfl, hq, -⟩ :=
    Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution X.toRingedSpace
      (DerivedCategory.Q.objPreimage M)
  have htf : ∀ n : ℤ, Stacks.IdealTorsion.IsIdealTorsionFree X.toRingedSpace (idealSheafι D)
      (P.X n) := fun n =>
    isIdealTorsionFree_of_isFlat_divisor D _ (hfl n)
  refine ⟨HomologicalComplex.liftObjectProperty
    (Stacks.IdealTorsion.Eta.torsionFreeProperty X.toRingedSpace (idealSheafι D)) P htf,
    hKF, hfl, ⟨?_⟩⟩
  exact @asIso _ _ _ _ (DerivedCategory.Q.map g)
      ((DerivedCategory.isIso_Q_map_iff_quasiIso _ g).2 hq) ≪≫
    DerivedCategory.Q.objObjPreimageIso M

/-! ### The comparison -/

section Comparison

variable [hD : Stacks.Divisors.IsPullbackDefined h D]

/-- The degreewise pullback of a complex `G^•` of `ℐ_D`-torsion-free modules, regarded as a
complex of `h^*ℐ_D`-torsion-free modules once its terms are known to be. -/
abbrev pullbackTorsionFreeComplex
    (K : CochainComplex
      (Stacks.IdealTorsion.Eta.TorsionFreeModule X.toRingedSpace (idealSheafι D)) ℤ)
    (hK : ∀ n : ℤ, Stacks.IdealTorsion.IsIdealTorsionFree Y.toRingedSpace
      (Stacks.IdealTorsion.Eta.pullbackIdealIncl h.toLRSHom.toShHom (idealSheaf D)
        (idealSheafι D))
      ((Stacks.IdealTorsion.Eta.pullbackComplex h.toLRSHom.toShHom
        ((Stacks.IdealTorsion.Eta.torsionFreeComplex X.toRingedSpace (idealSheafι D)).obj K)).X
          n)) :
    CochainComplex (Stacks.IdealTorsion.Eta.TorsionFreeModule Y.toRingedSpace
      (Stacks.IdealTorsion.Eta.pullbackIdealIncl h.toLRSHom.toShHom (idealSheaf D)
        (idealSheafι D))) ℤ :=
  HomologicalComplex.liftObjectProperty
    (Stacks.IdealTorsion.Eta.torsionFreeProperty Y.toRingedSpace
      (Stacks.IdealTorsion.Eta.pullbackIdealIncl h.toLRSHom.toShHom (idealSheaf D)
        (idealSheafι D)))
    (Stacks.IdealTorsion.Eta.pullbackComplex h.toLRSHom.toShHom
      ((Stacks.IdealTorsion.Eta.torsionFreeComplex X.toRingedSpace (idealSheafι D)).obj K)) hK

/-- **The canonical comparison `φ : Lh^*(Lη_I M) ⟶ Lη_J(Lh^* M)`** for an arbitrary morphism of
schemes `h : Y ⟶ X` along which `D` pulls back to an effective Cartier divisor, at an object
`M = [G^•]` presented by a K-flat complex `G^•` of `ℐ_D`-torsion-free modules whose termwise
pullback is `h^*ℐ_D`-torsion-free. See the module docstring for its five constituents. -/
def derivedEtaPullbackMap
    (K : CochainComplex
      (Stacks.IdealTorsion.Eta.TorsionFreeModule X.toRingedSpace (idealSheafι D)) ℤ)
    (hKF : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex X.toRingedSpace
      ((Stacks.IdealTorsion.Eta.torsionFreeComplex X.toRingedSpace (idealSheafι D)).obj K))
    (hK : ∀ n : ℤ, Stacks.IdealTorsion.IsIdealTorsionFree Y.toRingedSpace
      (Stacks.IdealTorsion.Eta.pullbackIdealIncl h.toLRSHom.toShHom (idealSheaf D)
        (idealSheafι D))
      ((Stacks.IdealTorsion.Eta.pullbackComplex h.toLRSHom.toShHom
        ((Stacks.IdealTorsion.Eta.torsionFreeComplex X.toRingedSpace (idealSheafι D)).obj K)).X
          n)) :
    (derivedPullback h.toLRSHom.toShHom).obj
        ((Stacks.IdealTorsion.Eta.derivedEta X.toRingedSpace (idealSheaf D) (idealSheafι D)
            (hasTorsionFreeResolutions D)).obj
          (DerivedCategory.Q.obj
            ((Stacks.IdealTorsion.Eta.torsionFreeComplex X.toRingedSpace
              (idealSheafι D)).obj K))) ⟶
      (Stacks.IdealTorsion.Eta.derivedEta Y.toRingedSpace (idealSheaf (D.comap h))
          (idealSheafι (D.comap h)) (hasTorsionFreeResolutions (D.comap h))).obj
        ((derivedPullback h.toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj
            ((Stacks.IdealTorsion.Eta.torsionFreeComplex X.toRingedSpace
              (idealSheafι D)).obj K))) :=
  haveI := mono_pullbackIdealIncl_of_isPullbackDefined h D hD
  haveI := Stacks.DerivedPullback.isIso_derivedPullbackComplexComparison_app_of_kFlat
    h.toLRSHom.toShHom _ hKF
  (derivedPullback h.toLRSHom.toShHom).map
      ((Stacks.IdealTorsion.Eta.derivedEta_iso X.toRingedSpace (idealSheaf D) (idealSheafι D)
        (hasTorsionFreeResolutions D)).hom.app K) ≫
    Stacks.IdealTorsion.Eta.derivedPullbackEtaCore h.toLRSHom.toShHom (idealSheaf D)
      (idealSheafι D)
      ((Stacks.IdealTorsion.Eta.torsionFreeComplex X.toRingedSpace (idealSheafι D)).obj K)
      (Stacks.IdealTorsion.Eta.torsionFreeComplex_torsionFree X.toRingedSpace (idealSheafι D) K)
      hK ≫
    ((Stacks.IdealTorsion.Eta.derivedEta_iso Y.toRingedSpace
        ((pullbackFunctor h.toLRSHom.toShHom).obj (idealSheaf D))
        (Stacks.IdealTorsion.Eta.pullbackIdealIncl h.toLRSHom.toShHom (idealSheaf D)
          (idealSheafι D))
        (hasTorsionFreeResolutions_pullbackIdealIncl_of_isPullbackDefined h D hD)).inv.app
      (pullbackTorsionFreeComplex h D K hK)) ≫
    (Stacks.IdealTorsion.Eta.IdealCongr.derivedEtaIso Y.toRingedSpace
      ((pullbackFunctor h.toLRSHom.toShHom).obj (idealSheaf D)) (idealSheaf (D.comap h))
      (Stacks.IdealTorsion.Eta.pullbackIdealIncl h.toLRSHom.toShHom (idealSheaf D)
        (idealSheafι D)) (idealSheafι (D.comap h))
      (Stacks.Divisors.pullbackIdealSheafComapIso h D hD)
      (Stacks.Divisors.pullbackIdealSheafComapIso_hom_comp_idealSheafι h D hD)
      (Stacks.IdealTorsion.Eta.pullbackComplex h.toLRSHom.toShHom
        ((Stacks.IdealTorsion.Eta.torsionFreeComplex X.toRingedSpace (idealSheafι D)).obj K)) hK
      (fun n => Stacks.IdealTorsion.Eta.isIdealTorsionFree_of_pullbackIdealIncl
        h.toLRSHom.toShHom (idealSheaf D) (idealSheafι D) (idealSheaf (D.comap h))
        (idealSheafι (D.comap h)) (Stacks.Divisors.pullbackIdealSheafComapIso h D hD)
        (Stacks.Divisors.pullbackIdealSheafComapIso_hom_comp_idealSheafι h D hD) _ (hK n))
      (hasTorsionFreeResolutions_pullbackIdealIncl_of_isPullbackDefined h D hD)
      (hasTorsionFreeResolutions (D.comap h))).hom ≫
    (Stacks.IdealTorsion.Eta.derivedEta Y.toRingedSpace (idealSheaf (D.comap h))
        (idealSheafι (D.comap h)) (hasTorsionFreeResolutions (D.comap h))).map
      (inv ((Stacks.DerivedPullback.derivedPullbackComplexComparison h.toLRSHom.toShHom).app
        ((Stacks.IdealTorsion.Eta.torsionFreeComplex X.toRingedSpace (idealSheafι D)).obj K)))

/-- **The comparison is invertible exactly when its non-formal part is**: all constituents of
`Stacks.Divisors.Eta.derivedEtaPullbackMap` other than
`Stacks.IdealTorsion.Eta.derivedPullbackEtaCore` are isomorphisms. -/
theorem isIso_derivedEtaPullbackMap_iff
    (K : CochainComplex
      (Stacks.IdealTorsion.Eta.TorsionFreeModule X.toRingedSpace (idealSheafι D)) ℤ)
    (hKF : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex X.toRingedSpace
      ((Stacks.IdealTorsion.Eta.torsionFreeComplex X.toRingedSpace (idealSheafι D)).obj K))
    (hK : ∀ n : ℤ, Stacks.IdealTorsion.IsIdealTorsionFree Y.toRingedSpace
      (Stacks.IdealTorsion.Eta.pullbackIdealIncl h.toLRSHom.toShHom (idealSheaf D)
        (idealSheafι D))
      ((Stacks.IdealTorsion.Eta.pullbackComplex h.toLRSHom.toShHom
        ((Stacks.IdealTorsion.Eta.torsionFreeComplex X.toRingedSpace (idealSheafι D)).obj K)).X
          n)) :
    haveI := mono_pullbackIdealIncl_of_isPullbackDefined h D hD
    IsIso (derivedEtaPullbackMap h D K hKF hK) ↔
      IsIso (Stacks.IdealTorsion.Eta.derivedPullbackEtaCore h.toLRSHom.toShHom (idealSheaf D)
        (idealSheafι D)
        ((Stacks.IdealTorsion.Eta.torsionFreeComplex X.toRingedSpace (idealSheafι D)).obj K)
        (Stacks.IdealTorsion.Eta.torsionFreeComplex_torsionFree X.toRingedSpace (idealSheafι D) K)
        hK) := by
  have := mono_pullbackIdealIncl_of_isPullbackDefined h D hD
  have := Stacks.DerivedPullback.isIso_derivedPullbackComplexComparison_app_of_kFlat
    h.toLRSHom.toShHom _ hKF
  unfold derivedEtaPullbackMap
  refine (@isIso_comp_left_iff _ _ _ _ _ _ _ ?_).trans (@isIso_comp_right_iff _ _ _ _ _ _ _ ?_)
  · exact Functor.map_isIso _ (Iso.hom ((Stacks.IdealTorsion.Eta.derivedEta_iso X.toRingedSpace
      (idealSheaf D) (idealSheafι D) (hasTorsionFreeResolutions D)).app K))
  · exact IsIso.comp_isIso'
      (Iso.isIso_inv ((Stacks.IdealTorsion.Eta.derivedEta_iso Y.toRingedSpace _ _ _).app _))
      (IsIso.comp_isIso' (Iso.isIso_hom _) (Functor.map_isIso _ _))

end Comparison

end Stacks.Divisors.Eta

end
