module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceAffinePushforward
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceRepresentedAffinePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback

/-!
# Weakly associated points of an affine direct image over an affine scheme of the site

Let `g : X ⟶ Y` be an affine morphism of algebraic spaces whose target is the algebraic space of
an affine scheme of the big fppf site, and let `H` be a quasi-coherent `𝒪_X`-module. The weakly
associated points of `g_*H` are contained in the images of those of `H`, and the two sets are
equal when `X` is locally Noetherian.

## Main results

* `AlgebraicGeometry.Space.schemeTargetAffinePushforwardWeaklyAssociatedImage`: the
  affine-scheme-target case of Stacks 0CU2.
* `AlgebraicGeometry.Space.weaklyAssociatedPoints_modulePushforward_subset_image_of_isAffineHom`:
  **Stacks 0CU2** for an arbitrary target.
* `AlgebraicGeometry.Space.weaklyAssociatedPoints_modulePushforward_schemeTargetAffine_eq_image`:
  the affine-scheme-target case of the equality, for a locally Noetherian source.

## References

* [Stacks Project, Tag 0CU2](https://stacks.math.columbia.edu/tag/0CU2)
* [Stacks Project, Tag 0CUU](https://stacks.math.columbia.edu/tag/0CUU)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
* [Stacks Project, Tag 05EX](https://stacks.math.columbia.edu/tag/05EX)
* [Stacks Project, Tag 05EY](https://stacks.math.columbia.edu/tag/05EY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The representation of the source of an affine morphism over an affine scheme of the
site**, with the weakly associated points of both sides of the statement transported to it: an
object `W` of the site, a morphism `q : W ⟶ V` with affine underlying morphism of schemes, an
isomorphism `X ≅ yoneda.obj W` and a quasi-coherent module `F` on `W`, such that the weakly
associated points of `g_*H` are those of `q_*F` and the images of those of `H` are the images of
those of `F`. -/
private theorem exists_representedSpaceMap_weaklyAssociatedPoints_transport
    (V : BigFppfOver B S hS) {X : AlgebraicSpaces B S hS} (g : X ⟶ schemeSpace V)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hg : IsAffineHom B S hS g.hom)
    (H : Modules.{u, u} B S hS X.1 X.2) (hH : H.IsQuasicoherentOnSite) :
    ∃ (W : BigFppfOver B S hS) (q : W ⟶ V)
      (F : Modules.{u, u} B S hS (yoneda.obj W)
        (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W)),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map q) ∧
        F.IsQuasicoherentOnSite ∧
        Nonempty (X.1 ≅ yoneda.obj W) ∧
        weaklyAssociatedPoints B S hS (schemeSpace V)
            ((modulePushforward B S hS g).obj H) =
          weaklyAssociatedPoints B S hS
            ⟨yoneda.obj V, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩
            ((modulePushforward B S hS (representedSpaceMap B S hS q)).obj F) ∧
        pointsMap B S hS X.1 g.hom '' weaklyAssociatedPoints B S hS X H =
          pointsMap B S hS (yoneda.obj W) (yoneda.map q) ''
            weaklyAssociatedPoints B S hS
              ⟨yoneda.obj W, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W⟩ F := by
  obtain ⟨W₀, p, q₀, sq₀⟩ := hg ⟨V, hV⟩ (𝟙 (schemeSpace V).obj)
  let W' : BigFppfOver B S hS := (BigAffineFppf.inclusion B S hS).obj W₀
  let q : W' ⟶ V := q₀
  have sq : IsPullback p (yoneda.map q) g.hom (𝟙 (schemeSpace V).obj) := sq₀
  have hW' : IsAffine ((BigFppfOver.toScheme B S hS).obj W') := W₀.property
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := hV
  have sq2 : IsPullback (𝟙 X.obj) g.hom g.hom (𝟙 (schemeSpace V).obj) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨e, hesnd⟩ : ∃ e : yoneda.obj W' ≅ X.1, e.hom ≫ g.hom = yoneda.map q :=
    ⟨sq.isoIsPullback _ _ sq2, sq.isoIsPullback_hom_snd _ _ sq2⟩
  let ψ : (⟨yoneda.obj W', _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W'⟩ :
      AlgebraicSpaces B S hS) ⟶ X := ObjectProperty.homMk e.hom
  have : IsIso ψ := (ObjectProperty.isIso_hom_iff ψ).1 (inferInstanceAs (IsIso e.hom))
  let fV : X ⟶ (⟨yoneda.obj V, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩ :
      AlgebraicSpaces B S hS) := ObjectProperty.homMk g.hom
  let g0 : (⟨yoneda.obj V, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩ :
      AlgebraicSpaces B S hS) ⟶
      ⟨yoneda.obj V, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩ :=
    ObjectProperty.homMk (𝟙 (yoneda.obj V))
  have : IsIso g0 := (ObjectProperty.isIso_hom_iff g0).1
    (inferInstanceAs (IsIso (𝟙 (yoneda.obj V))))
  have hid : IsEtale B S hS g0.hom :=
    (fun _ _ hφ => by simpa using hφ : IsEtale B S hS (𝟙 (yoneda.obj V)))
  have sqS : IsPullback ψ (representedSpaceMap B S hS q) fV g0 :=
    IsPullback.of_horiz_isIso
      ⟨ObjectProperty.hom_ext _ (hesnd.trans (Category.comp_id _).symm)⟩
  have hψEt : IsEtale B S hS ψ.hom :=
    isEtale_of_isPullback B S hS (representedSpaceMap B S hS q) ψ g0 fV sqS.flip hid
  refine ⟨W', q, (etaleModulePullback B S hS ψ hψEt).obj H, inferInstance,
    isQuasicoherentOnSite_etaleModulePullback B S hS ψ hψEt H hH, ⟨e.symm⟩, ?_, ?_⟩
  · refine Set.ext fun t => ?_
    have hpid : pointsMap B S hS (yoneda.obj V) g0.hom t = t :=
      congrFun (pointsMap_id B S hS (yoneda.obj V)) t
    have step1 := isWeaklyAssociatedPoint_etaleModulePullback_iff B S hS g0 hid
      ((modulePushforward B S hS fV).obj H) t
    rw [hpid] at step1
    exact step1.symm.trans (isWeaklyAssociatedPoint_congr B S hS
      ((modulePushforwardEtaleBaseChangeIso B S hS ψ (representedSpaceMap B S hS q) fV
        g0 sqS hid).app H) t).symm
  · have hψpoint : ∀ w : points B S hS (yoneda.obj W'),
        pointsMap B S hS X.1 g.hom (pointsMap B S hS (yoneda.obj W') ψ.hom w) =
          pointsMap B S hS (yoneda.obj W') (yoneda.map q) w := fun w => by
      rw [← pointsMap_comp_apply]
      exact congrArg (fun k => pointsMap B S hS (yoneda.obj W') k w) hesnd
    have hinv : ∀ x : points B S hS X.1,
        pointsMap B S hS (yoneda.obj W') ψ.hom (pointsMap B S hS X.1 e.inv x) = x := fun x => by
      show pointsMap B S hS (yoneda.obj W') e.hom (pointsMap B S hS X.1 e.inv x) = x
      rw [← pointsMap_comp_apply, e.inv_hom_id, pointsMap_id, id_eq]
    refine Set.ext fun t => ⟨?_, ?_⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨pointsMap B S hS X.1 e.inv x, ?_, ?_⟩
      · exact (isWeaklyAssociatedPoint_etaleModulePullback_iff B S hS ψ hψEt H _).2
          ((hinv x).symm ▸ hx)
      · rw [← hψpoint, hinv x]
    · rintro ⟨w, hw, rfl⟩
      exact ⟨pointsMap B S hS (yoneda.obj W') ψ.hom w,
        (isWeaklyAssociatedPoint_etaleModulePullback_iff B S hS ψ hψEt H w).1 hw,
        hψpoint w⟩

/-- **The affine-scheme-target case of Stacks 0CU2.** For an affine morphism `g` of algebraic
spaces whose target is an affine scheme of the site and a quasi-coherent `𝒪_X`-module `H`, every
weakly associated point of `g_*H` is the image of a weakly associated point of `H`. -/
theorem schemeTargetAffinePushforwardWeaklyAssociatedImage :
    SchemeTargetAffinePushforwardWeaklyAssociatedImage B S hS := by
  intro V X g hV hg H hH
  obtain ⟨W, q, F, hq, hF, -, hleft, hright⟩ :=
    exists_representedSpaceMap_weaklyAssociatedPoints_transport B S hS V g hV hg H hH
  rw [hleft, hright]
  exact weaklyAssociatedPoints_modulePushforward_representedSpaceMap_subset_image_of_isAffineHom
    B S hS q hq F hF

/-- Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over `S` and let `F` be a
quasi-coherent `𝒪_X`-module. Then every weakly associated point of `f_*F` is the image of a
weakly associated point of `F`. -/
@[stacks 0CU2]
theorem weaklyAssociatedPoints_modulePushforward_subset_image_of_isAffineHom
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    weaklyAssociatedPoints B S hS Y ((modulePushforward B S hS f).obj F) ⊆
      pointsMap B S hS X.1 f.hom '' weaklyAssociatedPoints B S hS X F :=
  affinePushforwardWeaklyAssociatedImage B S hS
    (schemeTargetAffinePushforwardWeaklyAssociatedImage B S hS) f hf F hF

/-- **The affine-scheme-target case of Stacks 0CU8.** For an affine morphism `g` of algebraic
spaces whose target is an affine scheme of the site, with `X` locally Noetherian, and a
quasi-coherent `𝒪_X`-module `H`, the weakly associated points of `g_*H` are exactly the images
of those of `H`. -/
theorem weaklyAssociatedPoints_modulePushforward_schemeTargetAffine_eq_image
    (V : BigFppfOver B S hS) {X : AlgebraicSpaces B S hS} (g : X ⟶ schemeSpace V)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hg : IsAffineHom B S hS g.hom)
    (hX : HasEtaleLocalProperty B S hS X.1
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian T))
    (H : Modules.{u, u} B S hS X.1 X.2) (hH : H.IsQuasicoherentOnSite) :
    weaklyAssociatedPoints B S hS (schemeSpace V) ((modulePushforward B S hS g).obj H) =
      pointsMap B S hS X.1 g.hom '' weaklyAssociatedPoints B S hS X H := by
  obtain ⟨W, q, F, hq, hF, ⟨e⟩, hleft, hright⟩ :=
    exists_representedSpaceMap_weaklyAssociatedPoints_transport B S hS V g hV hg H hH
  have hW : _root_.AlgebraicGeometry.IsLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).obj W) :=
    (exists_atlas_iff_of_representable B S hS X.1
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian T) W e).1 hX
  rw [hleft, hright]
  exact weaklyAssociatedPoints_modulePushforward_representedSpaceMap_eq_image_of_isAffineHom
    B S hS q hq hW F hF

end AlgebraicGeometry.Space

end
