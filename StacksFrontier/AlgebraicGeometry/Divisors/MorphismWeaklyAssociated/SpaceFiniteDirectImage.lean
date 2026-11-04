module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceRelativeEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceRepresentedAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceRepresentedFinitePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpBaseChange

/-!
# Weakly associated points of a finite direct image on algebraic spaces

Let `i : Z ⟶ X` be a finite morphism of algebraic spaces over a scheme `S` and let `G` be a
quasi-coherent `𝒪_Z`-module. The weakly associated points of the direct image `i_*G` are the
images of the weakly associated points of `G`, and relatively over a morphism `f : X ⟶ Y` the
relative weak assassin `WeakAss_{X/Y}(i_*G)` is the image of `WeakAss_{Z/Y}(G)`.

## Main definitions

* `AlgebraicGeometry.Space.FiniteAffineTargetWeaklyAssociatedImage`: the statement of
  Stacks 0CU9 for a finite morphism of affine algebraic spaces whose target is an affine scheme of
  the site, as a proposition.

## Main results

* `AlgebraicGeometry.Space.weaklyAssociatedPoints_congr`: isomorphic `𝒪_X`-modules have the
  same weakly associated points.
* `AlgebraicGeometry.Space.finiteAffineTargetWeaklyAssociatedImage`: the
  affine-scheme-target case of Stacks 0CU9.
* `AlgebraicGeometry.Space.weaklyAssociatedPoints_modulePushforward_eq_image_of_isFinite`:
  `WeakAss(f_*F) = f(WeakAss(F))` for a finite morphism `f`.
* `AlgebraicGeometry.Space.relativeWeaklyAssociatedPoints_modulePushforward_eq_image_of_isFinite`:
  `WeakAss_{X/Y}(i_*G) = i(WeakAss_{Z/Y}(G))` for a finite morphism `i`.

## References

* [Stacks Project, Tag 0CU9](https://stacks.math.columbia.edu/tag/0CU9)
* [Stacks Project, Tag 0CV4](https://stacks.math.columbia.edu/tag/0CV4)
* [Stacks Project, Tag 0CUD](https://stacks.math.columbia.edu/tag/0CUD)
* [Stacks Project, Tag 0CUU](https://stacks.math.columbia.edu/tag/0CUU)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 05EZ](https://stacks.math.columbia.edu/tag/05EZ)
* [Stacks Project, Tag 0CTW](https://stacks.math.columbia.edu/tag/0CTW)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Isomorphic `𝒪_X`-modules have the same weakly associated points. -/
theorem weaklyAssociatedPoints_congr {X : AlgebraicSpaces B S hS}
    {F F' : Modules.{u, m} B S hS X.1 X.2} (e : F ≅ F') :
    weaklyAssociatedPoints B S hS X F = weaklyAssociatedPoints B S hS X F' :=
  Set.ext fun x => isWeaklyAssociatedPoint_congr B S hS e x

/-! ### The absolute statement -/

/-- **Stacks 0CU9 for a finite morphism of affine algebraic spaces whose target is an affine
scheme of the site**: for such a morphism `f` and a quasi-coherent `𝒪_X`-module `F`, the weakly
associated points of `f_*F` are the images of those of `F`. -/
def FiniteAffineTargetWeaklyAssociatedImage : Prop :=
  ∀ {X : AlgebraicSpaces B S hS} (V : BigFppfOver B S hS),
    IsAffine ((BigFppfOver.toScheme B S hS).obj V) → IsAffineSpace B S hS X.1 →
      ∀ f : X ⟶ schemeSpace V, IsFinite B S hS f.hom →
        ∀ F : Modules.{u, u} B S hS X.1 X.2, F.IsQuasicoherentOnSite →
          weaklyAssociatedPoints B S hS (schemeSpace V)
              ((modulePushforward B S hS f).obj F) =
            pointsMap B S hS X.1 f.hom '' weaklyAssociatedPoints B S hS X F

/-- **The affine-scheme-target case of Stacks 0CU9.** For a finite morphism `f` of algebraic
spaces whose target is an affine scheme of the site and a quasi-coherent `𝒪_X`-module `F`, the
weakly associated points of `f_*F` are the images of those of `F`. -/
theorem finiteAffineTargetWeaklyAssociatedImage :
    FiniteAffineTargetWeaklyAssociatedImage B S hS := by
  intro X V hV _ f hf F hF
  obtain ⟨W, p, i, -, hp, sq⟩ := hf V hV (𝟙 (schemeSpace V).obj)
  have sq2 : IsPullback (𝟙 X.obj) f.hom f.hom (𝟙 (schemeSpace V).obj) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨e, hesnd⟩ : ∃ e : yoneda.obj W ≅ X.1, e.hom ≫ f.hom = yoneda.map p :=
    ⟨sq.isoIsPullback _ _ sq2, sq.isoIsPullback_hom_snd _ _ sq2⟩
  let ψ : (⟨yoneda.obj W, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W⟩ :
      AlgebraicSpaces B S hS) ⟶ X := ObjectProperty.homMk e.hom
  have : IsIso ψ := (ObjectProperty.isIso_hom_iff ψ).1 (by show IsIso e.hom; infer_instance)
  let fV : X ⟶ (⟨yoneda.obj V, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩ :
      AlgebraicSpaces B S hS) := ObjectProperty.homMk f.hom
  let g0 : (⟨yoneda.obj V, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩ :
      AlgebraicSpaces B S hS) ⟶
      ⟨yoneda.obj V, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩ :=
    ObjectProperty.homMk (𝟙 (yoneda.obj V))
  have : IsIso g0 := (ObjectProperty.isIso_hom_iff g0).1
    (by show IsIso (𝟙 (yoneda.obj V)); infer_instance)
  have hid : IsEtale B S hS g0.hom := by
    show IsEtale B S hS (𝟙 (yoneda.obj V))
    exact fun _ _ hφ => by simpa using hφ
  have sqS : IsPullback ψ (representedSpaceMap B S hS p) fV g0 :=
    IsPullback.of_horiz_isIso ⟨ObjectProperty.hom_ext _ (hesnd.trans (Category.comp_id _).symm)⟩
  have hψEt : IsEtale B S hS ψ.hom :=
    isEtale_of_isPullback B S hS (representedSpaceMap B S hS p) ψ g0 fV sqS.flip hid
  have hG : ((etaleModulePullback B S hS ψ hψEt).obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_etaleModulePullback B S hS ψ hψEt F hF
  have hrep := weaklyAssociatedPoints_modulePushforward_representedSpaceMap_eq_image B S hS p hp
    ((etaleModulePullback B S hS ψ hψEt).obj F) hG
  have hψpoint : ∀ w : points B S hS (yoneda.obj W),
      pointsMap B S hS X.1 f.hom (pointsMap B S hS (yoneda.obj W) ψ.hom w) =
        pointsMap B S hS (yoneda.obj W) (yoneda.map p) w := fun w => by
    rw [← pointsMap_comp_apply]
    exact congrArg (fun k => pointsMap B S hS (yoneda.obj W) k w) hesnd
  have hinv : ∀ x : points B S hS X.1,
      pointsMap B S hS (yoneda.obj W) ψ.hom (pointsMap B S hS X.1 e.inv x) = x := fun x => by
    show pointsMap B S hS (yoneda.obj W) e.hom (pointsMap B S hS X.1 e.inv x) = x
    rw [← pointsMap_comp_apply, e.inv_hom_id, pointsMap_id, id_eq]
  have himg : pointsMap B S hS (yoneda.obj W) (yoneda.map p) ''
        weaklyAssociatedPoints B S hS
          ⟨yoneda.obj W, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W⟩
          ((etaleModulePullback B S hS ψ hψEt).obj F) =
      pointsMap B S hS X.1 f.hom '' weaklyAssociatedPoints B S hS X F := by
    refine Set.ext fun t => ⟨?_, ?_⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨pointsMap B S hS (yoneda.obj W) ψ.hom w,
        (isWeaklyAssociatedPoint_etaleModulePullback_iff B S hS ψ hψEt F w).1 hw, hψpoint w⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨pointsMap B S hS X.1 e.inv x,
        (isWeaklyAssociatedPoint_etaleModulePullback_iff B S hS ψ hψEt F _).2 ((hinv x).symm ▸ hx),
        by rw [← hψpoint, hinv x]⟩
  refine Set.ext fun t => ?_
  rw [← himg, ← hrep]
  have hpid : pointsMap B S hS (yoneda.obj V) g0.hom t = t :=
    congrFun (pointsMap_id B S hS (yoneda.obj V)) t
  have step1 := isWeaklyAssociatedPoint_etaleModulePullback_iff B S hS g0 hid
    ((modulePushforward B S hS fV).obj F) t
  rw [hpid] at step1
  have step2 := isWeaklyAssociatedPoint_congr B S hS
    ((modulePushforwardEtaleBaseChangeIso B S hS ψ (representedSpaceMap B S hS p) fV
      g0 sqS hid).app F) t
  exact step1.symm.trans step2.symm

/-- **Weakly associated points of a finite direct image.** Let `f : X ⟶ Y` be a finite morphism
of algebraic spaces over a scheme `S` and let `F` be a quasi-coherent `𝒪_X`-module. Then
`WeakAss(f_*F) = f(WeakAss(F))`. -/
@[stacks 0CU9]
theorem weaklyAssociatedPoints_modulePushforward_eq_image_of_isFinite
    {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsFinite B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) :
    weaklyAssociatedPoints B S hS Y ((modulePushforward B S hS f).obj F) =
      pointsMap B S hS X.1 f.hom '' weaklyAssociatedPoints B S hS X F := by
  ext y
  obtain ⟨V, b, hV, hb, v, hv⟩ := exists_affine_etale_chart_at_point B S hS Y.1 Y.2 y
  let g : schemeSpace V ⟶ Y := ObjectProperty.homMk b
  have hg : IsEtale B S hS g.hom := (isEtale_iff_presheaf_of_yoneda B S hS b).2 hb
  let X' := AlgebraicSpaces.fiberProduct B S hS g f
  let f' : X' ⟶ schemeSpace V := ObjectProperty.homMk (pullback.fst g.hom f.hom)
  let i : X' ⟶ X := ObjectProperty.homMk (pullback.snd g.hom f.hom)
  have sq : IsPullback i f' f g := (AlgebraicSpaces.isPullback_fiberProduct B S hS g f).flip
  have hiEt : IsEtale B S hS i.hom := isEtale_of_isPullback B S hS f' i g f sq.flip hg
  have hsqp : IsPullback i.hom f'.hom f.hom g.hom :=
    (IsPullback.of_hasPullback g.hom f.hom).flip
  have hf' : IsFinite B S hS f'.hom := isFinite_of_isPullback B S hS hsqp hf
  have hFi : ((etaleModulePullback B S hS i hiEt).obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_etaleModulePullback B S hS i hiEt F hF
  have hX'aff : IsAffineSpace B S hS X'.1 :=
    hf'.isAffineSpace_source (isAffineSpace_yoneda B S hS V hV)
  have hchart := finiteAffineTargetWeaklyAssociatedImage B S hS V hV hX'aff f' hf' _ hFi
  have hgv : pointsMap B S hS (schemeSpace V).1 g.hom v = y := hv
  have hiff : y ∈ weaklyAssociatedPoints B S hS Y ((modulePushforward B S hS f).obj F) ↔
      v ∈ weaklyAssociatedPoints B S hS (schemeSpace V)
        ((modulePushforward B S hS f').obj ((etaleModulePullback B S hS i hiEt).obj F)) := by
    rw [← hgv]
    exact (isWeaklyAssociatedPoint_etaleModulePullback_iff B S hS g hg _ v).symm.trans
      (isWeaklyAssociatedPoint_congr B S hS
        ((modulePushforwardEtaleBaseChangeIso B S hS i f' f g sq hg).app F) v).symm
  constructor
  · intro hy
    have h2 := hiff.1 hy
    rw [hchart] at h2
    obtain ⟨x', hx', hx'v⟩ := h2
    refine ⟨pointsMap B S hS X'.1 i.hom x', ?_, ?_⟩
    · exact (isWeaklyAssociatedPoint_etaleModulePullback_iff B S hS i hiEt F x').1 hx'
    · rwa [← pointsMap_comp_apply,
        show i.hom ≫ f.hom = f'.hom ≫ g.hom from congrArg (fun k => k.hom) sq.w,
        pointsMap_comp_apply, hx'v]
  · rintro ⟨x, hx, hxy⟩
    have hvx : pointsMap B S hS (schemeSpace V).1 g.hom v =
        pointsMap B S hS X.1 f.hom x := by rw [hgv, hxy]
    obtain ⟨w, hw₁, hw₂⟩ := exists_point_of_isPullback B S hS sq.flip v x hvx
    have hwF : w ∈ weaklyAssociatedPoints B S hS X'
        ((etaleModulePullback B S hS i hiEt).obj F) :=
      (isWeaklyAssociatedPoint_etaleModulePullback_iff B S hS i hiEt F w).2 (hw₂ ▸ hx)
    refine hiff.2 ?_
    rw [hchart]
    exact ⟨w, hwF, hw₁⟩

/-! ### The relative weak assassin -/

variable {X Y Z : AlgebraicSpaces B S hS}

/-- **The relative weak assassin of a finite direct image.** Let `f : X ⟶ Y` be a morphism of
algebraic spaces over a scheme `S`, let `i : Z ⟶ X` be a finite morphism and let `G` be a
quasi-coherent `𝒪_Z`-module. Then the relative weak assassin `WeakAss_{X/Y}(i_*G)` is the image
under `i` of `WeakAss_{Z/Y}(G)`. -/
@[stacks 0CV4]
theorem relativeWeaklyAssociatedPoints_modulePushforward_eq_image_of_isFinite
    (f : X ⟶ Y) (i : Z ⟶ X)
    (hi : IsFinite B S hS i.hom) (G : Modules.{u, u} B S hS Z.1 Z.2)
    (hG : G.IsQuasicoherentOnSite) :
    relativeWeaklyAssociatedPoints B S hS f ((modulePushforward B S hS i).obj G) =
      pointsMap B S hS Z.1 i.hom '' relativeWeaklyAssociatedPoints B S hS (i ≫ f) G := by
  have hcomp : ∀ w : points B S hS Z.1,
      pointsMap B S hS Z.1 (i ≫ f).hom w =
        pointsMap B S hS X.1 f.hom (pointsMap B S hS Z.1 i.hom w) :=
    fun w => pointsMap_comp_apply B S hS i.hom f.hom w
  have key : ∀ p : FieldValuedPoint B S hS Y.1,
      weaklyAssociatedPoints B S hS (fibreAtFieldValuedPoint B S hS f p)
          ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS f p)).obj
            ((modulePushforward B S hS i).obj G)) =
        pointsMap B S hS (fibreAtFieldValuedPoint B S hS (i ≫ f) p).1
            (fibreAtFieldValuedPointMap B S hS i f p).hom ''
          weaklyAssociatedPoints B S hS (fibreAtFieldValuedPoint B S hS (i ≫ f) p)
            ((modulePullback B S hS
              (fibreAtFieldValuedPointProjection B S hS (i ≫ f) p)).obj G) := fun p ↦
    weaklyAssociatedPoints_modulePullback_modulePushforward_of_isFinite B S hS
      (fibreAtFieldValuedPointProjection B S hS f p) i
      (fibreAtFieldValuedPointMap B S hS i f p)
      (fibreAtFieldValuedPointProjection B S hS (i ≫ f) p)
      (isPullback_fibreAtFieldValuedPointMap B S hS i f p) hi G hG
  ext x
  constructor
  · rintro ⟨p, hp, θ, hθ, hwa⟩
    have hmem : θ ∈ weaklyAssociatedPoints B S hS (fibreAtFieldValuedPoint B S hS f p)
        ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS f p)).obj
          ((modulePushforward B S hS i).obj G)) := hwa
    rw [key p] at hmem
    obtain ⟨ζ, hζ, hζθ⟩ := hmem
    have himg : pointsMap B S hS Z.1 i.hom
        (pointsMap B S hS (fibreAtFieldValuedPoint B S hS (i ≫ f) p).1
          (fibreAtFieldValuedPointProjection B S hS (i ≫ f) p).hom ζ) = x := by
      rw [← pointsMap_fibreAtFieldValuedPointMap B S hS i f p ζ, hζθ, hθ]
    refine ⟨_, ⟨p, ?_, ζ, rfl, hζ⟩, himg⟩
    rwa [hcomp, himg]
  · rintro ⟨z, ⟨p, hp, ζ, hζz, hwa⟩, hzx⟩
    refine ⟨p, ?_, pointsMap B S hS (fibreAtFieldValuedPoint B S hS (i ≫ f) p).1
      (fibreAtFieldValuedPointMap B S hS i f p).hom ζ, ?_, ?_⟩
    · rw [hp, hcomp, hzx]
    · rwa [pointsMap_fibreAtFieldValuedPointMap B S hS i f p ζ, hζz]
    · have hmem : pointsMap B S hS (fibreAtFieldValuedPoint B S hS (i ≫ f) p).1
          (fibreAtFieldValuedPointMap B S hS i f p).hom ζ ∈
          pointsMap B S hS (fibreAtFieldValuedPoint B S hS (i ≫ f) p).1
              (fibreAtFieldValuedPointMap B S hS i f p).hom ''
            weaklyAssociatedPoints B S hS (fibreAtFieldValuedPoint B S hS (i ≫ f) p)
              ((modulePullback B S hS
                (fibreAtFieldValuedPointProjection B S hS (i ≫ f) p)).obj G) :=
        ⟨ζ, hwa, rfl⟩
      rwa [← key p] at hmem

end AlgebraicGeometry.Space

end
