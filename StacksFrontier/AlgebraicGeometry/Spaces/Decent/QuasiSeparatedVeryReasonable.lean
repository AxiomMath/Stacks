module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonableConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonablePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ZariskiLocallyQuasiSeparatedVeryReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints

/-!
# A quasi-separated morphism of algebraic spaces is very reasonable

A quasi-separated morphism of algebraic spaces is very reasonable: every base change of it along
a morphism out of a representable presheaf is a very reasonable algebraic space.

## Main results

* `AlgebraicGeometry.Space.isVeryReasonableSpace_pullback_of_isQuasiSeparated_of_isAffine`: a
  base change of a quasi-separated morphism over an affine test object is a very reasonable
  algebraic space.
* `AlgebraicGeometry.Space.isVeryReasonable_of_isQuasiSeparated`: a quasi-separated morphism of
  algebraic spaces is very reasonable.

## References

* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03KE](https://stacks.math.columbia.edu/tag/03KE)
* [Stacks Project, Tag 03KM](https://stacks.math.columbia.edu/tag/03KM)
* [Stacks Project, Tag 03KZ](https://stacks.math.columbia.edu/tag/03KZ)
* [Stacks Project, Tag 03M5](https://stacks.math.columbia.edu/tag/03M5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A base change of a quasi-separated morphism of algebraic spaces over `S` along a morphism
from the presheaf represented by an *affine* object of the site is a very reasonable algebraic
space. -/
theorem isVeryReasonableSpace_pullback_of_isQuasiSeparated_of_isAffine
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : IsQuasiSeparated B S hS f) (V : BigFppfOver B S hS)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) (g : yoneda.obj V ⟶ Y) :
    IsVeryReasonableSpace B S hS (pullback f g) := by
  have halg : IsAlgebraicSpace B S hS (pullback f g) :=
    isAlgebraicSpace_pullback B S hS f g hX (isAlgebraicSpace_yoneda B S hS V) hY
  exact isVeryReasonableSpace_of_isAbsolutelyZariskiLocallyQuasiSeparated B S hS
    B.contains_terminal _ halg
    (isAbsolutelyZariskiLocallyQuasiSeparated_of_isAbsolutelyQuasiSeparated B S hS _
      B.contains_terminal halg
      ((isQuasiSeparated_pullbackSnd_iff_isAbsolutelyQuasiSeparated B S hS
          B.contains_terminal hX f V hV g).1
        (isQuasiSeparated_pullbackSnd B S hS g hf)))

/-- A quasi-separated morphism of algebraic spaces over `S` is very reasonable. -/
@[stacks 03M5 "quasi-separated implies very reasonable"]
theorem isVeryReasonable_of_isQuasiSeparated (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y} (hf : IsQuasiSeparated B S hS f) :
    IsVeryReasonable B S hS f := by
  classical
  intro T g
  have hXT : IsAlgebraicSpace B S hS (pullback g f) :=
    isAlgebraicSpace_pullback B S hS g f (isAlgebraicSpace_yoneda B S hS T) hX hY
  have hbc := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) (F := yoneda)
  choose V inc hincOpen hincRange hVaff using fun W :
      ((BigFppfOver.toScheme B S hS).obj T).affineOpens ↦
    BigFppfOver.exists_affineOpen_restrict B S hS T W
  have hopenIncl : ∀ W, IsOpenImmersion B S hS (yoneda.map (inc W)) := fun W ↦
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ (inc W)).2 (hincOpen W)
  set R : ((BigFppfOver.toScheme B S hS).obj T).affineOpens → Subfunctor (yoneda.obj T) :=
    fun W ↦ Subfunctor.range (yoneda.map (inc W))
  set M : ((BigFppfOver.toScheme B S hS).obj T).affineOpens → Subfunctor (pullback g f) :=
    fun W ↦ (R W).preimage (pullback.fst g f)
  have hRopen : ∀ W, IsOpenSubspace B S hS (R W) := fun W ↦
    isOpenSubspace_range_of_isOpenImmersion (V W) (yoneda.map (inc W)) (hopenIncl W)
  have hcomp (W) : (rangeIsoOfIsOpenImmersion (V W) (yoneda.map (inc W)) (hopenIncl W)).hom ≫
      (R W).ι = yoneda.map (inc W) := by
    have _ : Mono (yoneda.map (inc W)) := mono_of_presheaf_isOpenImmersion (hopenIncl W)
    exact Subfunctor.toRange_ι (yoneda.map (inc W))
  have hsq : ∀ W, IsPullback ((R W).fromPreimage (pullback.fst g f)) (M W).ι (R W).ι
      (pullback.fst g f) := fun W ↦ Subfunctor.isPullback_preimage _ _
  have hcart (W) : IsPullback ((M W).ι ≫ pullback.snd g f)
      ((R W).fromPreimage (pullback.fst g f) ≫
        (rangeIsoOfIsOpenImmersion (V W) (yoneda.map (inc W)) (hopenIncl W)).inv)
      f (yoneda.map (inc W) ≫ g) := by
    set eW := rangeIsoOfIsOpenImmersion (V W) (yoneda.map (inc W)) (hopenIncl W)
    have hinv : eW.inv ≫ yoneda.map (inc W) = (R W).ι :=
      calc eW.inv ≫ yoneda.map (inc W) = eW.inv ≫ eW.hom ≫ (R W).ι := by rw [hcomp W]
        _ = (R W).ι := by simp
    have hiso : IsPullback eW.inv ((R W).ι ≫ g) (yoneda.map (inc W) ≫ g) (𝟙 Y) :=
      IsPullback.of_horiz_isIso ⟨by simp only [← Category.assoc, hinv, Category.comp_id]⟩
    have hpaste := ((hsq W).paste_vert (IsPullback.of_hasPullback g f)).paste_horiz hiso
    simpa only [Category.comp_id] using hpaste.flip
  have halgM : ∀ W, IsAlgebraicSpace B S hS (M W).toFunctor := fun W ↦
    (isAlgebraicSpace_pullback B S hS f (yoneda.map (inc W) ≫ g) hX
      (isAlgebraicSpace_yoneda B S hS (V W)) hY).of_iso (hcart W).isoPullback.symm
  have hMopen : ∀ W, IsOpenSubspace B S hS (M W) := fun W ↦
    ⟨halgM W, hbc.of_isPullback (hsq W) (hRopen W).2⟩
  have hMvr : ∀ W, IsVeryReasonableSpace B S hS (M W).toFunctor := fun W ↦
    isVeryReasonableSpace_of_relativelyRepresentable B S hS (hcart W).isoPullback.hom
      (Functor.relativelyRepresentable.of_isIso yoneda _)
      (isVeryReasonableSpace_pullback_of_isQuasiSeparated_of_isAffine B S hS hX hY hf
        (V W) (hVaff W) (yoneda.map (inc W) ≫ g))
  refine isVeryReasonableSpace_of_isZariskiCover B S hS _ _ M ?_ hMvr
  refine (isZariskiCover_iff_iUnion_points B S hS (pullback g f) hXT _ M hMopen).2 ?_
  refine Set.eq_univ_iff_forall.2 fun x ↦ ?_
  suffices hlift : ∀ W : ((BigFppfOver.toScheme B S hS).obj T).affineOpens,
      pointsToScheme B S hS T (pointsMap B S hS (pullback g f) (pullback.fst g f) x) ∈ W.1 →
      x ∈ Set.range (pointsMap B S hS (M W).toFunctor (M W).ι) by
    obtain ⟨-, ⟨W₀, hW₀, rfl⟩, hmem, -⟩ :=
      ((BigFppfOver.toScheme B S hS).obj T).isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (pointsToScheme B S hS T
          (pointsMap B S hS (pullback g f) (pullback.fst g f) x))) isOpen_univ
    exact Set.mem_iUnion.2 ⟨⟨W₀, hW₀⟩, hlift ⟨W₀, hW₀⟩ hmem⟩
  intro W hmem
  obtain ⟨r, hr⟩ := exists_pointsMap_yonedaMap_eq_of_mem_range B S hS (inc W)
    (pointsMap B S hS (pullback g f) (pullback.fst g f) x)
    (by rwa [hincRange W])
  set eW := rangeIsoOfIsOpenImmersion (V W) (yoneda.map (inc W)) (hopenIncl W)
  have hrR : pointsMap B S hS (R W).toFunctor (R W).ι
      (pointsMap B S hS (yoneda.obj (V W)) eW.hom r) =
      pointsMap B S hS (pullback g f) (pullback.fst g f) x := by
    have h1 : pointsMap B S hS (yoneda.obj (V W)) (eW.hom ≫ (R W).ι) r =
        pointsMap B S hS (pullback g f) (pullback.fst g f) x := by rwa [hcomp W]
    rwa [pointsMap_comp, Function.comp_apply] at h1
  have hsq' : IsPullback
      (ObjectProperty.homMk ((R W).fromPreimage (pullback.fst g f)) :
        (⟨(M W).toFunctor, halgM W⟩ : AlgebraicSpaces B S hS) ⟶ ⟨(R W).toFunctor, (hRopen W).1⟩)
      (ObjectProperty.homMk (M W).ι : (⟨(M W).toFunctor, halgM W⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨pullback g f, hXT⟩)
      (ObjectProperty.homMk (R W).ι : (⟨(R W).toFunctor, (hRopen W).1⟩ :
        AlgebraicSpaces B S hS) ⟶ ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
      (ObjectProperty.homMk (pullback.fst g f) : (⟨pullback g f, hXT⟩ :
        AlgebraicSpaces B S hS) ⟶ ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) (hsq W)
  obtain ⟨m, -, hmx⟩ := exists_point_of_isPullback B S hS hsq'
    (pointsMap B S hS (yoneda.obj (V W)) eW.hom r) x hrR
  exact ⟨m, hmx⟩

end AlgebraicGeometry.Space

end
