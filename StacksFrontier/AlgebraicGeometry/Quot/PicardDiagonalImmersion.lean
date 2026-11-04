module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctorDiagonal
import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Inputs
import StacksFrontier.AlgebraicGeometry.Quot.PicardExactSequence
import StacksFrontier.AlgebraicGeometry.Spaces.DescentLocus.Theorem
import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStructureSheafPushforward

/-!
# The diagonal of the relative Picard functor is an immersion

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` which is flat, of finite
presentation and proper, and such that `𝒪_T ⟶ f_{T,*}𝒪_{X_T}` is an isomorphism for every scheme
`T` over `B`. Then the diagonal `Pic_{X/B} ⟶ Pic_{X/B} ×_B Pic_{X/B}` is representable by
immersions; in other words `Pic_{X/B} ⟶ B` is locally separated.

For a scheme `T` over `B` and two points `x, y ∈ Pic_{X/B}(T)`, the base change of the diagonal
along `(x, y) : T ⟶ Pic_{X/B} ×_B Pic_{X/B}` is the subfunctor of `h_T` of the morphisms
`T' ⟶ T` along which `x` and `y` agree
(`AlgebraicGeometry.Space.PicardSituation.picardEqualizer`), so the statement is that each of
these subfunctors is represented by immersions.

## Main results

* `AlgebraicGeometry.Space.PicardSituation.isImmersion_picardEqualizer_and_isLocallySeparated`:
  the diagonal of `Pic_{X/B}` is representable by immersions, and `Pic_{X/B} ⟶ B` is locally
  separated.

## References

* [Stacks Project, Tag 0D2D](https://stacks.math.columbia.edu/tag/0D2D)
* [Stacks Project, Tag 0D2C](https://stacks.math.columbia.edu/tag/0D2C)
* [Stacks Project, Tag 0D23](https://stacks.math.columbia.edu/tag/0D23)
* [Stacks Project, Tag 0D27](https://stacks.math.columbia.edu/tag/0D27)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### From schemes to algebraic spaces over the base -/

/-- For `f` flat, proper and of finite presentation with `𝒪_T ≅ f_{T,*}𝒪_{X_T}` for every scheme
`T` over the target, the same holds after base change along every algebraic space over the
target. -/
private theorem isIso_structureSharp_pullback_snd_of_forall_schemesOver
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hp : IsProper B S hS f.hom)
    (hfl : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (hiso : ∀ T : SchemesOver Y, IsIso (structureSharp B S hS (baseChangeInclusion f T)))
    {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) :
    IsIso (structureSharp B S hS (pullback.snd f g)) := by
  refine (isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre B S hS f hp hfl hfp
    fun p => ?_).2 Y' g
  let h : (schemeSpaceFunctor B S hS).obj (p.siteObject B S hS Y.1) ⟶ Y :=
    ObjectProperty.homMk (yonedaEquiv.symm p.value)
  refine (bijective_algebraMap_fibreOverFieldValuedPoint_iff B S hS f.hom p X.2 Y.2).2 ?_
  exact bijective_globalFunctionsMap_of_isIso_structureSharp B S hS _
    (baseChangeInclusion f (CostructuredArrow.mk h)) (hiso (CostructuredArrow.mk h))

/-! ### Transport of a descent isomorphism along a morphism -/

/-- An isomorphism `a^*N ≅ b^*L` gives `(e ≫ a)^*N ≅ (e ≫ b)^*L`. -/
private theorem nonempty_iso_modulePullback_comp {P Q A C : AlgebraicSpaces B S hS} (e : P ⟶ Q)
    {a : Q ⟶ A} {b : Q ⟶ C} {a' : P ⟶ A} {b' : P ⟶ C} (ha : e ≫ a = a') (hb : e ≫ b = b')
    {N : Modules.{u, u} B S hS A.1 A.2} {L : Modules.{u, u} B S hS C.1 C.2}
    (h : Nonempty ((modulePullback B S hS a).obj N ≅ (modulePullback B S hS b).obj L)) :
    Nonempty ((modulePullback B S hS a').obj N ≅ (modulePullback B S hS b').obj L) := by
  subst ha hb
  obtain ⟨α⟩ := h
  exact ⟨((modulePullbackCompIso B S hS e a).app N).symm ≪≫ (modulePullback B S hS e).mapIso α ≪≫
    (modulePullbackCompIso B S hS e b).app L⟩

/-! ### Invertible modules and rank one -/

/-- An invertible module on an algebraic space is finite locally free of rank one. -/
private theorem isFiniteLocallyFreeOfIntRank_one_of_isInvertibleModule
    {Z : AlgebraicSpaces B S hS} {L : Modules.{u, u} B S hS Z.1 Z.2}
    (hL : IsInvertibleModule Z L) :
    SheafOfModules.IsFiniteLocallyFreeOfIntRank L ((1 : ℕ) : ℤ) :=
  (DescentStratum.isFiniteLocallyFreeOfIntRank_iff_ringedSite L 1).2
    ((isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one L).1 hL)

/-- A module on an algebraic space finite locally free of rank one is invertible. -/
private theorem isInvertibleModule_of_isFiniteLocallyFreeOfIntRank_one
    {Z : AlgebraicSpaces B S hS} {L : Modules.{u, u} B S hS Z.1 Z.2}
    (hL : SheafOfModules.IsFiniteLocallyFreeOfIntRank L ((1 : ℕ) : ℤ)) :
    IsInvertibleModule Z L :=
  (isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one L).2
    ((DescentStratum.isFiniteLocallyFreeOfIntRank_iff_ringedSite L 1).1 hL)

/-! ### The subfunctor cut out by an immersion -/

/-- The subfunctor of `h_T` cut out by an immersion `j : Z ⟶ h_T` of presheaves is represented
by immersions. -/
private theorem isImmersion_range_ι {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : BigFppfOver B S hS} (j : Z ⟶ yoneda.obj T) (hj : IsImmersion B S hS j) :
    IsImmersion B S hS (Subfunctor.range j).ι := by
  have _ : Mono j := mono_of_isImmersion (hf := hj)
  have _ : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hiso : Arrow.mk j ≅ Arrow.mk (Subfunctor.range j).ι :=
    Arrow.isoMk (asIso (Subfunctor.toRange j)) (Iso.refl _) (by simp)
  exact (MorphismProperty.arrow_mk_iso_iff _ hiso).1 hj

namespace PicardSituation

variable (s : PicardSituation B S hS)

/-- The projection `X_T ⟶ T` of the base change to a test scheme is flat, proper and of finite
presentation when `f` is. -/
private theorem baseChangeInclusion_properties (hflat : IsFlat B S hS s.f.hom)
    (hfp : IsFinitePresentation B S hS s.f.hom) (hp : IsProper B S hS s.f.hom)
    (T : s.SchemesOver) :
    IsProper B S hS (baseChangeInclusion s.f T).hom ∧
      IsFlat B S hS (baseChangeInclusion s.f T).hom ∧
        IsFinitePresentation B S hS (baseChangeInclusion s.f T).hom :=
  ⟨(isProper_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS s.f T.hom) hp,
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS s.f T.hom) hflat,
    (isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS s.f T.hom) hfp⟩

/-- For `f` flat, proper and of finite presentation with `s.StructureSheafMapIso`, the base
change `X_T ⟶ T` to a test scheme `T` satisfies: `𝒪_{Y'} ⟶ f'_*𝒪_{X'}` is an isomorphism for the
base change `f'` of `X_T ⟶ T` along every algebraic space `Y' ⟶ T`. -/
private theorem isIso_structureSharp_baseChangeInclusion_pullback_snd
    (hflat : IsFlat B S hS s.f.hom) (hfp : IsFinitePresentation B S hS s.f.hom)
    (hp : IsProper B S hS s.f.hom) (h : s.StructureSheafMapIso) (T : s.SchemesOver)
    {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ (schemeSpaceFunctor B S hS).obj T.left) :
    IsIso (structureSharp B S hS (pullback.snd (baseChangeInclusion s.f T) g)) := by
  obtain ⟨hpT, hflT, hfpT⟩ := s.baseChangeInclusion_properties hflat hfp hp T
  let D : CoherentSituation B S hS := ⟨s.X, s.base, s.f, hfp⟩
  exact isIso_structureSharp_pullback_snd_of_forall_schemesOver _ hpT hflT hfpT
    (D.structureSheafMapIso_baseChange T.hom h) g

/-- **Descent of `L` along `X_U ⟶ U` is the triviality of its class in the Picard sequence.**
For a test scheme `T`, an invertible module `L` on `X_T` and `g : U ⟶ T`, the module `L`
descends along the base change of `X_T ⟶ T` to `U` (`HasDescentAt`) exactly when
the pullback of the class of `L` to `X_U` lies in the image of `Pic(U)`. -/
private theorem hasDescentAt_iff_mem_range_basePicardPullback
    (hflat : IsFlat B S hS s.f.hom) (hfp : IsFinitePresentation B S hS s.f.hom)
    (hp : IsProper B S hS s.f.hom) (h : s.StructureSheafMapIso) (T : s.SchemesOver)
    (L : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2)
    (hL : IsInvertibleModule (s.baseChange T) L) {U : BigFppfOver B S hS} (g : U ⟶ T.left) :
    HasDescentAt (baseChangeInclusion s.f T) L ((schemeSpaceFunctor B S hS).map g) ↔
      s.picardMap (CostructuredArrow.liftHom (schemeSpaceFunctor B S hS) s.base T g)
          (picardClass _ L hL) ∈
        Set.range (s.basePicardPullback
          (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g ≫ T.hom))) := by
  let m := CostructuredArrow.liftHom (schemeSpaceFunctor B S hS) s.base T g
  let U' : s.SchemesOver := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g ≫ T.hom)
  have hpb : IsPullback (baseChangeMap s.f m) (baseChangeInclusion s.f U')
      (baseChangeInclusion s.f T) ((schemeSpaceFunctor B S hS).map g) :=
    isPullback_overBaseChangeMap s.f ((schemesOverToOver s.base).map m)
  rw [picardMap_eq, picardPullback_picardClass]
  constructor
  · rintro ⟨N, hN, hNL⟩
    have hrk : SheafOfModules.IsFiniteLocallyFreeOfIntRank
        ((modulePullback B S hS (pullback.snd (baseChangeInclusion s.f T)
          ((schemeSpaceFunctor B S hS).map g))).obj N) ((1 : ℕ) : ℤ) :=
      isFiniteLocallyFreeOfIntRank_of_iso B S hS hNL.some.symm
        (DescentStratum.isFiniteLocallyFreeOfIntRank_modulePullback _
          (isFiniteLocallyFreeOfIntRank_one_of_isInvertibleModule hL))
    have hNi : IsInvertibleModule _ N :=
      isInvertibleModule_of_isFiniteLocallyFreeOfIntRank_one
        (DescentStratum.isFiniteLocallyFreeOfIntRank_of_modulePullback _
          (DescentStratum.surjective_pointsMap_snd _
            (fun g' => s.isIso_structureSharp_baseChangeInclusion_pullback_snd hflat hfp hp h T g')
            _) hN hrk)
    refine ⟨picardClass _ N hNi, ?_⟩
    rw [basePicardPullback_picardClass, picardClass_eq_picardClass_iff]
    exact nonempty_iso_modulePullback_comp hpb.isoPullback.hom hpb.isoPullback_hom_snd
      hpb.isoPullback_hom_fst hNL
  · rintro ⟨y, hy⟩
    obtain ⟨N, hN, rfl⟩ := exists_picardClass _ y
    rw [basePicardPullback_picardClass, picardClass_eq_picardClass_iff] at hy
    refine ⟨N, DescentStratum.isFiniteLocallyFree_of_isFiniteLocallyFreeOfIntRank
      (isFiniteLocallyFreeOfIntRank_one_of_isInvertibleModule hN), ?_⟩
    exact nonempty_iso_modulePullback_comp hpb.isoPullback.inv hpb.isoPullback_inv_snd
      hpb.isoPullback_inv_fst hy

/-- For `f` flat, proper and of finite presentation with `s.StructureSheafMapIso`, the
equalizer of the images in `Pic_{X/B}(T)` of a class of `Pic(X_T)` and of `0` is represented by
immersions. -/
private theorem isImmersion_picardEqualizer_picardClassMap_zero
    (hflat : IsFlat B S hS s.f.hom) (hfp : IsFinitePresentation B S hS s.f.hom)
    (hp : IsProper B S hS s.f.hom) (h : s.StructureSheafMapIso) (T : s.SchemesOver)
    (v : s.picardAt T) :
    IsImmersion B S hS (s.picardEqualizer T (s.picardClassMap T v) (s.picardClassMap T 0)).ι := by
  obtain ⟨L, hL, rfl⟩ := exists_picardClass _ v
  obtain ⟨hpT, hflT, hfpT⟩ := s.baseChangeInclusion_properties hflat hfp hp T
  obtain ⟨Z, j, hj, -, hZ⟩ :=
    exists_isImmersion_isFinitePresentation_factorsThrough_iff_hasDescentAt
      (baseChangeInclusion s.f T) hflT hpT hfpT L
      (DescentStratum.isFiniteLocallyFree_of_isFiniteLocallyFreeOfIntRank
        (isFiniteLocallyFreeOfIntRank_one_of_isInvertibleModule hL))
      (fun g => s.isIso_structureSharp_baseChangeInclusion_pullback_snd hflat hfp hp h T g)
  have heq : s.picardEqualizer T (s.picardClassMap T (picardClass _ L hL))
      (s.picardClassMap T 0) = Subfunctor.range j.hom := by
    ext ⟨U⟩ g
    let m := CostructuredArrow.liftHom (schemeSpaceFunctor B S hS) s.base T g
    refine (s.mem_picardEqualizer_iff _ _ m).trans ?_
    have h0 : s.picardMap m (0 : s.picardAt T) = 0 := picardPullback_zero _
    rw [← s.picardClassMap_picardMap, ← s.picardClassMap_picardMap, h0,
      (s.exact_picardSequence h _).2,
      ← s.hasDescentAt_iff_mem_range_basePicardPullback hflat hfp hp h T L hL g,
      ← hZ ((schemeSpaceFunctor B S hS).map g)]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨yonedaEquiv k.hom, ?_⟩
      have hk' : k.hom ≫ j.hom = yoneda.map g := congrArg InducedCategory.Hom.hom hk
      exact (congrArg yonedaEquiv hk').trans (yonedaEquiv_yoneda_map g)
    · rintro ⟨z, hz⟩
      refine ⟨ObjectProperty.homMk (yonedaEquiv.symm z), ?_⟩
      apply ObjectProperty.hom_ext
      apply yonedaEquiv.injective
      show yonedaEquiv (yonedaEquiv.symm z ≫ j.hom) = yonedaEquiv (yoneda.map g)
      rwa [yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
  rw [heq]
  exact isImmersion_range_ι j.hom hj

/-- Let `f : X ⟶ B` be a morphism of algebraic spaces over `S` which is flat, of finite
presentation and proper, such that `𝒪_T ⟶ f_{T,*}𝒪_{X_T}` is an isomorphism for every scheme `T`
over `B`. Then the diagonal `Pic_{X/B} ⟶ Pic_{X/B} ×_B Pic_{X/B}` is representable by
immersions: for every scheme `T` over `B` and all `x, y ∈ Pic_{X/B}(T)`, the subfunctor of `h_T`
of the morphisms `T' ⟶ T` with `x|_{T'} = y|_{T'}` (the base change of the diagonal along
`(x, y)`) is represented by immersions. In other words, `Pic_{X/B} ⟶ B` is locally separated:
every morphism of presheaves `q : F ⟶ B` whose fibres are identified with `Pic_{X/B}`, naturally
in the test scheme, has diagonal an immersion. -/
@[stacks 0D2D]
theorem isImmersion_picardEqualizer_and_isLocallySeparated (hflat : IsFlat B S hS s.f.hom)
    (hfp : IsFinitePresentation B S hS s.f.hom) (hp : IsProper B S hS s.f.hom)
    (h : s.StructureSheafMapIso) :
    (∀ (T : s.SchemesOver) (x y : s.picardFunctor.obj (op T)),
      IsImmersion B S hS (s.picardEqualizer T x y).ι) ∧
    ∀ (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (q : F ⟶ s.base.1)
      (e : ∀ T : s.SchemesOver, s.picardFunctor.obj (op T) ≃
        {x : F.obj (op T.left) //
          q.app (op T.left) x =
            yonedaEquiv (show yoneda.obj T.left ⟶ s.base.1 from T.hom.hom)}),
      (∀ (T U : s.SchemesOver) (g : T ⟶ U) (x : s.picardFunctor.obj (op U)),
        (e T (s.picardFunctor.map g.op x)).val = F.map g.left.op (e U x).val) →
      IsLocallySeparated B S hS q := by
  have himm : ∀ (T : s.SchemesOver) (x y : s.picardFunctor.obj (op T)),
      IsImmersion B S hS (s.picardEqualizer T x y).ι := by
    refine s.isImmersion_picardEqualizer_of_picardClassMap fun T v w => ?_
    rw [s.picardEqualizer_picardClassMap_sub]
    exact s.isImmersion_picardEqualizer_picardClassMap_zero hflat hfp hp h T (v - w)
  exact ⟨himm, fun F q e he => (s.isLocallySeparated_iff_of_represents F q e he).2 himm⟩

end PicardSituation

end AlgebraicGeometry.Space

end
