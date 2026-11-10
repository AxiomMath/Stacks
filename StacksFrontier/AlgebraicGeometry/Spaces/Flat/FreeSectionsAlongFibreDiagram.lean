module

public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.ExistenceFreeSectionsAlongFibreChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.UniversalPurityOfFlatPure

/-!
# Stacks 0CVW: free sections along a fibre, as a diagram of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`, let `𝓕` be a quasi-coherent
`𝒪_X`-module and let `y ∈ |Y|`, with set-theoretic fibre `F = f^{-1}({y}) ⊆ |X|`. Assume that `f`
is of finite type, that `𝓕` is of finite type, and that `𝓕` is flat over `Y` at every point of
`F`. Stacks 0CVW asserts that there are an étale morphism `(Y', y') ⟶ (Y, y)` with `Y'` a scheme
and a commutative diagram
```
  X  ←ᵍ  X'
  ↓      ↓
  Y  ←  Spec 𝒪_{Y', y'}
```
such that `X' ⟶ X ×_Y Spec 𝒪_{Y', y'}` is étale, `|X'_{y'}| ⟶ F` is surjective, `X'` is
affine, and `Γ(X', g^*𝓕)` is a free `𝒪_{Y', y'}`-module.

`AlgebraicGeometry.Space.exists_etale_affine_free_sections_along_fibre` states and proves exactly
that, every scheme of the diagram being an object of the big fppf site of `S`.

## The proof

It follows the source.

* `AlgebraicGeometry.Space.exists_affineChart_hasFreeSectionsAlongFibre_chartFibre` makes the
  source's reduction to an affine étale chart `q : Y₁ ⟶ Y` through a point `w` over `y` and an
  affine étale chart `U` of `X` covering `X ×_Y Y₁`, étale over it, and applies Stacks 05L1 to
  `U ⟶ Y₁` at `w`.
* `AlgebraicGeometry.HasFreeSectionsAlongFibreOver.exists_affine` shrinks the elementary étale
  neighbourhood Stacks 05L1 produces to an affine one, `σ : W ⟶ Y₁`. Being affine and étale over
  the affine `Y₁`, it is an object `Y'` of the site; the étale morphism `(Y', y') ⟶ (Y, y)` is
  `σ` followed by `q`. The affine `X'` of Stacks 05L1, of finite type over
  `Spec 𝒪_{Y', y'}`, is an object of the site too.
* Stacks 05L1 gives étaleness of `X' ⟶ U ×_{Y₁} Spec 𝒪_{Y', y'}`, and
  `CategoryTheory.Limits.isPullback_pullbackLift_baseChange` exhibits
  `U ×_{Y₁} Spec 𝒪_{Y', y'} ⟶ X ×_Y Spec 𝒪_{Y', y'}` as a base change of the étale
  `U ⟶ X ×_Y Y₁`; the composite is the source's étaleness clause.
* The covering clause of Stacks 05L1 says that the fibre of `U` over `w` is the image of the
  closed fibre of `X'`, and the first step identifies `F` with the image of that fibre of `U`.
* `Γ(X', g^*𝓕)` is the module of global sections of the pullback to `X'` of `𝓕|_U`, the two
  being identified through the base change of chart restrictions of a quasi-coherent module,
  `AlgebraicGeometry.Space.nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent`, and
  the composition comparison of Stacks 03LU.

## References

* [Stacks Project, Tag 0CVW](https://stacks.math.columbia.edu/tag/0CVW)
* [Stacks Project, Tag 05L1](https://stacks.math.columbia.edu/tag/05L1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks in this presheaf category times out at the default limit
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_FreeSectionsAlongFibreDiagram :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_FreeSectionsAlongFibreDiagram
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- A morphism of the site étale on schemes, followed by an étale morphism of presheaves, is
étale. -/
private theorem isEtale_yoneda_map_comp {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {V C : BigFppfOver B S hS} (ν : V ⟶ C) (hν : Etale ((BigFppfOver.toScheme B S hS).map ν))
    (q : yoneda.obj C ⟶ Y) (hq : IsEtale B S hS q) : IsEtale B S hS (yoneda.map ν ≫ q) :=
  isEtale_comp B S hS
    ((isEtale_iff_presheaf_of_yoneda B S hS _).2 ((presheaf_yoneda_map_etale_iff B S hS ν).2 hν))
    hq

/-- Let `a : A ⟶ X` and `q : C ⟶ Y` lie over `f` through `ĝ : A ⟶ C`, with `A ⟶ X ×_Y C`
étale. If `cs : Zs ⟶ A` and `κ : Zs ⟶ SS` lie over `ĝ` and `hs : SS ⟶ C`, and the induced
morphism of schemes `Zs ⟶ A ×_C SS` is étale, then `Zs ⟶ X ×_Y SS` is étale. -/
private theorem isEtale_pullbackLift_yoneda_of_etale {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) {A C SS Zs : BigFppfOver B S hS} (q : yoneda.obj C ⟶ Y) (a : yoneda.obj A ⟶ X)
    (ĝ : A ⟶ C) (hsq : yoneda.map ĝ ≫ q = a ≫ f)
    (hLet : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.lift (yoneda.map ĝ) a hsq))
    (hs : SS ⟶ C) {cg : yoneda.obj SS ⟶ Y} (hcg : yoneda.map hs ≫ q = cg)
    (cs : Zs ⟶ A) (κ : Zs ⟶ SS) (hℓ : cs ≫ ĝ = κ ≫ hs)
    (hcomm : yoneda.map κ ≫ cg = (yoneda.map cs ≫ a) ≫ f)
    {h' : (BigFppfOver.toScheme B S hS).obj SS ⟶ (BigFppfOver.toScheme B S hS).obj C}
    (hh' : (BigFppfOver.toScheme B S hS).map hs = h')
    (hc : (BigFppfOver.toScheme B S hS).map cs ≫ (BigFppfOver.toScheme B S hS).map ĝ =
      (BigFppfOver.toScheme B S hS).map κ ≫ h')
    (het : Etale (pullback.lift _ _ hc)) :
    IsEtale B S hS (pullback.lift (yoneda.map κ) (yoneda.map cs ≫ a) hcomm) := by
  subst hh'
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  let m0 : yoneda.obj (pullback ĝ hs) ⟶ pullback cg f :=
    pullback.lift (yoneda.map (pullback.snd ĝ hs)) (yoneda.map (pullback.fst ĝ hs) ≫ a)
      ((congrArg (yoneda.map (pullback.snd ĝ hs) ≫ ·) hcg.symm).trans
        (by rw [← Category.assoc, ← Functor.map_comp, ← pullback.condition,
          Functor.map_comp, Category.assoc, hsq, Category.assoc]))
  let n0 : pullback cg f ⟶ pullback q f :=
    pullback.lift (pullback.fst cg f ≫ yoneda.map hs) (pullback.snd cg f)
      ((Category.assoc _ _ _).trans ((congrArg (pullback.fst cg f ≫ ·) hcg).trans
        pullback.condition))
  have SQ : IsPullback (yoneda.map (pullback.fst ĝ hs)) m0 (pullback.lift (yoneda.map ĝ) a hsq)
      n0 :=
    isPullback_pullbackLift_baseChange q f (yoneda.map ĝ) a hsq
      (yoneda.map hs) cg hcg (yoneda.map (pullback.fst ĝ hs)) (yoneda.map (pullback.snd ĝ hs))
      ((IsPullback.of_hasPullback ĝ hs).map yoneda)
  have sqS : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst ĝ hs))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd ĝ hs))
      ((BigFppfOver.toScheme B S hS).map ĝ) ((BigFppfOver.toScheme B S hS).map hs) :=
    (IsPullback.of_hasPullback ĝ hs).map (BigFppfOver.toScheme B S hS)
  have hℓet : Etale ((BigFppfOver.toScheme B S hS).map (pullback.lift cs κ hℓ)) := by
    have hfac : (BigFppfOver.toScheme B S hS).map (pullback.lift cs κ hℓ) ≫
        sqS.isoPullback.hom = pullback.lift _ _ hc := by
      apply pullback.hom_ext
      · rw [Category.assoc, IsPullback.isoPullback_hom_fst, ← Functor.map_comp,
          pullback.lift_fst, pullback.lift_fst]
      · rw [Category.assoc, IsPullback.isoPullback_hom_snd, ← Functor.map_comp,
          pullback.lift_snd, pullback.lift_snd]
    rwa [← MorphismProperty.cancel_right_of_respectsIso @Etale _ sqS.isoPullback.hom, hfac]
  have hlift : pullback.lift (yoneda.map κ) (yoneda.map cs ≫ a) hcomm =
      yoneda.map (pullback.lift cs κ hℓ) ≫ m0 := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Functor.map_comp,
        pullback.lift_snd]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc,
        ← Functor.map_comp, pullback.lift_fst]
  rw [hlift]
  exact isEtale_yoneda_map_comp B S hS _ hℓet _
    (isEtale_of_isPullback_yoneda B S hS SQ ((isEtale_iff_presheaf_of_yoneda B S hS _).2 hLet))

/-- For an étale chart `U` of `X` and a morphism `cs : Zs ⟶ U` of the site, the restriction to
its identity chart of the pullback of `𝓕` along `Zs ⟶ U ⟶ X` is the pullback along `cs` of the
restriction of `𝓕` to `U`. -/
private noncomputable def restrictToChartIdModulePullbackIso {X : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (U : SmallEtale B S hS X.1)
    {Zs : BigFppfOver B S hS} (cs : Zs ⟶ U.obj.left) :
    restrictToChart B S hS (isAlgebraicSpace_yoneda B S hS Zs)
        ((modulePullback B S hS (X := ⟨yoneda.obj Zs, isAlgebraicSpace_yoneda B S hS Zs⟩)
          (Y := X) (ObjectProperty.homMk (yoneda.map cs ≫ U.obj.hom))).obj F)
        (idEtaleChart B S hS Zs) ≅
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map cs)).obj
        (chartModule B S hS X.2 F U) :=
  let aU : schemeSpace U.obj.left ⟶ X := ObjectProperty.homMk U.obj.hom
  let N := (modulePullback B S hS aU).obj F
  let e₁ : chartModule B S hS X.2 F U ≅ representedZariskiRestriction B S hS U.obj.left
      (isAlgebraicSpace_yoneda B S hS U.obj.left) N :=
    restrictToChartIsoRepresentedZariskiRestrictionPullback B S hS U.obj.hom
      ((isEtale_iff_presheaf_of_yoneda B S hS U.obj.hom).2 U.property) F inferInstance
  let e₂ : representedZariskiRestriction B S hS U.obj.left
      (isAlgebraicSpace_yoneda B S hS U.obj.left) N ≅
      restrictToChartScheme B S hS (yoneda.obj U.obj.left)
        (isAlgebraicSpace_yoneda B S hS U.obj.left) N (idEtaleChart B S hS U.obj.left) :=
    restrictToChartIsoRestrictToChartScheme B S hS _ N (selfChart B S hS U.obj.left)
  let eG : (modulePullback B S hS (X := ⟨yoneda.obj Zs, isAlgebraicSpace_yoneda B S hS Zs⟩)
      (Y := X) (ObjectProperty.homMk (yoneda.map cs ≫ U.obj.hom))).obj F ≅
      (modulePullback B S hS (representedSpaceMap B S hS cs)).obj N :=
    ((modulePullbackCompIso B S hS (representedSpaceMap B S hS cs) aU).app F).symm
  restrictToChartIso B S hS _ eG (idEtaleChart B S hS Zs) ≪≫
    restrictToChartIsoRestrictToChartScheme B S hS _ _ (idEtaleChart B S hS Zs) ≪≫
    (nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent cs N
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS aU F
        inferInstance)).some ≪≫
    (Scheme.Modules.pullback _).mapIso (e₁ ≪≫ e₂).symm

/-- Let `ĝ : A ⟶ C` and `ν : V ⟶ C` be morphisms of the site and `v` a point of `V`. A pair of
morphisms of schemes `c : Z ⟶ A` and `a : Z ⟶ Spec 𝒪_{V, v}` lying over `ĝ` and `ν` is compatible
with the structure morphisms to `S`. -/
private theorem comp_inclusion_map_hom_eq_of_comp_eq {A C V : BigFppfOver B S hS} (ĝ : A ⟶ C)
    (ν : V ⟶ C) (v : (BigFppfOver.toScheme B S hS).obj V) {Z : Scheme.{u}}
    (c : Z ⟶ (BigFppfOver.toScheme B S hS).obj A)
    (a : Z ⟶ (BigFppfOver.toScheme B S hS).obj (BigFppfOver.specStalk B S hS V v))
    (h : c ≫ (BigFppfOver.toScheme B S hS).map ĝ =
      a ≫ ((BigFppfOver.toScheme B S hS).obj V).fromSpecStalk v ≫
        (BigFppfOver.toScheme B S hS).map ν) :
    c ≫ B.inclusion.map A.hom = a ≫ B.inclusion.map (BigFppfOver.specStalk B S hS V v).hom := by
  have hw {T₁ T₂ : BigFppfOver B S hS} (g : T₁ ⟶ T₂) :
      (BigFppfOver.toScheme B S hS).map g ≫ B.inclusion.map T₂.hom = B.inclusion.map T₁.hom :=
    (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w g))
  have hSS : B.inclusion.map (BigFppfOver.specStalk B S hS V v).hom =
      ((BigFppfOver.toScheme B S hS).obj V).fromSpecStalk v ≫ B.inclusion.map V.hom := by
    rw [← Over.w (BigFppfOver.specStalkTo B S hS V v), Functor.map_comp]
    exact congrArg (· ≫ B.inclusion.map V.hom) (BigFppfOver.toScheme_map_specStalkTo B S hS V v)
  rw [← hw ĝ, hSS, ← hw ν, ← Category.assoc, h]
  exact congrArg (a ≫ ·) (Category.assoc _ _ _)

/-- For an étale chart `U` of `X` and morphisms `cs : Zs ⟶ U` and `κ : Zs ⟶ Spec 𝒪_{V, v}` of
the site, the image in `|X|` of the closed fibre of `Zs` is the same read on schemes or on
points. -/
private theorem image_pointOfEtaleChart_closedFibre {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : SmallEtale B S hS X) {V Zs : BigFppfOver B S hS}
    (v : (BigFppfOver.toScheme B S hS).obj V) (cs : Zs ⟶ U.obj.left)
    (κ : Zs ⟶ BigFppfOver.specStalk B S hS V v) :
    (fun z => pointOfEtaleChart B S hS U ((BigFppfOver.toScheme B S hS).map cs z)) ''
        ((BigFppfOver.toScheme B S hS).map κ ⁻¹'
          {IsLocalRing.closedPoint (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v)}) =
      pointsMap B S hS (yoneda.obj Zs) (yoneda.map cs ≫ U.obj.hom) ''
        (pointsMap B S hS (yoneda.obj Zs) (yoneda.map κ) ⁻¹'
          {BigFppfOver.specStalkClosedPoint B S hS V v}) := by
  have hgpt (z : (BigFppfOver.toScheme B S hS).obj Zs) :
      pointsMap B S hS (yoneda.obj Zs) (yoneda.map cs ≫ U.obj.hom)
        ((pointsEquivScheme B S hS Zs).symm z) =
        pointOfEtaleChart B S hS U ((BigFppfOver.toScheme B S hS).map cs z) := by
    rw [pointsMap_comp_apply, pointsMap_yoneda_map_symm B S hS cs z]
    rfl
  have hκpt (z : (BigFppfOver.toScheme B S hS).obj Zs) :
      pointsMap B S hS (yoneda.obj Zs) (yoneda.map κ) ((pointsEquivScheme B S hS Zs).symm z) =
          BigFppfOver.specStalkClosedPoint B S hS V v ↔
        (BigFppfOver.toScheme B S hS).map κ z =
          IsLocalRing.closedPoint (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v) := by
    rw [pointsMap_yoneda_map_symm B S hS κ z, BigFppfOver.specStalkClosedPoint]
    exact (pointsEquivScheme B S hS _).symm.injective.eq_iff
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(pointsEquivScheme B S hS Zs).symm z, (hκpt z).2 hz, hgpt z⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨z, rfl⟩ := (pointsEquivScheme B S hS Zs).symm.surjective p
    exact ⟨z, (hκpt z).1 hp, (hgpt z).symm⟩

/-- The point of `yoneda V` given by a point `x` of the scheme `V` maps along `ν : V ⟶ T` to the
point `w` of `yoneda T` lying over `ν x`. -/
private theorem pointsMap_yoneda_map_pointsEquivScheme_symm {V T : BigFppfOver B S hS}
    (ν : V ⟶ T) (x : (BigFppfOver.toScheme B S hS).obj V) (w : points B S hS (yoneda.obj T))
    (h : (BigFppfOver.toScheme B S hS).map ν x = pointsToScheme B S hS T w) :
    pointsMap B S hS (yoneda.obj V) (yoneda.map ν) ((pointsEquivScheme B S hS V).symm x) = w := by
  apply injective_pointsToScheme B S hS T
  rw [pointsToScheme_pointsMap_yoneda]
  exact (congrArg ((BigFppfOver.toScheme B S hS).map ν)
    ((pointsEquivScheme B S hS V).apply_symm_apply x)).trans h

/-- If `Z ⟶ A ×_C T` is étale and `A ⟶ C` is locally of finite type, then `Z ⟶ T` is locally of
finite type. -/
private theorem locallyOfFiniteType_of_etale_pullbackLift {Z A C T : Scheme.{u}} (g : A ⟶ C)
    [LocallyOfFiniteType g] (h : T ⟶ C) (c : Z ⟶ A) (α : Z ⟶ T) (hc : c ≫ g = α ≫ h)
    (het : Etale (pullback.lift c α hc)) : LocallyOfFiniteType α := by
  rw [← pullback.lift_snd c α hc]
  exact MorphismProperty.comp_mem _ _ _ inferInstance inferInstance

/-- **Stacks Project, Tag 0CVW.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`, let
`𝓕` be a quasi-coherent `𝒪_X`-module and let `y ∈ |Y|`, with fibre `F = f^{-1}({y}) ⊆ |X|`.
Assume

1. `f` is of finite type (`hf`),
2. `𝓕` is of finite type (`hFt`), and
3. `𝓕` is flat over `Y` at every point of `F` (`hflat`).

Then there are a scheme `Y'` with a point `y'` and an étale morphism `e : Y' ⟶ Y` sending `y'`
to `y`, an affine scheme `X'` with morphisms `g : X' ⟶ X` and `k : X' ⟶ Spec 𝒪_{Y', y'}` making
the square over `f` commute, such that the induced `X' ⟶ X ×_Y Spec 𝒪_{Y', y'}` is étale, `F`
is the image under `g` of the fibre `X'_{y'}` of `X'` over the closed point of
`Spec 𝒪_{Y', y'}` (so `|X'_{y'}| ⟶ F` is surjective), and `Γ(X', g^*𝓕)` is a free
`𝒪_{Y', y'}`-module, the module structure coming from `k`.

The schemes `Y'`, `Spec 𝒪_{Y', y'}` (`AlgebraicGeometry.BigFppfOver.specStalk`) and `X'` are
objects of the big fppf site of `S`, morphisms of algebraic spaces out of them are morphisms out
of the presheaves they represent, and `Γ(X', g^*𝓕)` is the module of global sections of the
restriction of `g^*𝓕` to the scheme `X'`, its identity chart. -/
@[stacks 0CVW]
theorem exists_etale_affine_free_sections_along_fibre {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsFiniteType B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] (hFt : SheafOfModules.IsFiniteTypeOnSite F)
    (y : points B S hS Y.1)
    (hflat : ∀ x : points B S hS X.1, pointsMap B S hS X.1 f.hom x = y →
      x ∈ flatLocus B S hS X.2 f.hom F) :
    ∃ (Y' : BigFppfOver B S hS) (y' : (BigFppfOver.toScheme B S hS).obj Y')
      (e : yoneda.obj Y' ⟶ Y.1) (X' : BigFppfOver B S hS) (g : yoneda.obj X' ⟶ X.1)
      (k : X' ⟶ BigFppfOver.specStalk B S hS Y' y')
      (hcomm : yoneda.map k ≫ yoneda.map (BigFppfOver.specStalkTo B S hS Y' y') ≫ e =
        g ≫ f.hom),
      IsEtale B S hS e ∧
      pointsMap B S hS (yoneda.obj Y') e ((pointsEquivScheme B S hS Y').symm y') = y ∧
      IsEtale B S hS (pullback.lift (yoneda.map k) g hcomm) ∧
      pointsMap B S hS X.1 f.hom ⁻¹' {y} =
        pointsMap B S hS (yoneda.obj X') g ''
          (pointsMap B S hS (yoneda.obj X') (yoneda.map k) ⁻¹'
            {BigFppfOver.specStalkClosedPoint B S hS Y' y'}) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj X') ∧
      (let M := restrictToChart B S hS (isAlgebraicSpace_yoneda B S hS X')
          ((modulePullback B S hS (X := ⟨yoneda.obj X', isAlgebraicSpace_yoneda B S hS X'⟩)
            (Y := X) (ObjectProperty.homMk g)).obj F)
          (idEtaleChart B S hS X')
       letI : Module (((BigFppfOver.toScheme B S hS).obj Y').presheaf.stalk y') Γ(M, ⊤) :=
         globalSectionsModuleOfSpecBase ((BigFppfOver.toScheme B S hS).map k) M
       Module.Free (((BigFppfOver.toScheme B S hS).obj Y').presheaf.stalk y') Γ(M, ⊤)) := by
  classical
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  -- the source's reduction to affine étale charts, and Stacks 05L1 on them
  obtain ⟨Y₁, q, U, ĝ, hsq, w, hY₁aff, -, hqet, hw, -, hLet, hlft, -, hfibEq, hfree⟩ :=
    exists_affineChart_hasFreeSectionsAlongFibre_chartFibre B S hS f hf F
      (isFiniteTypeOnCharts_of_isFiniteTypeOnSite B S hS X F inferInstance hFt) y hflat
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₁) := hY₁aff
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map ĝ) := hlft
  have : (chartModule B S hS X.2 F U).IsQuasicoherent :=
    isQuasicoherent_restrictToChart B S hS X F inferInstance U
  -- Stacks 05L1 over an affine elementary étale neighbourhood `σ : W ⟶ Y₁`
  obtain ⟨W, σ, wpt, hWaff, hσet, hσw, -, Z', αZ, cZ, hcommZ, hetZ, hcovZ, hZaff, hfreeZ⟩ :=
    hfree.exists_affine
  -- the neighbourhood is an object `V` of the site, étale over `Y₁` by `ν`
  have hWc : B.Contains W := contains_of_locallyOfFiniteType_of_quasiCompact B S hS (Y₀ := Y₁) σ
  let V : BigFppfOver B S hS := BigFppfOver.mk B S hS hWc (σ ≫ B.inclusion.map Y₁.hom)
  let ν : V ⟶ Y₁ := siteHomMk B S hS (T₁ := V) (T₂ := Y₁) σ rfl
  have : Etale ((BigFppfOver.toScheme B S hS).map ν) := hσet
  let x₀ : (BigFppfOver.toScheme B S hS).obj V := wpt
  let SS := BigFppfOver.specStalk B S hS V x₀
  let hs : SS ⟶ Y₁ := BigFppfOver.specStalkTo B S hS V x₀ ≫ ν
  have hTs : (BigFppfOver.toScheme B S hS).map hs = W.fromSpecStalk x₀ ≫ σ := by
    rw [Functor.map_comp, BigFppfOver.toScheme_map_specStalkTo]
    rfl
  -- `Z'` is an object `Zs` of the site over `Spec 𝒪_{V, v}`
  have : LocallyOfFiniteType αZ := locallyOfFiniteType_of_etale_pullbackLift _ _ cZ αZ hcommZ hetZ
  let αZ' : Z' ⟶ (BigFppfOver.toScheme B S hS).obj SS := αZ
  have : LocallyOfFiniteType αZ' := ‹LocallyOfFiniteType αZ›
  have : QuasiCompact αZ' := (inferInstance : QuasiCompact αZ)
  have hZc : B.Contains Z' :=
    contains_of_locallyOfFiniteType_of_quasiCompact B S hS (Y₀ := SS) αZ'
  let Zs : BigFppfOver B S hS := BigFppfOver.mk B S hS hZc (αZ ≫ B.inclusion.map SS.hom)
  let κ : Zs ⟶ SS := siteHomMk B S hS (T₁ := Zs) (T₂ := SS) αZ rfl
  let cs : Zs ⟶ U.obj.left := siteHomMk B S hS (T₁ := Zs) (T₂ := U.obj.left) cZ
    (comp_inclusion_map_hom_eq_of_comp_eq B S hS ĝ ν x₀ cZ αZ' hcommZ)
  have hℓ : cs ≫ ĝ = κ ≫ hs :=
    hom_ext_toScheme B S hS (by rwa [Functor.map_comp, Functor.map_comp, hTs])
  -- the base map `Spec 𝒪_{V, v} ⟶ Y` and the commutative square
  let cg : yoneda.obj SS ⟶ Y.1 :=
    yoneda.map (BigFppfOver.specStalkTo B S hS V x₀) ≫ yoneda.map ν ≫ q
  have hcg : yoneda.map hs ≫ q = cg := by
    rw [Functor.map_comp, Category.assoc]
  have hcomm : yoneda.map κ ≫ cg = (yoneda.map cs ≫ U.obj.hom) ≫ f.hom := by
    rw [← hcg, ← Category.assoc, ← Functor.map_comp, ← hℓ, Functor.map_comp, Category.assoc,
      hsq, Category.assoc]
  refine ⟨V, x₀, yoneda.map ν ≫ q, Zs, yoneda.map cs ≫ U.obj.hom, κ, hcomm, ?_, ?_,
    isEtale_pullbackLift_yoneda_of_etale B S hS f.hom q U.obj.hom ĝ hsq hLet hs hcg cs κ hℓ hcomm
      hTs hcommZ hetZ, ?_, hZaff, ?_⟩
  · -- `(V, v) ⟶ (Y, y)` is étale
    exact isEtale_yoneda_map_comp B S hS ν hσet q ((isEtale_iff_presheaf_of_yoneda B S hS q).2 hqet)
  · rwa [pointsMap_comp_apply, pointsMap_yoneda_map_pointsEquivScheme_symm B S hS ν x₀ w hσw]
  · -- the fibre over `y` is the image of the closed fibre of `X'`
    rw [hfibEq, hcovZ, Set.image_image]
    exact image_pointOfEtaleChart_closedFibre B S hS U x₀ cs κ
  · -- `Γ(X', g^*𝓕)` is free: it is the module of sections Stacks 05L1 produces
    let R : CommRingCat.{u} := .of (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk x₀)
    exact @Module.Free.of_equiv R R _ _ _ _
      (globalSectionsModuleOfSpecBase (R := R) ((BigFppfOver.toScheme B S hS).map κ) _) _ _
      (globalSectionsModuleOfSpecBase (R := R) ((BigFppfOver.toScheme B S hS).map κ) _)
      (RingHom.id R) (RingHom.id R) _ _
      (globalSectionsLinearEquivOfIso (R := R) ((BigFppfOver.toScheme B S hS).map κ)
        (restrictToChartIdModulePullbackIso B S hS F U cs)).symm
      hfreeZ

end AlgebraicGeometry.Space

end
